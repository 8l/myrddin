#include <stdlib.h>
#include <stdio.h>
#include <stdint.h>
#include <string.h>
#include <assert.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <sys/wait.h>
#include <ctype.h>
#include <fcntl.h>
#include <unistd.h>
#include <regex.h>
#include <err.h>

#include "parse.h"

#include "../config.h"

/* make libparse happy */
Node *file;
char *filename;

/* the name of the output file */
char *libname;
char *binname;
/* additional paths to search for packages */
char **incpaths;
size_t nincpaths;
/* libraries to link against. */
char **libs;
size_t nlibs;

regex_t usepat;

static void usage(char *prog)
{
    printf("%s [-h] [-I path] [-l lib] [-b bin] inputs...\n", prog);
    printf("\t-h\tprint this help\n");
    printf("\t-b bin\tBuild a binary called 'bin'\n");
    printf("\t-l lib\tBuild a library called 'name'\n");
    printf("\t-I path\tAdd 'path' to use search path\n");
}

int hassuffix(char *path, char *suffix)
{
    int pathlen;
    int sufflen;

    pathlen = strlen(path);
    sufflen = strlen(suffix);
    
    if (sufflen > pathlen)
        return 0;
    return !strcmp(&path[pathlen-sufflen], suffix);
}

int isquoted(char *path)
{
    return path[0] == '"' && path[strlen(path) - 1] == '"';
}

char *fromuse(char *path)
{
    char buf[1024];
    /* skip initial quote */
    path++;
    swapsuffix(buf, 1024, path, ".use\"", ".myr");
    return strdup(buf);
}

void printl(char **lst)
{
    printf("\t");
    printf("%s\t", *lst++);
    while (*lst)
        printf("%s ", *lst++);
    printf("\n");
}

void gencmd(char ***cmd, size_t *ncmd, char *bin, char *file, char **extra, size_t nextra)
{
    size_t i;

    *cmd = NULL;
    *ncmd = 0;
    lappend(cmd, ncmd, bin);
    for (i = 0; i < nincpaths; i++) {
        lappend(cmd, ncmd, "-I");
        lappend(cmd, ncmd, incpaths[i]);
    }
    for (i = 0; i < nextra; i++)
        lappend(cmd, ncmd, extra[i]);
    lappend(cmd, ncmd, file);
    lappend(cmd, ncmd, NULL); 
}

int run(char **cmd)
{
    pid_t pid;
    int status;

    printl(cmd);
    pid = fork();
    if (pid == -1) {
        die("Could not fork\n");
    } else if (pid == 0) {
        if (execvp(cmd[0], cmd) == -1)
            err(1, "Failed to exec %s", cmd[0]);
    } else {
        waitpid(pid, &status, 0);
    }
    return WIFEXITED(status) && WEXITSTATUS(status) == 0;
}

int isfresh(char *from, char *to)
{
    struct stat from_sb, to_sb;

    if (stat(from, &from_sb))
        die("Could not find %s\n", from);
    if (stat(to, &to_sb) == -1)
        return 1;

    return from_sb.st_mtime >= to_sb.st_mtime;
}

void getdeps(char *file, char **deps, size_t depsz, size_t *ndeps)
{
    char buf[2048]; /* if you hit this limit, shoot yourself */

    regmatch_t m[2];
    size_t i;
    FILE *f;

    f = fopen(file, "r");
    if (!f)
        die("Could not open file %s\n", file);

    i = 0;
    while (fgets(buf, sizeof buf, f)) {
        if (regexec(&usepat, buf, 2, m, 0) == REG_NOMATCH)
            continue;
        if (i == depsz)
            die("Too many deps for file %s\n", file);
        deps[i++] = strdupn(&buf[m[1].rm_so], m[1].rm_eo - m[1].rm_so);
    }
    *ndeps = i;
}

void compile(char *file)
{
    size_t i, ndeps;
    char **cmd;
    size_t ncmd;
    char *localdep;
    char *deps[512];
    char buf[1024];
    char *extra[2] = {"-o", "" /* filename */};

    if (hassuffix(file, ".myr")) {
        getdeps(file, deps, 512, &ndeps);
        for (i = 0; i < ndeps; i++) {
            if (isquoted(deps[i])) {
                localdep = fromuse(deps[i]);
                compile(localdep);
                free(localdep);
            } else {
                lappend(&libs, &nlibs, deps[i]);
            }
        }
        swapsuffix(buf, sizeof buf, file, ".myr", ".use");
        if (isfresh(file, buf)) {
            gencmd(&cmd, &ncmd, "muse", file, NULL, 0);
            run(cmd);
        }

        swapsuffix(buf, sizeof buf, file, ".myr", ".o");
        if (isfresh(file, buf)) {
            gencmd(&cmd, &ncmd, "6m", file, NULL, 0);
            run(cmd);
        }
    } else if (hassuffix(file, ".s")) {
        swapsuffix(buf, sizeof buf, file, ".s", ".o");
        if (isfresh(file, buf)) {
            extra[1] = buf;
            gencmd(&cmd, &ncmd, "as", file, extra, 2);
            run(cmd);
        }
    }
}

void mergeuse(char **files, size_t nfiles)
{
    char **args;
    size_t i, nargs;
    char buf[1024];

    args = NULL;
    nargs = 0;
    lappend(&args, &nargs, strdup("muse"));
    lappend(&args, &nargs, strdup("-mo"));
    lappend(&args, &nargs, strdup(libname));
    for (i = 0; i < nfiles; i++) {
        if (hassuffix(files[i], ".myr"))
            swapsuffix(buf, sizeof buf, files[i], ".myr", ".o");
        else if (hassuffix(files[i], ".s"))
            swapsuffix(buf, sizeof buf, files[i], ".s", ".o");
        else
            die("Unknown file type %s\n", files[i]);
        lappend(&args, &nargs, strdup(buf));
    }
    lappend(&args, &nargs, NULL);

    run(args);

    for (i = 0; i < nargs; i++)
        free(args[i]);
    lfree(&args, &nargs);
}

void archive(char **files, size_t nfiles)
{
    char **args;
    size_t i, nargs;
    char buf[1024];

    args = NULL;
    nargs = 0;
    snprintf(buf, sizeof buf, "lib%s.a", libname);
    lappend(&args, &nargs, strdup("ar"));
    lappend(&args, &nargs, strdup("-rcs"));
    lappend(&args, &nargs, strdup(buf));
    for (i = 0; i < nfiles; i++) {
        if (hassuffix(files[i], ".myr"))
            swapsuffix(buf, sizeof buf, files[i], ".myr", ".o");
        else if (hassuffix(files[i], ".s"))
            swapsuffix(buf, sizeof buf, files[i], ".s", ".o");
        else
            die("Unknown file type %s\n", files[i]);
        lappend(&args, &nargs, strdup(buf));
    }
    lappend(&args, &nargs, NULL);

    run(args);

    for (i = 0; i < nargs; i++)
        free(args[i]);
    lfree(&args, &nargs);
}

void linkobj(char **files, size_t nfiles)
{
    char **args;
    size_t i, nargs;
    char buf[1024];

    if (!binname)
        binname = "a.out";

    args = NULL;
    nargs = 0;
    lappend(&args, &nargs, strdup("ld"));
    lappend(&args, &nargs, strdup("-o"));
    lappend(&args, &nargs, strdup(binname));
    for (i = 0; i < nfiles; i++) {
        if (hassuffix(files[i], ".myr"))
            swapsuffix(buf, sizeof buf, files[i], ".myr", ".o");
        else if (hassuffix(files[i], ".s"))
            swapsuffix(buf, sizeof buf, files[i], ".s", ".o");
        else
            die("Unknown file type %s\n", files[i]);
        lappend(&args, &nargs, strdup(buf));
    }
    lappend(&args, &nargs, strdup("-L"));
    snprintf(buf, sizeof buf, "%s%s", Instroot, "/myr/lib");
    lappend(&args, &nargs, strdup(buf));
    for (i = 0; i < nincpaths; i++) {
        lappend(&args, &nargs, strdup("-L"));
        lappend(&args, &nargs, strdup(incpaths[i]));
    }
    for (i = 0; i < nlibs; i++) {
        lappend(&args, &nargs, strdup("-l"));
        lappend(&args, &nargs, strdup(libs[i]));
    }
    lappend(&args, &nargs, NULL);

    run(args);

    for (i = 0; i < nargs; i++)
        free(args[i]);
    lfree(&args, &nargs);
}

int main(int argc, char **argv)
{
    int opt;
    int i;

    while ((opt = getopt(argc, argv, "hb:l:I:")) != -1) {
        switch (opt) {
            case 'b':
                binname = optarg;
                break;
            case 'l':
                libname = optarg;
                break;
            case 'I':
                lappend(&incpaths, &nincpaths, optarg);
                break;
            case 'h':
                usage(argv[0]);
                exit(0);
                break;
            default:
                usage(argv[0]);
                exit(0);
                break;
        }
    }

    if (libname && binname)
        die("Can't specify both library and binary names");

    regcomp(&usepat, "^[[:space:]]*use[[:space:]]+([^[:space:]]+)", REG_EXTENDED);
    for (i = optind; i < argc; i++)
        compile(argv[i]);
    if (libname) {
        mergeuse(&argv[optind], argc - optind);
        archive(&argv[optind], argc - optind);
    } else {
        linkobj(&argv[optind], argc - optind);
    }

    return 0;
}
