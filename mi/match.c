#include <stdlib.h>
#include <stdio.h>
#include <inttypes.h>
#include <stdarg.h>
#include <ctype.h>
#include <string.h>
#include <assert.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <unistd.h>

#include "parse.h"
#include "mi.h"

typedef struct Dtree Dtree;
struct Dtree {
    /* If the values are equal, go to 'sub'. If 'val' is null, anything matches. */
    Node *patexpr;      /* the full pattern for this node */
    Node **val;         /* pattern values to compare against */
    size_t nval;
    Node **load;        /* expression value being compared */
    size_t nload;
    Dtree **sub;        /* submatch to use if if equal */
    size_t nsub;
    Dtree *any;         /* tree for a wildcard match. */

    /* captured variables and action */
    Node **cap;
    size_t ncap;
    Node *act;

    int id;
};

static Dtree *addpat(Dtree *t, Node *pat, Node *val, Node ***cap, size_t *ncap);
void dtdump(Dtree *dt, FILE *f);

/* We treat all integer types, boolean types, etc, as having 2^n constructors.
 *
 * since, of course, we can't represent all of the constructors for 64 bit
 * integers using 64 bit values, we just approximate it. We'd have failed (run
 * out of memory, etc) long before getting to this code if we actually had that
 * many branches of the switch statements anyways.
 */
static size_t nconstructors(Type *t)
{
    if (!t)
        return 0;

    t = tybase(t);
    switch (t->type) {
        case Tyvoid:    return 0;               break;
        case Tybool:    return 2;               break;
        case Tychar:    return 0x10ffff;        break;

        /* signed ints */
        case Tyint8:    return 0x100;           break;
        case Tyint16:   return 0x10000;         break;
        case Tyint32:   return 0x100000000;     break;
        case Tyint:     return 0x100000000;     break;
        case Tylong:    return ~0ull;           break;
        case Tyint64:   return ~0ull;           break;

        /* unsigned ints */
        case Tybyte:    return 0x100;           break;
        case Tyuint8:   return 0x100;           break;
        case Tyuint16:  return 0x10000;         break;
        case Tyuint32:  return 0x100000000;     break;
        case Tyuint:    return 0x100000000;     break;
        case Tyulong:   return ~0ull;           break;
        case Tyuint64:  return ~0ull;           break;

        /* floats */
        case Tyflt32:   return ~0ull;           break;
        case Tyflt64:   return ~0ull;           break;

        /* complex types */
        case Typtr:     return 1;       break;
        case Tyfunc:    return 0;       break;
        case Tyarray:   return 1;       break;
        case Tytuple:   return 1;       break;
        case Tystruct:  return 1;
        case Tyunion:   return t->nmemb;        break;
        case Tyslice:   return ~0ULL;   break;
        case Tyvar: case Typaram: case Tyunres: case Tyname:
        case Tybad: case Tyvalist: case Tygeneric: case Ntypes:
            die("Invalid constructor type %s in match", tystr(t));
            break;
    }
    return 0;
}

static int ndt;
static Dtree *mkdtree()
{
    Dtree *t;

    t = zalloc(sizeof(Dtree));
    t->id = ndt++;
    return t;
}

static Dtree *addwild(Dtree *t, Node *pat, Node *val, Node ***cap, size_t *ncap)
{
    if (t->any)
        return t->any;
    t->any = mkdtree();
    t->any->patexpr = pat;
    lappend(cap, ncap, pat);
    return t->any;
}

static Dtree *addunion(Dtree *t, Node *pat, Node *val, Node ***cap, size_t *ncap)
{
    Dtree *sub;
    size_t i;

    if (t->any)
        return t->any;
    /* if we have the value already... */
    sub = NULL;
    for (i = 0; i < t->nval; i++) {
        if (nameeq(t->val[i], pat->expr.args[0])) {
            if (pat->expr.nargs > 1)
                return addpat(t->sub[i], pat->expr.args[1], NULL, cap, ncap);
            else
                return t->sub[i];
        }
    }

    sub = mkdtree();
    sub->patexpr = pat;
    lappend(&t->val, &t->nval, pat->expr.args[0]);
    lappend(&t->sub, &t->nsub, sub);
    if (pat->expr.nargs == 2)
        sub = addpat(sub, pat->expr.args[1], NULL, cap, ncap);
    return sub;
}

static Dtree *addlit(Dtree *t, Node *pat, Node *val, Node ***cap, size_t *ncap)
{
    Dtree *sub;
    size_t i;

    if (t->any)
        return t->any;
    for (i = 0; i < t->nval; i++) {
        if (liteq(t->val[i]->expr.args[0], pat->expr.args[0]))
            return t->sub[i];
    }

    sub = mkdtree();
    sub->patexpr = pat;
    lappend(&t->val, &t->nval, pat);
    lappend(&t->sub, &t->nsub, sub);
    return sub;
}

static Dtree *addtup(Dtree *t, Node *pat, Node *val, Node ***cap, size_t *ncap)
{
    size_t i;

    if (t->any)
        return t->any;
    for (i = 0; i < pat->expr.nargs; i++)
        t = addpat(t, pat->expr.args[i], NULL, cap, ncap);
    return t;
}

static Dtree *addarr(Dtree *t, Node *pat, Node *val, Node ***cap, size_t *ncap)
{
    size_t i;

    if (t->any)
        return t->any;
    for (i = 0; i < pat->expr.nargs; i++)
        t = addpat(t, pat->expr.args[i], NULL, cap, ncap);
    return t;
}

static Dtree *addstruct(Dtree *t, Node *pat, Node *val, Node ***cap, size_t *ncap)
{
    Node *elt;
    size_t i, j;

    if (t->any)
        return t->any;
    for (i = 0; i < pat->expr.nargs; i++) {
        elt = pat->expr.args[i];
        for (j = 0; j < t->nval; j++) {
            if (!strcmp(namestr(elt->expr.idx), namestr(t->val[j]->expr.idx)))
                t = addpat(t, pat->expr.args[i], NULL, cap, ncap);
            break;
        }
    }
    return t;
}

static Dtree *addpat(Dtree *t, Node *pat, Node *val, Node ***cap, size_t *ncap)
{
    Dtree *ret;
    Node *dcl;

    if (pat == NULL)
        return t;
    switch (exprop(pat)) {
        case Ovar:
            dcl = decls[pat->expr.did];
            if (dcl->decl.isconst)
                ret = addpat(t, dcl->decl.init, val, cap, ncap);
            else
                ret = addwild(t, pat, val, cap, ncap);
            break;
        case Oucon:
            ret = addunion(t, pat, val, cap, ncap);
            break;
        case Olit:
            ret = addlit(t, pat, val, cap, ncap);
            break;
        case Otup:
            ret = addtup(t, pat, val, cap, ncap);
            break;
        case Oarr:
            ret = addarr(t, pat, val, cap, ncap);
            break;
        case Ostruct:
            ret = addstruct(t, pat, val, cap, ncap);
            break;
        default:
            ret = NULL;
            fatal(pat, "unsupported pattern %s of type %s", opstr[exprop(pat)], tystr(exprtype(pat)));
            break;
    }
    return ret;
}

static int isexhaustive(Dtree *dt)
{
    Type *subt;
    size_t i;

    if (dt->any)
        return 1;

    if (dt->nsub > 0) {
        subt = tybase(exprtype(dt->sub[0]->patexpr));
        if (dt->nsub != nconstructors(subt))
            return 0;
    }
    switch (exprop(dt->patexpr)) {
        case Ovar:
            return 1;
        case Olit:
            return 1;
        case Oucon:
            for (i = 0; i < dt->nsub; i++)
                if (!isexhaustive(dt->sub[i]))
                    return 0;
            return 1;
            break;
        case Otup:
            for (i = 0; i < dt->nsub; i++)
                if (!isexhaustive(dt->sub[i]))
                    return 0;
            return 1;
            break;
        case Oarr:
            for (i = 0; i < dt->nsub; i++)
                if (!isexhaustive(dt->sub[i]))
                    return 0;
            return 1;
            break;
        case Ostruct:
            for (i = 0; i < dt->nsub; i++)
                if (!isexhaustive(dt->sub[i]))
                    return 0;
            return 1;
            break;
        default:
            die("Invalid pattern in exhaustivenes check. BUG.");
            break;
    }
    return 0;
}

static int exhaustivematch(Node *m, Dtree *t, Type *tt)
{
    size_t i;

    if (t->any)
        return 1;
    if (t->nsub != nconstructors(tt))
        return 0;
    for (i = 0; i < t->nsub; i++)
        if (!isexhaustive(t->sub[i]))
            return 0;
    return 1;
}

static Node *genmatch(Dtree *dt)
{
    return NULL;
}

Node *gensimpmatch(Node *m)
{
    Dtree *t, *leaf;
    Node **pat, **cap;
    size_t npat, ncap;
    size_t i;

    pat = m->matchstmt.matches;
    npat = m->matchstmt.nmatches;
    t = mkdtree();
    for (i = 0; i < npat; i++) {
        cap = NULL;
        ncap = 0;
        leaf = addpat(t, pat[i]->match.pat, NULL, &cap, &ncap);
        /* TODO: NULL is returned by unsupported patterns. */
        if (!leaf)
            return NULL;
        if (leaf->act)
            fatal(pat[i], "pattern matched by earlier case on line %d", leaf->act->loc.line);
        leaf->act = pat[i]->match.block;
        leaf->cap = cap;
        leaf->ncap = ncap;
    }
    if (!exhaustivematch(m, t, exprtype(m->matchstmt.val)))
        fatal(m, "nonexhaustive pattern set in match statement");
    return genmatch(t);
}

char *dtnodestr(Node *n)
{
    switch (exprop(n)) {
        case Ovar:
            return namestr(n->expr.args[0]);
        case Olit:
            return litstr[n->expr.args[0]->lit.littype];
        case Oucon:
            return namestr(n->expr.args[0]);
        case Otup:
            return "tuple";
        case Oarr:
            return "array";
        case Ostruct:
            return "struct";
        default:
            die("Invalid pattern in exhaustivenes check. BUG.");
            break;
    }
    return "???";
}

void dtdumpnode(Dtree *dt, FILE *f, int depth, int iswild)
{
    Node *e;
    size_t i;
    if (dt->patexpr) {
        e = dt->patexpr;
        indentf(depth, "%s%s %s : %s\n", iswild ? "WILDCARD " : "", opstr[exprop(e)], dtnodestr(e), tystr(exprtype(e)));
    } 
    if (dt->cap)
        for (i = 0; i < dt->ncap; i++)
            indentf(depth + 1, "capture %s\n", dtnodestr(dt->cap[i]));
    if (dt->act)
        indentf(depth + 1, "action\n");
    for (i = 0; i < dt->nsub; i++)
        dtdumpnode(dt->sub[i], f, depth + 1, 0);
    if (dt->any)
        dtdumpnode(dt->any, f, depth + 1, 1);
}

void dtdump(Dtree *dt, FILE *f)
{
    dtdumpnode(dt, f, 0, 0);
}
