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

size_t maxnid;
Node **decls;
size_t ndecls;
Node **exportimpls;
size_t nexportimpls;

Node *mknode(Srcloc loc, Ntype nt)
{
    Node *n;

    n = zalloc(sizeof(Node));
    n->nid = maxnid++;
    n->type = nt;
    n->loc = loc;
    return n;
}

Node *mkfile(char *name)
{
    Node *n;

    n = mknode(Zloc, Nfile);
    lappend(&n->file.files, &n->file.nfiles, strdup(name));
    return n;
}

Node *mkuse(Srcloc loc, char *use, int islocal)
{
    Node *n;

    n = mknode(loc, Nuse);
    n->use.name = strdup(use);
    n->use.islocal = islocal;

    return n;
}

Node *mksliceexpr(Srcloc loc, Node *sl, Node *base, Node *off)
{
    if (!base)
        base = mkintlit(loc, 0);
    if (!off)
        off = mkexpr(loc, Omemb, sl, mkname(loc, "len"), NULL);
    return mkexpr(loc, Oslice, sl, base, off, NULL);
}

Node *mkexprl(Srcloc loc, Op op, Node **args, size_t nargs)
{
    Node *n;

    n = mknode(loc, Nexpr);
    n->expr.op = op;
    n->expr.args = args;
    n->expr.nargs = nargs;
    return n;
}

Node *mkexpr(Srcloc loc, Op op, ...)
{
    Node *n;
    va_list ap;
    Node *arg;

    n = mknode(loc, Nexpr);
    n->expr.op = op;
    va_start(ap, op);
    while ((arg = va_arg(ap, Node*)) != NULL)
        lappend(&n->expr.args, &n->expr.nargs, arg);
    va_end(ap);

    return n;
}

Node *mkcall(Srcloc loc, Node *fn, Node **args, size_t nargs) 
{
    Node *n;
    size_t i;

    n = mkexpr(loc, Ocall, fn, NULL);
    for (i = 0; i < nargs; i++)
        lappend(&n->expr.args, &n->expr.nargs, args[i]);
    return n;
}

Node *mkifstmt(Srcloc loc, Node *cond, Node *iftrue, Node *iffalse)
{
    Node *n;

    n = mknode(loc, Nifstmt);
    n->ifstmt.cond = cond;
    n->ifstmt.iftrue = iftrue;
    n->ifstmt.iffalse = iffalse;

    return n;
}

Node *mkloopstmt(Srcloc loc, Node *init, Node *cond, Node *incr, Node *body)
{
    Node *n;

    n = mknode(loc, Nloopstmt);
    n->loopstmt.init = init;
    n->loopstmt.cond = cond;
    n->loopstmt.step = incr;
    n->loopstmt.body = body;

    return n;
}

Node *mkiterstmt(Srcloc loc, Node *elt, Node *seq, Node *body)
{
    Node *n;

    n = mknode(loc, Niterstmt);
    n->iterstmt.elt = elt;
    n->iterstmt.seq = seq;
    n->iterstmt.body = body;

    return n;
}

Node *mkmatchstmt(Srcloc loc, Node *val, Node **matches, size_t nmatches)
{
    Node *n;

    n = mknode(loc, Nmatchstmt);
    n->matchstmt.val = val;
    n->matchstmt.matches = matches;
    n->matchstmt.nmatches = nmatches;
    return n;
}

Node *mkmatch(Srcloc loc, Node *pat, Node *body)
{
    Node *n;

    n = mknode(loc, Nmatch);
    n->match.pat = pat;
    n->match.block = body;
    return n;
}

Node *mkfunc(Srcloc loc, Node **args, size_t nargs, Type *ret, Node *body)
{
    Node *n;
    Node *f;
    size_t i;

    f = mknode(loc, Nfunc);
    f->func.args = args;
    f->func.nargs = nargs;
    f->func.body = body;
    f->func.scope = mkstab();
    f->func.type = mktyfunc(loc, args, nargs, ret);

    for (i = 0; i < nargs; i++)
        putdcl(f->func.scope, args[i]);

    n = mknode(loc, Nlit);
    n->lit.littype = Lfunc;
    n->lit.fnval = f;
    return n;
}

Node *mkblock(Srcloc loc, Stab *scope)
{
    Node *n;

    n = mknode(loc, Nblock);
    n->block.scope = scope;
    return n;
}

Node *mkimplstmt(Srcloc loc, Node *name, Type *t, Node **decls, size_t ndecls)
{
    Node *n;

    n = mknode(loc, Nimpl);
    n->impl.traitname = name;
    n->impl.type = t;
    n->impl.decls = decls;
    n->impl.ndecls = ndecls;
    return n;
}


Node *mkintlit(Srcloc loc, uvlong val)
{
    return mkexpr(loc, Olit, mkint(loc, val), NULL);
}

Node *mklbl(Srcloc loc, char *lbl)
{
    Node *n;

    assert(lbl != NULL);
    n = mknode(loc, Nlit);
    n->lit.littype = Llbl;
    n->lit.lblval = strdup(lbl);
    return mkexpr(loc, Olit, n, NULL);
}

Node *mkstr(Srcloc loc, char *val)
{
    Node *n;

    n = mknode(loc, Nlit);
    n->lit.littype = Lstr;
    n->lit.strval = strdup(val);

    return n;
}

Node *mkint(Srcloc loc, uint64_t val)
{
    Node *n;

    n = mknode(loc, Nlit);
    n->lit.littype = Lint;
    n->lit.intval = val;

    return n;
}

Node *mkchar(Srcloc loc, uint32_t val)
{
    Node *n;

    n = mknode(loc, Nlit);
    n->lit.littype = Lchr;
    n->lit.chrval = val;

    return n;
}

Node *mkfloat(Srcloc loc, double val)
{
    Node *n;

    n = mknode(loc, Nlit);
    n->lit.littype = Lflt;
    n->lit.fltval = val;

    return n;
}

Node *mkidxinit(Srcloc loc, Node *idx, Node *init)
{
    init->expr.idx = idx;
    return init;
}

Node *mkname(Srcloc loc, char *name)
{
    Node *n;

    n = mknode(loc, Nname);
    n->name.name = strdup(name);

    return n;
}

Node *mknsname(Srcloc loc, char *ns, char *name)
{
    Node *n;

    n = mknode(loc, Nname);
    n->name.ns = strdup(ns);
    n->name.name = strdup(name);

    return n;
}

Node *mkdecl(Srcloc loc, Node *name, Type *ty)
{
    Node *n;

    n = mknode(loc, Ndecl);
    n->decl.did = ndecls;
    n->decl.name = name;
    n->decl.type = ty;
    lappend(&decls, &ndecls, n);
    return n;
}

Ucon *mkucon(Srcloc loc, Node *name, Type *ut, Type *et)
{
    Ucon *uc;

    uc = zalloc(sizeof(Ucon));
    uc->loc = loc;
    uc->name = name;
    uc->utype = ut;
    uc->etype = et;
    return uc;
}

Node *mkbool(Srcloc loc, int val)
{
    Node *n;

    n = mknode(loc, Nlit);
    n->lit.littype = Lbool;
    n->lit.boolval = val;

    return n;
}

char *declname(Node *n)
{
    Node *name;
    assert(n->type == Ndecl);
    name = n->decl.name;
    return name->name.name;
}

Type *decltype(Node *n)
{
    assert(n->type == Ndecl);
    return nodetype(n);
}

Type *exprtype(Node *n)
{
    assert(n->type == Nexpr);
    return nodetype(n);
}

Type *nodetype(Node *n)
{
    switch (n->type) {
        case Ndecl:     return n->decl.type;            break;
        case Nexpr:     return n->expr.type;            break;
        case Nlit:      return n->lit.type;             break;
        default:        die("Node %s has no type", nodestr(n->type)); break;
    }
    return NULL;
}

int liteq(Node *a, Node *b)
{
    assert(a->type == Nlit && b->type == Nlit);
    if (a->lit.littype != b->lit.littype)
        return 0;
    if (!tyeq(a->lit.type, b->lit.type))
        return 0;
    switch (a->lit.littype) {
        case Lchr:
            return a->lit.chrval == b->lit.chrval;
        case Lbool:
            return a->lit.boolval == b->lit.boolval;
        case Lint:
            return a->lit.intval == b->lit.intval;
        case Lflt:
            return a->lit.fltval == b->lit.fltval;
        case Lstr:
            return !strcmp(a->lit.strval, b->lit.strval);
        case Lfunc:
            return a->lit.fnval == b->lit.fnval;
        case Llbl:
            return !strcmp(a->lit.lblval, b->lit.lblval);
            break;
    }
    return 0;
}

/* name hashing */
ulong namehash(void *p)
{
    Node *n;

    n = p;
    return strhash(namestr(n)) ^ strhash(n->name.ns);
}

int nameeq(void *p1, void *p2)
{
    Node *a, *b;
    a = p1;
    b = p2;
    if (a == b)
        return 1;

    return streq(namestr(a), namestr(b)) && streq(a->name.ns, b->name.ns);
}

void setns(Node *n, char *ns)
{
    n->name.ns = strdup(ns);
}

Op exprop(Node *e)
{
    assert(e->type == Nexpr);
    return e->expr.op;
}

char *namestr(Node *name)
{
    if (!name)
        return "";
    assert(name->type == Nname);
    return name->name.name;
}

static size_t did(Node *n)
{
    if (n->type == Ndecl) {
        return n->decl.did;
    } else if (n->type == Nexpr) {
        assert(exprop(n) == Ovar);
        return n->expr.did;
    }
    dump(n, stderr);
    die("Can't get did");
    return 0;
}

/* Hashes a Ovar expr or an Ndecl  */
ulong varhash(void *dcl)
{
    /* large-prime hash. meh. */
    return did(dcl) * 366787;
}

/* Checks if the did of two vars are equal */
int vareq(void *a, void *b)
{
    return did(a) == did(b);
}
