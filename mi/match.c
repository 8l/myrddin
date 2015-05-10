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
typedef struct Action Action;

struct Action {
    Node **cap;
    size_t ncap;
    Node **capval;
    size_t ncapval;
    Node *act;
};

struct Dtree {
    Srcloc loc;         /* location that this dtree was made */
    Node  *load;        /* expression value being compared */

    Node *patexpr;      /* the full pattern for this node */
    Node **val;         /* pattern values to compare against */
    size_t nval;

    Dtree **sub;        /* submatch to use if if equal */
    size_t nsub;
    Dtree *any;         /* tree for a wildcard match. */

    Action *act;

    int id;
};

static Dtree *addpat(Dtree *t, Node *pat, Node *val, Action *act);
void dtdump(Dtree *dt, FILE *f);

/* We treat all integer types, boolean types, etc, as having 2^n constructors.
 *
 * since, of course, we can't represent 2^n for 64 bit values, we just get close.
 * If someone tries for that many constructors, we've already lost.
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
static Dtree *mkdtree(Srcloc loc)
{
    Dtree *t;

    t = zalloc(sizeof(Dtree));
    t->id = ndt++;
    t->loc = loc;
    return t;
}

static uint64_t intlitval(Node *lit)
{
    assert(exprop(lit) == Olit);
    lit = lit->expr.args[0];
    assert(lit->lit.littype == Lint);
    return lit->lit.intval;
}

static Node *idxload(Node *val, size_t i)
{
    Node *idx, *load;
    Type *t;

    t = tybase(exprtype(val));
    assert(t->type == Tyarray || t->type == Tyslice);
    idx = mkintlit(val->loc, i);
    idx->expr.type = mktype(val->loc, Tyuint64);
    load = mkexpr(val->loc, Oidx, val, idx, NULL);
    load->expr.type = tybase(exprtype(val))->sub[0];
    return load;
}

static Dtree *addwild(Dtree *t, Node *pat, Node *val, Action *act)
{
    if (t->any)
        return t->any;
    t->any = mkdtree(pat->loc);
    t->any->patexpr = pat;
    lappend(&act->cap, &act->ncap, pat);
    lappend(&act->capval, &act->ncapval, val);
    return t->any;
}

static Dtree *addunion(Dtree *t, Node *pat, Node *val, Action *act)
{
    Node *u, *c;
    Dtree *sub;
    Ucon *uc;
    size_t i;

    if (t->any)
        return t->any;
    if (!t->load) {
        t->load = mkexpr(val->loc, Outag, val, NULL);
        t->load->expr.type = mktype(val->loc, Tyuint32);
    }
    /* if we have the value already... */
    sub = NULL;
    uc = finducon(exprtype(pat), pat->expr.args[0]);
    for (i = 0; i < t->nval; i++) {
        if (intlitval(t->val[i]) == uc->id) {
            if (pat->expr.nargs > 1) {
                u = mkexpr(val->loc, Oudata, val, NULL);
                u->expr.type = exprtype(pat->expr.args[1]);
                return addpat(t->sub[i], pat->expr.args[1], u, act);
            } else {
                return t->sub[i];
            }
        }
    }

    sub = mkdtree(pat->loc);
    sub->patexpr = pat;
    c = mkintlit(pat->loc, uc->id);
    c->expr.type = mktype(pat->loc, Tyuint32);
    lappend(&t->val, &t->nval, c);
    lappend(&t->sub, &t->nsub, sub);
    if (pat->expr.nargs == 2) {
        u = mkexpr(val->loc, Oudata, val, NULL);
        u->expr.type = exprtype(pat->expr.args[1]);
        sub = addpat(sub, pat->expr.args[1], u, act);
    }
    return sub;
}

static Dtree *addatomiclit(Dtree *t, Node *pat, Node *val, Action *act)
{
    Dtree *sub;
    size_t i;

    if (!t->load)
        t->load = val;
    if (t->any)
        return t->any;
    for (i = 0; i < t->nval; i++) {
        if (liteq(t->val[i]->expr.args[0], pat->expr.args[0]))
            return t->sub[i];
    }

    sub = mkdtree(pat->loc);
    sub->patexpr = pat;
    lappend(&t->val, &t->nval, pat);
    lappend(&t->sub, &t->nsub, sub);
    return sub;
}

static Dtree *addstrlit(Dtree *t, Node *pat, Node *val, Action *act)
{
    Node *load, *subpat;
    Node *lit, *len;
    size_t i, n;
    Dtree *rest;

    if (t->any)
        return t->any;
    if (!t->load) {
        load = mkexpr(val->loc, Osllen, val, NULL);
        load->expr.type = mktype(val->loc, Tyuint64);
    }

    lit = pat->expr.args[0];
    n = lit->lit.strval.len;
    len = mkintlit(pat->loc, n);
    len->expr.type = mktype(pat->loc, Tyuint64);
    rest = addatomiclit(t, len, load, act);
    for (i = 0; i < n; i++) {
        load = idxload(val, i);
        subpat = mkintlit(pat->loc, lit->lit.strval.buf[i]);
        subpat->expr.type = mktype(pat->loc, Tybyte);

        rest = addatomiclit(rest, subpat, load, act);
    }
    return rest;
}

static Dtree *addlit(Dtree *t, Node *pat, Node *val, Action *act)
{
    Node *lit;

    assert(exprop(pat) == Olit);
    lit = pat->expr.args[0];
    if (lit->lit.littype == Lstr)
        return addstrlit(t, pat, val, act);
    else
        return addatomiclit(t, pat, val, act);
}

static Dtree *addtup(Dtree *t, Node *pat, Node *val, Action *act)
{
    Node *load, *idx;
    size_t i;

    if (t->any)
        return t->any;
    for (i = 0; i < pat->expr.nargs; i++) {
        idx = mkintlit(pat->loc, i);
        idx->expr.type = mktype(pat->loc, Tyuint64);
        load  = mkexpr(pat->loc, Otupget, val, idx, NULL);
        load->expr.type = exprtype(pat->expr.args[i]);
        t = addpat(t, pat->expr.args[i], load, act);
    }
    return t;
}

static Dtree *addarr(Dtree *t, Node *pat, Node *val, Action *act)
{
    size_t i;

    if (t->any)
        return t->any;
    for (i = 0; i < pat->expr.nargs; i++)
        t = addpat(t, pat->expr.args[i], idxload(pat, i), act);
    return t;
}

static Dtree *addstruct(Dtree *t, Node *pat, Node *val, Action *act)
{
    Node *elt, *memb;
    Type *ty;
    size_t i, j;

    if (t->any)
        return t->any;
    ty = tybase(exprtype(pat));
    for (i = 0; i < pat->expr.nargs; i++) {
        elt = pat->expr.args[i];
        for (j = 0; j < ty->nmemb; j++) {
            if (!strcmp(namestr(elt->expr.idx), declname(ty->sdecls[j]))) {
                memb = mkexpr(pat->loc, Omemb, val, elt->expr.idx, NULL);
                memb->expr.type = exprtype(elt);
                t = addpat(t, pat->expr.args[i], memb, act);
                break;
            }
        }
    }
    return t;
}

static Dtree *addpat(Dtree *t, Node *pat, Node *val, Action *act)
{
    Dtree *ret;
    Node *dcl;

    if (pat == NULL)
        return t;
    switch (exprop(pat)) {
        case Ovar:
            dcl = decls[pat->expr.did];
            if (dcl->decl.isconst)
                ret = addpat(t, dcl->decl.init, val, act);
            else
                ret = addwild(t, pat, val, act);
            break;
        case Oucon:
            ret = addunion(t, pat, val, act);
            break;
        case Olit:
            ret = addlit(t, pat, val, act);
            break;
        case Otup:
            ret = addtup(t, pat, val, act);
            break;
        case Oarr:
            ret = addarr(t, pat, val, act);
            break;
        case Ostruct:
            ret = addstruct(t, pat, val, act);
            break;
        /* FIXME: address patterns.
         * match ptr
         * | &123:      if ptr# == 123
        case Oaddr:
         **/
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
            fatal(dt->patexpr, "unsupported pattern in match statement");
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

static Node *addcaps(Action *act)
{
    Node *e, *blk;
    size_t i;

    blk = act->act;
    for (i = 0; i < act->ncap; i++) {
        e = mkexpr(act->cap[i]->loc, Oasn, act->cap[i], act->capval[i], NULL);
        e->expr.type = exprtype(act->cap[i]);
        linsert(&blk->block.stmts, &blk->block.nstmts, 0, e);
    }
    return blk;
}

static Node *genmatch(Dtree *dt)
{
    Node *tab, *jmp, *lit, *any;
    size_t i, ndst;
    Node **dst;
    
    if (dt->nsub == 0 && dt->act)
        return addcaps(dt->act);

    dst = NULL;
    ndst = 0;
    any = NULL;
    for (i = 0; i < dt->nsub; i++) {
        lappend(&dst, &ndst, genmatch(dt->sub[i]));
    }
    if (dt->any)
        any = genmatch(dt->any);

    if (!dt->load)
        return any;

    lit = mkjtab(dt->loc, dt->val, dt->nval, dst, ndst, any);
    tab = mkexpr(dt->loc, Olit, lit, NULL);
    jmp = mkexpr(dt->loc, Ojtab, dt->load, tab, NULL);
    tab->expr.type = mktype(tab->loc, Tyvoid);
    jmp->expr.type = mktype(tab->loc, Tyvoid);
    return jmp;
}

Node *gensimpmatch(Node *m)
{
    Dtree *t, *leaf;
    size_t i, npat;
    Action *act;
    Node **pat;
    Node *val;

    pat = m->matchstmt.matches;
    npat = m->matchstmt.nmatches;
    val = m->matchstmt.val;
    t = mkdtree(m->loc);
    for (i = 0; i < npat; i++) {
        act = zalloc(sizeof(Action));
        leaf = addpat(t, pat[i]->match.pat, val, act);
        /* TODO: NULL is returned by unsupported patterns. */
        if (!leaf)
            return NULL;
        if (leaf->act)
            fatal(pat[i], "pattern matched by earlier case on line %d", leaf->loc.line);
        act->act = pat[i]->match.block;
        leaf->act = act;
    }
    if (!exhaustivematch(m, t, exprtype(m->matchstmt.val)))
        fatal(m, "nonexhaustive pattern set in match statement");
    //dtdump(t, stdout);
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

    if (dt->load)
        indentf(depth, "LOAD\n");
    if (dt->patexpr) {
        e = dt->patexpr;
        indentf(depth, "%s%s %s : %s\n", iswild ? "WILDCARD " : "", opstr[exprop(e)], dtnodestr(e), tystr(exprtype(e)));
    } 
    if (dt->act)
        for (i = 0; i < dt->act->ncap; i++)
            indentf(depth + 1, "capture %s\n", dtnodestr(dt->act->cap[i]));
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
