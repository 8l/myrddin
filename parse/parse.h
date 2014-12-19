#ifdef __GNUC__
#	define FATAL __attribute__((noreturn))
#else
#	define FATAL
#endif

typedef uint8_t         byte;
typedef unsigned int    uint;
typedef unsigned long   ulong;
typedef long long       vlong;
typedef unsigned long long uvlong;

typedef struct Srcloc Srcloc;

typedef struct Bitset Bitset;
typedef struct Htab Htab;
typedef struct Optctx Optctx;
typedef struct Str Str;

typedef struct Tok Tok;
typedef struct Node Node;
typedef struct Ucon Ucon;
typedef struct Stab Stab;

typedef struct Type Type;
typedef struct Trait Trait;

typedef enum {
#define O(op, pure) op,
#include "ops.def"
    Numops,
#undef O
} Op;

typedef enum {
#define N(nt) nt,
#include "nodes.def"
#undef N
} Ntype;

typedef enum {
#define L(lt) lt,
#include "lits.def"
#undef L
} Littype;

typedef enum {
#define Ty(t, n) t,
#include "types.def"
#undef Ty
    Ntypes
} Ty;

typedef enum {
#define Tc(c, n) c,
#include "trait.def"
#undef Tc
    Ntraits
} Tc;

#define Zloc ((Srcloc){-1, 0})

struct Srcloc {
    int line;
    int file;
};

struct Str {
    size_t len;
    char *buf;
};

typedef enum {
    Visintern,
    Visexport,
    Vishidden,
    Visbuiltin,
} Vis;

typedef enum {
    Dclconst = 1 << 0,
    Dclextern = 1 << 1,
} Dclflags;

struct Bitset {
    size_t nchunks;
    size_t *chunks;
};

struct Htab {
    size_t nelt;
    size_t sz;
    ulong (*hash)(void *k);
    int (*cmp)(void *a, void *b);
    void **keys;
    void **vals;
    ulong *hashes;
    char  *dead;
};

struct Tok {
    int type;
    Srcloc loc;
    char *id;

    /* values parsed out */
    vlong intval;
    Ty inttype; /* for explicitly specified suffixes */
    double fltval;
    uint32_t chrval;
    Str strval;
};

struct Stab {
    Stab *super;
    Node *name;

    /* Contents of stab.
     * types and values are in separate namespaces. */
    Htab *dcl;
    Htab *closure;      /* the syms we close over */
    Htab *ns;           /* namespaces */
    Htab *ty;           /* types */
    Htab *tr;           /* traits */
    Htab *uc;           /* union constructors */
    Htab *impl;         /* trait implementations: really a set of implemented traits. */
};

struct Type {
    Ty type;
    int tid;
    Srcloc loc;
    Vis vis;

    int resolved;       /* Have we resolved the subtypes? Prevents infinite recursion. */
    int fixed;          /* Have we fixed the subtypes? Prevents infinite recursion. */

    Bitset *traits;      /* the type constraints matched on this type */
    Node **traitlist;    /* The names of the constraints on the type. Used to fill the bitset */
    size_t ntraitlist;   /* The length of the constraint list above */

    Type **param;       /* Tyname: type parameters that match the type args */
    size_t nparam;      /* Tyname: count of type parameters */
    Type **arg;         /* Tyname: type arguments instantiated */
    size_t narg;        /* Tyname: count of type arguments */
    Type **inst;        /* Tyname: instances created */
    size_t ninst;       /* Tyname: count of instances created */

    Type **sub;         /* sub-types; shared by all composite types */
    size_t nsub;        /* For compound types */
    size_t nmemb;       /* for aggregate types (struct, union) */
    union {
        Node *name;     /* Tyname: unresolved name. Tyalias: alias name */
        Node *asize;    /* array size */
        char *pname;    /* Typaram: name of type parameter */
        Node **sdecls;  /* Tystruct: decls in struct */
        Ucon **udecls;  /* Tyunion: decls in union */
    };
    char  issynth;       /* Tyname: whether this is synthesized or not */
    char  ishidden;      /* Tyname: whether this is hidden or not */
    char  ispkglocal;    /* Tyname: whether this is package local or not */
};

struct Ucon {
    Srcloc loc;
    size_t id;  /* unique id */
    int synth;  /* is it generated? */
    Node *name; /* ucon name */
    Type *utype;        /* type of the union this is an element of */
    Type *etype;        /* type for the element */
};

struct Trait {
    int uid;            /* unique id */
    Vis vis;
    int isproto;        /* is it a prototype (for exporting purposes) */
    int ishidden;       /* should user code be able to use this? */
    Node *name;         /* the name of the trait */
    Type *param;        /* the type parameter */
    Node **memb;        /* type must have these members */
    size_t nmemb;
    Node **funcs;       /* and declare these funcs */
    size_t nfuncs;
};

struct Node {
    Srcloc loc;
    Ntype type;
    int nid;
    union {
        struct {
            char  **files;
            size_t nfiles;
            size_t nuses;
            Node **uses;
            size_t nlibdeps;
            char **libdeps;
            size_t nstmts;
            Node **stmts;
            Stab  *globls;
        } file;

        struct {
            Op op;
            Type *type;
            int isconst;
            size_t did; /* for Ovar, we want a mapping to the decl id */
            size_t nargs;
            Node *idx; /* used when this is in an indexed initializer */
            Node **args;
        } expr;

        struct {
            char *ns;
            char *name;
        } name;

        struct {
            int islocal;
            char *name;
        } use;

        struct {
            Littype littype;
            Type    *type;
            size_t   nelt;
            union {
                uvlong   intval;
                double   fltval;
                uint32_t chrval;
                Str      strval;
                char    *lblval;
                int      boolval;
                Node    *fnval;
            };
        } lit;

        struct {
            Node *init;
            Node *cond;
            Node *step;
            Node *body;
        } loopstmt;

        struct {
            Node *elt;
            Node *seq;
            Node *body;
        } iterstmt;

        struct {
            Node *cond;
            Node *iftrue;
            Node *iffalse;
        } ifstmt;

        struct {
            Node *val;
            size_t nmatches;
            Node **matches;
        } matchstmt;

        struct {
            Node *pat;
            Node *block;
        } match;

        struct {
            Stab *scope;
            size_t nstmts;
            Node **stmts;
        } block;

        struct {
            size_t did;
            Node *name;
            Type *type;
            Node *init;
            /* 
             If we have a link to a trait, we should only look it up
             when specializing, but we should not create a new decl
             node for it. That will be done when specializing the
             impl.
            */
            Trait *trait;
            char  vis;
            char  isglobl;
            char  isconst;
            char  isgeneric;
            char  isextern;
            char  ispkglocal;
            char  ishidden;
            char  isimport;
            char  isnoret;
            char  isexportinit;
        } decl;

        struct {
            long  uid;
            Node *name;
            Type *elt;
            Type *alt;
        } uelt;

        struct {
            Stab *scope;
            Type *type;
            size_t nargs;
            Node **args;
            Node *body;
        } func;

        struct {
            Node *name;
            size_t traitid;

            Node **funcs;
            size_t nfuncs;
            Node **membs;
            size_t nmembs;
        } trait;

        struct {
            Node *traitname;
            Trait *trait;
            Type *type;
            Node **decls;
            size_t ndecls;
            Vis vis;
            char isproto;
        } impl;
    };
};

struct Optctx {
    /* public exports */
    char *optarg;
    char **args;
    size_t nargs;

    /* internal state */
    char *optstr;
    char **optargs;
    size_t noptargs;
    size_t argidx;
    int optdone;    /* seen -- */
    int finished;
    char *curarg;
};

/* globals */
extern Srcloc curloc;
extern char *filename;
extern Tok *curtok;     /* the last token we tokenized */
extern Node *file;      /* the current file we're compiling */
extern Type **tytab;    /* type -> type map used by inference. size maintained by type creation code */
extern Type **types;
extern size_t ntypes;
extern Trait **traittab;  /* int -> trait map */
extern size_t ntraittab;
extern Node **decls;    /* decl id -> decl map */
extern size_t ndecls;
extern Node **exportimpls;
extern size_t nexportimpls;
extern size_t maxnid;      /* the maximum node id generated so far */

extern int ispureop[];

/* data structures */
Bitset *mkbs(void);
void    bsfree(Bitset *bs);
Bitset *bsdup(Bitset *bs);
Bitset *bsclear(Bitset *bs);
void delbs(Bitset *bs);
void bsput(Bitset *bs, size_t elt);
void bsdel(Bitset *bs, size_t elt);
void bsunion(Bitset *a, Bitset *b);
void bsintersect(Bitset *a, Bitset *b);
void bsdiff(Bitset *a, Bitset *b);
int  bseq(Bitset *a, Bitset *b);
int  bsissubset(Bitset *set, Bitset *sub);
int  bsisempty(Bitset *set);
int  bsiter(Bitset *bs, size_t *elt);
size_t bsmax(Bitset *bs);
size_t bscount(Bitset *bs);
/* inline for speed */
static inline int bshas(Bitset *bs, size_t elt)
{
    if (elt >= bs->nchunks*8*sizeof(size_t))
        return 0;
    return (bs->chunks[elt/(8*sizeof(size_t))] & (1ULL << (elt % (8*sizeof(size_t))))) != 0;
}

Htab *mkht(ulong (*hash)(void *key), int (*cmp)(void *k1, void *k2));
void htfree(Htab *ht);
int htput(Htab *ht, void *k, void *v);
void htdel(Htab *ht, void *k);
void *htget(Htab *ht, void *k);
int hthas(Htab *ht, void *k);
void **htkeys(Htab *ht, size_t *nkeys);
/* useful key types */
int liteq(Node *a, Node *b);
ulong strhash(void *key);
int streq(void *a, void *b);
ulong strlithash(void *key);
int strliteq(void *a, void *b);
ulong ptrhash(void *key);
int ptreq(void *a, void *b);
ulong inthash(uint64_t key);
int inteq(uint64_t a, uint64_t b);
ulong tyhash(void *t);
int tyeq(void *a, void *b);
ulong namehash(void *t);
int nameeq(void *a, void *b);

/* util functions */
void *zalloc(size_t size);
void *xalloc(size_t size);
void *zrealloc(void *p, size_t oldsz, size_t size);
void *xrealloc(void *p, size_t size);
void die(char *msg, ...) FATAL;
void fatal(Node *n, char *fmt, ...) FATAL;
void lfatal(Srcloc l, char *fmt, ...) FATAL;
void lfatalv(Srcloc l, char *fmt, va_list ap) FATAL;
char *strdupn(char *s, size_t len);
char *strjoin(char *u, char *v);
void *memdup(void *mem, size_t len);

/* parsing etc */
void tokinit(char *file);
int yylex(void);
int yyparse(void);

/* stab creation */
Stab *mkstab(void);

void putns(Stab *st, Stab *scope);
void puttype(Stab *st, Node *n, Type *ty);
void puttrait(Stab *st, Node *n, Trait *trait);
void putimpl(Stab *st, Node *impl);
void updatetype(Stab *st, Node *n, Type *t);
void putdcl(Stab *st, Node *dcl);
void forcedcl(Stab *st, Node *dcl);
void putucon(Stab *st, Ucon *uc);

Stab *getns(Stab *st, Node *n);
Stab *getns_str(Stab *st, char *n);
Node *getdcl(Stab *st, Node *n);
Type *gettype_l(Stab *st, Node *n);
Type *gettype(Stab *st, Node *n);
Node *getimpl(Stab *st, Node *impl);
Trait *gettrait(Stab *st, Node *n);
Ucon *getucon(Stab *st, Node *n);

Stab *curstab(void);
void pushstab(Stab *st);
void popstab(void);

/* type creation */
void tyinit(Stab *st); /* sets up built in types */

Type *mktype(Srcloc l, Ty ty);
Type *tydup(Type *t); /* shallow duplicate; all subtypes/members/... kept */
Type *mktyvar(Srcloc l);
Type *mktyparam(Srcloc l, char *name);
Type *mktyname(Srcloc l, Node *name, Type **params, size_t nparams, Type *base);
Type *mktyunres(Srcloc l, Node *name, Type **params, size_t nparams);
Type *mktyarray(Srcloc l, Type *base, Node *sz);
Type *mktyslice(Srcloc l, Type *base);
Type *mktyidxhack(Srcloc l, Type *base);
Type *mktyptr(Srcloc l, Type *base);
Type *mktytuple(Srcloc l, Type **sub, size_t nsub);
Type *mktyfunc(Srcloc l, Node **args, size_t nargs, Type *ret);
Type *mktystruct(Srcloc l, Node **decls, size_t ndecls);
Type *mktyunion(Srcloc l, Ucon **decls, size_t ndecls);
Trait *mktrait(Srcloc l, Node *name, Type *param, Node **memb, size_t nmemb, Node **funcs, size_t nfuncs, int isproto);
Type *mktylike(Srcloc l, Ty ty); /* constrains tyvar t like it was builtin ty */
int   istysigned(Type *t);
int   istyunsigned(Type *t);
int   istyfloat(Type *t);
int   istyprimitive(Type *t);
int   isgeneric(Type *t);
int   hasparams(Type *t);

/* type manipulation */
Type *tybase(Type *t);
char *tyfmt(char *buf, size_t len, Type *t);
char *tystr(Type *t);

int hastrait(Type *t, Trait *c);
int settrait(Type *t, Trait *c);
int traiteq(Type *t, Trait **traits, size_t len);
int traitfmt(char *buf, size_t len, Type *t);
char *traitstr(Type *t);

/* node creation */
Node *mknode(Srcloc l, Ntype nt);
Node *mkfile(char *name);
Node *mkuse(Srcloc l, char *use, int islocal);
Node *mksliceexpr(Srcloc l, Node *sl, Node *base, Node *off);
Node *mkexprl(Srcloc l, Op op, Node **args, size_t nargs);
Node *mkexpr(Srcloc l, Op op, ...); /* NULL terminated */
Node *mkcall(Srcloc l, Node *fn, Node **args, size_t nargs);
Node *mkifstmt(Srcloc l, Node *cond, Node *iftrue, Node *iffalse);
Node *mkloopstmt(Srcloc l, Node *init, Node *cond, Node *incr, Node *body);
Node *mkiterstmt(Srcloc l, Node *elt, Node *seq, Node *body);
Node *mkmatchstmt(Srcloc l, Node *val, Node **matches, size_t nmatches);
Node *mkmatch(Srcloc l, Node *pat, Node *body);
Node *mkblock(Srcloc l, Stab *scope);
Node *mkimplstmt(Srcloc l, Node *name, Type *type, Node **impls, size_t nimpls);
Node *mkintlit(Srcloc l, uvlong val);
Node *mkidxinit(Srcloc l, Node *idx, Node *init);

Node *mkbool(Srcloc l, int val);
Node *mkint(Srcloc l, uint64_t val);
Node *mkchar(Srcloc l, uint32_t val);
Node *mkstr(Srcloc l, Str str);
Node *mkfloat(Srcloc l, double flt);
Node *mkfunc(Srcloc l, Node **args, size_t nargs, Type *ret, Node *body);
Node *mkname(Srcloc l, char *name);
Node *mknsname(Srcloc l, char *ns, char *name);
Node *mkdecl(Srcloc l, Node *name, Type *ty);
Node *mklbl(Srcloc l, char *lbl);
Node *mkslice(Srcloc l, Node *base, Node *off);
Ucon *mkucon(Srcloc l, Node *name, Type *ut, Type *uet);

/* node util functions */
char *namestr(Node *name);
char *declname(Node *n);
Type *decltype(Node *n);
Type *exprtype(Node *n);
Type *nodetype(Node *n);
void addstmt(Node *file, Node *stmt);
void setns(Node *n, char *ns);
void updatens(Stab *st, char *ns);
ulong varhash(void *dcl);
int vareq(void *a, void *b);
Op exprop(Node *n);

/* specialize generics */
Node *specializedcl(Node *n, Type *to, Node **name);
Type *tyspecialize(Type *t, Htab *tymap, Htab *delayed);
Node *genericname(Node *n, Type *t);

/* usefiles */
int  loaduse(FILE *f, Stab *into, Vis vis);
void readuse(Node *use, Stab *into, Vis vis);
void writeuse(FILE *fd, Node *file);
void tagexports(Stab *st, int hidelocal);

/* typechecking/inference */
void infer(Node *file);
Type *tysearch(Type *t);

/* debug */
void dump(Node *t, FILE *fd);
void dumpsym(Node *s, FILE *fd);
void dumpstab(Stab *st, FILE *fd);
char *opstr(Op o);
char *nodestr(Ntype nt);
char *litstr(Littype lt);
char *tidstr(Ty tid);

/* option parsing */
void optinit(Optctx *ctx, char *optstr, char **optargs, size_t noptargs);
int optnext(Optctx *c);
int optdone(Optctx *c);

/* convenience funcs */
void lappend(void *l, size_t *len, void *n); /* hack; nl is void* b/c void*** is incompatible with T*** */
void linsert(void *l, size_t *len, size_t idx, void *n);
void *lpop(void *l, size_t *len);
void ldel(void *l, size_t *len, size_t idx);
void lfree(void *l, size_t *len);

/* serializing/unserializing */
void be64(vlong v, byte buf[8]);
vlong host64(byte buf[8]);
void be32(long v, byte buf[4]);
long host32(byte buf[4]);
static inline intptr_t ptoi(void *p) {return (intptr_t)p;}
static inline void* itop(intptr_t i) {return (void*)i;}

void wrbuf(FILE *fd, void *buf, size_t sz);
void rdbuf(FILE *fd, void *buf, size_t sz);
char rdbyte(FILE *fd);
void wrbyte(FILE *fd, char val);
char rdbyte(FILE *fd);
void wrint(FILE *fd, long val);
long rdint(FILE *fd);
void wrstr(FILE *fd, char *val);
char *rdstr(FILE *fd);
void wrstrbuf(FILE *fd, Str str);
void rdstrbuf(FILE *fd, Str *str);
void wrflt(FILE *fd, double val);
double rdflt(FILE *fd);
void wrbool(FILE *fd, int val);
int rdbool(FILE *fd);

size_t max(size_t a, size_t b);
size_t min(size_t a, size_t b);
size_t align(size_t sz, size_t a);

/* suffix replacement */
char *swapsuffix(char *buf, size_t sz, char *s, char *suf, char *swap);

/* indented printf */
void indentf(int depth, char *fmt, ...);
void findentf(FILE *fd, int depth, char *fmt, ...);
void vfindentf(FILE *fd, int depth, char *fmt, va_list ap); 

/* Options to control the compilation */
extern char debugopt[128];
extern int asmonly;
extern char *outfile;
extern char **incpaths;
extern size_t nincpaths;

void yyerror(const char *s);
