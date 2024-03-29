typedef char *pvcontents;
typedef char *strconst;
typedef U32 PV;
typedef char *op_tr_array;
typedef int comment;
typedef SV *svindex;
typedef OP *opindex;
typedef IV IV64;

EXT int iv_overflows INIT(0);
void *bset_obj_store _((void *, I32));
void freadpv _((U32, void *));

EXT SV *sv;
EXT OP *op;
EXT XPV pv;

EXT void **obj_list;
EXT I32 obj_list_fill INIT(-1);

#ifdef INDIRECT_BGET_MACROS
#define FREAD(argp, len, nelem) bs.fread((char*)(argp),(len),(nelem),bs.data)
#define FGETC() bs.fgetc(bs.data)
#else
#define FREAD(argp, len, nelem) fread((argp), (len), (nelem), fp)
#define FGETC() getc(fp)
#endif /* INDIRECT_BGET_MACROS */

#define BGET_U32(arg)	FREAD(&arg, sizeof(U32), 1); arg = ntohl((U32)arg)
#define BGET_I32(arg)	FREAD(&arg, sizeof(I32), 1); arg = (I32)ntohl((U32)arg)
#define BGET_U16(arg)	FREAD(&arg, sizeof(U16), 1); arg = ntohs((U16)arg)
#define BGET_U8(arg)	arg = FGETC()

#if INDIRECT_BGET_MACROS
#define BGET_PV(arg)	do {		\
	BGET_U32(arg);			\
	if (arg)			\
	    bs.freadpv(arg, bs.data);	\
	else {				\
	    pv.xpv_pv = 0;		\
	    pv.xpv_len = 0;		\
	    pv.xpv_cur = 0;		\
	}				\
    } while (0)
#else
#define BGET_PV(arg)	do {			\
	BGET_U32(arg);				\
	if (arg) {				\
	    New(666, pv.xpv_pv, arg, char);	\
	    fread(pv.xpv_pv, 1, arg, fp);	\
	    pv.xpv_len = arg;			\
	    pv.xpv_cur = arg - 1;		\
	} else {				\
	    pv.xpv_pv = 0;			\
	    pv.xpv_len = 0;			\
	    pv.xpv_cur = 0;			\
	}					\
    } while (0)
#endif /* INDIRECT_BGET_MACROS */

#define BGET_comment(arg) \
	do { arg = FGETC(); } while (arg != '\n' && arg != EOF)

/*
 * In the following, sizeof(IV)*4 is just a way of encoding 32 on 64-bit-IV
 * machines such that 32-bit machine compilers don't whine about the shift
 * count being too high even though the code is never reached there.
 */
#define BGET_IV64(arg) do {				\
	U32 hi, lo;					\
	BGET_U32(hi);					\
	BGET_U32(lo);					\
	if (sizeof(IV) == 8)				\
	    arg = (IV) (hi << (sizeof(IV)*4) | lo);	\
	else if (((I32)hi == -1 && (I32)lo < 0)		\
		 || ((I32)hi == 0 && (I32)lo >= 0)) {	\
	    arg = (I32)lo;				\
	}						\
	else {						\
	    iv_overflows++;				\
	    arg = 0;					\
	}						\
    } while (0)

#define BGET_op_tr_array(arg) do {	\
	unsigned short *ary;		\
	int i;				\
	New(666, ary, 256, unsigned short); \
	FREAD(ary, 256, 2);		\
	for (i = 0; i < 256; i++)	\
	    ary[i] = ntohs(ary[i]);	\
	arg = (char *) ary;		\
    } while (0)

#define BGET_pvcontents(arg)	arg = pv.xpv_pv
#define BGET_strconst(arg)	do {	\
	for (arg = tokenbuf; (*arg = FGETC()); arg++) /* nothing */;	\
	arg = tokenbuf;			\
    } while (0)

#define BGET_double(arg)	do {	\
	char *str;			\
	BGET_strconst(str);		\
	arg = atof(str);		\
    } while (0)

#define BGET_objindex(arg) do {	\
	U32 ix;			\
	BGET_U32(ix);		\
	arg = obj_list[ix];	\
    } while (0)

#define BSET_ldspecsv(sv, arg) sv = specialsv_list[arg]
				    
#define BSET_sv_refcnt_add(svrefcnt, arg)	svrefcnt += arg
#define BSET_gp_refcnt_add(gprefcnt, arg)	gprefcnt += arg
#define BSET_gp_share(sv, arg)	do {	\
	gp_free((GV*)sv);		\
	GvGP(sv) = GvGP(arg);		\
    } while (0)

#define BSET_gv_fetchpv(sv, arg)	sv = (SV*)gv_fetchpv(arg, TRUE, SVt_PV)
#define BSET_gv_stashpv(sv, arg)	sv = (SV*)gv_stashpv(arg, TRUE)
#define BSET_sv_magic(sv, arg)		sv_magic(sv, Nullsv, arg, 0, 0)
#define BSET_mg_pv(mg, arg)	mg->mg_ptr = arg; mg->mg_len = pv.xpv_cur
#define BSET_sv_upgrade(sv, arg)	(void)SvUPGRADE(sv, arg)
#define BSET_xpv(sv)	do {	\
	SvPV_set(sv, pv.xpv_pv);	\
	SvCUR_set(sv, pv.xpv_cur);	\
	SvLEN_set(sv, pv.xpv_len);	\
    } while (0)
#define BSET_av_extend(sv, arg)	av_extend((AV*)sv, arg)

#define BSET_av_push(sv, arg)	av_push((AV*)sv, arg)
#define BSET_hv_store(sv, arg)	\
	hv_store((HV*)sv, pv.xpv_pv, pv.xpv_cur, arg, 0)
#define BSET_pv_free(pv)	Safefree(pv.xpv_pv)
#define BSET_pregcomp(op, arg) \
	cPMOP->op_pmregexp = arg ? pregcomp(arg, arg + pv.xpv_cur, cPMOP) : 0
#define BSET_newsv(sv, arg)	sv = NEWSV(666,0); SvUPGRADE(sv, arg)
#define BSET_newop(op, arg)	op = (OP*)safemalloc(optype_size[arg])
#define BSET_newopn(op, arg)	do {	\
	OP *oldop = op;			\
	BSET_newop(op, arg);		\
	oldop->op_next = op;		\
    } while (0)

#define BSET_ret(foo) return

/*
 * Kludge special-case workaround for OP_MAPSTART
 * which needs the ppaddr for OP_GREPSTART. Blech.
 */
#define BSET_op_type(op, arg)	do {	\
	op->op_type = arg;		\
	op->op_ppaddr = (arg != OP_MAPSTART) ? ppaddr[arg] : pp_grepstart; \
    } while (0)
#define BSET_op_ppaddr(op, arg) croak("op_ppaddr not yet implemented")
#define BSET_curpad(pad, arg) pad = AvARRAY(arg)

#define BSET_OBJ_STORE(obj, ix)		\
	(I32)ix > obj_list_fill ?	\
	bset_obj_store(obj, (I32)ix) : (obj_list[ix] = obj)
