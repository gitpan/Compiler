/*
 *      Copyright (c) 1996 Malcolm Beattie
 *
 *      You may distribute under the terms of either the GNU General Public
 *      License or the Artistic License, as specified in the README file.
 *
 */
/*
 * This file is autogenerated from bytecode.pl. Changes made here will be lost.
 */
#ifdef INDIRECT_BGET_MACROS
struct bytestream {
    void *data;
    int (*fgetc)(void *);
    int (*fread)(char *, size_t, size_t, void*);
    void (*freadpv)(U32, void*);
};
void freadpv _((U32, void *));
void byterun _((struct bytestream));
#else
void byterun _((FILE *));
#endif /* INDIRECT_BGET_MACROS */

enum {
    INSN_RET,			/* 0 */
    INSN_LDSV,			/* 1 */
    INSN_LDOP,			/* 2 */
    INSN_STSV,			/* 3 */
    INSN_STOP,			/* 4 */
    INSN_LDSPECSV,			/* 5 */
    INSN_NEWSV,			/* 6 */
    INSN_NEWOP,			/* 7 */
    INSN_NEWOPN,			/* 8 */
    INSN_NEWPV,			/* 9 */
    INSN_NOP,			/* 10 */
    INSN_PV_CUR,			/* 11 */
    INSN_PV_FREE,			/* 12 */
    INSN_SV_UPGRADE,			/* 13 */
    INSN_SV_REFCNT,			/* 14 */
    INSN_SV_REFCNT_ADD,			/* 15 */
    INSN_SV_FLAGS,			/* 16 */
    INSN_XRV,			/* 17 */
    INSN_XPV,			/* 18 */
    INSN_XIV32,			/* 19 */
    INSN_XIV64,			/* 20 */
    INSN_XNV,			/* 21 */
    INSN_XLV_TARGOFF,			/* 22 */
    INSN_XLV_TARGLEN,			/* 23 */
    INSN_XLV_TARG,			/* 24 */
    INSN_XLV_TYPE,			/* 25 */
    INSN_XBM_USEFUL,			/* 26 */
    INSN_XBM_PREVIOUS,			/* 27 */
    INSN_XBM_RARE,			/* 28 */
    INSN_XFM_LINES,			/* 29 */
    INSN_XIO_LINES,			/* 30 */
    INSN_XIO_PAGE,			/* 31 */
    INSN_XIO_PAGE_LEN,			/* 32 */
    INSN_XIO_LINES_LEFT,			/* 33 */
    INSN_XIO_TOP_NAME,			/* 34 */
    INSN_COMMENT,			/* 35 */
    INSN_XIO_TOP_GV,			/* 36 */
    INSN_XIO_FMT_NAME,			/* 37 */
    INSN_XIO_FMT_GV,			/* 38 */
    INSN_XIO_BOTTOM_NAME,			/* 39 */
    INSN_XIO_BOTTOM_GV,			/* 40 */
    INSN_XIO_SUBPROCESS,			/* 41 */
    INSN_XIO_TYPE,			/* 42 */
    INSN_XIO_FLAGS,			/* 43 */
    INSN_XCV_STASH,			/* 44 */
    INSN_XCV_START,			/* 45 */
    INSN_XCV_ROOT,			/* 46 */
    INSN_XCV_GV,			/* 47 */
    INSN_XCV_FILEGV,			/* 48 */
    INSN_XCV_DEPTH,			/* 49 */
    INSN_XCV_PADLIST,			/* 50 */
    INSN_XCV_OUTSIDE,			/* 51 */
    INSN_XCV_FLAGS,			/* 52 */
    INSN_AV_EXTEND,			/* 53 */
    INSN_AV_PUSH,			/* 54 */
    INSN_XAV_FILL,			/* 55 */
    INSN_XAV_MAX,			/* 56 */
    INSN_XAV_FLAGS,			/* 57 */
    INSN_XHV_RITER,			/* 58 */
    INSN_XHV_NAME,			/* 59 */
    INSN_HV_STORE,			/* 60 */
    INSN_SV_MAGIC,			/* 61 */
    INSN_MG_OBJ,			/* 62 */
    INSN_MG_PRIVATE,			/* 63 */
    INSN_MG_FLAGS,			/* 64 */
    INSN_MG_PV,			/* 65 */
    INSN_XMG_STASH,			/* 66 */
    INSN_GV_FETCHPV,			/* 67 */
    INSN_GV_STASHPV,			/* 68 */
    INSN_GP_SV,			/* 69 */
    INSN_GP_REFCNT,			/* 70 */
    INSN_GP_REFCNT_ADD,			/* 71 */
    INSN_GP_AV,			/* 72 */
    INSN_GP_HV,			/* 73 */
    INSN_GP_CV,			/* 74 */
    INSN_GP_FILEGV,			/* 75 */
    INSN_GP_IO,			/* 76 */
    INSN_GP_FORM,			/* 77 */
    INSN_GP_CVGEN,			/* 78 */
    INSN_GP_LINE,			/* 79 */
    INSN_GP_SHARE,			/* 80 */
    INSN_XGV_FLAGS,			/* 81 */
    INSN_OP_NEXT,			/* 82 */
    INSN_OP_SIBLING,			/* 83 */
    INSN_OP_PPADDR,			/* 84 */
    INSN_OP_TARG,			/* 85 */
    INSN_OP_TYPE,			/* 86 */
    INSN_OP_SEQ,			/* 87 */
    INSN_OP_FLAGS,			/* 88 */
    INSN_OP_PRIVATE,			/* 89 */
    INSN_OP_FIRST,			/* 90 */
    INSN_OP_LAST,			/* 91 */
    INSN_OP_OTHER,			/* 92 */
    INSN_OP_TRUE,			/* 93 */
    INSN_OP_FALSE,			/* 94 */
    INSN_OP_CHILDREN,			/* 95 */
    INSN_OP_PMREPLROOT,			/* 96 */
    INSN_OP_PMREPLROOTGV,			/* 97 */
    INSN_OP_PMREPLSTART,			/* 98 */
    INSN_OP_PMNEXT,			/* 99 */
    INSN_PREGCOMP,			/* 100 */
    INSN_OP_PMSHORT,			/* 101 */
    INSN_OP_PMFLAGS,			/* 102 */
    INSN_OP_PMPERMFLAGS,			/* 103 */
    INSN_OP_PMSLEN,			/* 104 */
    INSN_OP_SV,			/* 105 */
    INSN_OP_GV,			/* 106 */
    INSN_OP_PV,			/* 107 */
    INSN_OP_PV_TR,			/* 108 */
    INSN_OP_REDOOP,			/* 109 */
    INSN_OP_NEXTOP,			/* 110 */
    INSN_OP_LASTOP,			/* 111 */
    INSN_COP_LABEL,			/* 112 */
    INSN_COP_STASH,			/* 113 */
    INSN_COP_FILEGV,			/* 114 */
    INSN_COP_SEQ,			/* 115 */
    INSN_COP_ARYBASE,			/* 116 */
    INSN_COP_LINE,			/* 117 */
    INSN_MAIN_START,			/* 118 */
    INSN_MAIN_ROOT,			/* 119 */
    INSN_CURPAD,			/* 120 */
    MAX_INSN = 120
};

enum {
    OPt_OP,		/* 0 */
    OPt_UNOP,		/* 1 */
    OPt_BINOP,		/* 2 */
    OPt_LOGOP,		/* 3 */
    OPt_CONDOP,		/* 4 */
    OPt_LISTOP,		/* 5 */
    OPt_PMOP,		/* 6 */
    OPt_SVOP,		/* 7 */
    OPt_GVOP,		/* 8 */
    OPt_PVOP,		/* 9 */
    OPt_LOOP,		/* 10 */
    OPt_COP		/* 11 */
};

EXT int optype_size[]
#ifdef DOINIT
= {
    sizeof(OP),
    sizeof(UNOP),
    sizeof(BINOP),
    sizeof(LOGOP),
    sizeof(CONDOP),
    sizeof(LISTOP),
    sizeof(PMOP),
    sizeof(SVOP),
    sizeof(GVOP),
    sizeof(PVOP),
    sizeof(LOOP),
    sizeof(COP)
}
#endif /* DOINIT */
;

EXT SV * specialsv_list[4]
#ifdef DOINIT
= { Nullsv, &sv_undef, &sv_yes, &sv_no }
#endif /* DOINIT */
;
