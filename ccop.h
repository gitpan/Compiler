typedef enum {
    OPc_NULL,	/* 0 */
    OPc_BASEOP,	/* 1 */
    OPc_UNOP,	/* 2 */
    OPc_BINOP,	/* 3 */
    OPc_LOGOP,	/* 4 */
    OPc_CONDOP,	/* 5 */
    OPc_LISTOP,	/* 6 */
    OPc_PMOP,	/* 7 */
    OPc_SVOP,	/* 8 */
    OPc_GVOP,	/* 9 */
    OPc_PVOP,	/* 10 */
    OPc_CVOP,	/* 11 */
    OPc_LOOP,	/* 12 */
    OPc_COP	/* 13 */
} opclass;

opclass	cc_opclass _((OP *o));
char *	cc_opclassname _((OP *o));		

#ifndef DOINIT
EXT char *ppnames[];
#else
EXT char *ppnames[] = {
	"pp_null",
	"pp_stub",
	"pp_scalar",
	"pp_pushmark",
	"pp_wantarray",
	"pp_const",
	"pp_gvsv",
	"pp_gv",
	"pp_gelem",
	"pp_padsv",
	"pp_padav",
	"pp_padhv",
	"pp_padany",
	"pp_pushre",
	"pp_rv2gv",
	"pp_rv2sv",
	"pp_av2arylen",
	"pp_rv2cv",
	"pp_anoncode",
	"pp_prototype",
	"pp_refgen",
	"pp_srefgen",
	"pp_ref",
	"pp_bless",
	"pp_backtick",
	"pp_glob",
	"pp_readline",
	"pp_rcatline",
	"pp_regcmaybe",
	"pp_regcomp",
	"pp_match",
	"pp_subst",
	"pp_substcont",
	"pp_trans",
	"pp_sassign",
	"pp_aassign",
	"pp_chop",
	"pp_schop",
	"pp_chomp",
	"pp_schomp",
	"pp_defined",
	"pp_undef",
	"pp_study",
	"pp_pos",
	"pp_preinc",
	"pp_i_preinc",
	"pp_predec",
	"pp_i_predec",
	"pp_postinc",
	"pp_i_postinc",
	"pp_postdec",
	"pp_i_postdec",
	"pp_pow",
	"pp_multiply",
	"pp_i_multiply",
	"pp_divide",
	"pp_i_divide",
	"pp_modulo",
	"pp_i_modulo",
	"pp_repeat",
	"pp_add",
	"pp_i_add",
	"pp_subtract",
	"pp_i_subtract",
	"pp_concat",
	"pp_stringify",
	"pp_left_shift",
	"pp_right_shift",
	"pp_lt",
	"pp_i_lt",
	"pp_gt",
	"pp_i_gt",
	"pp_le",
	"pp_i_le",
	"pp_ge",
	"pp_i_ge",
	"pp_eq",
	"pp_i_eq",
	"pp_ne",
	"pp_i_ne",
	"pp_ncmp",
	"pp_i_ncmp",
	"pp_slt",
	"pp_sgt",
	"pp_sle",
	"pp_sge",
	"pp_seq",
	"pp_sne",
	"pp_scmp",
	"pp_bit_and",
	"pp_bit_xor",
	"pp_bit_or",
	"pp_negate",
	"pp_i_negate",
	"pp_not",
	"pp_complement",
	"pp_atan2",
	"pp_sin",
	"pp_cos",
	"pp_rand",
	"pp_srand",
	"pp_exp",
	"pp_log",
	"pp_sqrt",
	"pp_int",
	"pp_hex",
	"pp_oct",
	"pp_abs",
	"pp_length",
	"pp_substr",
	"pp_vec",
	"pp_index",
	"pp_rindex",
	"pp_sprintf",
	"pp_formline",
	"pp_ord",
	"pp_chr",
	"pp_crypt",
	"pp_ucfirst",
	"pp_lcfirst",
	"pp_uc",
	"pp_lc",
	"pp_quotemeta",
	"pp_rv2av",
	"pp_aelemfast",
	"pp_aelem",
	"pp_aslice",
	"pp_each",
	"pp_values",
	"pp_keys",
	"pp_delete",
	"pp_exists",
	"pp_rv2hv",
	"pp_helem",
	"pp_hslice",
	"pp_unpack",
	"pp_pack",
	"pp_split",
	"pp_join",
	"pp_list",
	"pp_lslice",
	"pp_anonlist",
	"pp_anonhash",
	"pp_splice",
	"pp_push",
	"pp_pop",
	"pp_shift",
	"pp_unshift",
	"pp_sort",
	"pp_reverse",
	"pp_grepstart",
	"pp_grepwhile",
	"pp_mapstart",
	"pp_mapwhile",
	"pp_range",
	"pp_flip",
	"pp_flop",
	"pp_and",
	"pp_or",
	"pp_xor",
	"pp_cond_expr",
	"pp_andassign",
	"pp_orassign",
	"pp_method",
	"pp_entersub",
	"pp_leavesub",
	"pp_caller",
	"pp_warn",
	"pp_die",
	"pp_reset",
	"pp_lineseq",
	"pp_nextstate",
	"pp_dbstate",
	"pp_unstack",
	"pp_enter",
	"pp_leave",
	"pp_scope",
	"pp_enteriter",
	"pp_iter",
	"pp_enterloop",
	"pp_leaveloop",
	"pp_return",
	"pp_last",
	"pp_next",
	"pp_redo",
	"pp_dump",
	"pp_goto",
	"pp_exit",
	"pp_open",
	"pp_close",
	"pp_pipe_op",
	"pp_fileno",
	"pp_umask",
	"pp_binmode",
	"pp_tie",
	"pp_untie",
	"pp_tied",
	"pp_dbmopen",
	"pp_dbmclose",
	"pp_sselect",
	"pp_select",
	"pp_getc",
	"pp_read",
	"pp_enterwrite",
	"pp_leavewrite",
	"pp_prtf",
	"pp_print",
	"pp_sysopen",
	"pp_sysread",
	"pp_syswrite",
	"pp_send",
	"pp_recv",
	"pp_eof",
	"pp_tell",
	"pp_seek",
	"pp_truncate",
	"pp_fcntl",
	"pp_ioctl",
	"pp_flock",
	"pp_socket",
	"pp_sockpair",
	"pp_bind",
	"pp_connect",
	"pp_listen",
	"pp_accept",
	"pp_shutdown",
	"pp_gsockopt",
	"pp_ssockopt",
	"pp_getsockname",
	"pp_getpeername",
	"pp_lstat",
	"pp_stat",
	"pp_ftrread",
	"pp_ftrwrite",
	"pp_ftrexec",
	"pp_fteread",
	"pp_ftewrite",
	"pp_fteexec",
	"pp_ftis",
	"pp_fteowned",
	"pp_ftrowned",
	"pp_ftzero",
	"pp_ftsize",
	"pp_ftmtime",
	"pp_ftatime",
	"pp_ftctime",
	"pp_ftsock",
	"pp_ftchr",
	"pp_ftblk",
	"pp_ftfile",
	"pp_ftdir",
	"pp_ftpipe",
	"pp_ftlink",
	"pp_ftsuid",
	"pp_ftsgid",
	"pp_ftsvtx",
	"pp_fttty",
	"pp_fttext",
	"pp_ftbinary",
	"pp_chdir",
	"pp_chown",
	"pp_chroot",
	"pp_unlink",
	"pp_chmod",
	"pp_utime",
	"pp_rename",
	"pp_link",
	"pp_symlink",
	"pp_readlink",
	"pp_mkdir",
	"pp_rmdir",
	"pp_open_dir",
	"pp_readdir",
	"pp_telldir",
	"pp_seekdir",
	"pp_rewinddir",
	"pp_closedir",
	"pp_fork",
	"pp_wait",
	"pp_waitpid",
	"pp_system",
	"pp_exec",
	"pp_kill",
	"pp_getppid",
	"pp_getpgrp",
	"pp_setpgrp",
	"pp_getpriority",
	"pp_setpriority",
	"pp_time",
	"pp_tms",
	"pp_localtime",
	"pp_gmtime",
	"pp_alarm",
	"pp_sleep",
	"pp_shmget",
	"pp_shmctl",
	"pp_shmread",
	"pp_shmwrite",
	"pp_msgget",
	"pp_msgctl",
	"pp_msgsnd",
	"pp_msgrcv",
	"pp_semget",
	"pp_semctl",
	"pp_semop",
	"pp_require",
	"pp_dofile",
	"pp_entereval",
	"pp_leaveeval",
	"pp_entertry",
	"pp_leavetry",
	"pp_ghbyname",
	"pp_ghbyaddr",
	"pp_ghostent",
	"pp_gnbyname",
	"pp_gnbyaddr",
	"pp_gnetent",
	"pp_gpbyname",
	"pp_gpbynumber",
	"pp_gprotoent",
	"pp_gsbyname",
	"pp_gsbyport",
	"pp_gservent",
	"pp_shostent",
	"pp_snetent",
	"pp_sprotoent",
	"pp_sservent",
	"pp_ehostent",
	"pp_enetent",
	"pp_eprotoent",
	"pp_eservent",
	"pp_gpwnam",
	"pp_gpwuid",
	"pp_gpwent",
	"pp_spwent",
	"pp_epwent",
	"pp_ggrnam",
	"pp_ggrgid",
	"pp_ggrent",
	"pp_sgrent",
	"pp_egrent",
	"pp_getlogin",
	"pp_syscall",
};
#endif
