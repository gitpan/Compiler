use strict;
my %alias_to = (
    U32 => [qw(PADOFFSET STRLEN)],
    I32 => [qw(SSize_t long)],
    U16 => [qw(OPCODE line_t short)],
    U8 => [qw(char)],
    objindex => [qw(svindex opindex)]		
);

my @optype= qw(OP UNOP BINOP LOGOP CONDOP LISTOP PMOP SVOP GVOP PVOP LOOP COP);

# Nullsv *must* come first in the following so that the condition
# ($$sv == 0) can continue to be used to test (sv == Nullsv).
my @specialsv = qw(Nullsv &sv_undef &sv_yes &sv_no);

my (%alias_from, $from, $tos);
while (($from, $tos) = each %alias_to) {
    map { $alias_from{$_} = $from } @$tos;
}

my $c_header = <<'EOT';
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
EOT

my $perl_header;
($perl_header = $c_header) =~ s{[/ ]?\*/?}{#}g;

if (-f "byterun.c") {
    rename("byterun.c", "byterun.c.old");
}
if (-f "byterun.h") {
    rename("byterun.h", "byterun.h.old");
}
if (-f "Asmdata.pm") {
    rename("Asmdata.pm", "Asmdata.pm.old");
}

#
# Start with boilerplate for Asmdata.pm
#
open(ASMDATA_PM, ">Asmdata.pm") or die "Asmdata.pm: $!";
print ASMDATA_PM $perl_header, <<'EOT';
package B::Asmdata;
use Exporter;
@ISA = qw(Exporter);
@EXPORT_OK = qw(%insn_data @insn_name @optype @specialsv_name);
use vars qw(%insn_data @insn_name @optype @specialsv_name);

EOT
print ASMDATA_PM <<"EOT";
\@optype = qw(@optype);
\@specialsv_name = qw(@specialsv);

# XXX insn_data is initialised this way because with a large
# %insn_data = (foo => [...], bar => [...], ...) initialiser
# I get a hard-to-track-down stack underflow and segfault.
EOT

#
# Boilerplate for byterun.c
#
open(BYTERUN_C, ">byterun.c") or die "byterun.c: $!";
print BYTERUN_C $c_header, <<'EOT';

#include "EXTERN.h"
#include "perl.h"
#include "bytecode.h"
#include "byterun.h"

#ifdef INDIRECT_BGET_MACROS
void byterun(bs)
struct bytestream bs;
#else
void byterun(fp)
FILE *fp;
#endif /* INDIRECT_BGET_MACROS */
{
    int insn;
    while ((insn = FGETC()) != EOF) {
	switch (insn) {
EOT


my (@insn_name, $insn_num, $insn, $lvalue, $argtype, $flags, $fundtype);

while (<DATA>) {
    chop;
    s/#.*//;			# remove comments
    next unless length;
    if (/^%number\s+(.*)/) {
	$insn_num = $1;
	next;
    } elsif (/%enum\s+(.*?)\s+(.*)/) {
	create_enum($1, $2);	# must come before instructions
	next;
    }
    ($insn, $lvalue, $argtype, $flags) = split;
    $insn_name[$insn_num] = $insn;
    $fundtype = $alias_from{$argtype} || $argtype;

    #
    # Add the case statement and code for the bytecode interpreter in byterun.c
    #
    printf BYTERUN_C "\t  case INSN_%s:\t\t/* %d */\n\t    {\n",
	uc($insn), $insn_num;
    my $optarg = $argtype eq "none" ? "" : ", arg";
    if ($optarg) {
	printf BYTERUN_C "\t\t$argtype arg;\n\t\tBGET_%s(arg);\n", $fundtype;
    }
    if ($flags =~ /x/) {
	print BYTERUN_C "\t\tBSET_$insn($lvalue$optarg);\n";
    } elsif ($flags =~ /s/) {
	# Store instructions store to obj_list[arg]. "lvalue" field is rvalue.
	print BYTERUN_C "\t\tBSET_OBJ_STORE($lvalue$optarg);\n";
    }
    elsif ($optarg && $lvalue ne "none") {
	print BYTERUN_C "\t\t$lvalue = arg;\n";
    }
    print BYTERUN_C "\t\tbreak;\n\t    }\n";

    #
    # Add the initialiser line for %insn_data in Asmdata.pm
    #
    print ASMDATA_PM <<"EOT";
\$insn_data{$insn} = [$insn_num, \\&PUT_$fundtype, "GET_$fundtype"];
EOT

    # Find the next unused instruction number
    do { $insn_num++ } while $insn_name[$insn_num];
}

#
# Finish off byterun.c
#
print BYTERUN_C <<'EOT';
	  default:
	    croak("Illegal bytecode instruction %d\n", insn);
	    /* NOTREACHED */
	}
    }
}
EOT

#
# Write the instruction and optype enum constants into byterun.h
#
open(BYTERUN_H, ">byterun.h") or die "byterun.h: $!";
print BYTERUN_H $c_header, <<'EOT';
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
EOT

my $i = 0;
my $add_enum_value = 0;
my $max_insn;
for ($i = 0; $i < @insn_name; $i++) {
    $insn = uc($insn_name[$i]);
    if (defined($insn)) {
	$max_insn = $i;
	if ($add_enum_value) {
	    print BYTERUN_H "    INSN_$insn = $i,\t\t\t/* $i */\n";
	    $add_enum_value = 0;
	} else {
	    print BYTERUN_H "    INSN_$insn,\t\t\t/* $i */\n";
	}
    } else {
	$add_enum_value = 1;
    }
}

print BYTERUN_H "    MAX_INSN = $max_insn\n};\n";

print BYTERUN_H "\nenum {\n";
for ($i = 0; $i < @optype - 1; $i++) {
    printf BYTERUN_H "    OPt_%s,\t\t/* %d */\n", $optype[$i], $i;
}
printf BYTERUN_H "    OPt_%s\t\t/* %d */\n};\n\n", $optype[$i], $i;
print BYTERUN_H <<'EOT';
EXT int optype_size[]
#ifdef DOINIT
= {
EOT
for ($i = 0; $i < @optype - 1; $i++) {
    printf BYTERUN_H "    sizeof(%s),\n", $optype[$i], $i;
}
printf BYTERUN_H "    sizeof(%s)\n}\n", $optype[$i], $i;
print BYTERUN_H <<'EOT';
#endif /* DOINIT */
;

EOT

printf BYTERUN_H <<'EOT', scalar(@specialsv);
EXT SV * specialsv_list[%d]
#ifdef DOINIT
EOT
print BYTERUN_H "= { ", join(", ", @specialsv), " }\n";
print BYTERUN_H <<'EOT';
#endif /* DOINIT */
;
EOT

#
# Finish off insn_data and create array initialisers in Asmdata.pm
#
print ASMDATA_PM <<'EOT';

my ($insn_name, $insn_data);
while (($insn_name, $insn_data) = each %insn_data) {
    $insn_name[$insn_data->[0]] = $insn_name;
}
# Fill in any gaps
@insn_name = map($_ || "unused", @insn_name);

1;
EOT

__END__
# First set instruction ord("#") to read comment to end-of-line (sneaky)
%number 35
comment		arg			comment
# Then make ord("\n") into a no-op
%number 10
nop		none			none
# Now for the rest of the ordinary ones, beginning with \0 which is
# ret so that \0-terminated strings can be read properly as bytecode.
%number 0
#
#opcode		lvalue			argtype		flags	
#
ret		none			none		x
ldsv		sv			svindex
ldop		op			opindex
stsv		sv			U32		s
stop		op			U32		s
ldspecsv	sv			U8		x
newsv		sv			U8		x
newop		op			U8		x
newopn		op			U8		x
newpv		none			PV
pv_cur		pv.xpv_cur		STRLEN
pv_free		pv			none		x
sv_upgrade	sv			char		x
sv_refcnt	SvREFCNT(sv)		U32
sv_refcnt_add	SvREFCNT(sv)		I32		x
sv_flags	SvFLAGS(sv)		U32
xrv		SvRV(sv)		svindex
xpv		sv			none		x
xiv32		SvIVX(sv)		I32
xiv64		SvIVX(sv)		IV64
xnv		SvNVX(sv)		double
xlv_targoff	LvTARGOFF(sv)		STRLEN
xlv_targlen	LvTARGLEN(sv)		STRLEN
xlv_targ	LvTARG(sv)		svindex
xlv_type	LvTYPE(sv)		char
xbm_useful	BmUSEFUL(sv)		I32
xbm_previous	BmPREVIOUS(sv)		U16
xbm_rare	BmRARE(sv)		U8
xfm_lines	FmLINES(sv)		I32
xio_lines	IoLINES(sv)		long
xio_page	IoPAGE(sv)		long
xio_page_len	IoPAGE_LEN(sv)		long
xio_lines_left	IoLINES_LEFT(sv)	long
xio_top_name	IoTOP_NAME(sv)		pvcontents
xio_top_gv	IoTOP_GV(sv)		svindex
xio_fmt_name	IoFMT_NAME(sv)		pvcontents
xio_fmt_gv	IoFMT_GV(sv)		svindex
xio_bottom_name	IoBOTTOM_NAME(sv)	pvcontents
xio_bottom_gv	IoBOTTOM_GV(sv)		svindex
xio_subprocess	IoSUBPROCESS(sv)	short
xio_type	IoTYPE(sv)		char
xio_flags	IoFLAGS(sv)		char
xcv_stash	*(SV**)&CvSTASH(sv)	svindex
xcv_start	CvSTART(sv)		opindex
xcv_root	CvROOT(sv)		opindex
xcv_gv		CvGV(sv)		svindex
xcv_filegv	CvFILEGV(sv)		svindex
xcv_depth	CvDEPTH(sv)		long
xcv_padlist	*(SV**)&CvPADLIST(sv)	svindex
xcv_outside	*(SV**)&CvOUTSIDE(sv)	svindex
xcv_flags	CvFLAGS(sv)		U8
av_extend	sv			SSize_t		x
av_push		sv			svindex		x
xav_fill	AvFILL(sv)		SSize_t
xav_max		AvMAX(sv)		SSize_t
xav_flags	AvFLAGS(sv)		U8
xhv_riter	HvRITER(sv)		I32
xhv_name	HvNAME(sv)		pvcontents
hv_store	sv			svindex		x
sv_magic	sv			char		x
mg_obj		SvMAGIC(sv)->mg_obj	svindex
mg_private	SvMAGIC(sv)->mg_private	U16
mg_flags	SvMAGIC(sv)->mg_flags	U8
mg_pv		SvMAGIC(sv)		pvcontents	x
xmg_stash	*(SV**)&SvSTASH(sv)	svindex
gv_fetchpv	sv			strconst	x
gv_stashpv	sv			strconst	x
gp_sv		GvSV(sv)		svindex
gp_refcnt	GvREFCNT(sv)		U32
gp_refcnt_add	GvREFCNT(sv)		I32		x
gp_av		*(SV**)&GvAV(sv)	svindex
gp_hv		*(SV**)&GvHV(sv)	svindex
gp_cv		*(SV**)&GvCV(sv)	svindex
gp_filegv	*(SV**)&GvFILEGV(sv)	svindex
gp_io		*(SV**)&GvIOp(sv)	svindex
gp_form		*(SV**)&GvFORM(sv)	svindex
gp_cvgen	GvCVGEN(sv)		U32
gp_line		GvLINE(sv)		line_t
gp_share	sv			svindex		x
xgv_flags	GvFLAGS(sv)		U8
op_next		op->op_next		opindex
op_sibling	op->op_sibling		opindex
op_ppaddr	op->op_ppaddr		strconst	x
op_targ		op->op_targ		PADOFFSET
op_type		op			OPCODE		x
op_seq		op->op_seq		U16
op_flags	op->op_flags		U8
op_private	op->op_private		U8
op_first	cUNOP->op_first		opindex
op_last		cBINOP->op_last		opindex
op_other	cLOGOP->op_other	opindex
op_true		cCONDOP->op_true	opindex
op_false	cCONDOP->op_false	opindex
op_children	cLISTOP->op_children	U32
op_pmreplroot	cPMOP->op_pmreplroot	opindex
op_pmreplrootgv	*(SV**)&cPMOP->op_pmreplroot	svindex
op_pmreplstart	cPMOP->op_pmreplstart	opindex
op_pmnext	*(OP**)&cPMOP->op_pmnext	opindex
pregcomp	op			pvcontents	x
op_pmshort	cPMOP->op_pmshort	svindex
op_pmflags	cPMOP->op_pmflags	U16
op_pmpermflags	cPMOP->op_pmpermflags	U16
op_pmslen	cPMOP->op_pmslen	char
op_sv		cSVOP->op_sv		svindex
op_gv		cGVOP->op_gv		svindex
op_pv		cPVOP->op_pv		pvcontents
op_pv_tr	cPVOP->op_pv		op_tr_array
op_redoop	cLOOP->op_redoop	opindex
op_nextop	cLOOP->op_nextop	opindex
op_lastop	cLOOP->op_lastop	opindex
cop_label	cCOP->cop_label		pvcontents
cop_stash	*(SV**)&cCOP->cop_stash		svindex
cop_filegv	cCOP->cop_filegv	svindex
cop_seq		cCOP->cop_seq		U32
cop_arybase	cCOP->cop_arybase	I32
cop_line	cCOP->cop_line		line_t
main_start	main_start		opindex
main_root	main_root		opindex
curpad		curpad			svindex		x
