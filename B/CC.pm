#      CC.pm
#
#      Copyright (c) 1996 Malcolm Beattie
#
#      You may distribute under the terms of either the GNU General Public
#      License or the Artistic License, as specified in the README file.
#
package B::CC;
use strict;
use B qw(minus_c main_start main_root class comppadlist peekop);
require B::C;

# These should probably be in B.xs
sub OPpASSIGN_BACKWARDS { 64 }
sub OPpLVAL_INTRO { 128 }
sub OPf_LIST { 1 }
sub OPf_KNOW { 2 }
sub OPf_MOD { 32 }

my %seen;
my $level;
my %callbacklist;
my @runtime_list;

my $pp_runtime_name = "pp_runtime"; # XXX should be configurable
my $main_start_sym;
my $main_root_sym;
my $comppadlist_sym;

sub runtime {
    my $line;
    foreach $line (@_) {
	push(@runtime_list, ("    " x $level) . $line);
	#warn "    " x $level, $line, "\n"; # debug
    }
}

sub output_runtime {
    my $line;
    foreach $line (@runtime_list) {
	print $line, "\n";
    }
}

sub add_callback {
    my ($op, $callback) = @_;
    #warn sprintf("adding callback $callback for %s\n", peekop($op)); # debug
    push (@{$callbacklist{$$op}}, $callback);
}

sub call_callbacks {
    my $op = shift;
    my $callback;
    foreach $callback (@{$callbacklist{$$op}}) {
	#warn sprintf("calling callback $callback for %s\n",peekop($op));#debug
	&$callback($op);
    }
    delete $callbacklist{$$op};
}

sub loadop {
    my $op = shift;
    runtime(sprintf("op = %s;", $op->save));
}

sub write_label {
    my $op = shift;
    $level--;
    runtime sprintf("  lab_%x:", $$op);
    $level++;
}

sub gimme {
    my $op = shift;
    my $flags = $op->flags;
    return (($flags & OPf_KNOW) ? ($flags & OPf_LIST) : "dowantarray()");
}

sub pp_and {
    my $op = shift;
    add_callback($op->next, sub { $level--; runtime("}"); });
    runtime("if (SvTRUE(*stack_sp)) {",
	    "    stack_sp--;");
    $level++;
    return $op->other;
}

sub pp_or {
    my $op = shift;
    runtime("if (!SvTRUE(*stack_sp)) {",
	    "    stack_sp--;");
    add_callback($op->next, sub { $level--; runtime("}"); });
    $level++;
    return $op->other;
}

sub pp_cond_expr {
    my $op = shift;

    runtime("if (SvTRUEx(*stack_sp--)) {");
    $level++;
    add_callback($op->next, sub {
	delete $seen{${$op->next}};
	$level--;
	runtime("}", "else {");
	$level++;
	compile($op->false);	# recurse
	runtime("}");
	$level--;
    });
    return $op->true;
}

sub pp_mapwhile {
    my $op = shift;
    # handle op_other
    warn "pp_mapwhile not yet implemented\n";
    return $op->next;
}

sub pp_grepwhile {
    my $op = shift;
    # handle op_other
    warn "pp_grepwhile not yet implemented\n";
    return $op->next;
}

sub pp_match {
    my $op = shift;
    # handle pmop
    warn "pp_match not yet implemented\n";
    return $op->next;
}

sub pp_subst{
    my $op = shift;
    # handle pmop
    warn "pp_subst not yet implemented\n";
    return $op->next;
}

sub pp_substcont {
    my $op = shift;
    # handle op_other
    warn "pp_substcont not yet implemented\n";
    return $op->next;
}

sub pp_enterloop {
    my $op = shift;
    my $o;
    my $nextop = $op->nextop;
    my $lastop = $op->lastop;
    my $redoop = $op->redoop;
    my $next = $op->next;
    my $gimme = gimme($op);

    my %uniqueops = map {$$_ => $_} $next, $nextop, $lastop, $redoop;
    foreach $o (values %uniqueops) {
	add_callback($o, sub { write_label($o) });
    }
    #warn sprintf("next %s, nextop %s, lastop %s, redoop %s\n", peekop($next),
    #		  peekop($nextop), peekop($lastop), peekop($redoop),); # debug
    runtime("{",
	    "    dSP; register CONTEXT *cx; I32 gimme = $gimme;",
	    "    ENTER; SAVETMPS; ENTER;",
	    "    PUSHBLOCK(cx, CXt_LOOP, SP); PUSHLOOP(cx, 0, SP); PUTBACK;",
	    "}");
    compile($next);
    return $lastop;
}

sub pp_enter {
    my $op = shift;
    my $flags = $op->flags;
    add_callback($op->next, sub { write_label($op->next) });
    runtime("{",
	    "    dSP;",
	    "    register CONTEXT *cx;");
    if ($flags & OPf_KNOW) {
	runtime(sprintf("    I32 gimme = 0x%x;", $flags & OPf_LIST));
    } else {
	runtime("    I32 gimme = (cxstack_ix>=0)? cxstack[cxstack_ix].blk_gimme : G_SCALAR;");
    }
    runtime("    ENTER;",
	    "    SAVETMPS;",
	    "    PUSHBLOCK(cx, CXt_BLOCK, sp);",
	    "    PUTBACK;",
	    "}");
    return $op->next;
}

sub pp_const {
    my $op = shift;
    my $svsym = $op->sv->save;
    runtime("{ dSP; XPUSHs($svsym); PUTBACK; }");
    return $op->next;
}

sub pp_nextstate {
    my $op = shift;
    my $opsym = $op->save;
    runtime("curcop = (COP*)$opsym;",
	    "TAINT_NOT;",
	    "stack_sp = stack_base + cxstack[cxstack_ix].blk_oldsp;",
	    "FREETMPS;");
    return $op->next;
}

sub pp_gvsv {
    my $op = shift;
    my $gvsym = $op->gv->save;
    my $f = ($op->private & OPpLVAL_INTRO) ? "save_scalar" : "GvSV";
    runtime("{ dSP; EXTEND(sp, 1); PUSHs($f($gvsym)); PUTBACK; }");
    return $op->next;
}

sub pp_null {
    my $op = shift;
    return $op->next;
}

sub pp_pushmark {
    my $op = shift;
    runtime("PUSHMARK(stack_sp);");
    return $op->next;
}

sub pp_stringify {
    my $op = shift;
    my $targ = $op->targ;
    runtime("{",
	    "    dSP;",
	    "    dTARG = PAD_SV($targ);",
	    "    STRLEN len;",
	    "    char *s;",
	    "    s = SvPV(TOPs,len);",
	    "    sv_setpvn(TARG,s,len);",
	    "    SETTARG;",
	    "    PUTBACK;",
	    "}");
    return $op->next;
}

sub pp_gv {
    my $op = shift;
    my $gvsym = $op->gv->save;
    runtime("{ dSP; XPUSHs($gvsym); PUTBACK; }");
    return $op->next;
}

sub pp_padsv {
    my $op = shift;
    my $targ = $op->targ;
    runtime(sprintf("{ dSP; XPUSHs(PAD_SV($targ));%s PUTBACK; }",
		    ($op->private & OPpLVAL_INTRO) ?
		    " SAVECLEARSV(curpad[$targ]);" : ""));
    return $op->next;
}

sub pp_readline {
    my $op = shift;
    runtime("last_in_gv = (GV*)(*stack_sp--);",
	    "(void) do_readline();");
    return $op->next;
}

sub pp_aelemfast {
    my $op = shift;
    my $svsym = $op->sv->save;
    my $priv = $op->private;
    my $mod = $op->flags & OPf_MOD;
    runtime("{   dSP;",
	    "    SV **svp = av_fetch(GvAV($svsym), $priv, $mod);",
	    "    PUSHs(svp ? *svp : &sv_undef);",
	    "    PUTBACK;",
	    "}");
    return $op->next;
}

sub pp_join {
    my $op = shift;
    my $targ = $op->targ;
    runtime("{",
	    "    dSP; dMARK;",
	    "    SV *TARG = PAD_SV($targ);",
	    "    MARK++;",
	    "    do_join(TARG, *MARK, MARK, SP);",
	    "    SP = MARK;",
	    "    SETs(TARG);",
	    "    PUTBACK",
	    "}");
    return $op->next;
}

sub pp_pushre {
    my $op = shift;
    my $opsym = $op->save;
    runtime("{ dSP; XPUSHs((SV*)$opsym); PUTBACK; }");
    return $op->next;
}

sub pp_unstack {
    my $op = shift;
    # XXX Do we need loadop for FREETMPS or LEAVE_SCOPE?
    runtime("TAINT_NOT;",
	    "stack_sp = stack_base + cxstack[cxstack_ix].blk_oldsp;",
	    "FREETMPS;",
	    "LEAVE_SCOPE(scopestack[scopestack_ix - 1]);");
    return $op->next;
}

sub pp_sassign {
    my $op = shift;
    my ($left, $right) = qw(left right);
    if ($op->private & OPpASSIGN_BACKWARDS) {
	($left, $right) = qw(right left);
    }
    runtime("{",
	    "    dSP; dPOPTOPssrl; MAGIC *mg;",
	    "    if (tainting && tainted && (!SvGMAGICAL($left) || !SvSMAGICAL($left) ||",
	    "                                !((mg = mg_find($left, 't')) && mg->mg_len & 1))) { TAINT_NOT; }",
	    "    SvSetSV($right, $left); SvSETMAGIC($right); SETs($right); PUTBACK;",
	    "}");
   return $op->next;
}

sub pp_stub {
    my $op = shift;
    runtime("{ dSP; if (GIMME != G_ARRAY) XPUSHs(&sv_undef); PUTBACK; }");
    return $op->next;
}

sub pp_predec {
    my $op = shift;
    runtime("{",
	    "    dSP;",
	    "    if (SvIOK(TOPs)) {",
	    "        --SvIVX(TOPs);",
	    "        SvFLAGS(TOPs) &= ~(SVf_NOK|SVf_POK|SVp_NOK|SVp_POK);",
	    "    }",
	    "    else",
	    "        sv_dec(TOPs);",
	    "    SvSETMAGIC(TOPs);",
	    "    PUTBACK;",
	    "}");
    return $op->next;
}

sub pp_preinc {
    my $op = shift;
    runtime("{",
	    "    dSP;",
	    "    if (SvIOK(TOPs)) {",
	    "        ++SvIVX(TOPs);",
	    "        SvFLAGS(TOPs) &= ~(SVf_NOK|SVf_POK|SVp_NOK|SVp_POK);",
	    "    }",
	    "    else",
	    "        sv_inc(TOPs);",
	    "    SvSETMAGIC(TOPs);",
	    "    PUTBACK;",
	    "}");
    return $op->next;
}


sub default_pp {
    my $op = shift;
    my $ppname = $op->ppaddr;
    loadop($op);
    runtime("DOOP($ppname);");
    return $op->next;
}

sub compile {
    my $op = shift;
    my $ppname;
    while ($$op) {
	$ppname = $op->ppaddr;
	#warn sprintf("compiling %s\n", peekop($op)); # debug
	if ($seen{$$op}) {
	    runtime(sprintf("goto lab_%x;", $$op));
	    #warn sprintf("returning from compile: seen %s before\n",
	    #		  peekop($op)); # debug
	    return;
	}
	$seen{$$op} = 1;
	call_callbacks($op);
	runtime(sprintf("/* %d. %s (0x%x) */", $op->seq, $ppname, $$op));
	{
	    no strict 'refs';
	    $op = defined(&$ppname) ? &$ppname($op) : default_pp($op);
	}
    }
}

sub save_runtime {
    runtime("#define DOOP(ppname) (void) ppname();",
	    "",
	    "PP($pp_runtime_name)",
	    "{");
    $level = 1;
    compile(main_start);
    warn "internal error: compile finished at level $level\n" if $level != 1;
    runtime("return 0;");
    $level--;
    runtime("}");
    $main_start_sym = main_start->save;
    $main_root_sym = main_root->save;
    $comppadlist_sym = comppadlist->save;
}

sub output_init {
    print <<"EOT";

static int
perl_init()
{
    perl_tree_init();

    main_start = $main_start_sym;
    main_root = $main_root_sym;
    main_start->op_ppaddr = $pp_runtime_name;
    curpad = AvARRAY((AV*)*av_fetch($comppadlist_sym, 1, TRUE));
    return 0;
}

EOT
}

sub import {
    my ($class) = @_;
    minus_c;
    eval 'END { save_runtime(); B::C::output_boilerplate(); B::C::output_all("perl_tree_init"); output_runtime(); output_init(); B::C::output_main(); }';
}

1;
