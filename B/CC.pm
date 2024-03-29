#      CC.pm
#
#      Copyright (c) 1996 Malcolm Beattie
#
#      You may distribute under the terms of either the GNU General Public
#      License or the Artistic License, as specified in the README file.
#
package B::CC;
use strict;
use B qw(main_start main_root class comppadlist peekop svref_2object ad
	timing_info);
use B::C qw(push_decl init_init push_init save_unused_subs objsym
	    output_all output_boilerplate output_main);
use B::Bblock qw(find_leaders);
use B::Stackobj qw(:types :flags);

# These should probably be elsewhere
# Flags for $op->flags
sub OPf_LIST () { 1 }
sub OPf_KNOW () { 2 }
sub OPf_MOD () { 32 }
sub OPf_STACKED () { 64 }
sub OPf_SPECIAL () { 128 }
# op-specific flags for $op->private 
sub OPpASSIGN_BACKWARDS () { 64 }
sub OPpLVAL_INTRO () { 128 }
sub OPpDEREF_AV () { 32 }
sub OPpDEREF_HV () { 64 }
sub OPpFLIP_LINENUM () { 64 }
sub G_ARRAY () { 1 }
# cop.h
sub CXt_NULL () { 0 }
sub CXt_SUB () { 1 }
sub CXt_EVAL () { 2 }
sub CXt_LOOP () { 3 }
sub CXt_SUBST () { 4 }
sub CXt_BLOCK () { 5 }

my %done;		# hash keyed by $$op of leaders of basic blocks
			# which have already been done.
my $leaders;		# ref to hash of basic block leaders. Keys are $$op
			# addresses, values are the $op objects themselves.
my @bblock_todo;	# list of leaders of basic blocks that need visiting
			# sometime.
my @cc_todo;		# list of tuples defining what PP code needs to be
			# saved (e.g. CV, main or PMOP repl code). Each tuple
			# is [$name, $root, $start, @padlist]. PMOP repl code
			# tuples inherit padlist.
my @stack;		# shadows perl's stack when contents are known.
			# Values are objects derived from class B::Stackobj
my @pad;		# Lexicals in current pad as Stackobj-derived objects
my @padlist;		# Copy of current padlist so PMOP repl code can find it
my @cxstack;		# Shadows the (compile-time) cxstack for next,last,redo
my $jmpbuf_ix = 0;	# Next free index for dynamically allocated jmpbufs
my %constobj;		# OP_CONST constants as Stackobj-derived objects
			# keyed by ad($sv).
my $need_freetmps = 0;	# We may postpone FREETMPS to the end of each basic
			# block or even to the end of each loop of blocks,
			# depending on optimisation options.
my $know_op = 0;	# Set when C variable op already holds the right op
			# (from an immediately preceding DOOP(ppname)).
my $errors = 0;		# Number of errors encountered
my %skip_stack;		# Hash of PP names which don't need write_back_stack
my %skip_lexicals;	# Hash of PP names which don't need write_back_lexicals
my %skip_invalidate;	# Hash of PP names which don't need invalidate_lexicals
my %ignore_op;		# Hash of ops which do nothing except returning op_next

BEGIN {
    foreach (qw(pp_scalar pp_regcmaybe pp_lineseq pp_scope pp_null)) {
	$ignore_op{$_} = 1;
    }
}

my @unused_sub_packages; # list of packages (given by -u options) to search
			 # explicitly and save every sub we find there, even
			 # if apparently unused (could be only referenced from
			 # an eval "" or from a $SIG{FOO} = "bar").

my ($module_name);
my ($debug_op, $debug_stack, $debug_cxstack, $debug_pad, $debug_runtime,
    $debug_shadow, $debug_queue, $debug_lineno, $debug_timings);

# Optimisation options. On the command line, use hyphens instead of
# underscores for compatibility with gcc-style options. We use
# underscores here because they are OK in (strict) barewords.
my ($freetmps_each_bblock, $freetmps_each_loop, $omit_taint);
my %optimise = (freetmps_each_bblock	=> \$freetmps_each_bblock,
		freetmps_each_loop	=> \$freetmps_each_loop,
		omit_taint		=> \$omit_taint);

# Could rewrite push_runtime() and output_runtime() to use a
# temporary file if memory is at a premium.
my $ppname;		# name of current fake PP function
my $runtime_list_ref;
my $declare_ref;	# Hash ref keyed by C variable type of declarations.

my @pp_list;		# list of [$ppname, $runtime_list_ref, $declare_ref]
			# tuples to be written out.

sub init_hash { map { $_ => 1 } @_ }

#
# Initialise the hashes for the default PP functions where we can avoid
# either write_back_stack, write_back_lexicals or invalidate_lexicals.
#
%skip_lexicals = init_hash qw(pp_enter pp_enterloop);
%skip_invalidate = init_hash qw(pp_enter pp_enterloop);

sub debug {
    if ($debug_runtime) {
	warn(@_);
    } else {
	runtime(map { chomp; "/* $_ */"} @_);
    }
}

sub declare {
    my ($type, $var) = @_;
    push(@{$declare_ref->{$type}}, $var);
}

sub push_runtime {
    push(@$runtime_list_ref, @_);
    warn join("\n", @_) . "\n" if $debug_runtime;
}

sub save_runtime {
    push(@pp_list, [$ppname, $runtime_list_ref, $declare_ref]);
}

sub output_runtime {
    my $ppdata;
    print qq(#include "cc_runtime.h"\n);
    foreach $ppdata (@pp_list) {
	my ($name, $runtime, $declare) = @$ppdata;
	print "\nstatic\nPP($name)\n{\n";
	my ($type, $varlist, $line);
	while (($type, $varlist) = each %$declare) {
	    print "\t$type ", join(", ", @$varlist), ";\n";
	}
	foreach $line (@$runtime) {
	    print $line, "\n";
	}
	print "}\n";
    }
}

sub runtime {
    my $line;
    foreach $line (@_) {
	push_runtime("\t$line");
    }
}

sub init_pp {
    $ppname = shift;
    $runtime_list_ref = [];
    $declare_ref = {};
    runtime("dSP;");
    declare("I32", "oldsave");
    declare("SV", "**svp");
    map { declare("SV", "*$_") } qw(sv src dst left right);
    declare("MAGIC", "*mg");
    push_decl("static OP * $ppname _((ARGSproto));");
    debug "init_pp: $ppname\n" if $debug_queue;
}

# Initialise runtime_callback function for Stackobj class
BEGIN { B::Stackobj::set_callback(\&runtime) }

# Initialise saveoptree_callback for B::C class
sub cc_queue {
    my ($name, $root, $start, @pl) = @_;
    debug "cc_queue: name $name, root $root, start $start, padlist (@pl)\n"
	if $debug_queue;
    if ($name eq "*ignore*") {
	$name = 0;
    } else {
	push(@cc_todo, [$name, $root, $start, (@pl ? @pl : @padlist)]);
    }
    my $fakeop = new B::FAKEOP ("next" => 0, sibling => 0, ppaddr => $name);
    $start = $fakeop->save;
    debug "cc_queue: name $name returns $start\n" if $debug_queue;
    return $start;
}
BEGIN { B::C::set_callback(\&cc_queue) }

sub valid_int { $_[0]->{flags} & VALID_INT }
sub valid_double { $_[0]->{flags} & VALID_DOUBLE }
sub valid_numeric { $_[0]->{flags} & (VALID_INT | VALID_DOUBLE) }
sub valid_sv { $_[0]->{flags} & VALID_SV }

sub top_int { @stack ? $stack[-1]->as_int : "TOPi" }
sub top_double { @stack ? $stack[-1]->as_double : "TOPn" }
sub top_numeric { @stack ? $stack[-1]->as_numeric : "TOPn" }
sub top_sv { @stack ? $stack[-1]->as_sv : "TOPs" }
sub top_bool { @stack ? $stack[-1]->as_numeric : "SvTRUE(TOPs)" }

sub pop_int { @stack ? (pop @stack)->as_int : "POPi" }
sub pop_double { @stack ? (pop @stack)->as_double : "POPn" }
sub pop_numeric { @stack ? (pop @stack)->as_numeric : "POPn" }
sub pop_sv { @stack ? (pop @stack)->as_sv : "POPs" }
sub pop_bool {
    if (@stack) {
	return ((pop @stack)->as_numeric);
    } else {
	# Careful: POPs has an auto-decrement and SvTRUE evaluates
	# its argument more than once.
	runtime("sv = POPs;");
	return "SvTRUE(sv)";
    }
}

sub write_back_lexicals {
    my $avoid = shift || 0;
    debug "write_back_lexicals($avoid) called from @{[(caller(1))[3]]}\n"
	if $debug_shadow;
    my $lex;
    foreach $lex (@pad) {
	next unless ref($lex);
	$lex->write_back unless $lex->{flags} & $avoid;
    }
}

sub write_back_stack {
    my $obj;
    return unless @stack;
    runtime(sprintf("EXTEND(sp, %d);", scalar(@stack)));
    foreach $obj (@stack) {
	runtime(sprintf("PUSHs((SV*)%s);", $obj->as_sv));
    }
    @stack = ();
}

sub invalidate_lexicals {
    my $avoid = shift || 0;
    debug "invalidate_lexicals($avoid) called from @{[(caller(1))[3]]}\n"
	if $debug_shadow;
    my $lex;
    foreach $lex (@pad) {
	next unless ref($lex);
	$lex->invalidate unless $lex->{flags} & $avoid;
    }
}

sub reload_lexicals {
    my $lex;
    foreach $lex (@pad) {
	next unless ref($lex);
	my $type = $lex->{type};
	if ($type == T_INT) {
	    $lex->as_int;
	} elsif ($type == T_DOUBLE) {
	    $lex->as_double;
	} else {
	    $lex->as_sv;
	}
    }
}

{
    package B::Pseudoreg;
    #
    # This class allocates pseudo-registers (OK, so they're C variables).
    #
    my %alloc;		# Keyed by variable name. A value of 1 means the
			# variable has been declared. A value of 2 means
			# it's in use.
    
    sub new_scope { %alloc = () }
    
    sub new ($$$) {
	my ($class, $type, $prefix) = @_;
	my ($ptr, $i, $varname, $status, $obj);
	$prefix =~ s/^(\**)//;
	$ptr = $1;
	$i = 0;
	do {
	    $varname = "$prefix$i";
	    $status = $alloc{$varname};
	} while $status == 2;
	if ($status != 1) {
	    # Not declared yet
	    B::CC::declare($type, "$ptr$varname");
	    $alloc{$varname} = 2;	# declared and in use
	}
	$obj = bless \$varname, $class;
	return $obj;
    }
    sub DESTROY {
	my $obj = shift;
	$alloc{$$obj} = 1; # no longer in use but still declared
    }
}
{
    package B::Shadow;
    #
    # This class gives a standard API for a perl object to shadow a
    # C variable and only generate reloads/write-backs when necessary.
    #
    # Use $obj->load($foo) instead of runtime("shadowed_c_var = foo").
    # Use $obj->write_back whenever shadowed_c_var needs to be up to date.
    # Use $obj->invalidate whenever an unknown function may have
    # set shadow itself.

    sub new {
	my ($class, $write_back) = @_;
	# Object fields are perl shadow variable, validity flag
	# (for *C* variable) and callback sub for write_back
	# (passed perl shadow variable as argument).
	bless [undef, 1, $write_back], $class;
    }
    sub load {
	my ($obj, $newval) = @_;
	$obj->[1] = 0;		# C variable no longer valid
	$obj->[0] = $newval;
    }
    sub write_back {
	my $obj = shift;
	if (!($obj->[1])) {
	    $obj->[1] = 1;	# C variable will now be valid
	    &{$obj->[2]}($obj->[0]);
	}
    }
    sub invalidate { $_[0]->[1] = 0 } # force C variable to be invalid
}
my $curcop = new B::Shadow (sub {
    my $opsym = shift->save;
    runtime("curcop = (COP*)$opsym;");
});

#
# Context stack shadowing. Mimics stuff in pp_ctl.c, cop.h and so on.
#
sub dopoptoloop {
    my $cxix = $#cxstack;
    while ($cxix >= 0 && $cxstack[$cxix]->{type} != CXt_LOOP) {
	$cxix--;
    }
    debug "dopoptoloop: returning $cxix" if $debug_cxstack;
    return $cxix;
}

sub dopoptolabel {
    my $label = shift;
    my $cxix = $#cxstack;
    while ($cxix >= 0 && $cxstack[$cxix]->{type} != CXt_LOOP
	   && $cxstack[$cxix]->{label} ne $label) {
	$cxix--;
    }
    debug "dopoptolabel: returning $cxix" if $debug_cxstack;
    return $cxix;
}

sub error {
    my $format = shift;
    my $file = $curcop->[0]->filegv->SV->PV;
    my $line = $curcop->[0]->line;
    $errors++;
    if (@_) {
	warn sprintf("%s:%d: $format\n", $file, $line, @_);
    } else {
	warn sprintf("%s:%d: %s\n", $file, $line, $format);
    }
}

#
# Load pad takes (the elements of) a PADLIST as arguments and loads
# up @pad with Stackobj-derived objects which represent those lexicals.
# If/when perl itself can generate type information (my int $foo) then
# we'll take advantage of that here. Until then, we'll use various hacks
# to tell the compiler when we want a lexical to be a particular type
# or to be a register.
#
sub load_pad {
    my ($namelistav, $valuelistav) = @_;
    @padlist = @_;
    my @namelist = $namelistav->ARRAY;
    my @valuelist = $valuelistav->ARRAY;
    my $ix;
    @pad = ();
    debug "load_pad: $#namelist names, $#valuelist values\n" if $debug_pad;
    # Temporary lexicals don't get named so it's possible for @valuelist
    # to be strictly longer than @namelist. We count $ix up to the end of
    # @valuelist but index into @namelist for the name. Any temporaries which
    # run off the end of @namelist will make $namesv undefined and we treat
    # that the same as having an explicit SPECIAL sv_undef object in @namelist.
    # [XXX If/when @_ becomes a lexical, we must start at 0 here.]
    for ($ix = 1; $ix < @valuelist; $ix++) {
	my $namesv = $namelist[$ix];
	my $type = T_UNKNOWN;
	my $flags = 0;
	my $name = "tmp$ix";
	my $class = class($namesv);
	if (!defined($namesv) || $class eq "SPECIAL") {
	    # temporaries have &sv_undef instead of a PVNV for a name
	    $flags = VALID_SV|TEMPORARY|REGISTER;
	} else {
	    if ($namesv->PV =~ /^\$(.*)_([di])(r?)$/) {
		$name = $1;
		if ($2 eq "i") {
		    $type = T_INT;
		    $flags = VALID_SV|VALID_INT;
		} elsif ($2 eq "d") {
		    $type = T_DOUBLE;
		    $flags = VALID_SV|VALID_DOUBLE;
		}
		$flags |= REGISTER if $3;
	    }
	}
	$pad[$ix] = new B::Stackobj::Padsv ($type, $flags, $ix,
					    "i_$name", "d_$name");
	declare("IV", $type == T_INT ? "i_$name = 0" : "i_$name");
	declare("double", $type == T_DOUBLE ? "d_$name = 0" : "d_$name");
	debug sprintf("curpad[$ix] = %s\n", $pad[$ix]->peek) if $debug_pad;
    }
}

#
# Debugging stuff
#
sub peek_stack { sprintf "stack = %s\n", join(" ", map($_->minipeek, @stack)) }

#
# OP stuff
#

sub label {
    my $op = shift;
    # XXX Preserve original label name for "real" labels?
    return sprintf("lab_%x", $$op);
}

sub write_label {
    my $op = shift;
    push_runtime(sprintf("  %s:", label($op)));
}

sub loadop {
    my $op = shift;
    my $opsym = $op->save;
    runtime("op = $opsym;") unless $know_op;
    return $opsym;
}

sub doop {
    my $op = shift;
    my $ppname = $op->ppaddr;
    my $sym = loadop($op);
    runtime("DOOP($ppname);");
    $know_op = 1;
    return $sym;
}

sub gimme {
    my $op = shift;
    my $flags = $op->flags;
    return (($flags & OPf_KNOW) ? ($flags & OPf_LIST) : "dowantarray()");
}

#
# Code generation for PP code
#

sub pp_null {
    my $op = shift;
    return $op->next;
}

sub pp_stub {
    my $op = shift;
    my $gimme = gimme($op);
    if ($gimme != 1) {
	# XXX Change to push a constant sv_undef Stackobj onto @stack
	write_back_stack();
	runtime("if ($gimme != G_ARRAY) XPUSHs(&sv_undef);");
    }
    return $op->next;
}

sub pp_unstack {
    my $op = shift;
    @stack = ();
    runtime("PP_UNSTACK;");
    return $op->next;
}

sub pp_and {
    my $op = shift;
    my $next = $op->next;
    reload_lexicals();
    unshift(@bblock_todo, $next);
    if (@stack >= 1) {
	my $bool = pop_bool();
	write_back_stack();
	runtime(sprintf("if (!$bool) goto %s;", label($next)));
    } else {
	runtime(sprintf("if (!%s) goto %s;", top_bool(), label($next)),
		"*sp--;");
    }
    return $op->other;
}
	    
sub pp_or {
    my $op = shift;
    my $next = $op->next;
    reload_lexicals();
    unshift(@bblock_todo, $next);
    if (@stack >= 1) {
	my $obj = pop @stack;
	write_back_stack();
	runtime(sprintf("if (%s) { XPUSHs(%s); goto %s; }",
			$obj->as_numeric, $obj->as_sv, label($next)));
    } else {
	runtime(sprintf("if (%s) goto %s;", top_bool(), label($next)),
		"*sp--;");
    }
    return $op->other;
}
	    
sub pp_cond_expr {
    my $op = shift;
    my $false = $op->false;
    unshift(@bblock_todo, $false);
    reload_lexicals();
    my $bool = pop_bool();
    write_back_stack();
    runtime(sprintf("if (!$bool) goto %s;", label($false)));
    return $op->true;
}
	    

sub pp_padsv {
    my $op = shift;
    my $ix = $op->targ;
    push(@stack, $pad[$ix]);
    if ($op->flags & OPf_MOD) {
	my $private = $op->private;
	if ($private & OPpLVAL_INTRO) {
	    runtime("SAVECLEARSV(curpad[$ix]);");
	} elsif ($private & (OPpDEREF_HV|OPpDEREF_AV)) {
	    loadop($op);
	    runtime("provide_ref(op, curpad[$ix]);");
	    $pad[$ix]->invalidate;
	}
    }
    return $op->next;
}

sub pp_const {
    my $op = shift;
    my $sv = $op->sv;
    my $obj = $constobj{ad($sv)};
    if (!defined($obj)) {
	$obj = $constobj{ad($sv)} = new B::Stackobj::Const ($sv);
    }
    push(@stack, $obj);
    return $op->next;
}

sub pp_nextstate {
    my $op = shift;
    $curcop->load($op);
    @stack = ();
    debug(sprintf("%s:%d\n", $op->filegv->SV->PV, $op->line)) if $debug_lineno;
    runtime("TAINT_NOT;") unless $omit_taint;
    runtime("sp = stack_base + cxstack[cxstack_ix].blk_oldsp;");
    if ($freetmps_each_bblock || $freetmps_each_loop) {
	$need_freetmps = 1;
    } else {
	runtime("FREETMPS;");
    }
    return $op->next;
}

sub pp_dbstate {
    my $op = shift;
    $curcop->invalidate; # XXX?
    return default_pp($op);
}

sub pp_rv2gv { $curcop->write_back; default_pp(@_) }
sub pp_bless { $curcop->write_back; default_pp(@_) }
sub pp_repeat { $curcop->write_back; default_pp(@_) }
# The following subs need $curcop->write_back if we decide to support arybase:
# pp_pos, pp_substr, pp_index, pp_rindex, pp_aslice, pp_lslice, pp_splice
sub pp_sort { $curcop->write_back; default_pp(@_) }
sub pp_caller { $curcop->write_back; default_pp(@_) }
sub pp_reset { $curcop->write_back; default_pp(@_) }

sub pp_gv {
    my $op = shift;
    my $gvsym = $op->gv->save;
    write_back_stack();
    runtime("XPUSHs((SV*)$gvsym);");
    return $op->next;
}

sub pp_gvsv {
    my $op = shift;
    my $gvsym = $op->gv->save;
    write_back_stack();
    if ($op->private & OPpLVAL_INTRO) {
	runtime("XPUSHs(save_scalar($gvsym));");
    } else {
	runtime("XPUSHs(GvSV($gvsym));");
    }
    return $op->next;
}

sub pp_aelemfast {
    my $op = shift;
    my $gvsym = $op->gv->save;
    my $ix = $op->private;
    my $flag = $op->flags & OPf_MOD;
    write_back_stack();
    runtime("svp = av_fetch(GvAV($gvsym), $ix, $flag);",
	    "PUSHs(svp ? *svp : &sv_undef);");
    return $op->next;
}

sub int_binop {
    my ($op, $operator) = @_;
    if ($op->flags & OPf_STACKED) {
	my $right = pop_int();
	if (@stack >= 1) {
	    my $left = top_int();
	    $stack[-1]->set_int(&$operator($left, $right));
	} else {
	    runtime(sprintf("sv_setiv(TOPs, %s);",&$operator("TOPi", $right)));
	}
    } else {
	my $targ = $pad[$op->targ];
	my $right = new B::Pseudoreg ("IV", "riv");
	my $left = new B::Pseudoreg ("IV", "liv");
	runtime(sprintf("$$right = %s; $$left = %s;", pop_int(), pop_int));
	$targ->set_int(&$operator($$left, $$right));
	push(@stack, $targ);
    }
    return $op->next;
}

sub INTS_CLOSED () { 0x1 }
sub INT_RESULT () { 0x2 }
sub NUMERIC_RESULT () { 0x4 }

sub numeric_binop {
    my ($op, $operator, $flags) = @_;
    my $force_int = 0;
    $force_int ||= ($flags & INT_RESULT);
    $force_int ||= ($flags & INTS_CLOSED && @stack >= 2
		    && valid_int($stack[-2]) && valid_int($stack[-1]));
    if ($op->flags & OPf_STACKED) {
	my $right = pop_numeric();
	if (@stack >= 1) {
	    my $left = top_numeric();
	    if ($force_int) {
		$stack[-1]->set_int(&$operator($left, $right));
	    } else {
		$stack[-1]->set_numeric(&$operator($left, $right));
	    }
	} else {
	    if ($force_int) {
		runtime(sprintf("sv_setiv(TOPs, %s);",
				&$operator("TOPi", $right)));
	    } else {
		runtime(sprintf("sv_setnv(TOPs, %s);",
				&$operator("TOPn", $right)));
	    }
	}
    } else {
	my $targ = $pad[$op->targ];
	$force_int ||= ($targ->{type} == T_INT);
	if ($force_int) {
	    my $right = new B::Pseudoreg ("IV", "riv");
	    my $left = new B::Pseudoreg ("IV", "liv");
	    runtime(sprintf("$$right = %s; $$left = %s;",
			    pop_numeric(), pop_numeric));
	    $targ->set_int(&$operator($$left, $$right));
	} else {
	    my $right = new B::Pseudoreg ("double", "rnv");
	    my $left = new B::Pseudoreg ("double", "lnv");
	    runtime(sprintf("$$right = %s; $$left = %s;",
			    pop_numeric(), pop_numeric));
	    $targ->set_numeric(&$operator($$left, $$right));
	}
	push(@stack, $targ);
    }
    return $op->next;
}

sub sv_binop {
    my ($op, $operator, $flags) = @_;
    if ($op->flags & OPf_STACKED) {
	my $right = pop_sv();
	if (@stack >= 1) {
	    my $left = top_sv();
	    if ($flags & INT_RESULT) {
		$stack[-1]->set_int(&$operator($left, $right));
	    } elsif ($flags & NUMERIC_RESULT) {
		$stack[-1]->set_numeric(&$operator($left, $right));
	    } else {
		# XXX Does this work?
		runtime(sprintf("sv_setsv($left, %s);",
				&$operator($left, $right)));
		$stack[-1]->invalidate;
	    }
	} else {
	    my $f;
	    if ($flags & INT_RESULT) {
		$f = "sv_setiv";
	    } elsif ($flags & NUMERIC_RESULT) {
		$f = "sv_setnv";
	    } else {
		$f = "sv_setsv";
	    }
	    runtime(sprintf("%s(TOPs, %s);", $f, &$operator("TOPs", $right)));
	}
    } else {
	my $targ = $pad[$op->targ];
	runtime(sprintf("right = %s; left = %s;", pop_sv(), pop_sv));
	if ($flags & INT_RESULT) {
	    $targ->set_int(&$operator("left", "right"));
	} elsif ($flags & NUMERIC_RESULT) {
	    $targ->set_numeric(&$operator("left", "right"));
	} else {
	    # XXX Does this work?
	    runtime(sprintf("sv_setsv(%s, %s);",
			    $targ->as_sv, &$operator("left", "right")));
	    $targ->invalidate;
	}
	push(@stack, $targ);
    }
    return $op->next;
}
    
sub bool_int_binop {
    my ($op, $operator) = @_;
    my $right = new B::Pseudoreg ("IV", "riv");
    my $left = new B::Pseudoreg ("IV", "liv");
    runtime(sprintf("$$right = %s; $$left = %s;", pop_int(), pop_int()));
    my $bool = new B::Stackobj::Bool (new B::Pseudoreg ("int", "b"));
    $bool->set_int(&$operator($$left, $$right));
    push(@stack, $bool);
    return $op->next;
}

sub bool_numeric_binop {
    my ($op, $operator) = @_;
    my $right = new B::Pseudoreg ("double", "rnv");
    my $left = new B::Pseudoreg ("double", "lnv");
    runtime(sprintf("$$right = %s; $$left = %s;",
		    pop_numeric(), pop_numeric()));
    my $bool = new B::Stackobj::Bool (new B::Pseudoreg ("int", "b"));
    $bool->set_numeric(&$operator($$left, $$right));
    push(@stack, $bool);
    return $op->next;
}

sub bool_sv_binop {
    my ($op, $operator) = @_;
    runtime(sprintf("right = %s; left = %s;", pop_sv(), pop_sv()));
    my $bool = new B::Stackobj::Bool (new B::Pseudoreg ("int", "b"));
    $bool->set_numeric(&$operator("left", "right"));
    push(@stack, $bool);
    return $op->next;
}

sub infix_op {
    my $opname = shift;
    return sub { "$_[0] $opname $_[1]" }
}

sub prefix_op {
    my $opname = shift;
    return sub { sprintf("%s(%s)", $opname, join(", ", @_)) }
}

BEGIN {
    my $plus_op = infix_op("+");
    my $minus_op = infix_op("-");
    my $multiply_op = infix_op("*");
    my $divide_op = infix_op("/");
    my $modulo_op = infix_op("%");
    my $lshift_op = infix_op("<<");
    my $rshift_op = infix_op("<<");
    my $ncmp_op = sub { "($_[0] > $_[1] ? 1 : ($_[0] < $_[1]) ? -1 : 0)" };
    my $scmp_op = prefix_op("sv_cmp");
    my $seq_op = prefix_op("sv_eq");
    my $sne_op = prefix_op("!sv_eq");
    my $slt_op = sub { "sv_cmp($_[0], $_[1]) < 0" };
    my $sgt_op = sub { "sv_cmp($_[0], $_[1]) > 0" };
    my $sle_op = sub { "sv_cmp($_[0], $_[1]) <= 0" };
    my $sge_op = sub { "sv_cmp($_[0], $_[1]) >= 0" };
    my $eq_op = infix_op("==");
    my $ne_op = infix_op("!=");
    my $lt_op = infix_op("<");
    my $gt_op = infix_op(">");
    my $le_op = infix_op("<=");
    my $ge_op = infix_op(">=");

    #
    # XXX The standard perl PP code has extra handling for
    # some special case arguments of these operators.
    #
    sub pp_add { numeric_binop($_[0], $plus_op, INTS_CLOSED) }
    sub pp_subtract { numeric_binop($_[0], $minus_op, INTS_CLOSED) }
    sub pp_multiply { numeric_binop($_[0], $multiply_op, INTS_CLOSED) }
    sub pp_divide { numeric_binop($_[0], $divide_op) }
    sub pp_modulo { int_binop($_[0], $modulo_op) } # differs from perl's
    sub pp_ncmp { numeric_binop($_[0], $ncmp_op, INT_RESULT) }

    sub pp_left_shift { int_binop($_[0], $lshift_op) }
    sub pp_right_shift { int_binop($_[0], $rshift_op) }
    sub pp_i_add { int_binop($_[0], $plus_op) }
    sub pp_i_subtract { int_binop($_[0], $minus_op) }
    sub pp_i_multiply { int_binop($_[0], $multiply_op) }
    sub pp_i_divide { int_binop($_[0], $divide_op) }
    sub pp_i_modulo { int_binop($_[0], $modulo_op) }

    sub pp_eq { bool_numeric_binop($_[0], $eq_op) }
    sub pp_ne { bool_numeric_binop($_[0], $ne_op) }
    sub pp_lt { bool_numeric_binop($_[0], $lt_op) }
    sub pp_gt { bool_numeric_binop($_[0], $gt_op) }
    sub pp_le { bool_numeric_binop($_[0], $le_op) }
    sub pp_ge { bool_numeric_binop($_[0], $ge_op) }

    sub pp_i_eq { bool_int_binop($_[0], $eq_op) }
    sub pp_i_ne { bool_int_binop($_[0], $ne_op) }
    sub pp_i_lt { bool_int_binop($_[0], $lt_op) }
    sub pp_i_gt { bool_int_binop($_[0], $gt_op) }
    sub pp_i_le { bool_int_binop($_[0], $le_op) }
    sub pp_i_ge { bool_int_binop($_[0], $ge_op) }

    sub pp_scmp { sv_binop($_[0], $scmp_op, INT_RESULT) }
    sub pp_slt { bool_sv_binop($_[0], $slt_op) }
    sub pp_sgt { bool_sv_binop($_[0], $sgt_op) }
    sub pp_sle { bool_sv_binop($_[0], $sle_op) }
    sub pp_sge { bool_sv_binop($_[0], $sge_op) }
    sub pp_seq { bool_sv_binop($_[0], $seq_op) }
    sub pp_sne { bool_sv_binop($_[0], $sne_op) }
}


sub pp_sassign {
    my $op = shift;
    my $backwards = $op->private & OPpASSIGN_BACKWARDS;
    my ($dst, $src);
    if (@stack >= 2) {
	$dst = pop @stack;
	$src = pop @stack;
	($src, $dst) = ($dst, $src) if $backwards;
	my $type = $src->{type};
	if ($type == T_INT) {
	    $dst->set_int($src->as_int);
	} elsif ($type == T_DOUBLE) {
	    $dst->set_numeric($src->as_numeric);
	} else {
	    $dst->set_sv($src->as_sv);
	}
	push(@stack, $dst);
    } elsif (@stack == 1) {
	if ($backwards) {
	    my $src = pop @stack;
	    my $type = $src->{type};
	    runtime("if (tainting && tainted) TAINT_NOT;");
	    if ($type == T_INT) {
		runtime sprintf("sv_setiv(TOPs, %s);", $src->as_int);
	    } elsif ($type == T_DOUBLE) {
		runtime sprintf("sv_setnv(TOPs, %s);", $src->as_double);
	    } else {
		runtime sprintf("sv_setsv(TOPs, %s);", $src->as_sv);
	    }
	    runtime("SvSETMAGIC(TOPs);");
	} else {
	    my $dst = pop @stack;
	    my $type = $dst->{type};
	    runtime("sv = POPs;");
	    runtime("MAYBE_TAINT_SASSIGN_SRC(sv);");
	    if ($type == T_INT) {
		$dst->set_int("SvIV(sv)");
	    } elsif ($type == T_DOUBLE) {
		$dst->set_double("SvNV(sv)");
	    } else {
		runtime("SvSetSV($dst->{sv}, sv);");
		$dst->invalidate;
	    }
	}
    } else {
	if ($backwards) {
	    runtime("src = POPs; dst = TOPs;");
	} else {
	    runtime("dst = POPs; src = TOPs;");
	}
	runtime("MAYBE_TAINT_SASSIGN_SRC(src);",
		"SvSetSV(dst, src);",
		"SvSETMAGIC(dst);",
		"SETs(dst);");
    }
    return $op->next;
}

sub pp_preinc {
    my $op = shift;
    if (@stack >= 1) {
	my $obj = $stack[-1];
	my $type = $obj->{type};
	if ($type == T_INT || $type == T_DOUBLE) {
	    $obj->set_int($obj->as_int . " + 1");
	} else {
	    runtime sprintf("PP_PREINC(%s);", $obj->as_sv);
	    $obj->invalidate();
	}
    } else {
	runtime sprintf("PP_PREINC(TOPs);");
    }
    return $op->next;
}

sub pp_pushmark {
    my $op = shift;
    write_back_stack();
    runtime("PUSHMARK(sp);");
    return $op->next;
}

sub pp_list {
    my $op = shift;
    write_back_stack();
    my $gimme = gimme($op);
    if ($gimme == 1) { # sic
	runtime("POPMARK;"); # need this even though not a "full" pp_list
    } else {
	runtime("PP_LIST($gimme);");
    }
    return $op->next;
}

sub pp_entersub {
    my $op = shift;
    write_back_lexicals(REGISTER|TEMPORARY);
    write_back_stack();
    my $sym = doop($op);
    runtime("if (op != ($sym)->op_next) op = (*op->op_ppaddr)();");
    runtime("SPAGAIN;");
    $know_op = 0;
    invalidate_lexicals(REGISTER|TEMPORARY);
    return $op->next;
}

sub doeval {
    my $op = shift;
    $curcop->write_back;
    write_back_lexicals(REGISTER|TEMPORARY);
    write_back_stack();
    my $sym = loadop($op);
    my $ppaddr = $op->ppaddr;
    runtime("PP_EVAL($ppaddr, ($sym)->op_next);");
    $know_op = 1;
    invalidate_lexicals(REGISTER|TEMPORARY);
    return $op->next;
}

sub pp_entereval { doeval(@_) }
sub pp_require { doeval(@_) }
sub pp_dofile { doeval(@_) }

sub pp_entertry {
    my $op = shift;
    $curcop->write_back;
    write_back_lexicals(REGISTER|TEMPORARY);
    write_back_stack();
    my $sym = doop($op);
    my $jmpbuf = sprintf("jmpbuf%d", $jmpbuf_ix++);
    declare("Sigjmp_buf", $jmpbuf);
    runtime(sprintf("PP_ENTERTRY(%s,%s);", $jmpbuf, label($op->other->next)));
    invalidate_lexicals(REGISTER|TEMPORARY);
    return $op->next;
}

sub pp_grepstart {
    my $op = shift;
    if ($need_freetmps && $freetmps_each_loop) {
	runtime("FREETMPS;"); # otherwise the grepwhile loop messes things up
	$need_freetmps = 0;
    }
    write_back_stack();
    doop($op);
    return $op->next->other;
}

sub pp_mapstart {
    my $op = shift;
    if ($need_freetmps && $freetmps_each_loop) {
	runtime("FREETMPS;"); # otherwise the mapwhile loop messes things up
	$need_freetmps = 0;
    }
    write_back_stack();
    doop($op);
    return $op->next->other;
}

sub pp_grepwhile {
    my $op = shift;
    my $next = $op->next;
    unshift(@bblock_todo, $next);
    write_back_lexicals();
    write_back_stack();
    my $sym = doop($op);
    # pp_grepwhile can return either op_next or op_other and we need to
    # be able to distinguish the two at runtime. Since it's possible for
    # both ops to be "inlined", the fields could both be zero. To get
    # around that, we hack op_next to be our own op (purely because we
    # know it's a non-NULL pointer and can't be the same as op_other).
    push_init("((LOGOP*)$sym)->op_next = $sym;");
    runtime(sprintf("if (op == ($sym)->op_next) goto %s;", label($next)));
    $know_op = 0;
    return $op->other;
}

sub pp_mapwhile {
    pp_grepwhile(@_);
}

sub pp_return {
    my $op = shift;
    write_back_lexicals(REGISTER|TEMPORARY);
    write_back_stack();
    doop($op);
    runtime("PUTBACK;", "return 0;");
    $know_op = 0;
    return $op->next;
}

sub nyi {
    my $op = shift;
    warn sprintf("%s not yet implemented properly\n", $op->ppaddr);
    return default_pp($op);
}

sub pp_range {
    my $op = shift;
    my $flags = $op->flags;
    if (!($flags & OPf_KNOW)) {
	error("context of range unknown at compile-time");
    }
    write_back_lexicals();
    write_back_stack();
    if (!($flags & OPf_LIST)) {
	# We need to save our UNOP structure since pp_flop uses
	# it to find and adjust out targ. We don't need it ourselves.
	$op->save;
	runtime sprintf("if (SvTRUE(curpad[%d])) goto %s;",
			$op->targ, label($op->false));
	unshift(@bblock_todo, $op->false);
    }
    return $op->true;
}

sub pp_flip {
    my $op = shift;
    my $flags = $op->flags;
    if (!($flags & OPf_KNOW)) {
	error("context of flip unknown at compile-time");
    }
    if ($flags & OPf_LIST) {
	return $op->first->false;
    }
    write_back_lexicals();
    write_back_stack();
    # We need to save our UNOP structure since pp_flop uses
    # it to find and adjust out targ. We don't need it ourselves.
    $op->save;
    my $ix = $op->targ;
    my $rangeix = $op->first->targ;
    runtime(($op->private & OPpFLIP_LINENUM) ?
	    "if (last_in_gv && SvIV(TOPs) == IoLINES(GvIOp(last_in_gv))) {"
	  : "if (SvTRUE(TOPs)) {");
    runtime("\tsv_setiv(curpad[$rangeix], 1);");
    if ($op->flags & OPf_SPECIAL) {
	runtime("sv_setiv(curpad[$ix], 1);");
    } else {
	runtime("\tsv_setiv(curpad[$ix], 0);",
		"\tsp--;",
		sprintf("\tgoto %s;", label($op->first->false)));
    }
    runtime("}",
	  qq{sv_setpv(curpad[$ix], "");},
	    "SETs(curpad[$ix]);");
    $know_op = 0;
    return $op->next;
}

sub pp_flop {
    my $op = shift;
    default_pp($op);
    $know_op = 0;
    return $op->next;
}

sub enterloop {
    my $op = shift;
    my $nextop = $op->nextop;
    my $lastop = $op->lastop;
    my $redoop = $op->redoop;
    $curcop->write_back;
    debug "enterloop: pushing on cxstack" if $debug_cxstack;
    push(@cxstack, {
	type => CXt_LOOP,
	op => $op,
	"label" => $curcop->[0]->label,
	nextop => $nextop,
	lastop => $lastop,
	redoop => $redoop
    });
    $nextop->save;
    $lastop->save;
    $redoop->save;
    return default_pp($op);
}

sub pp_enterloop { enterloop(@_) }
sub pp_enteriter { enterloop(@_) }

sub pp_leaveloop {
    my $op = shift;
    if (!@cxstack) {
	die "panic: leaveloop";
    }
    debug "leaveloop: popping from cxstack" if $debug_cxstack;
    pop(@cxstack);
    return default_pp($op);
}

sub pp_next {
    my $op = shift;
    my $cxix;
    if ($op->flags & OPf_SPECIAL) {
	$cxix = dopoptoloop();
	if ($cxix < 0) {
	    error('"next" used outside loop');
	    return $op->next; # ignore the op
	}
    } else {
	$cxix = dopoptolabel($op->pv);
	if ($cxix < 0) {
	    error('Label not found at compile time for "next %s"', $op->pv);
	    return $op->next; # ignore the op
	}
    }
    default_pp($op);
    my $nextop = $cxstack[$cxix]->{nextop};
    push(@bblock_todo, $nextop);
    runtime(sprintf("goto %s;", label($nextop)));
    return $op->next;
}

sub pp_redo {
    my $op = shift;
    my $cxix;
    if ($op->flags & OPf_SPECIAL) {
	$cxix = dopoptoloop();
	if ($cxix < 0) {
	    error('"redo" used outside loop');
	    return $op->next; # ignore the op
	}
    } else {
	$cxix = dopoptolabel($op->pv);
	if ($cxix < 0) {
	    error('Label not found at compile time for "redo %s"', $op->pv);
	    return $op->next; # ignore the op
	}
    }
    default_pp($op);
    my $redoop = $cxstack[$cxix]->{redoop};
    push(@bblock_todo, $redoop);
    runtime(sprintf("goto %s;", label($redoop)));
    return $op->next;
}

sub pp_last {
    my $op = shift;
    my $cxix;
    if ($op->flags & OPf_SPECIAL) {
	$cxix = dopoptoloop();
	if ($cxix < 0) {
	    error('"last" used outside loop');
	    return $op->next; # ignore the op
	}
    } else {
	$cxix = dopoptolabel($op->pv);
	if ($cxix < 0) {
	    error('Label not found at compile time for "last %s"', $op->pv);
	    return $op->next; # ignore the op
	}
	# XXX Add support for "last" to leave non-loop blocks
	if ($cxstack[$cxix]->{type} != CXt_LOOP) {
	    error('Use of "last" for non-loop blocks is not yet implemented');
	    return $op->next; # ignore the op
	}
    }
    default_pp($op);
    my $lastop = $cxstack[$cxix]->{lastop}->next;
    push(@bblock_todo, $lastop);
    runtime(sprintf("goto %s;", label($lastop)));
    return $op->next;
}

sub pp_subst {
    my $op = shift;
    write_back_lexicals();
    write_back_stack();
    my $sym = doop($op);
    my $replroot = $op->pmreplroot;
    if (ad($replroot)) {
	runtime sprintf("if (op == ((PMOP*)(%s))->op_pmreplroot) goto %s;",
			$sym, label($replroot));
	$op->pmreplstart->save;
	push(@bblock_todo, $replroot);
    }
    invalidate_lexicals();
    return $op->next;
}

sub pp_substcont {
    my $op = shift;
    write_back_lexicals();
    write_back_stack();
    doop($op);
    my $pmop = $op->other;
    my $pmopsym = objsym($pmop);
    runtime sprintf("if (op == ((PMOP*)(%s))->op_pmreplstart) goto %s;",
		    $pmopsym, label($pmop->pmreplstart));
    invalidate_lexicals();
    return $pmop->next;
}

sub default_pp {
    my $op = shift;
    my $ppname = $op->ppaddr;
    write_back_lexicals() unless $skip_lexicals{$ppname};
    write_back_stack() unless $skip_stack{$ppname};
    doop($op);
    # XXX If the only way that ops can write to a TEMPORARY lexical is
    # when it's named in $op->targ then we could call
    # invalidate_lexicals(TEMPORARY) and avoid having to write back all
    # the temporaries. For now, we'll play it safe and write back the lot.
    invalidate_lexicals() unless $skip_invalidate{$ppname};
    return $op->next;
}

sub compile_op {
    my $op = shift;
    my $ppname = $op->ppaddr;
    if (exists $ignore_op{$ppname}) {
	return $op->next;
    }
    debug peek_stack() if $debug_stack;
    if ($debug_op) {
	debug sprintf("%s [%s]\n",
		     peekop($op),
		     $op->flags & OPf_STACKED ? "OPf_STACKED" : $op->targ);
    }
    no strict 'refs';
    if (defined(&$ppname)) {
	$know_op = 0;
	return &$ppname($op);
    } else {
	return default_pp($op);
    }
}

sub compile_bblock {
    my $op = shift;
    #warn "compile_bblock: ", peekop($op), "\n"; # debug
    write_label($op);
    $know_op = 0;
    do {
	$op = compile_op($op);
    } while (defined($op) && $$op && !exists($leaders->{$$op}));
    write_back_stack(); # boo hoo: big loss
    reload_lexicals();
    return $op;
}

sub cc {
    my ($name, $root, $start, @padlist) = @_;
    my $op;
    init_pp($name);
    load_pad(@padlist);
    B::Pseudoreg->new_scope;
    @cxstack = ();
    if ($debug_timings) {
	warn sprintf("Basic block analysis at %s\n", timing_info);
    }
    $leaders = find_leaders($root, $start);
    @bblock_todo = ($start, values %$leaders);
    if ($debug_timings) {
	warn sprintf("Compilation at %s\n", timing_info);
    }
    while (@bblock_todo) {
	$op = shift @bblock_todo;
	#warn sprintf("Considering basic block %s\n", peekop($op)); # debug
	next if !defined($op) || !$$op || $done{$$op};
	#warn "...compiling it\n"; # debug
	do {
	    $done{$$op} = 1;
	    $op = compile_bblock($op);
	    if ($need_freetmps && $freetmps_each_bblock) {
		runtime("FREETMPS;");
		$need_freetmps = 0;
	    }
	} while defined($op) && $$op && !$done{$$op};
	if ($need_freetmps && $freetmps_each_loop) {
	    runtime("FREETMPS;");
	    $need_freetmps = 0;
	}
	if (!$$op) {
	    runtime("PUTBACK;", "return 0;");
	} elsif ($done{$$op}) {
	    runtime(sprintf("goto %s;", label($op)));
	}
    }
    if ($debug_timings) {
	warn sprintf("Saving runtime at %s\n", timing_info);
    }
    save_runtime();
}

sub cc_recurse {
    my $ccinfo;
    my $start;
    $start = cc_queue(@_) if @_;
    while ($ccinfo = shift @cc_todo) {
	cc(@$ccinfo);
    }
    return $start;
}    

sub cc_obj {
    my ($name, $cvref) = @_;
    my $cv = svref_2object($cvref);
    my @padlist = $cv->PADLIST->ARRAY;
    my $curpad_sym = $padlist[1]->save;
    cc_recurse($name, $cv->ROOT, $cv->START, @padlist);
}

sub cc_main {
    my @comppadlist = comppadlist->ARRAY;
    my $curpad_sym = $comppadlist[1]->save;
    my $start = cc_recurse("pp_main", main_root, main_start, @comppadlist);
    if (@unused_sub_packages) {
	save_unused_subs(@unused_sub_packages);
	# That only queues them. Now we need to generate code for them.
	cc_recurse();
    }
    return if $errors;
    push_init(sprintf("main_root = sym_%x;", ad(main_root)),
	      "main_start = $start;",
	      "curpad = AvARRAY($curpad_sym);");
    output_boilerplate();
    print "\n";
    output_all("perl_init");
    output_runtime();
    print "\n";
    output_main();
    if ($debug_timings) {
	warn sprintf("Done at %s\n", timing_info);
    }
}

sub compile {
    my @options = @_;
    my ($option, $opt, $arg);
  OPTION:
    while ($option = shift @options) {
	if ($option =~ /^-(.)(.*)/) {
	    $opt = $1;
	    $arg = $2;
	} else {
	    unshift @options, $option;
	    last OPTION;
	}
	if ($opt eq "-" && $arg eq "-") {
	    shift @options;
	    last OPTION;
	} elsif ($opt eq "o") {
	    $arg ||= shift @options;
	    open(STDOUT, ">$arg") or return "$arg: $!\n";
	} elsif ($opt eq "n") {
	    $arg ||= shift @options;
	    $module_name = $arg;
	} elsif ($opt eq "u") {
	    $arg ||= shift @options;
	    push(@unused_sub_packages, $arg);
	} elsif ($opt eq "f") {
	    $arg ||= shift @options;
	    my $value = $arg !~ s/^no-//;
	    $arg =~ s/-/_/g;
	    my $ref = $optimise{$arg};
	    if (defined($ref)) {
		$$ref = $value;
	    } else {
		warn qq(ignoring unknown optimisation option "$arg"\n);
	    }
	} elsif ($opt eq "O") {
	    $arg = 1 if $arg eq "";
	    my $ref;
	    foreach $ref (values %optimise) {
		$$ref = 0;
	    }
	    if ($arg >= 2) {
		$freetmps_each_loop = 1;
	    }
	    if ($arg >= 1) {
		$freetmps_each_bblock = 1 unless $freetmps_each_loop;
	    }
	} elsif ($opt eq "D") {
            $arg ||= shift @options;
	    foreach $arg (split(//, $arg)) {
		if ($arg eq "o") {
		    B->debug(1);
		} elsif ($arg eq "O") {
		    $debug_op = 1;
		} elsif ($arg eq "s") {
		    $debug_stack = 1;
		} elsif ($arg eq "c") {
		    $debug_cxstack = 1;
		} elsif ($arg eq "p") {
		    $debug_pad = 1;
		} elsif ($arg eq "r") {
		    $debug_runtime = 1;
		} elsif ($arg eq "S") {
		    $debug_shadow = 1;
		} elsif ($arg eq "q") {
		    $debug_queue = 1;
		} elsif ($arg eq "l") {
		    $debug_lineno = 1;
		} elsif ($arg eq "t") {
		    $debug_timings = 1;
		}
	    }
	}
    }
    init_init();
    if (@options) {
	return sub {
	    my ($objname, $ppname);
	    foreach $objname (@options) {
		$objname = "main::$objname" unless $objname =~ /::/;
		($ppname = $objname) =~ s/^.*?:://;
		eval "cc_obj(qq(pp_sub_$ppname), \\&$objname)";
		die "cc_obj(qq(pp_sub_$ppname, \\&$objname) failed: $@" if $@;
		return if $errors;
	    }
	    output_boilerplate();
	    print "\n";
	    output_all($module_name || "init_module");
	    output_runtime();
	}
    } else {
	return sub { cc_main() };
    }
}

1;
