package B::Xref;
use strict;
use B qw(peekop class ad comppadlist main_start svref_2object walksymtable);

# Constants (should probably be elsewhere)
sub OPpLVAL_INTRO () { 128 }
sub SVf_POK () { 0x40000 }
sub UNKNOWN () { "(unknown)" }

my @lexnames;			# names of lexicals in current pad
my %done;			# keyed by $$op: set when each $op is done
my $top = UNKNOWN;		# shadows top element of stack
my $file;			# shadows current filename
my $line;			# shadows current line number

# Options
my ($debug_op, $nodefs);

sub output {
    my $message = shift;
    print "$file:$line: ";
    if (@_) {
	printf("$message\n", @_);
    } else {
	print "$message\n";
    }
}

sub nameofgv {
    my $gv = shift;
    my $name = $gv->NAME;
    my $stash = $gv->STASH->NAME;
    return $stash eq "main" ? $name : "${stash}::${name}";
}

sub load_pad {
    my ($namelistav, $valuelistav) = @_;
    my @namelist = $namelistav->ARRAY;
    my $ix;
    @lexnames = ();
    for ($ix = 1; $ix < @namelist; $ix++) {
	my $namesv = $namelist[$ix];
	next if class($namesv) eq "SPECIAL";
	$lexnames[$ix] = $namesv->PV;
    }
}

sub xref {
    my $start = shift;
    my $op;
    for ($op = $start; $$op; $op = $op->next) {
	last if $done{$$op}++;
	warn peekop($op), "\n" if $debug_op;
	my $ppname = $op->ppaddr;
	if ($ppname =~ /^pp_(or|and|mapwhile|grepwhile)$/) {
	    xref($op->other);
	} elsif ($ppname eq "pp_match" || $ppname eq "pp_subst") {
	    xref($op->pmreplstart);
	} elsif ($ppname eq "pp_substcont") {
	    xref($op->other->pmreplstart);
	    $op = $op->other;
	    redo;
	} elsif ($ppname eq "pp_cond_expr") {
	    # pp_cond_expr never returns op_next
	    xref($op->true);
	    $op = $op->false;
	    redo;
	} elsif ($ppname eq "pp_enterloop") {
	    xref($op->redoop);
	    xref($op->nextop);
	    xref($op->lastop);
	} elsif ($ppname eq "pp_subst") {
	    xref($op->pmreplstart);
	} else {
	    no strict 'refs';
	    &$ppname($op) if defined(&$ppname);
	}
    }
}

sub xref_object {
    my $cvref = shift;
    my $cv = svref_2object($cvref);
    load_pad($cv->PADLIST->ARRAY);
    xref($cv->START);
}

sub xref_main {
    load_pad(comppadlist->ARRAY);
    xref(main_start);
}

sub pp_nextstate {
    my $op = shift;
    $file = $op->filegv->SV->PV;
    $line = $op->line;
    $top = UNKNOWN;
}

sub pp_padsv {
    my $op = shift;
    $top = $lexnames[$op->targ];
    output("%s lexical %s",
	   $op->private & OPpLVAL_INTRO ? "introduced" : "used", $top);
}

sub pp_padav { pp_padsv(@_) }
sub pp_padhv { pp_padsv(@_) }

sub pp_rv2cv { $top = "&$top"; output("dereference as $top") }
sub pp_rv2hv { $top = "%$top"; output("dereference as $top") }
sub pp_rv2sv { $top = "\$$top"; output("dereference as $top") }
sub pp_rv2av { $top = "\@$top"; output("dereference as $top") }
sub pp_rv2gv { $top = "*$top"; output("dereference as $top") }

sub pp_gvsv {
    my $op = shift;
    $top = '$' . nameofgv($op->gv);
    output("%s %s", $op->private & OPpLVAL_INTRO ? "localised" : "used", $top);
}

sub pp_gv {
    my $op = shift;
    $top = nameofgv($op->gv);
    output("%s %s",
	$op->private & OPpLVAL_INTRO ? "localised" : "used", $top);
}

sub pp_const {
    my $op = shift;
    my $sv = $op->sv;
    $top = $sv->FLAGS & SVf_POK ? $sv->PV : UNKNOWN;
}

sub pp_method {
    my $op = shift;
    $top = "method $top";
}

sub pp_entersub {
    my $op = shift;
    if ($top =~ s/^method //) {
	# kludge
	output("called method $top");
    } else {
	output("called sub $top");
    }
    $top = UNKNOWN;
}

#
# Stuff for cross referencing definitions of variables and subs
#

sub B::GV::xref {
    my $gv = shift;
    my $cv = $gv->CV;
    if (ad($cv)) {
	return if $done{$$cv}++;
	$file = $gv->FILEGV->SV->PV;
	$line = $gv->LINE;
	output("definition of sub %s", nameofgv($gv));
    }
    my $form = $gv->FORM;
    if (ad($form)) {
	return if $done{$$form}++;
	$file = $gv->FILEGV->SV->PV;
	$line = $gv->LINE;
	output("definition of format %s", nameofgv($gv));
    }
}

sub xref_definitions {
    my ($pack, %exclude);
    return if $nodefs;
    foreach $pack (qw(B O AutoLoader DynaLoader Config DB VMS
		      strict vars FileHandle Exporter Carp)) {
        $exclude{$pack."::"} = 1;
    }
    no strict qw(vars refs);
    walksymtable(\%{"main::"}, "xref", sub { !defined($exclude{$_[0]}) });
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
	} elsif ($opt eq "d") {
	    $nodefs = 1;
	} elsif ($opt eq "D") {
            $arg ||= shift @options;
	    foreach $arg (split(//, $arg)) {
		if ($arg eq "o") {
		    B->debug(1);
		} elsif ($arg eq "O") {
		    $debug_op = 1;
		}
	    }
	}
    }
    if (@options) {
	return sub {
	    my $objname;
	    xref_definitions();
	    foreach $objname (@options) {
		$objname = "main::$objname" unless $objname =~ /::/;
		eval "xref_object(\\&$objname)";
		die "xref_object(\\&$objname) failed: $@" if $@;
	    }
	}
    } else {
	return sub {
	    xref_definitions();
	    xref_main();
	}
    }
}

1;
