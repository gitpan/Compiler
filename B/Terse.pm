package B::Terse;
use strict;
use B qw(peekop class ad walkoptree walkoptree_exec
	 main_start main_root cstring);

sub compile {
    my $order = shift;
    if ($order eq "exec") {
	return sub { walkoptree_exec(main_start, "terse") }
    } else {
	return sub { walkoptree(main_root, "terse") }
    }
}

sub indent {
    my $level = shift;
    return "    " x $level;
}

sub B::OP::terse {
    my ($op, $level) = @_;
    print indent($level), peekop($op), "\n";
}

sub B::SVOP::terse {
    my ($op, $level) = @_;
    print indent($level), peekop($op), "  ";
    $op->sv->terse(0);
}

sub B::GVOP::terse {
    my ($op, $level) = @_;
    print indent($level), peekop($op), "  ";
    $op->gv->terse(0);
}

sub B::PMOP::terse {
    my ($op, $level) = @_;
    my $precomp = $op->precomp;
    print indent($level), peekop($op),
	defined($precomp) ? " /$precomp/\n" : " (regexp not compiled)\n";

}

sub B::PVOP::terse {
    my ($op, $level) = @_;
    print indent($level), peekop($op), " ", cstring($op->pv), "\n";
}

sub B::COP::terse {
    my ($op, $level) = @_;
    my $label = $op->label;
    if ($label) {
	$label = " label ".cstring($label);
    }
    print indent($level), peekop($op), $label, "\n";
}

sub B::PV::terse {
    my ($sv, $level) = @_;
    print indent($level);
    printf "%s (0x%lx) %s\n", class($sv), ad($sv), cstring($sv->PV);
}

sub B::AV::terse {
    my ($sv, $level) = @_;
    print indent($level);
    printf "%s (0x%lx) FILL %d\n", class($sv), ad($sv), $sv->FILL;
}

sub B::GV::terse {
    my ($gv, $level) = @_;
    my $stash = $gv->STASH->NAME;
    if ($stash eq "main") {
	$stash = "";
    } else {
	$stash = $stash . "::";
    }
    print indent($level);
    printf "%s (0x%lx) *%s%s\n", class($gv), ad($gv), $stash, $gv->NAME;
}

sub B::IV::terse {
    my ($sv, $level) = @_;
    print indent($level);
    printf "%s (0x%lx) %d\n", class($sv), ad($sv), $sv->IV;
}

sub B::NV::terse {
    my ($sv, $level) = @_;
    print indent($level);
    printf "%s (0x%lx) %s\n", class($sv), ad($sv), $sv->NV;
}

sub B::NULL::terse {
    my ($sv, $level) = @_;
    print indent($level);
    printf "%s (0x%lx)\n", class($sv), ad($sv);
}
    
1;
