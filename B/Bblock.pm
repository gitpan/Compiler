package B::Bblock;
use strict;
use B qw(ad peekop walkoptree walkoptree_exec main_root main_start);
use B::Terse;

my %bblock;
my @bblock_ends;

sub mark_leader {
    my $op = shift;
    if (ad($op)) {
	$bblock{ad($op)} = $op;
    }
}

sub walk_bblocks {
    my ($op, $lastop, $leader, $bblock);
    mark_leader(main_start);
    walkoptree(main_root, "mark_if_leader");
    my @leaders = values %bblock;
    while ($leader = shift @leaders) {
	$lastop = $leader;
	$op = $leader->next;
	while (ad($op) && !exists($bblock{ad($op)})) {
	    $bblock{ad($op)} = $leader;
	    $lastop = $op;
	    $op = $op->next;
	}
	push(@bblock_ends, [$leader, $lastop]);
    }
    foreach $bblock (@bblock_ends) {
	($leader, $lastop) = @$bblock;
	printf "%s .. %s\n", peekop($leader), peekop($lastop);
	for ($op = $leader; ad($op) != ad($lastop); $op = $op->next) {
	    printf "    %s\n", peekop($op);
	}
	printf "    %s\n", peekop($lastop);
    }
    print "-------\n";
    walkoptree_exec(main_start, "terse");
}

sub B::OP::mark_if_leader {
    my $op = shift;
    if ($op->ppaddr eq "pp_enter") {
	mark_leader($op->next);
    }
}

sub B::COP::mark_if_leader {
    my $op = shift;
    if ($op->label) {
	mark_leader($op);
    }
}

sub B::LOOP::mark_if_leader {
    my $op = shift;
    mark_leader($op->next);
    mark_leader($op->nextop);
    mark_leader($op->redoop);
    mark_leader($op->lastop);
}

sub B::LOGOP::mark_if_leader {
    my $op = shift;
    mark_leader($op->next);
    mark_leader($op->other);
}

sub B::CONDOP::mark_if_leader {
    my $op = shift;
    mark_leader($op->next);
    mark_leader($op->true);
    mark_leader($op->false);
}

# PMOP stuff omitted

sub compile {
    return \&walk_bblocks;
}

# Basic block leaders:
#     Any COP (pp_nextstate) with a non-NULL label
#     The op *after* a pp_enter
#     The ops pointed at by nextop, redoop and lastop of a LOOP
#     The op pointed at by op_other of a LOGOP
#     The ops pointed at by op_true and op_false of a CONDOP
#     The op pointed at by op_pmreplstart of a PMOP
#     The op pointed at by op_other->op_pmreplstart of pp_substcont?


1;
