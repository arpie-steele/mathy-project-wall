#!/usr/bin/perl

use strict;
use warnings;

use Encode;
use GenCompare;
use Math::OperatorTreeNode;

our $VERSION = '1.0';

my $cplus = encode('utf-8', "\N{CIRCLED PLUS}");

my @letters = map { encode('utf-8', $_ ); } (
	"\N{MATHEMATICAL ITALIC CAPITAL A}",
	"\N{MATHEMATICAL ITALIC CAPITAL B}",
	"\N{MATHEMATICAL ITALIC CAPITAL C}"
    );

my @list = map { Math::OperatorTreeNode->new($_); } @letters;
my $goal = $list[-1];
$goal = Math::OperatorTreeNode->new($cplus, $goal, $goal);
# $goal = Math::OperatorTreeNode->new($cplus, $goal, $goal);

my $n = 0;
my $found = 0;
while ( ! $found ) {
    for my $i ( 0 .. $n ) {
	my $j = $n - $i;
	my $left = $list[$i];
	my $right = $list[$j];
	push @list, Math::OperatorTreeNode->new($cplus, $left, $right);
	if ( $i == $j && 0 == $goal->compare($left) ) {
	    $found = 1;
	}
    }
    $n ++;
}

@list = sort { GenCompare::compare($a, $b); } @list;

foreach my $tree ( @list ) {
    print $tree->to_infix(), "\n";
}
