#!/usr/bin/perl

use strict;
use warnings;

use Carp;
use Encode qw(encode);
use English qw(-no_match_vars);
use GenCompare;
use Math::OperatorTreeNode;

our $VERSION = '1.1';

# Use a circled plus as our binary operator for aesthetics.

my $cplus = "\N{CIRCLED PLUS}";

# Use a circled plus as our binary operator for aesthetics

my @letters = (
    "\N{MATHEMATICAL ITALIC CAPITAL A}",
    "\N{MATHEMATICAL ITALIC CAPITAL B}",
    "\N{MATHEMATICAL ITALIC CAPITAL C}",
);

my @list = map { Math::OperatorTreeNode->new($_); } @letters;
my $goal = $list[-1];
$goal = Math::OperatorTreeNode->new( $cplus, $goal, $goal );

# $goal = Math::OperatorTreeNode->new($cplus, $goal, $goal);

my $n     = 0;
my $found = 0;
while ( !$found ) {
    for my $i ( 0 .. $n ) {
        my $j          = $n - $i;
        my $left_node  = $list[$i];
        my $right_node = $list[$j];
        push @list, $left_node->new( $cplus, $left_node, $right_node );
        if ( $i == $j && 0 == $goal->compare($left_node) ) {
            $found = 1;
        }
    }
    $n++;
}

@list = sort { GenCompare::compare( $a, $b ); } @list;

foreach my $tree (@list) {
    print { \*STDOUT } encode( 'UTF-8', $tree->to_infix() ), "\n"
      or croak "print: STDOUT: $OS_ERROR";
}
