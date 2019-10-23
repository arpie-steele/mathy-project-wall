package Math::OperatorTreeNode;

use strict;
use warnings;

use Scalar::Util qw(blessed);
use base qw(GenTreeNode);

our $VERSION = '1.0';

sub infix_walker {
    my ($type, $n, $accum) = @_;
    if ( defined $type && ref $type && blessed($type) && $type->can('format_infix') ) {
	my @objs;
        if ( $n ) {
	    @objs = splice @{$accum}, -$n;
	}
	push @{$accum}, $type->format_infix(@objs);
    } elsif ( $n ) {
	my $type_name = defined $type ? $type : 'UNDEF';
	my @objs = splice @{$accum}, -$n;
	push @{$accum}, '( ' . ( join " $type_name ", @objs ) . ' )';
    } else {
	my $type_name = defined $type ? $type : 'UNDEF';
	push @{$accum}, $type;
    }
    return;
}

sub to_infix {
    my ($self) = @_;
    my @stack;
    $self->walk(GenTreeNode::POSTFIX_ORDER, \&infix_walker, \@stack);
    return $stack[0];
}
