package GenTreeNode;

use strict;
use warnings;

use GenCompare;

use constant PREFIX_ORDER => 1;
use constant POSTFIX_ORDER => -1;

our $VERSION = '1.0';

sub new {
    my ($class_or_ref, $node_type, @children) = @_;
    my $class = ref $class_or_ref || $class_or_ref;
    return bless { 't' => $node_type, 'c' => [ @children ] }, $class;
}

sub compare {
    my ($this, $that) = @_;
    my $result = GenCompare::compare( 
	( ( exists $this->{'t'} ) ? $this->{'t'} : undef ),
	( ( $that && exists $that->{'t'} ) ? $that->{'t'} : undef )
    );
    if ( $result ) {
	return $result;
    }
    return GenCompare::compare( 
	( ( exists $this->{'c'} ) ? $this->{'c'} : undef ),
	( ( $that && exists $that->{'c'} ) ? $that->{'c'} : undef )
    );
}

sub walk {
    my ($self, $order, $process, $accum) = @_;
    if ( ! defined $self ) {
	$process->(undef, 0, $accum);
	return;
    }
    if ( $order >= 0 ) {
	$process->($self->{'t'}, scalar @{$self->{'c'}}, $accum);
    }
    foreach my $child ( @{$self->{'c'}} ) {
	walk($child, $order, $process, $accum);
    }
    if ( $order < 0 ) {
	$process->($self->{'t'}, scalar @{$self->{'c'}}, $accum);
    }
    return;
}
