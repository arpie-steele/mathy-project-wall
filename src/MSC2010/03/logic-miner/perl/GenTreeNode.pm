package GenTreeNode;

use strict;
use warnings;

use Carp;
use GenCompare;

use constant PREFIX_ORDER  => 1;     ## no critic (ProhibitConstantPragma)
use constant POSTFIX_ORDER => -1;    ## no critic (ProhibitConstantPragma)

our $VERSION = '1.1';

# Constructor. $node_payload should be object which has compare() method.

sub new {
    my ( $class_or_ref, $node_payload, @children ) = @_;
    my $class = ref $class_or_ref || $class_or_ref;
    return bless { 't' => $node_payload, 'c' => [@children] }, $class;
}

# Returns true if node payload initialized

sub has_node_payload {
    my ($self) = @_;
    return exists $self->{'t'} && $self->{'t'};
}

# Returns node payload

sub peek_node_payload {
    my ($self) = @_;
    return $self->{'t'};
}

# Returns true if children array initialized which our constructor guarantees

sub has_children_array {
    my ($self) = @_;
    return exists $self->{'c'} && $self->{'c'};
}

# Return a array reference of all chilren

sub peek_children_array {
    my ($self) = @_;
    return $self->{'c'};
}

# Return a list of all chilren

sub peek_all_children {
    my ($self) = @_;
    return @{ $self->{'c'} };
}

# Return the count of children

sub count_children {
    my ($self) = @_;
    return scalar @{ $self->{'c'} };
}

# Check that the given index is legal. Throws exception if not.

sub index_check {
    my ( $self, $index ) = @_;
    if (   $index >= scalar @{ $self->{'c'} }
        || $index < -scalar @{ $self->{'c'} } )
    {
        croak
"index $index out of range [ @{[ - scalar @{$self->{'c'}} ]}, @{[ ( scalar @{$self->{'c'}} ) - 1 ]} ]";
    }
    return;
}

# Retrieve child by index number, numbering them from ( 0 .. $count-1 )
# or ( -$count .. -1 ).

sub peek_at_child {
    my ( $self, $index ) = @_;
    $self->index_check($index);
    return $self->{'c'}->[$index];
}

# Compare this tree/node with another. Returns less than zero if this
# comes first.

sub compare {
    my ( $this, $that ) = @_;
    my $result = GenCompare::compare(
        ( ( $this->has_node_payload() ) ? $this->peek_node_payload() : undef ),
        (
            ( $that && $that->has_node_payload() )
            ? $that->peek_node_payload()
            : undef
        )
    );
    if ($result) {
        return $result;
    }
    return GenCompare::compare(
        (
            ( $this->has_children_array() ) ? $this->peek_children_array()
            : undef
        ),
        (
            ( $that && $that->has_children_array() )
            ? $that->peek_children_array()
            : undef
        )
    );
}

# Run the subroutine $process(node_payload, num_children, $accum)  on all
# nodes in the tree, with parent nodes preceeding/following their children
# depending on $order being PREFIX_ORDER/POSTFIX_ORDER, respectively.

sub walk {
    my ( $self, $order, $process, $accum ) = @_;
    if ( !defined $self ) {
        $process->( undef, 0, $accum );
        return;
    }
    if ( $order >= 0 ) {
        $process->(
            $self->peek_node_payload(),
            $self->count_children(), $accum
        );
    }
    foreach my $child ( $self->peek_all_children() ) {
        walk( $child, $order, $process, $accum );
    }
    if ( $order < 0 ) {
        $process->(
            $self->peek_node_payload(),
            $self->count_children(), $accum
        );
    }
    return;
}

1;
