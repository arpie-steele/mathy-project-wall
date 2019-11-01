package Math::OperatorPayload;

use strict;
use warnings;

use Carp;
use Scalar::Util qw(blessed);
use Math::OperatorTreeNode;
use base qw(Math::Symbol);

# use constant Math::OperatorTreeNode::DEFAULT_FORMAT;
# use constant Math::OperatorTreeNode::ASCII_FORMAT;
# use constant Math::OperatorTreeNode::UNICODE_FORMAT;
# use constant Math::OperatorTreeNode::HTML_FORMAT;
# use constant Math::OperatorTreeNode::ALT_HTML_FORMAT;
# use constant Math::OperatorTreeNode::TEX_FORMAT;

our $VERSION = '1.0';

# Constructor. $node_payload should be object which has compare() method.

sub new {
    my ( $class_or_ref, $name, @syntax ) = @_;
    my $class = ref $class_or_ref || $class_or_ref;
    my $self = $class->SUPER::new($name);
    $self->{'s'} = [@syntax];
    $self->{'_'} =
      [ grep { !defined $_ || ref $_ && blessed($_) && $_->isa('Math::Slot'); }
          @syntax ];
    return $self;
}

sub count_slots {
    my ($self) = @_;
    return scalar @{ $self->{'_'} };
}

sub create_node {
    my ( $self, @nodes ) = @_;
    my @slots = scalar @{ $self->{'_'} };
    my $n     = scalar @nodes;
    my $m     = scalar @slots;
    if ( $n < $m ) { croak "Too few nodes ($n), expected $m"; }
    if ( $m < $n ) { croak "Too many nodes ($n), expected $m"; }
    return Math::OperatorTreeNode->new( $self, @nodes );
}

# Prototype for the format_infix() method for payload objects that
# don't define one of their own.

sub format_infix {
    my ( $self, $format, @objs ) = @_;
    my $routine =
      exists $self->{'f'} && exists $self->{'f'}->{$format}
      ? $self->{'f'}->{$format}
      : undef;
    if ( !$routine && exists $self->{'ud'} && $self->{'ud'} ) {
        $routine = $self->can('default_format');
    }
    return $routine->( $self, $format, @objs );
}

sub default_format_asc {
    my ( $self, $format, @objs ) = @_;
    my @syntax = @{ $self->{'s'} };
    my @output;
    foreach my $elem (@syntax) {
        if ( ref $elem && blessed($elem) && $elem->can('format_string') ) {
            push @output, $elem->format_string($format);
        }
        elsif ( !defined $elem
            || ref $elem && blessed($elem) && $elem->isa('Math::Slot') )
        {
            if ( !scalar @objs ) {
                croak 'Syntax requires too many slots';
            }
            push @output, shift @objs;
        }
        else {
            push @output, $elem;
        }
    }
    if ( scalar @objs ) {
        croak 'Syntax requires too few slots';
    }
    return join q( ), @output;
}

1;
