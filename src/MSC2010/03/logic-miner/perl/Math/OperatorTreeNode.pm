package Math::OperatorTreeNode;

use strict;
use warnings;

use Scalar::Util qw(blessed);
use base qw(GenTreeNode);

use constant DEFAULT_FORMAT  => 'def';    ## no critic (ProhibitConstantPragma)
use constant ASCII_FORMAT    => 'asc';    ## no critic (ProhibitConstantPragma)
use constant UNICODE_FORMAT  => 'uni';    ## no critic (ProhibitConstantPragma)
use constant HTML_FORMAT     => 'htm';    ## no critic (ProhibitConstantPragma)
use constant ALT_HTML_FORMAT => 'alt';    ## no critic (ProhibitConstantPragma)
use constant TEX_FORMAT      => 'tex';    ## no critic (ProhibitConstantPragma)

our $VERSION = '1.1';

my %format_table;

INIT {
    $format_table{DEFAULT_FORMAT}  = \&default_format_asc;
    $format_table{ASCII_FORMAT}    = \&default_format_asc;
    $format_table{UNICODE_FORMAT}  = \&default_format_asc;
    $format_table{HTML_FORMAT}     = \&default_format_asc;
    $format_table{ALT_HTML_FORMAT} = \&default_format_asc;
    $format_table{TEX_FORMAT}      = \&default_format_asc;
}

# Internal routine which when passed a node payload, a non-negative
# integer n, and array reference it will pop n children off the array
# and push the result of running the payload's format_infix() method
# on the popped items. If there is no format_infix routine, it defaults
# to infix representation with a string value of the payload as the
# separator.

sub infix_walker {
    my ( $payload, $n, $accum ) = @_;
    my @objs;
    if ($n) {
        @objs = splice @{ $accum->[0] }, -$n;
    }
    if (   defined $payload
        && ref $payload
        && blessed($payload)
        && $payload->can('format_infix') )
    {
        push @{ $accum->[0] }, $payload->format_infix( $accum->[1], @objs );
    }
    else {
        push @{ $accum->[0] },
          default_format_infix( $payload, $accum->[1], @objs );
    }
    return;
}

# Prototype for the format_infix() method for payload objects that
# don't define one of their own.

sub default_format_infix {
    my ( $payload, $format, @objs ) = @_;
    my $routine =
      exists $format_table{$format}
      ? $format_table{$format}
      : $format_table{DEFAULT_FORMAT};
    return $routine->( $payload, @objs );
}

# Default formating which joins children with the string respresentation
# of their parent node.

sub default_format_asc {
    my ( $payload, @objs ) = @_;
    my $payload_name = defined $payload ? $payload : 'UNDEF';
    if ( scalar @objs ) {
        return '( ' . ( join " $payload_name ", @objs ) . ' )';
    }
    return $payload_name;
}

# Object method for OperatorTreeNode which allows it to translate
# trees to strings that resemble math notation.

sub to_infix {
    my ( $self, $format ) = @_;
    $format ||= DEFAULT_FORMAT;
    my @stack = ( [], $format );
    $self->walk( GenTreeNode::POSTFIX_ORDER, \&infix_walker, \@stack );
    return $stack[0]->[0];
}

1;
