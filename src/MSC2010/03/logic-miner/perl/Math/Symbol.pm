package Math::Symbol;

use strict;
use warnings;

use Carp;
use Math::OperatorTreeNode;
use Scalar::Util qw(blessed);
use base qw(GenCompare);

# use constant Math::OperatorTreeNode::DEFAULT_FORMAT;
# use constant Math::OperatorTreeNode::ASCII_FORMAT;
# use constant Math::OperatorTreeNode::UNICODE_FORMAT;
# use constant Math::OperatorTreeNode::HTML_FORMAT;
# use constant Math::OperatorTreeNode::ALT_HTML_FORMAT;
# use constant Math::OperatorTreeNode::TEX_FORMAT;

our $VERSION = '1.0';

# Constructor.

sub new {
    my ( $class_or_ref, $name ) = @_;
    my $class = ref $class_or_ref || $class_or_ref;
    return bless {
        'n' => $name,
        'f' => { Math::OperatorTreeNode::DEFAULT_FORMAT => $name }
    }, $class;
}

sub add_symbol_format {
    my ( $self, $format, $value ) = @_;
    if ( exists $self->{'f'} && exists $self->{'f'}->{$format} ) {
        croak "Format $format already exists for symbol $self->{'n'}";
    }
    $self->{'f'}->{$format} = $value;
    return;
}

sub peek_name {
    my ($self) = @_;
    return $self->{'n'};
}

sub format_string {
    my ( $self, $format ) = @_;
    my $value =
      exists $self->{'f'} && exists $self->{'f'}->{$format}
      ? $self->{'f'}->{$format}
      : $self->{'f'}->{Math::OperatorTreeNode::DEFAULT_FORMAT};
    return $value;
}

sub compare {
    my ( $this, $that ) = @_;
    my $result =
      GenCompare::compare( $this->peek_name(), $that && $that->peek_name() );
    if ($result) {
        return $result;
    }
    return 0;
}

1;
