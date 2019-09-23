package Metamath::Token;

use strict;
use warnings;

use warnings FATAL => 'all';

use Carp;

sub new {
    my ($class_or_ref, $string, $optional_filename, $optional_line_number) = @_;
    my $obj = bless { }, ref $class_or_ref || $class_or_ref;
    if ( defined $optional_filename && defined $optional_line_number ) {
	$obj->set_fn($optional_filename);
	$obj->set_ln($optional_line_number);
    }
    $obj->set_string($string);
    return $obj;
}

sub set_fn {
    my ($self, $value) = @_;
    $self->{'fn'} = $value;
    return $self;
}

sub set_ln {
    my ($self, $value) = @_;
    $self->{'ln'} = $value;
    return $self;
}

sub set_string {
    my ($self, $value) = @_;
    $self->{'str'} = $value;
    if ( $value =~ /\A\s+\z/xms ) {
        $self->{'ws'} = 1;
    }
    return $self;
}

sub is_ws {
    my ($self) = @_;
    if ( exists $self->{'ws'} && $self->{'ws'} ) { return $self->{'ws'}; }
    return;
}

sub glue {
    my ($self, $other) = @_;
    if ( ! $self->is_ws()  || ! $other->is_ws() ) {
	croak "Only whitespace tokens may be glued together.";
    }
    $self->{'str'} .= $other->{'str'};
    return $self;
}

1;
