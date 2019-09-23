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

sub get_fn {
    my ($self) = @_;
    if ( exists $self->{'fn'} ) { return $self->{'fn'}; }
    return '<UNKNOWN>';
}

sub set_ln {
    my ($self, $value) = @_;
    $self->{'ln'} = $value;
    return $self;
}

sub get_ln {
    my ($self) = @_;
    if ( exists $self->{'ln'} ) { return $self->{'ln'}; }
    return '<UNKNOWN>';
}

sub set_string {
    my ($self, $value) = @_;
    $self->{'str'} = $value;
    if ( $value =~ /\A\s+\z/xms ) {
        $self->{'ws'} = 1;
    }
    return $self;
}

sub get_string {
    my ($self) = @_;
    if ( exists $self->{'str'} ) { return $self->{'str'}; }
    croak "Hey! There was supposed to be a string here...";
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

sub dump {
    my ($self) = @_;
    my $fn = $self->get_fn();
    my $ln = $self->get_ln();
    my $str = $self->get_string();
    print "$fn line $ln : $str\n";
}

sub dump_ws {
    my ($self) = @_;
    my $fn = $self->get_fn();
    my $ln = $self->get_ln();
    my $str = $self->get_string();
    my $len = length $str;
    my $nl = 0;
    foreach my $c ( split //xms, $str ) { if ($c eq "\n") { $nl ++; } }
    print "$fn line $ln : WS length = $len, NL = $nl\n";
}

1;
