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
    my $type = $self->get_types();
    print "$fn line $ln : $type $str\n";
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

sub get_types {
    my ($self) = @_;
    my %types;
    if ( exists $self->{'types'} ) {
        %types = %{$self->{'types'}};
    } elsif ( $self->is_ws() ) {
        $types{'*'} = 'WS';
        $self->{'types'} = \%types;
    } else {
        my $str = $self->get_string();
        if ( $str =~ /\A[\w.-]+\z/xms ) {
	    $types{'TOP'} = 'LABEL';
	    $types{'BODY'} = 'LABEL';
	    $types{'LABEL'} = 'LABEL';
	    $types{'FILENAME'} = 'FILENAME';
	    $types{'COMMENT'} = 'COMMENT';
	    $types{'MATH'} = 'SYMBOL';
        } elsif ( $str =~ /\A[^[:^graph:]\$]+\z/xms ) {
	    $types{'FILENAME'} = 'FILENAME';
	    $types{'COMMENT'} = 'COMMENT';
	    $types{'MATH'} = 'SYMBOL';
	}
        if ( $str eq q{$(} ) {
	    $types{'TOP'} = 'BEGIN_COMMENT';
	    $types{'BODY'} = 'BEGIN_COMMENT';
	    $types{'*'} = 'BEGIN_COMMENT';
        }
        if ( $str eq q(${) ) {
	    $types{'TOP'} = 'BEGIN_BLOCK';
	    $types{'BODY'} = 'BEGIN_BLOCK';
        }
        if ( $str eq q($}) ) {
	    $types{'TOP'} = 'END_BLOCK';
	    $types{'BODY'} = 'END_BLOCK';
        }
        if ( $str eq q{$[} ) {
	    $types{'TOP'} = 'BEGIN_FILE_INCLUDE';
        }
        if ( $str eq q{$]} ) {
	    $types{'TOP'} = 'END_FILE_INCLUDE';
        }
        if ( $str eq q{$t} ) {
	    $types{'COMMENT'} = 'TYPESETTING';
        }
        if ( $str =~ /\A[\#]{4,}\z/ ) {
	    $types{'COMMENT'} = 'H1MARKER';
        }
        if ( $str =~ /\A(:?[\#][*]){2,}[\#]?\z/ ) {
	    $types{'COMMENT'} = 'H2MARKER';
        }
        if ( $str =~ /\A(:?[=][-]){2,}[=]?\z/ ) {
	    $types{'COMMENT'} = 'H3MARKER';
        }
        if ( $str =~ /\A(:?[-][.]){2,}[-]?\z/ ) {
	    $types{'COMMENT'} = 'H4MARKER';
        }
        if ( $str eq q{$)} ) {
	    %types = ();
	    $types{'COMMENT'} = 'END_COMMENT';
	    $types{'*'} = 'ERROR';
        }
        if ( ! exists $types{'*'} ) {
	    $types{'*'} = 'UNKNOWN';
        }
    }
    if ( wantarray ) {
        my @pairs = map { ( $_ => $types{$_} ) ; } reverse sort keys %types;
	return @pairs;
    }
    if ( 1 == scalar keys %types ) {
	return (values %types)[0];
    }
    my $strval = join q(, ), map { "$_ => $types{$_}" } reverse sort keys %types;
    return "($strval)";
}

1;
