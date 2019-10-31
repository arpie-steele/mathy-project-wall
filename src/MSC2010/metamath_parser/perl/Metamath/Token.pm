package Metamath::Token;

use strict;
use warnings;

use warnings FATAL => 'all';

use Carp;
use English qw(-no_match_vars);

our $VERSION = '0.1';

sub new {
    my ( $class_or_ref, $string, $optional_filename, $optional_line_number ) =
      @_;
    my $obj = bless {}, ref $class_or_ref || $class_or_ref;
    if ( defined $optional_filename && defined $optional_line_number ) {
        $obj->set_fn($optional_filename);
        $obj->set_ln($optional_line_number);
    }
    $obj->set_string($string);
    return $obj;
}

sub set_fn {
    my ( $self, $value ) = @_;
    $self->{'fn'} = $value;
    return $self;
}

sub get_fn {
    my ($self) = @_;
    if ( exists $self->{'fn'} ) { return $self->{'fn'}; }
    return '<UNKNOWN>';
}

sub set_ln {
    my ( $self, $value ) = @_;
    $self->{'ln'} = $value;
    return $self;
}

sub get_ln {
    my ($self) = @_;
    if ( exists $self->{'ln'} ) { return $self->{'ln'}; }
    return '<UNKNOWN>';
}

sub set_string {
    my ( $self, $value ) = @_;
    $self->{'str'} = $value;
    if ( $value =~ /\A\s+\z/xms ) {
        $self->{'ws'} = 1;
    }
    return $self;
}

sub get_string {
    my ($self) = @_;
    if ( exists $self->{'str'} ) { return $self->{'str'}; }
    croak 'Hey! There was supposed to be a string here...';
}

sub is_ws {
    my ($self) = @_;
    if ( exists $self->{'ws'} && $self->{'ws'} ) { return $self->{'ws'}; }
    return;
}

sub glue {
    my ( $self, $other ) = @_;
    if ( !$self->is_ws() || !$other->is_ws() ) {
        croak 'Only whitespace tokens may be glued together.';
    }
    $self->{'str'} .= $other->{'str'};
    return $self;
}

sub dump_str {
    my ($self) = @_;
    my $fn     = $self->get_fn();
    my $ln     = $self->get_ln();
    my $str    = $self->get_string();
    my $type   = $self->get_types();
    print "$fn line $ln : $type $str\n" or croak "print: STDOUT: $OS_ERROR";
    return;
}

sub dump_ws {
    my ($self) = @_;
    my $fn     = $self->get_fn();
    my $ln     = $self->get_ln();
    my $str    = $self->get_string();
    my $len    = length $str;
    my $nl     = 0;
    foreach my $c ( split //xms, $str ) {
        if ( $c eq "\n" ) { $nl++; }
    }
    print "$fn line $ln : WS length = $len, NL = $nl\n"
      or croak "print: STDOUT: $OS_ERROR";
    return;
}

## no critic (ProhibitExcessComplexity)
sub get_types {
    my ($self) = @_;
    my %types;
    if ( exists $self->{'types'} ) {
        %types = %{ $self->{'types'} };
    }
    elsif ( $self->is_ws() ) {
        $types{q(*)} = 'WS';
        $self->{'types'} = \%types;
    }
    else {
        my $str = $self->get_string();
        if ( $str =~ /\A[\w.-]+\z/xms ) {
            $types{'TOP'}      = 'LABEL';
            $types{'BODY'}     = 'LABEL';
            $types{'LABEL'}    = 'LABEL';
            $types{'FILENAME'} = 'FILENAME';
            $types{'COMMENT'}  = 'COMMENT';
            $types{'MATH'}     = 'SYMBOL';
        }
        elsif ( $str =~ /\A[^[:^graph:]\$]+\z/xms ) {
            $types{'FILENAME'} = 'FILENAME';
            $types{'COMMENT'}  = 'COMMENT';
            $types{'MATH'}     = 'SYMBOL';
        }
        ## no critic (ProhibitFixedStringMatches, ProhibitComplexRegexes)
        if (
            $str =~ m{\A(?:theorem|lemma|definition|compare|proposition
	    |corollary|axiom|rule|remark|exercise|problem|notation|example
	    |property|figure|postulate|equation|scheme|chapter)\z}xms
          )
        {
            $types{'COMMENT'} = 'BIB_KEYWORD';
        }
        if ( $str =~ /\A(?:of|in|from|on)\z/xms ) {
            $types{'COMMENT'} = 'BIB_NOISE';
        }
        ## use critic (ProhibitFixedStringMatches)
        if ( $str =~ /\A\[[\w.-]+\]\z/xms ) {
            $types{'COMMENT'} = 'BIB_REF';
        }
        if ( $str eq q{$(} ) {    ## no critic (RequireInterpolationOfMetachars)
            $types{'TOP'}  = 'BEGIN_COMMENT';
            $types{'BODY'} = 'BEGIN_COMMENT';
            $types{q(*)}   = 'BEGIN_COMMENT';
        }
        if ( $str eq q(${) ) {    ## no critic (RequireInterpolationOfMetachars)
            $types{'TOP'}  = 'BEGIN_BLOCK';
            $types{'BODY'} = 'BEGIN_BLOCK';
        }
        if ( $str eq q($}) ) {    ## no critic (RequireInterpolationOfMetachars)
            $types{'TOP'}  = 'END_BLOCK';
            $types{'BODY'} = 'END_BLOCK';
        }
        if ( $str eq q{$[} ) {    ## no critic (RequireInterpolationOfMetachars)
            $types{'TOP'} = 'BEGIN_FILE_INCLUDE';
        }
        if ( $str eq q{$]} ) {    ## no critic (RequireInterpolationOfMetachars)
            $types{'TOP'} = 'END_FILE_INCLUDE';
        }
        if ( $str eq q{$t} ) {    ## no critic (RequireInterpolationOfMetachars)
            $types{'COMMENT'} = 'TYPESETTING';
        }
        if ( $str eq q{``} ) {
            $types{'COMMENT'}      = 'ESCAPED_BACKQUOTE';
            $types{'COMMENT_MATH'} = 'ESCAPED_BACKQUOTE';
        }
        if ( $str eq q{`} ) {
            $types{'COMMENT_MATH'} = 'END_MATHMODE_MARKER';
            $types{'COMMENT'}      = 'BEGIN_MATHMODE_MARKER';
        }
        if ( $str eq q{~~} ) {
            $types{'COMMENT'} = 'ESCAPED_TILDE';
        }
        if ( $str eq q{~} ) {
            $types{'COMMENT'} = 'LABEL_REFERENCE';
        }
        if ( $str =~ /\A[\#]{4,}\z/xms ) {
            $types{'COMMENT'} = 'H1_MARKER';
        }
        if ( $str =~ /\A(:?[\#][*]){2,}[\#]?\z/xms ) {
            $types{'COMMENT'} = 'H2_MARKER';
        }
        if ( $str =~ /\A(:?[=][-]){2,}[=]?\z/xms ) {
            $types{'COMMENT'} = 'H3_MARKER';
        }
        if ( $str =~ /\A(:?[-][.]){2,}[-]?\z/xms ) {
            $types{'COMMENT'} = 'H4_MARKER';
        }
        if ( $str eq q{$)} ) {    ## no critic (RequireInterpolationOfMetachars)
            %types            = ();
            $types{'COMMENT'} = 'END_COMMENT';
            $types{q(*)}      = 'ERROR';
        }
        if ( !exists $types{q(*)} ) {
            $types{q(*)} = 'UNKNOWN';
        }
    }
    if (wantarray) {
        my @pairs = map { ( $_ => $types{$_} ); } reverse sort keys %types;
        return @pairs;
    }
    if ( 1 == scalar keys %types ) {
        return ( values %types )[0];
    }
    my $strval = join q(, ),
      map { "$_ => $types{$_}" } reverse sort keys %types;
    return "($strval)";
}
## use critic (ProhibitExcessComplexity)

1;
