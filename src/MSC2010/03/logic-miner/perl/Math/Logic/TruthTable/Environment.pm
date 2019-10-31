package Math::Logic::TruthTable::Environment;

use strict;
use warnings;
use Carp;
use Config;

our $VERSION = '1.1';

sub all_ones {
    my $max_octet = ( 1 << $Config{'charbits'} ) - 1;
    return chr $max_octet;
}

sub all_zeroes { return chr 0; }

sub new {
    my ($class_or_ref) = @_;
    my $bits           = 0;
    my $test           = 1;
    while ( $test < $Config{'charbits'} ) { $bits++; $test <<= 1; }
    if ( 2**$bits != $Config{'charbits'} || ( $bits & ( $bits + 1 ) ) ) {
        croak "Unsupported number of bits per char: $Config{'charbits'}";
    }
    return bless { 'charpower' => $test, },
      ( ref $class_or_ref || $class_or_ref );
}

sub add_variable {
    my ( $self, $variable_label ) = @_;
    if ( defined $self->{'label_to_index'}->{$variable_label} ) {
        croak "We have already used the label $variable_label with index "
          . $self->{'label_to_index'}->{$variable_label};
    }
    my $index = scalar @{ $self->{'index_to_label'} };
    $self->{'label_to_index'}->{$variable_label} = $index;
    push @{ $self->{'index_to_label'} }, $variable_label;
    delete $self->{'initialized'};
    return;
}

sub initialize_representations {
    my ($self) = @_;
    if ( exists $self->{'initialized'} ) {
        return;
    }
    my $nvars     = scalar @{ $self->{'index_to_label'} };
    my $max_index = $nvars - 1;
    my $width     = 1;
    my $max_bit;
    my $all_vars_true;

    if ( $nvars >= $self->{'charpower'} ) {
        $width         = 2**( $nvars - $self->{'charpower'} );
        $all_vars_true = all_ones() x $width;
        $max_bit       = 2**$self->{'charpower'} - 1;
        $self->{'is_numeric_representation'} = undef;
    }
    else {
        $all_vars_true = 2**( 2**$nvars ) - 1;    # Number, not string
        $max_bit       = 2**$nvars - 1;
        $self->{'is_numeric_representation'} = 1;
    }
    $self->{'rep1'} = $all_vars_true;
    $self->{'rep0'} = ( $all_vars_true ^ $all_vars_true ) & $all_vars_true;

    foreach my $index ( 0 .. $max_index ) {
        my $representation;
        if ( $index > 2 ) {
            my $half_width = 2**( $index - $self->{'charpower'} );
            $representation =
              ( all_zeroes() x $half_width ) . ( all_ones() x $half_width );
            my $factor = ( length $all_vars_true ) / ( length $representation );
            if ( $factor > 1 ) {
                $representation = $representation x $factor;
            }
        }
        elsif ( $max_bit == 2**$self->{'charpower'} - 1 ) {
            $representation = q();
            my $test_bit = 1 << $index;
            foreach my $bit ( 0 .. $max_bit ) {
                vec( $representation, $bit, 1 ) = ( $bit & $test_bit ) ? 1 : 0;
            }
            $representation = $representation x $width;
        }
        else {
            $representation = 0;
            my $test_bit = 1 << $index;
            foreach my $bit ( 0 .. $max_bit ) {
                if ( $bit & $test_bit ) { $representation |= 2**$bit; }
            }
        }
        push @{ $self->{'representations'} }, $representation;
    }
    return;
}
1;
