#!/usr/bin/perl
# -*- cperl -*-
# $Id: logic_loop.pl,v 1.7 2013/02/12 06:09:40 rpenner Exp rpenner $

use strict;
use warnings;

use 5.008;
use Carp;
use Data::Dumper;

our $VERSION = '0.1';

my $theorem_list = TheoremList->new('theorems');
my (@variables)  = qw(ph ps ch th ta et ze si rh mu la ka);
my $lg_bits      = scalar @variables;
my ( %masks, %octet_bit_patterns, $TRUE_OCTET, $FALSE_OCTET );

{
    my $bits_per_octet = length unpack 'B*', pack 'B', 0;
    my $id             = 0;
    my $width          = 1;

    $TRUE_OCTET  = pack "B$bits_per_octet", ( '1' x $bits_per_octet );
    $FALSE_OCTET = pack "B$bits_per_octet", ( '0' x $bits_per_octet );

    while ( $width < $bits_per_octet ) {
        my $bit_pattern =
          ( ( '0' x $width ) . ( '1' x $width ) ) x
          ( $bits_per_octet / ( 2 * $width ) );
        $octet_bit_patterns{$id} = pack "B$bits_per_octet", $bit_pattern;
        $id++;
        $width *= 2;
    }
}

my $lg_bits_per_octet = scalar keys %octet_bit_patterns;

my $TRUE = $TRUE_OCTET x ( 2**( $lg_bits - $lg_bits_per_octet ) );

for my $i ( 0 .. ( $lg_bits - 1 ) ) {
    my $pattern;
    if ( exists $octet_bit_patterns{$i} ) {
        $pattern =
          $octet_bit_patterns{$i} x ( 2**( $lg_bits - $lg_bits_per_octet ) );
    }
    else {
        $pattern = $FALSE_OCTET x ( 2**( $i - $lg_bits_per_octet ) );
        $pattern .= $TRUE_OCTET x ( 2**( $i - $lg_bits_per_octet ) );
        $pattern = $pattern x ( 2**( $lg_bits - $i - 1 ) );
    }
    $masks{ $variables[$i] } = $pattern;
}

sub promote_variable_to_zeroary_operator {
    my ($letter) = @_;
    return {
        'slots' => 0,
        'mask'  => sub { return $masks{$letter}; },
        'infix' => $letter,
        'name'  => 'w' . $letter
    };
}

my (@terms) = map { promote_variable_to_zeroary_operator($_); } @variables;

## no critic (ProhibitMagicNumbers)
splice @terms, 4;
## use critic (ProhibitMagicNumbers)

push @terms,
  (
    {
        'slots' => 1,
        'mask'  => sub { return ~$_[0]; },
        'infix' => '-. _',
        'name'  => 'wn'
    },
    {
        'slots' => 2,
        'mask'  => sub { return ~$_[0] | $_[1]; },
        'infix' => '( _ -> _ )',
        'name'  => 'wi'
    },
    {
        'slots' => 2,
        'mask'  => sub { return ~( $_[0] ^ $_[1] ); },
        'infix' => '( _ <-> _ )',
        'name'  => 'wb'
    },
    {
        'slots' => 2,
        'mask'  => sub { return $_[0] | $_[1]; },
        'infix' => '( _ \/ _ )',
        'name'  => 'wo'
    },
    {
        'slots' => 2,
        'mask'  => sub { return $_[0] & $_[1]; },
        'infix' => '( _ /\ _ )',
        'name'  => 'wa'
    },
    {
        'slots' => 3,
        'mask'  => sub { return $_[0] | $_[1] | $_[2]; },
        'infix' => '( _ \/ _ \/ _ )',
        'name'  => 'w3o'
    },
    {
        'slots' => 3,
        'mask'  => sub { return $_[0] & $_[1] & $_[2]; },
        'infix' => '( _ /\ _ /\ _ )',
        'name'  => 'w3a'
    },
    {
        'slots' => 2,
        'mask'  => sub { return ~( $_[0] & $_[1] ); },
        'infix' => '( _ -/\ _ )',
        'name'  => 'wnand'
    },
    {
        'slots' => 3,
        'mask'  => sub { return ~( $_[0] & $_[1] & $_[2] ); },
        'infix' => '( _ -/\ _ -/\ _ )',
        'name'  => 'w3nand'
    },
    {
        'slots' => 2,
        'mask'  => sub { return $_[0] ^ $_[1]; },
        'infix' => '( _ (+) _ )',
        'name'  => 'wxo'
    },
  );

my @incomplete = ( TermSequence->new(undef) );
my %mask2strings;
my $old_incomplete_size = scalar @incomplete;
my $old_theorems_size   = $theorem_list->count();

while ( scalar @incomplete ) {
    my $original_sequence = shift @incomplete;
    my $target_index      = $original_sequence->first_undef_index();
    foreach my $term (@terms) {
        my $sequence = $original_sequence->clone();
        my @insert = map { undef } ( 1 .. $term->{'slots'} );
        $sequence->replace_element( $target_index, @insert, $term );
        if ( $term->{'slots'} != 0 || defined $sequence->first_undef_index() ) {
            push @incomplete, $sequence;
        }
        else {
            my @stack;
            foreach my $item ( $sequence->terms() ) {
                my $slots  = $item->{'slots'};
                my $mask   = $item->{'mask'};
                my $infix  = $item->{'infix'};
                my $name   = $item->{'name'};
                my @inputs = splice @stack, 0, $slots;
                my $value  = $mask->( map { $_->[0] } @inputs );
                my $string = $infix;
                $string =~ s/\b[_]\b/(shift @inputs)->[1]/egmxs;
                unshift @stack, [ $value => $string ];
            }
            my $mask   = $stack[0][0];
            my $string = $stack[0][1];
            push @{ $mask2strings{$mask} }, $string;
            if ( $mask eq $TRUE ) {
                $theorem_list->add_unique_theorems($string);
            }

        }

    }
    ## no critic (ProhibitMagicNumbers)
    my $incomplete_size = scalar @incomplete;
    last if ($incomplete_size) > 100_000_000;
    if ( $incomplete_size > 100_000 + $old_incomplete_size ) {
        my $theorems_size = $theorem_list->count();
        if ( $theorems_size > $old_theorems_size ) {
            $theorem_list->incremental_store();
            print "$old_incomplete_size => $incomplete_size",
              "\t$old_theorems_size => $theorems_size\n"
              or croak;
            $old_incomplete_size = $incomplete_size;
            $old_theorems_size   = $theorems_size;
        }
    }
    ## use critic (ProhibitMagicNumbers)
}

$theorem_list->incremental_store();

# print Dumper( \%mask2strings ) or croak;
print Dumper($theorem_list) or croak;
## use critic (RequireUseOfExceptions)

exit 0;

package TermSequence;
use strict;
use warnings;

use Carp;

sub new {
    my ( $object_or_class, @elements ) = @_;
    my $class = ref $object_or_class ? ref $object_or_class : $object_or_class;
    my $object = bless [@elements], $class;
    return $object;
}

sub clone {
    my ($self) = @_;
    return $self->new( @{$self} );
}

sub terms {
    my ($self) = @_;
    return @{$self};
}

sub first_undef_index {
    my ($self) = @_;
    my $undef_index = 0;
    foreach my $value ( @{$self} ) {
        if ( !defined $value ) {
            return $undef_index;
        }
        $undef_index++;
    }
    return;
}

sub replace_element {
    my ( $self, $element_index, @list ) = @_;
    return splice @{$self}, $element_index, 1, @list;
}

## no critic (ProhibitMultiplePackages)
package TheoremList;
## use critic (ProhibitMultiplePackages)

use strict;
use warnings;

use Carp;
use English qw(-no_match_vars);

sub new {
    my ( $object_or_class, $filename ) = @_;
    my $class = ref $object_or_class ? ref $object_or_class : $object_or_class;
    my $object =
      bless { 'filename' => $filename, 'set' => {}, 'next_threshold' => 0 },
      $class;
    $object->load();
    return $object;
}

sub store {
    my ($self)   = @_;
    my $filename = $self->{'filename'};
    my $theorems = $self->{'set'};
    if ( -f $filename ) {
        rename $filename, $filename . q(~);
    }
    open my $fh, '>', $filename
      or croak "Cannot write $filename: $OS_ERROR";
    print {$fh} map { ( $_, qq(\n) ) }
      sort { $theorems->{$a} <=> $theorems->{$b} } keys %{$theorems}
      or croak "Cannot write to $filename: OS_ERROR";
    close $fh
      or croak "Cannot close $filename: $OS_ERROR";
    $self->{'next_threshold'} = $self->count();
    return;
}

sub incremental_store {
    my ($self)    = @_;
    my $threshold = $self->{'next_threshold'};
    my $filename  = $self->{'filename'};
    my $theorems  = $self->{'set'};
    open my $fh, '>>', $filename
      or croak "Cannot write $filename: $OS_ERROR";
    print {$fh} map { ( $_, qq(\n) ) }
      sort { $theorems->{$a} <=> $theorems->{$b} }
      grep { $theorems->{$_} >= $threshold } keys %{$theorems}
      or croak "Cannot write to $filename: OS_ERROR";
    close $fh
      or croak "Cannot close $filename: $OS_ERROR";
    $self->{'next_threshold'} = $self->count();
    return;
}

sub load {
    my ($self) = @_;
    my $filename = $self->{'filename'};
    if ( !-f $filename ) {
        return;
    }
    open my $fh, '<', $filename
      or croak "Cannot load $filename: $OS_ERROR";
    $self->add_unique_theorems(<$fh>);
    close $fh
      or croak "Cannot close $filename: $OS_ERROR";
    $self->{'next_threshold'} = $self->count();
    return;
}

sub add_unique_theorems {
    my ( $self, @theorems ) = @_;
    foreach my $theorem (@theorems) {
        chomp $theorem;
        if ( !exists $self->{'set'}->{$theorem} ) {
            my $order = $self->count();
            $self->{'set'}->{$theorem} = $order;
        }
    }
    return;
}

sub count {
    my ($self) = @_;
    return scalar keys %{ $self->{'set'} };
}

## no critic (ProhibitMultiplePackages)
package LogicContext;
## use critic (ProhibitMultiplePackages)
