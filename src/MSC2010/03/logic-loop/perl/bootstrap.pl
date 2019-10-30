#!/usr/bin/perl

use strict;
use warnings;
use Carp;
use English qw(-no_match_vars);

our $VERSION = '1.0';

my $bits_per_octet = length unpack 'B*', pack 'B', 0;
my $id             = 0;
my $width          = 1;

while ( $width < $bits_per_octet ) {
    my $bit_pattern =
      ( ( '0' x $width ) . ( '1' x $width ) ) x
      ( $bits_per_octet / ( 2 * $width ) );
    my $code = sprintf '\\0x%02X', ord pack "B$bits_per_octet", $bit_pattern;
    print $id, ': ', $bit_pattern, ': ', $code, "\n"
      or croak "print: STDOUT: $OS_ERROR";
    $id++;
    $width *= 2;
}

