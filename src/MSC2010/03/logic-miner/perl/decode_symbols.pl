#!/usr/bin/perl
# -*- cperl -*-
# $Id$

# Read a UTF-8 text file (either specified by name(s) on the command line
# or the Standard Input) and output non-ASCII or non-printable characters
# as perl escapes with the full Unicode name.

# Almost certainly won't work on EBCDIC systems.

use strict;
use warnings;
use charnames ();
use Carp;
use Encode qw(decode encode);
use English qw(-no_match_vars);

our $VERSION = '1.1';

# Memorize char that takes the place of improper bytes in UTF-8 file
# when processed through decode()
my $rc_code = ord "\N{REPLACEMENT CHARACTER}";

while ( defined( my $line = <ARGV> ) ) {
    print { \*STDOUT } decode_utf_line($line)
      or croak "print: STDOUT: $OS_ERROR";
}

exit 0;

# Return ASCII string with Perl replacements given any UTF-8 (disk
# format string)

sub decode_utf_line {
    my ($line) = @_;
    return decode_unicode_line( decode( 'UTF-8', $line ) );
}

# Return ASCII string with Perl replacements given any Unicode (internal
# format string)

sub decode_unicode_line {
    my ($line) = @_;
    my @chars = split //xms, $line;
    my @output_ascii;
    foreach my $c (@chars) {
        push @output_ascii, decode_unicode_char($c);
    }
    return join q(), @output_ascii;
}

# Return perl ASCII name for any Unicode/ASCII character.

sub decode_unicode_char {
    my ($c) = @_;
    if ( $c =~ /[[:ascii:]]/xms && $c =~ /[[:print:]\s]/xms ) {
        return $c;
    }
    my $num  = ord $c;
    my $code = charnames::viacode($num);
    if ( !defined $code
        || $code eq 'REPLACEMENT CHARACTER' && $rc_code != $num )
    {
        $code = sprintf '%x', $num;
        return join q(), '\\x{', $code, '}';
    }
    return join q(), '\\N{', $code, '}';
}

# Return UTF-8 testing string with all chars in a given range

sub encode_test_chars {
    my ( $low_limit, $high_limit ) = @_;
    my @chars;
    foreach my $i ( $low_limit .. $high_limit ) {
        push @chars, chr $i;
    }
    return encode( 'UTF-8', join q(), @chars );
}

# vim: set ai sw=4
