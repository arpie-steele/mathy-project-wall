#!/usr/bin/perl
# -*- cperl -*-
# $Id$

use strict;
use warnings;
use charnames ();
use Encode qw(decode);

our $VERSION = '1.0';

while ( defined( my $line = <ARGV> ) ) {
    my @chars = split //xms, decode( 'UTF-8', $line );
    foreach my $c (@chars) {
        my $code = ord $c;
        if ( $code > 126 ) {
            print '\\N{', charnames::viacode($code), '}';
        }
        else { print $c }
    }
}

# vim: set ai sw=4
