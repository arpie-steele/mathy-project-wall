package Metamath::Characters;

use strict;
use warnings;
use charnames ();

# The only characters that are allowed to appear in a Metamath
# source file are the 94 non-whitespace printable ASCII characters,
# which are digits, upper and lower case letters, and the following
# 32 special characters:

# !"#$%&'()*+,-./: ;<=>?@[\]^_`{|}~

# plus the following characters which are the “white space” characters:
# space (a printable character), tab, carriage return, line feed, and
# form feed. We will use typewriter font to display the printable
# characters.

# \t  = \011 = chr(9)  = \x09 = \cI # HT, TAB, CHARACTER TABULATION, HORIZONTAL TABULATION
# \n  = \012 = chr(10) = \x0A = \cJ # LF, NL, EOL, LINE FEED, NEW LINE, END OF LINE
# \f  = \014 = chr(12) = \x0C = \cL # NP, FF, FORM FEED
# \r  = \015 = chr(13) = \x0D = \cM # CR, CARRIAGE RETURN
# ' ' = \040 = chr(32) = \x20 = ' ' # SP, SPACE

sub display_statistics {

    my $digits                   = qr/[[:digit:]]/xms;
    my $upper                    = qr/[[:upper:]]/xms;
    my $lower                    = qr/[[:lower:]]/xms;
    my $special                  = qr/[[:punct:]]/xms;
    my $non_whitespace_printable = qr/[[:graph:]]/xms;
    my $printable                = qr/[[:graph:] ]/xms;
    my $math                     = qr/[^[:^graph:]\$]/xms;
    my $label                    = qr/[\w.-]/xms;
    my $whitespace               = qr/[\t\n\f\r ]/xms;
    my $legal_chars              = qr/[\t\n\f\r [:graph:]]/xms;

    my %counts;
    my %code;
    foreach my $code ( 0 .. 127 ) {
        my $char = chr $code;

        my $display = sprintf '\\%03o', $code;
        if ( $char =~ $non_whitespace_printable ) {
            $display = $char;
        }
        elsif ( $char eq "\N{HT}" ) { $display = '\\N{HT}' }
        elsif ( $char eq "\N{LF}" ) { $display = '\\N{LF}' }
        elsif ( $char eq "\N{FF}" ) { $display = '\\N{FF}' }
        elsif ( $char eq "\N{CR}" ) { $display = '\\N{CR}' }
        elsif ( $char eq "\N{SP}" ) { $display = '\\N{SP}' }
        my @flags;
        if ( $char =~ $digits )                   { push @flags, 'DIGITS'; }
        if ( $char =~ $upper )                    { push @flags, 'UPPER'; }
        if ( $char =~ $lower )                    { push @flags, 'LOWER'; }
        if ( $char =~ $special )                  { push @flags, 'SPECIAL'; }
        if ( $char =~ $non_whitespace_printable ) { push @flags, 'NWP'; }
        if ( $char =~ $printable )                { push @flags, 'PRINT'; }
        if ( $char =~ $whitespace )               { push @flags, 'WS'; }

        if ( $char =~ $legal_chars ) {
            $counts{'LEGAL'}++;
            push @{ $code{'LEGAL'} }, $display;
        }
        else { push @flags, 'ILLEGAL'; }
        if ( $char =~ $math )  { push @flags, 'MATH'; }
        if ( $char =~ $label ) { push @flags, 'LABEL'; }

        foreach my $flag (@flags) {
            $counts{$flag}++;
            push @{ $code{$flag} }, $display;
        }

        my $name = charnames::viacode($code);

        print "chr($code) = $name\t(@flags)\n";

    }

    foreach my $flag ( sort keys %counts ) {
        print "$flag\t$counts{$flag}\t";
        print @{ $code{$flag} }, "\n";
    }

    return;
}

1;
