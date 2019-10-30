package Metamath::Characters;

use strict;
use warnings;
use charnames ();
use Carp;
use English qw(-no_match_vars);

our $VERSION = '0.1';

# The only characters that are allowed to appear in a Metamath
# source file are the 94 non-whitespace printable ASCII characters,
# which are digits, upper and lower case letters, and the following
# 32 special characters:

# !"#$%&'()*+,-./: ;<=>?@[\]^_`{|}~

# plus the following characters which are the "white space" characters:
# space (a printable character), tab, carriage return, line feed, and
# form feed. We will use typewriter font to display the printable
# characters.

# \t  = \011 = chr(9)  = \x09 = \cI # HT, TAB, CHARACTER TABULATION, HORIZONTAL TABULATION
# \n  = \012 = chr(10) = \x0A = \cJ # LF, NL, EOL, LINE FEED, NEW LINE, END OF LINE
# \f  = \014 = chr(12) = \x0C = \cL # NP, FF, FORM FEED
# \r  = \015 = chr(13) = \x0D = \cM # CR, CARRIAGE RETURN
# ' ' = \040 = chr(32) = \x20 = ' ' # SP, SPACE

my $highest_ascii_mark;
my %regex;
my %display_form;
my @easy_flags;
my @easy_flags2;
my %easy_flag;

sub lazy_package_init {
    if ($highest_ascii_mark) { return; }
    $highest_ascii_mark                = 1 + ord q(~);
    $regex{'digits'}                   = qr/[[:digit:]]/xms;
    $regex{'upper'}                    = qr/[[:upper:]]/xms;
    $regex{'lower'}                    = qr/[[:lower:]]/xms;
    $regex{'special'}                  = qr/[[:punct:]]/xms;
    $regex{'non_whitespace_printable'} = qr/[[:graph:]]/xms;
    $regex{'printable'}                = qr/[[:graph:] ]/xms;
    $regex{'math'}                     = qr/[^[:^graph:]\$]/xms;
    $regex{'label'}                    = qr/[\w.-]/xms;
    ## no critic (ProhibitEnumeratedClasses)
    $regex{'whitespace'}  = qr/[\t\n\f\r ]/xms;
    $regex{'legal_chars'} = qr/[\t\n\f\r [:graph:]]/xms;
    ## use critic (ProhibitEnumeratedClasses)

    foreach my $code ( 0 .. $highest_ascii_mark ) {
        my $char = chr $code;
        if ( $char !~ $regex{'non_whitespace_printable'} ) {
            $display_form{$char} = sprintf '\\%03o', $code;
        }
    }
    $display_form{"\N{HT}"} = '\\N{HT}';
    $display_form{"\N{LF}"} = '\\N{LF}';
    $display_form{"\N{FF}"} = '\\N{FF}';
    $display_form{"\N{CR}"} = '\\N{CR}';
    $display_form{"\N{SP}"} = '\\N{SP}';
    push @easy_flags, 'DIGITS';
    $easy_flag{ $easy_flags[-1] } = $regex{'digits'};
    push @easy_flags, 'UPPER';
    $easy_flag{ $easy_flags[-1] } = $regex{'upper'};
    push @easy_flags, 'LOWER';
    $easy_flag{ $easy_flags[-1] } = $regex{'lower'};
    push @easy_flags, 'SPECIAL';
    $easy_flag{ $easy_flags[-1] } = $regex{'special'};
    push @easy_flags, 'NWP';
    $easy_flag{ $easy_flags[-1] } = $regex{'non_whitespace_printable'};
    push @easy_flags, 'PRINT';
    $easy_flag{ $easy_flags[-1] } = $regex{'printable'};
    push @easy_flags, 'WS';
    $easy_flag{ $easy_flags[-1] } = $regex{'whitespace'};
    push @easy_flags2, 'MATH';
    $easy_flag{ $easy_flags2[-1] } = $regex{'math'};
    push @easy_flags2, 'LABEL';
    $easy_flag{ $easy_flags2[-1] } = $regex{'label'};
    return;
}

sub display_statistics {
    my %counts;
    my %code;

    lazy_package_init();

    foreach my $code ( 0 .. $highest_ascii_mark ) {
        my $char = chr $code;

        my $display =
          ( exists $display_form{$char} ) ? $display_form{$char} : $char;

        my @flags;

        foreach my $easy_flag (@easy_flags) {
            if ( $char =~ $easy_flag{$easy_flag} ) { push @flags, $easy_flag; }
        }

        if ( $char =~ $regex{'legal_chars'} ) {
            $counts{'LEGAL'}++;
            push @{ $code{'LEGAL'} }, $display;
        }
        else { push @flags, 'ILLEGAL'; }

        foreach my $easy_flag (@easy_flags2) {
            if ( $char =~ $easy_flag{$easy_flag} ) { push @flags, $easy_flag; }
        }

        foreach my $flag (@flags) {
            $counts{$flag}++;
            push @{ $code{$flag} }, $display;
        }

        my $name = charnames::viacode($code);

        print "chr($code) = $name\t(@flags)\n"
          or croak "print: STDOUT: $OS_ERROR";

    }

    foreach my $flag ( sort keys %counts ) {
        print "$flag\t$counts{$flag}\t", @{ $code{$flag} }, "\n"
          or croak "print: STDOUT: $OS_ERROR";
    }

    return;
}

1;
