package Metamath::Database;

use strict;
use warnings;

# A Metamath database is built up from a top-level source file
# together with any source files that are brought in through file
# inclusion commands (see below).

package Metamath::SourceFile;

use strict;
use warnings;

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


my $digits = qr/[[:digit:]]/xms;
my $upper = qr/[[:upper:]]/xms;
my $lower = qr/[[:lower:]]/xms;
my $special = qr/[[:punct:]]/xms;
my $non_whitespace_printable = qr/[[:graph:]]/xms;
my $printable = qr/[[:graph:] ]/xms;
my $math = qr/[^[:^graph:]\$]/xms;
my $label = qr/[\w.-]/xms;
my $whitespace = qr/[\t\n\f\r ]/xms;
my $legal_chars = qr/[\t\n\f\r [:graph:]]/xms;

my %counts;
my %code;
foreach my $code ( 0..127 ) {
my $char = chr $code;

my $display = sprintf '\\%03o', $code;
if ( $char =~ $non_whitespace_printable ) {
$display = $char ;
} elsif ( $char eq "\N{HT}" ) { $display = '\\N{HT}' }
elsif ( $char eq "\N{LF}" ) { $display = '\\N{LF}' }
elsif ( $char eq "\N{FF}" ) { $display = '\\N{FF}' }
elsif ( $char eq "\N{CR}" ) { $display = '\\N{CR}' }
elsif ( $char eq "\N{SP}" ) { $display = '\\N{SP}' }
my @flags;
if ( $char =~ $digits ) { push @flags, 'DIGITS'; }
if ( $char =~ $upper ) { push @flags, 'UPPER'; }
if ( $char =~ $lower ) { push @flags, 'LOWER'; }
if ( $char =~ $special ) { push @flags, 'SPECIAL'; }
if ( $char =~ $non_whitespace_printable ) { push @flags, 'NWP'; }
if ( $char =~ $printable ) { push @flags, 'PRINT'; }
if ( $char =~ $whitespace ) { push @flags, 'WS'; }
if ( $char =~ $legal_chars ) { $counts{'LEGAL'} ++; push @{$code{'LEGAL'}}, $display; } else { push @flags, 'ILLEGAL'; }
if ( $char =~ $math ) { push @flags, 'MATH'; }
if ( $char =~ $label ) { push @flags, 'LABEL'; }


foreach my $flag ( @flags ) { $counts{$flag}++;  push @{$code{$flag}}, $display}

my $name = charnames::viacode($code);

print "chr($code) = $name\t(@flags)\n";

}

foreach my $flag ( sort keys %counts ) {
print "$flag\t$counts{$flag}\t";
print @{$code{$flag}}, "\n";
}

return;
}

package Metamath::TokenKinds;

use strict;
use warnings;
use Carp;
use Data::Dumper;

# A Metamath database consists of a sequence of three kinds of
# tokens separated by white space (which is any sequence of one or
# more white space characters). The set of keyword tokens is ${, $},
# $c, $v, $f, $e, $d, $a, $p, $., $=, $(, $), $[, and $]. The last
# four are called auxiliary or preprocessing keywords. A label token
# consists of any combination of letters, digits, and the characters
# hyphen, underscore, and period. A math symbol token may consist of
# any combination of the 93 printable standard ascii characters other
# than space or $ . All tokens are case-sensitive.

sub tokenize_stream {
    my ($fh, $fn) = @_;

    my @main_keyword_tokens = map { '$' . $_ } ( '{', '}', 'c', 'v', 'f', 'e', 'd', 'a', 'p', '.', '=' );
    my @auxiliary_keyword_tokens = map { '$' . $_ } ( '(', ')', '[', ']' );

    my $keyword_token_pattern = qr/\$[{}cvfedap.=()\[\]]/xms;

    my $label_token_pattern = qr/[\w.-]+/xms;
    my $math_symbol_token_pattern = qr/[^[:^graph:]\$]+/xms;

    my $token_separator = qr/[\t\n\f\r ]+/xms;

    my $comment_word_pattern = qr/(?:(?:[^[:^graph:]\$]+|[\$]+[^[:^graph:]\$()])+[\$]*|[\$]+)/xms;

    my @output;
    my $ln = 0;
    my $in_comment = 0;
    while ( defined (my $line = <$fh>) ) {
	$ln ++;
	my @potential_tokens = split /($token_separator)/xms, $line, -1;
	my @tokens;
	foreach my $pot ( @potential_tokens ) {
	    if ( ! length $pot ) { next; }
	    if ( $pot =~ /\A($token_separator)\z/ ) { push @tokens, [ 'WS', $1 ]; next; }
	    my $kw = ( $pot =~ /\A($keyword_token_pattern)\z/ );
	    my $lb = ( $pot =~ /\A($label_token_pattern)\z/ );
	    my $ma = ( $pot =~ /\A($math_symbol_token_pattern)\z/ );
	    my $co = ( $pot =~ /\A($comment_word_pattern)\z/ );
	    if ( $in_comment && $kw && $co && $pot ne '$(' && $pot ne '$)' ) {
		$kw = undef;
	    }
	    if ( $kw ) {
		if ( $lb || $ma ) { croak "Debug file $fn, line $ln : $pot is both keyword and label or math symbol\n"; }
		if ( $pot eq '$(' ) {
		    if ( $in_comment ) { croak "Debug file $fn, line $ln : $pot is not allowed in comment." }
		    $in_comment = 1;
		}
		if ( $pot eq '$)' ) {
		    if ( ! $in_comment ) { croak "Debug file $fn, line $ln : $pot is not allowed outside of comment." }
		    $in_comment = undef;
		}
		push @tokens, [ 'KEYWORD', $pot ]; next;
	    }
	    if ( $lb && $ma || $in_comment && $lb && $co || $in_comment && $ma && $co ) { 
		push @tokens, [ 'AMBIGUOUS', $pot ]; next;
	    }
	    if ( $lb ) { push @tokens, [ 'LABEL', $pot ]; next; }
	    if ( $ma ) { push @tokens, [ 'MATHSYMBOL', $pot ]; next; }
	    if ( $in_comment && $co ) { push @tokens, [ 'COMMENT', $pot ]; next; }
	    push @tokens, [ 'ERROR', $pot ];
	}
	# print Dumper [ $fn, $ln, \@tokens ];
	# push @output, \@tokens;
    }
    return  \@output;
}

package main;

# Metamath::Characters::display_statistics();

Metamath::TokenKinds::tokenize_stream(\*STDIN, 'STDIN');
