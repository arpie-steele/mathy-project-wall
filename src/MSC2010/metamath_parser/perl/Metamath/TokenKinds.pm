package Metamath::TokenKinds;

use strict;
use warnings;
use Carp;
use Data::Dumper;

our $VERSION = '0.1';

# A Metamath database consists of a sequence of three kinds of
# tokens separated by white space (which is any sequence of one or
# more white space characters). The set of keyword tokens is ${, $},
# $c, $v, $f, $e, $d, $a, $p, $., $=, $(, $), $[, and $]. The last
# four are called auxiliary or preprocessing keywords. A label token
# consists of any combination of letters, digits, and the characters
# hyphen, underscore, and period. A math symbol token may consist of
# any combination of the 93 printable standard ascii characters other
# than space or $ . All tokens are case-sensitive.

## no critic (ProhibitExcessComplexity)
sub tokenize_stream {
    my ( $fh, $fn ) = @_;

    my @main_keyword_tokens = map { q($) . $_ } qw( { } c v f e d a p . = );
    my @auxiliary_keyword_tokens = map { q($) . $_ } qw{ ( ) [ ] };

    my $keyword_token_pattern = qr/\$[{}cvfedap.=()\[\]]/xms;

    my $label_token_pattern       = qr/[\w.-]+/xms;
    my $math_symbol_token_pattern = qr/[^[:^graph:]\$]+/xms;

    my $token_separator =
      qr/[\t\n\f\r ]+/xms;    ## no critic (ProhibitEnumeratedClasses)

    my $comment_word_pattern =
      qr/(?:(?:[^[:^graph:]\$]+|[\$]+[^[:^graph:]\$()])+[\$]*|[\$]+)/xms;

    my @output;
    my $ln         = 0;
    my $in_comment = 0;
    while ( defined( my $line = <$fh> ) ) {
        $ln++;
        my @potential_tokens = split /($token_separator)/xms, $line,
          -1;                 ## no critic (ProhibitMagicNumbers)
        my @tokens;
        foreach my $pot (@potential_tokens) {
            if ( !length $pot ) { next; }
            if ( $pot =~ /\A($token_separator)\z/xms ) {
                push @tokens, [ 'WS', $1 ];
                next;
            }
            my $kw = ( $pot =~ /\A($keyword_token_pattern)\z/xms );
            my $lb = ( $pot =~ /\A($label_token_pattern)\z/xms );
            my $ma = ( $pot =~ /\A($math_symbol_token_pattern)\z/xms );
            my $co = ( $pot =~ /\A($comment_word_pattern)\z/xms );
            if ( $in_comment && $kw && $co && $pot ne '$(' && $pot ne '$)' )
            {    ## no critic (RequireInterpolationOfMetachars)
                $kw = undef;
            }
            if ($kw) {
                if ( $lb || $ma ) {
                    croak
"Debug file $fn, line $ln : $pot is both keyword and label or math symbol\n";
                }
                if ( $pot eq '$(' )
                {    ## no critic (RequireInterpolationOfMetachars)
                    if ($in_comment) {
                        croak
"Debug file $fn, line $ln : $pot is not allowed in comment.";
                    }
                    $in_comment = 1;
                }
                if ( $pot eq '$)' )
                {    ## no critic (RequireInterpolationOfMetachars)
                    if ( !$in_comment ) {
                        croak
"Debug file $fn, line $ln : $pot is not allowed outside of comment.";
                    }
                    $in_comment = undef;
                }
                push @tokens, [ 'KEYWORD', $pot ];
                next;
            }
            if (   $lb && $ma
                || $in_comment && $lb && $co
                || $in_comment && $ma && $co )
            {
                push @tokens, [ 'AMBIGUOUS', $pot ];
                next;
            }
            if ($lb) { push @tokens, [ 'LABEL',      $pot ]; next; }
            if ($ma) { push @tokens, [ 'MATHSYMBOL', $pot ]; next; }
            if ( $in_comment && $co ) {
                push @tokens, [ 'COMMENT', $pot ];
                next;
            }
            push @tokens, [ 'ERROR', $pot ];
        }

        # print Dumper [ $fn, $ln, \@tokens ];
        # push @output, \@tokens;
    }
    return \@output;
}

1;
