#!/usr/bin/perl

use strict;
use warnings;
use Carp;
use English qw(-no_match_vars);
use Math::BigInt;

our $VERSION = '1.1';

# Search for small integer solutions to
# n ( (s-2) n + (4-s) ) / 2 = m (m + 1) ( (s-2) m + (5 - s) ) / 6 , s >= 3, n >= 2, m >= 2

# Trivial: m = n = 0
# Trivial: m = n = 1
# Trivial: s = 2, n = (m)(m + 1)/2
# Trivial: s = 3 k + 2, n = 3 k^3 - 3 k + 1, m = 3 k^2 - 2

my $start_time = time;

## no critic (ProhibitMagicNumbers)
my $one    = Math::BigInt->bone();
my $two    = Math::BigInt->new(2);
my $three  = Math::BigInt->new(3);
my $four   = Math::BigInt->new(4);
my $five   = Math::BigInt->new(5);
my $six    = Math::BigInt->new(6);
my $nine   = Math::BigInt->new(9);
my $twelve = Math::BigInt->new(12);

my $top_height = 1_000_000_000;

## use critic (ProhibitMagicNumbers)

my $highest_total;

## no critic (ProhibitCStyleForLoops)
for ( my $height = 1 ; $height <= $top_height ; $height++ ) {

    my $m   = Math::BigInt->new($height);
    my $mm1 = $m->copy()->bsub($one);
    my $mp1 = $m->copy()->badd($one);
    my $mp2 = $m->copy()->badd($two);

    # SM0 = (2 m - 5)(m)(m + 1)/6
    # SM1 = (m - 1)(m)(m + 1)/6

    ## no critic (ProhibitLongChainsOfMethodCalls)
    my $sm0 =
      $m->copy()->bmul($two)->bsub($five)->bmul($m)->bmul($mp1)->bdiv($six);
    my $sm1 = $mm1->copy()->bmul($m)->bmul($mp1)->bdiv($six);

# 3 <= s -> (3 + sqrt(9 + 12 (m - 1)(m)(m+1)))/6 < n <= (-3 + sqrt(9 + 12(m)(m+1)(m+2)) )/6
# n in Integers -> floor((9 + sqrt(9 + 12 (m - 1)(m)(m+1)))/6) <= n <= floor((-3 + sqrt(9 + 12(m)(m+1)(m+2)) )/6)

    my $nlb =
      $mm1->copy()->bmul($m)->bmul($mp1)->bmul($twelve)->badd($nine)->bsqrt()
      ->badd($nine)->bdiv($six);
    my $nub =
      $m->copy()->bmul($mp1)->bmul($mp2)->bmul($twelve)->badd($nine)->bsqrt()
      ->bsub($three)->bdiv($six);

    # print "$m, $nlb, $nub\n" or croak "print: STDOUT: $OS_ERROR";

    my $trivial_n;    # initial to undefined

    # Guess k = floor(sqrt( (m + 2) / 3 )) then test 3 k^2 -2 == m
    my $k = $m->copy()->badd($two)->bdiv($three)->bsqrt();
    if ( $k->copy()->bmul($k)->bmul($three)->bsub($two)->bsub($m)->is_zero() ) {

        # m =  3 k^2 -2, n = 3 k^3 - 3k + 1 is a known answer

        $trivial_n =
          $k->copy()->bmul($k)->bmul($k)->bsub($k)->bmul($three)->badd($one);

# print "$m, $nlb, $nub, skip $trivial_n\n" or croak "print: STDOUT: $OS_ERROR";
    }

    for ( my $n = $nlb->copy() ; $n->bcmp($nub) <= 0 ; $n->binc() ) {

        # print "m = $m, n = $n\n" or croak "print: STDOUT: $OS_ERROR";

        # s = ( (n - 2) n - SM0 ) / ( (n - 1) n / 2 - SM1 )

        my $s0 = $n->copy()->bsub($two)->bmul($n)->bsub($sm0);
        my $s1 = $n->copy()->bsub($one)->bmul($n)->bdiv($two)->bsub($sm1);
        my ( $s, $rem ) = $s0->copy()->bdiv($s1);

        if ( $rem->is_zero ) {

            my $is_trivial = q();
            if ( defined $trivial_n && $trivial_n->bcmp($n) == 0 ) {
                $is_trivial = ' (trivial)';
            }

            # Total = ( (s - 2) n + (4 - s) ) n / 2
            my $total =
              $s->copy()->bsub($two)->bmul($n)->badd($four)->bsub($s)->bmul($n)
              ->bdiv($two);

            my $new_record = q();
            if ( !defined $highest_total || $highest_total->bcmp($total) < 0 ) {
                $highest_total = $total;
                $new_record    = q( *NEW RECORD*);
            }

            my $now     = scalar localtime time;
            my $seconds = time - $start_time;

            print
"m = $m, n = $n, s = $s, total = $total$is_trivial$new_record\n$seconds : $now\n"
              or croak "print: STDOUT: $OS_ERROR";

        }
        elsif ( defined $trivial_n && $trivial_n->bcmp($n) == 0 ) {
            print "ERROR m = $m, n = $n, s = $s + $rem/$s1\n"
              or croak "print: STDOUT: $OS_ERROR";
        }

    }

}

__END__
m = 3, n = 4, s = 3, total = 10 *NEW RECORD*
m = 5, n = 7, s = 10, total = 175 *NEW RECORD*
m = 6, n = 9, s = 14, total = 441 *NEW RECORD*
m = 8, n = 15, s = 3, total = 120
m = 11, n = 22, s = 6, total = 946 *NEW RECORD*
m = 15, n = 34, s = 88, total = 48280 *NEW RECORD*
m = 17, n = 41, s = 30, total = 23001
m = 18, n = 45, s = 8, total = 5985
m = 20, n = 55, s = 3, total = 1540
m = 24, n = 70, s = 4, total = 4900
m = 26, n = 77, s = 276, total = 801801 *NEW RECORD*
m = 28, n = 86, s = 322, total = 1169686 *NEW RECORD*
m = 33, n = 110, s = 43, total = 245905
m = 34, n = 115, s = 50, total = 314755
m = 34, n = 119, s = 3, total = 7140
m = 103, n = 604, s = 2378, total = 432684460 *NEW RECORD*
m = 113, n = 694, s = 823, total = 197427385
m = 162, n = 1191, s = 145, total = 101337426
m = 204, n = 1683, s = 41, total = 55202400
m = 259, n = 2407, s = 31265, total = 90525801730 *NEW RECORD*
m = 420, n = 4970, s = 2386, total = 29437553530
m = 624, n = 9000, s = 374, total = 15064335000
m = 664, n = 9879, s = 210903, total = 10290361955160 *NEW RECORD*
m = 1191, n = 23731, s = 19605, total = 5519583702676
m = 1310, n = 27375, s = 83135, total = 31148407558500 *NEW RECORD*
m = 2169, n = 58322, s = 9525, total = 16195753597485
m = 2245, n = 61414, s = 223613, total = 421687634347915 *NEW RECORD*
m = 5695, n = 248132, s = 60, total = 1785508245600
m = 6511, n = 303336, s = 10, total = 368050005576
m = 6936, n = 333506, s = 16420, total = 913053565546276 *NEW RECORD*
m = 8583, n = 459096, s = 17, total = 1580765544996
m = 9215, n = 510720, s = 1152, total = 149979784926720
m = 10044, n = 581175, s = 11, total = 1519937678700
m = 12691, n = 825436, s = 9325, total = 3176083959788026 *NEW RECORD*
m = 14858, n = 1045635, s = 31368, total = 17147031694579605 *NEW RECORD*
m = 16906, n = 1269127, s = 11, total = 7248070597636
m = 19629, n = 1587767, s = 191070870, total = 240845063989967856315 *NEW RECORD*
m = 30810, n = 3122317, s = 4980, total = 24264913354964425
m = 34956, n = 3773306, s = 125070, total = 890348736143873526
m = 49785, n = 6413415, s = 8, total = 123395663059845
m = 91839, n = 16068720, s = 8, total = 774611255177760
