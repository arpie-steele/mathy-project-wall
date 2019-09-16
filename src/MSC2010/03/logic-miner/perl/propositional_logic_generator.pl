#!/usr/bin/perl
# -*- cperl -*-
# $Id$

# MSC Primary 03B35; Secondary 03B05

use strict;
use warnings;
use Encode qw(encode);

use Carp;

use warnings FATAL => qw(all);

use Data::Dumper;
$Data::Dumper::Useqq = 1;

our $VERSION = '1.0';
our $shucks;

my $length_limit = 10;

my $label_prefix = 'rpenner';

my $is_numeric_representation;
my $all_vars_true;
my @logical_vars;
my @logical_ops;
my @database;

add_logical_variable( 'phi',   "\N{MATHEMATICAL ITALIC SMALL PHI}",   'ph' );
add_logical_variable( 'psi',   "\N{MATHEMATICAL ITALIC SMALL PSI}",   'ps' );
add_logical_variable( 'chi',   "\N{MATHEMATICAL ITALIC SMALL CHI}",   'ch' );
add_logical_variable( 'theta', "\N{MATHEMATICAL ITALIC SMALL THETA}", 'th' );
if (0) {
    add_logical_variable( 'tau',  "\N{MATHEMATICAL ITALIC SMALL TAU}",  'ta' );
    add_logical_variable( 'eta',  "\N{MATHEMATICAL ITALIC SMALL ETA}",  'et' );
    add_logical_variable( 'zeta', "\N{MATHEMATICAL ITALIC SMALL ZETA}", 'ze' );
    add_logical_variable( 'sigma', "\N{MATHEMATICAL ITALIC SMALL SIGMA}",
        'si' );
    add_logical_variable( 'rho', "\N{MATHEMATICAL ITALIC SMALL RHO}", 'rh' );
    add_logical_variable( 'mu',  "\N{MATHEMATICAL ITALIC SMALL MU}",  'mu' );
    add_logical_variable( 'lamda', "\N{MATHEMATICAL ITALIC SMALL LAMDA}",
        'la' );
    add_logical_variable( 'kappa', "\N{MATHEMATICAL ITALIC SMALL KAPPA}",
        'ka' );
}

initialize_representations();

# print Dumper([$all_vars_true, @logical_vars]);

add_logical_op( 2, 'iff', "\N{LEFT RIGHT ARROW}",
    '<->', sub { return ( ~( $_[0] ^ $_[1] ) & $all_vars_true ); } );
add_logical_op( 2, 'implies', "\N{RIGHTWARDS ARROW}",
    '->', sub { return ( ( ( ~$_[0] ) & $all_vars_true ) | $_[1] ); } );
add_logical_op( 1, 'not', "\N{NOT SIGN}", '-.',
    sub { return ( ( ~$_[0] ) & $all_vars_true ); } );
if (0) {
    add_logical_op( 2, 'or', "\N{LOGICAL OR}",
        '\\/', sub { return $_[0] | $_[1]; } );
    add_logical_op( 3, 'or3', "\N{LOGICAL OR}",
        '\\/', sub { return $_[0] | $_[1] | $_[2]; } );
    add_logical_op( 2, 'and', "\N{LOGICAL AND}",
        '/\\', sub { return $_[0] & $_[1]; } );
    add_logical_op( 3, 'and3', "\N{LOGICAL AND}",
        '/\\', sub { return ( $_[0] & $_[1] & $_[2] ); } );
    add_logical_op( 4, 'and4', "\N{LOGICAL AND}",
        '/\\', sub { return $_[0] & $_[1] & $_[2] & $_[3]; } );
    add_logical_op( 2, 'nand', "\N{NAND}", '-/\\',
        sub { return ( ~( $_[0] & $_[1] ) & $all_vars_true ); } );
    add_logical_op( 3, 'nand3', "\N{NAND}", '-/\\',
        sub { return ( ~( $_[0] & $_[1] & $_[2] ) & $all_vars_true ); } );
    add_logical_op( 2, 'xor', "\N{XOR}", '\\/_',
        sub { return ( $_[0] ^ $_[1] ) & $all_vars_true; } );
    add_logical_func( 3, 'hadd',
        sub { return ( ( $_[0] ^ $_[1] ) ^ $_[2] ) & $all_vars_true; } );
    add_logical_func( 3, 'cadd',
        sub { return ( ( $_[0] & $_[1] ) | ( $_[2] & ( $_[0] | $_[1] ) ) ); } );
    add_logical_func( 3, 'if-',
        sub { return ( $_[0] & $_[1] ) | ( ( ~$_[0] ) & $_[2] ); } );
    add_logical_op( 0, 'TRUE', "\N{DOWN TACK}",
        'T.', sub { return $all_vars_true; } );
    add_logical_op( 0, 'FALSE', "\N{UP TACK}", 'F.',
        sub { return ( ( ~$all_vars_true ) & $all_vars_true ); } );
}

{
    my $n = scalar @logical_vars;
    foreach my $i ( 0 .. ( $n - 1 ) ) {
        print
"$logical_vars[$i]{'nam'} is $logical_vars[$i]{'asc'} or $logical_vars[$i]{'utf'} in UNICODE.\n";

        # print Dumper($logical_vars[$i]);
    }
    my $m = scalar @logical_ops;
    foreach my $i ( 1 .. $m ) {
        print
"$logical_ops[-$i]{'nam'} is $logical_ops[-$i]{'asc'} or $logical_ops[-$i]{'utf'} in UNICODE.\n";

        # print Dumper($logical_ops[-$i]);
    }
}

my @wip;

load_data();

if ( !scalar @wip ) {
    push @wip, [undef];
}

$SIG{INT} = \&catch_zap;

while ( scalar @wip ) {
    last if $shucks;
    my $tree   = shift @wip;
    my $length = scalar @{$tree};
    my @slots  = grep { !defined $tree->[$_] } ( 0 .. ( $length - 1 ) );

    # print Dumper([$tree, @slots]);
    if ( !scalar @slots ) {
        prove_and_add($tree);
        next;
    }
    else {
        my $polish = infix_std($tree);
        my $proofs;

        my $db_last = ( scalar @database ) - 1;
        foreach my $row_index ( 0 .. $db_last ) {
            my $row = $database[$row_index];
            if ( $polish =~ $row->[0] ) {
                $row->[5]++;
                if ( $row->[3] ) {
                    foreach my $ri ( @{ $row->[3] } ) { $database[$ri]->[5]++; }
                }
                print
"WEEDING slots: @{[scalar @slots]}, FROM: $row->[4] : $row->[1]\n";
                $proofs = 1;
            }
            last;
        }
        if ($proofs) {
            next;
        }
    }

    my $highest_var = 0;
    foreach my $i ( 0 .. ( $length - 1 ) ) {
        if ( defined $tree->[$i] && $highest_var <= $tree->[$i] ) {
            $highest_var = 1 + $tree->[$i];
        }
    }

    my $n = scalar @logical_vars;
    if ( $n <= $highest_var ) { $highest_var = $n - 1; }
    foreach my $i ( reverse 0 .. $highest_var ) {
        my @copy = @{$tree};
        $copy[ $slots[0] ] = $i;
        push @wip, \@copy;

        # print "\n\nTREE: @{$tree}\nCOPY: @copy\n";
    }

    my $m = scalar @logical_ops;
    foreach my $i ( 1 .. $m ) {
        my $arity = $logical_ops[ -$i ]{'nsl'};
        if ( $length_limit < $arity + $length ) { next; }
        my @copy = @{$tree};
        splice @copy, $slots[0], 1, map { $_ ? undef : -$i } ( 0 .. $arity );
        push @wip, \@copy;

        # print "\n\nTREE: @{$tree}\nCOPY: @copy\n";
    }
}

foreach
  my $row ( sort { $a->[5] <=> $b->[5] || $a->[4] cmp $b->[4] } @database )
{
    print $row->[5], " : ", $row->[4], " : ", $row->[1], "\n";
}

exit 0;

sub catch_zap {
    my $signame = shift;
    $shucks++;
    carp "Somebody sent me a SIG$signame";
}

sub load_data {
    my %lookup;
    my $n = scalar @logical_vars;
    foreach my $i ( reverse 0 .. ( $n - 1 ) ) {
        my $name = $logical_vars[$i]{'nam'};
        if ( exists $lookup{$name} ) {
            croak "COLLISION at name $name between $i and $lookup{$name}\n";
        }
        $lookup{$name} = $i;
    }
    my $m = scalar @logical_ops;
    foreach my $i ( 1 .. $m ) {
        my $name = $logical_ops[ -$i ]{'nam'};
        if ( exists $lookup{$name} ) {
            croak "COLLISION at name $name between -$i and $lookup{$name}\n";
        }
        $lookup{$name} = -$i;
    }
    while ( defined( my $line = <DATA> ) ) {
        $line =~ s/[#].*\z//xms;
        $line =~ s/\s+\z//xms;
        $line =~ s/\A\s+//xms;
        next if !$line;
        my ( $label, @words ) = split /\s+/xms, $line;
        my $error = 0;
        my @tree;
        foreach my $word (@words) {

            if ( !exists $lookup{$word} ) {
                carp "in $label: Unknown symbol: $word\n";
                $error = 1;
                last;
            }
            push @tree, $lookup{$word};
        }
        if ( !$error ) {
            my $infix = infix( \@tree, 'utf' );
            print "LOADING: $label: ", infix( \@tree, 'utf' ), "\n";
            my $representaion_value = eval_tree( \@tree );
            if (   $is_numeric_representation
                && $representaion_value == $all_vars_true
                || !$is_numeric_representation
                && $representaion_value eq $all_vars_true )
            {
                prove_and_add( \@tree, $label );

                # push @wip, [ map { $_ >= 0 ? undef : $_ } @tree ] ;

            }
            else {
                print "OOPS -- that's not true.\n";
            }
        }
    }
    return;
}

sub eval_tree {
    my ($tree) = @_;
    my $length = scalar @{$tree};
    my @slots = grep { !defined $tree->[$_] } ( 0 .. ( $length - 1 ) );
    if ( scalar @slots ) { die "tree has slots free: @slots\n"; }
    my @infix_stack;
    my @representation_stack;
    foreach my $k ( 1 .. $length ) {
        my $node = $tree->[ -$k ];
        if ( $node < 0 ) {
            my $arity = $logical_ops[$node]{'nsl'};
            my $sub   = $logical_ops[$node]{'sub'};
            my @params;
            if ($arity) {
                push @params, splice @representation_stack, 0, $arity;
            }
            unshift @representation_stack, $sub->(@params);

            # print "apply $logical_ops[$node]{'nam'}\n";
            # print "stack: @representation_stack\n";

        }
        else {

      # print "push $logical_vars[$node]{'nam'}, $logical_vars[$node]{'rep'}\n";
            unshift @representation_stack, $logical_vars[$node]{'rep'};
        }
    }
    return shift @representation_stack;
}

sub infix {
    my ( $tree, $type ) = @_;
    $type ||= 'utf';
    my $length = scalar @{$tree};

    my @slots = grep { !defined $tree->[$_] } ( 0 .. ( $length - 1 ) );
    if ( scalar @slots ) { die "tree has slots free: @slots\n"; }
    my @infix_stack;
    foreach my $k ( 1 .. $length ) {
        my $node = $tree->[ -$k ];
        if ( $node < 0 ) {
            my $is_func = $logical_ops[$node]{'fun'};
            my $arity   = $logical_ops[$node]{'nsl'};
            my $display = $logical_ops[$node]{$type};
            my @params;
            if ($arity) {
                push @params, splice @infix_stack, 0, $arity;
            }
            if ($is_func) {
                unshift @infix_stack,
                  $display . ' ( ' . ( join " , ", @params ) . ' )';
            }
            elsif ( $arity == 0 ) {
                unshift @infix_stack, $display;
            }
            elsif ( $arity == 1 ) {
                unshift @infix_stack, join q( ), $display, @params;
            }
            else {
                unshift @infix_stack,
                  '( ' . ( join " $display ", @params ) . ' )';
            }

        }
        else {
            unshift @infix_stack, $logical_vars[$node]{'utf'};
        }
    }
    return shift @infix_stack;
}

sub infix_std {
    my ($tree) = @_;

    my $length = scalar @{$tree};
    my @slots = grep { !defined $tree->[$_] } ( 0 .. ( $length - 1 ) );

    if ( scalar @slots ) {

        # die "tree has slots free: @slots\n";
        my $fake_content = scalar @logical_vars;
        my @copy         = @{$tree};
        foreach my $position (@slots) {
            $copy[$position] = $fake_content;
            $fake_content++;
        }
        $tree = \@copy;
    }

    my @infix_stack;
    foreach my $k ( 1 .. $length ) {
        my $node = $tree->[ -$k ];
        if ( $node < 0 ) {
            my $arity = $logical_ops[$node]{'nsl'};
            my @params;
            if ($arity) {
                push @params, splice @infix_stack, 0, $arity;
            }
            unshift @infix_stack, '{' . ( join ',', $node, @params ) . '}';

        }
        else {
            unshift @infix_stack, $node;
        }
    }
    return shift @infix_stack;
}

sub infix_pat {
    my ($tree) = @_;

    my @standins;
    my $length = scalar @{$tree};

    my @slots = grep { !defined $tree->[$_] } ( 0 .. ( $length - 1 ) );
    if ( scalar @slots ) { die "tree has slots free: @slots\n"; }

    my @infix_stack;
    foreach my $k ( 1 .. $length ) {
        my $node = $tree->[ -$k ];
        if ( $node < 0 ) {
            my $arity = $logical_ops[$node]{'nsl'};
            my @params;
            if ($arity) {
                push @params, map { ( ',', @{$_} ); } splice @infix_stack, 0,
                  $arity;
            }
            unshift @infix_stack, [ '{', $node, @params, '}' ];

        }
        else {
            unshift @infix_stack, [$node];
        }
    }
    return join q(), replace_vars( \@standins, @{ shift @infix_stack } );
}

sub replace_vars {
    my ( $standins, @nodes ) = @_;
    my @result;
    foreach my $node (@nodes) {
        if ( $node =~ /\A\d+\z/xms ) {
            if ( $node < scalar @{$standins} ) {
                push @result, $standins->[$node];
            }
            else {
                my $k = 2 * ( 1 + scalar @{$standins} );
                push @result, '(\w+|({(?:(?:(?>[^{}]+)|(?' . $k . '))*)}))';
                push @{$standins}, '\\' . ( 1 + 2 * scalar @{$standins} );
            }
        }
        else {
            push @result, $node;
        }
    }
    return @result;
}

sub add_logical_func {
    my ( $slots, $name, $eval_code ) = @_;
    my $index = 1 + scalar @logical_ops;
    my $op    = {
        'ind' => -$index,
        'nam' => $name,
        'nsl' => $slots,
        'uni' => $name,
        'utf' => $name,
        'asc' => $name,
        'sub' => $eval_code,
        'fun' => 1,
    };
    unshift @logical_ops, $op;
    return;
}

sub add_logical_op {
    my ( $slots, $name, $unicode_symbol, $ascii_symbol, $eval_code ) = @_;
    my $index = 1 + scalar @logical_ops;
    my $op    = {
        'ind' => -$index,
        'nam' => $name,
        'nsl' => $slots,
        'uni' => $unicode_symbol,
        'utf' => encode( 'UTF-8', $unicode_symbol ),
        'asc' => $ascii_symbol,
        'sub' => $eval_code,
        'fun' => 0,
    };
    unshift @logical_ops, $op;
    return;
}

sub add_logical_variable {
    my ( $name, $unicode_symbol, $ascii_symbol ) = @_;
    my $index = scalar @logical_vars;
    my $var   = {
        'ind' => $index,
        'nam' => $name,
        'uni' => $unicode_symbol,
        'utf' => encode( 'UTF-8', $unicode_symbol ),
        'asc' => $ascii_symbol,
    };
    push @logical_vars, $var;
    return;
}

sub initialize_representations {
    my $nvars     = scalar @logical_vars;
    my $max_index = $nvars - 1;
    my $width     = 1;
    my $max_bit;
    if ( $nvars > 2 ) {
        $width                     = 2**( $nvars - 3 );
        $all_vars_true             = "\xff" x $width;
        $max_bit                   = 7;
        $is_numeric_representation = undef;
    }
    else {
        $all_vars_true             = 2**( 2**$nvars ) - 1;  # Number, not string
        $max_bit                   = 2**$nvars - 1;
        $is_numeric_representation = 1;
    }

    foreach my $index ( 0 .. $max_index ) {
        my $representation;
        if ( $index > 2 ) {
            my $half_width = 2**( $index - 3 );
            $representation =
              ( "\x00" x $half_width ) . ( "\xff" x $half_width );
            my $factor = ( length $all_vars_true ) / ( length $representation );
            if ( $factor > 1 ) {
                $representation = $representation x $factor;
            }
        }
        elsif ( $max_bit == 7 ) {
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
        $logical_vars[$index]{'rep'} = $representation;
    }
    return;
}

sub prove_and_add {
    my ( $tree, $label, $pattern, $infix, $polish, $old_proofs ) = @_;
    my $representaion_value = eval_tree($tree);
    if ( $is_numeric_representation && $representaion_value == $all_vars_true
        || !$is_numeric_representation
        && $representaion_value eq $all_vars_true )
    {
        $label   ||= $label_prefix . scalar @database;
        $pattern ||= infix_pat($tree);
        $infix   ||= infix( $tree, 'utf' );
        $polish  ||= infix_std($tree);
        my $proofs;

        my $db_last = ( scalar @database ) - 1;
        foreach my $row_index ( 0 .. $db_last ) {
            my $row = $database[$row_index];
            if ( $polish =~ $row->[0] ) {
                $row->[5]++;
                $proofs = [$row_index];
                if ( $row->[3] ) {
                    foreach my $ri ( @{ $row->[3] } ) { $database[$ri]->[5]++; }
                    push @{$proofs}, @{ $row->[3] };
                }
                last;
            }
        }

        if ( $proofs && 1 < scalar @{$proofs} ) {
            print "\n\nINFIX: $infix\n";
            foreach my $ri ( @{$proofs} ) {
                print "PROVE FROM: ", $database[$ri][4], ": ",
                  $database[$ri][1], "\n";
            }
        }

        if ( !defined $proofs ) {
            print "\n\nINFIX: $infix\n";
            if ( defined $old_proofs ) { $proofs = $old_proofs; }
            add_to_database( $tree, $label, $pattern, $infix, $polish,
                $proofs );
        }
    }
    return;
}

sub add_to_database {
    my ( $tree, $label, $pattern, $infix, $polish, $proofs ) = @_;
    $label   ||= $label_prefix . scalar @database;
    $pattern ||= infix_pat($tree);
    $infix   ||= infix( $tree, 'utf' );
    $polish  ||= infix_std($tree);
    my $new_proofs = [];
    if ($proofs) { push @{$new_proofs}, @{$proofs}; }

    my $max_var = -1;
    foreach my $node ( @{$tree} ) {
        if ( $node > $max_var ) { $max_var = $node; }
    }
    if ( 1 || $max_var >= 0 ) {
        unshift @{$new_proofs}, scalar @database;
        push @database,
          [
            qr/\A$pattern\z/xms, $infix, $polish, $proofs,
            $label, 0, [ @{$tree} ], $max_var
          ];
    }

    # if ( scalar @{$tree} > $length_limit ) { return; }

    my %lookup;
    my $n = scalar @logical_vars;
    foreach my $i ( reverse 0 .. ( $n - 1 ) ) {
        my $name = $logical_vars[$i]{'nam'};
        if ( exists $lookup{$name} ) {
            croak "COLLISION at name $name between $i and $lookup{$name}\n";
        }
        $lookup{$name} = $i;
    }
    my $m = scalar @logical_ops;
    foreach my $i ( 1 .. $m ) {
        my $name = $logical_ops[ -$i ]{'nam'};
        if ( exists $lookup{$name} ) {
            croak "COLLISION at name $name between -$i and $lookup{$name}\n";
        }
        $lookup{$name} = -$i;
    }

    if ( 2 + ( scalar @{$tree} ) <= $length_limit
        && ( exists $lookup{'iff'} || exists $lookup{'and'} ) )
    {
        my $count = 0;
        foreach my $ri ( 0 .. ( ( scalar @database ) - 1 ) ) {
            my $row = $database[$ri];
            if ( $max_var + 1 + $row->[7] < $n
                && 1 + ( scalar @{$tree} ) + ( scalar @{ $row->[6] } ) <=
                $length_limit )
            {
                my @extra =
                  map { $_ >= 0 ? $_ + 1 + $max_var : $_ } @{ $row->[6] };
                my @extra_proofs = ( @$new_proofs, $ri );
                if ( $row->[3] ) { push @extra_proofs, @{ $row->[3] }; }

                if ( exists $lookup{'iff'} ) {
                    prove_and_add(
                        [ $lookup{'iff'}, @{$tree}, @extra ],
                        $label . 'X' . $count,
                        undef, undef, undef, \@extra_proofs
                    );
                    $count++;
                }
                if ( exists $lookup{'and'} ) {
                    prove_and_add(
                        [ $lookup{'and'}, @{$tree}, @extra ],
                        $label . 'X' . $count,
                        undef, undef, undef, \@extra_proofs
                    );
                    $count++;
                }
            }
        }
    }

    #  ⊢ (𝜑 ↔ 𝜓)    ⇒   ⊢ (𝜓 ↔ 𝜑)
    if (
        ( scalar @{$tree} ) <= $length_limit
        && (   ( exists $lookup{'iff'} && $tree->[0] == $lookup{'iff'} )
            || ( exists $lookup{'and'} && $tree->[0] == $lookup{'and'} )
            || ( exists $lookup{'or'}  && $tree->[0] == $lookup{'or'} )
            || ( exists $lookup{'xor'} && $tree->[0] == $lookup{'xor'} ) )
      )
    {
        my ( $index, $want ) = ( 1, 1 );
        while ($want) {
            if ( $tree->[$index] < 0 ) {
                $want += $logical_ops[ $tree->[$index] ]->{'nsl'};
            }
            $want--;
            $index++;
        }
        my @new_tree = @{$tree};
        my @first_clause = splice @new_tree, $index;
        splice @new_tree, 1, 0, @first_clause;
        my %variable_map;
        my $next_variable = 0;
        foreach my $node (@new_tree) {
            if ( $node >= 0 ) {
                if ( !exists $variable_map{$node} ) {
                    $variable_map{$node} = $next_variable;
                    $next_variable++;
                }
            }
        }
        @new_tree = map { $_ < 0 ? $_ : $variable_map{$_}; } @new_tree;
        prove_and_add( \@new_tree, $label . 'C',
            undef, undef, undef, $new_proofs );
    }

    #
    if (
           ( scalar @{$tree} ) <= $length_limit
        && exists $lookup{'not'}
        && $tree->[0] == $lookup{'not'}
        && (   ( exists $lookup{'iff'} && $tree->[1] == $lookup{'iff'} )
            || ( exists $lookup{'and'} && $tree->[1] == $lookup{'and'} )
            || ( exists $lookup{'or'}  && $tree->[1] == $lookup{'or'} )
            || ( exists $lookup{'xor'} && $tree->[1] == $lookup{'xor'} ) )
      )
    {
        my ( $index, $want ) = ( 2, 1 );
        while ($want) {
            if ( $tree->[$index] < 0 ) {
                $want += $logical_ops[ $tree->[$index] ]->{'nsl'};
            }
            $want--;
            $index++;
        }
        my @new_tree = @{$tree};
        my @first_clause = splice @new_tree, $index;
        splice @new_tree, 2, 0, @first_clause;
        my %variable_map;
        my $next_variable = 0;
        foreach my $node (@new_tree) {
            if ( $node >= 0 ) {
                if ( !exists $variable_map{$node} ) {
                    $variable_map{$node} = $next_variable;
                    $next_variable++;
                }
            }
        }
        @new_tree = map { $_ < 0 ? $_ : $variable_map{$_}; } @new_tree;
        prove_and_add( \@new_tree, $label . 'C3',
            undef, undef, undef, $new_proofs );
    }

    # biimpi ⊢ (𝜑 ↔ 𝜓)    ⇒   ⊢ (𝜑 → 𝜓)
    if (   ( scalar @{$tree} ) <= $length_limit
        && exists $lookup{'implies'}
        && exists $lookup{'iff'}
        && $tree->[0] == $lookup{'iff'} )
    {
        prove_and_add(
            [
                $lookup{'implies'},
                ( map { $tree->[$_]; } ( 1 .. ( ( scalar @{$tree} - 1 ) ) ) )
            ],
            $label . 'B',
            undef, undef, undef,
            $new_proofs
        );
    }

 # biimpd ⊢ (𝜑 → (𝜓 ↔ 𝜒))    ⇒   ⊢ (𝜑 → (𝜓 → 𝜒))
    if (   ( scalar @{$tree} ) <= $length_limit
        && exists $lookup{'implies'}
        && exists $lookup{'iff'}
        && $tree->[0] == $lookup{'implies'} )
    {
        my ( $index, $want ) = ( 1, 1 );
        while ($want) {
            if ( $tree->[$index] < 0 ) {
                $want += $logical_ops[ $tree->[$index] ]->{'nsl'};
            }
            $want--;
            $index++;
        }
        if ( $tree->[$index] == $lookup{'iff'} ) {
            prove_and_add(
                [
                    (
                        map {
                            ( $_ == $index ) ? $lookup{'implies'} : $tree->[$_];
                          } ( 0 .. ( ( scalar @{$tree} - 1 ) ) )
                    )
                ],
                $label . 'B2',
                undef,
                undef,
                undef,
                $new_proofs
            );
        }
    }

    # pm2.21i ⊢ ¬ 𝜑    ⇒   ⊢ (𝜑 → 𝜓)
    if (   ( 1 + scalar @{$tree} ) <= $length_limit
        && exists $lookup{'implies'}
        && exists $lookup{'not'}
        && $tree->[0] == $lookup{'not'}
        && $tree->[1] != $lookup{'not'}
        && $max_var + 1 < $n )
    {
        prove_and_add(
            [
                $lookup{'implies'},
                ( map { $tree->[$_]; } ( 1 .. ( ( scalar @{$tree} - 1 ) ) ) ),
                $max_var + 1
            ],
            $label . 'D3',
            undef, undef, undef,
            $new_proofs
        );
    }
    if (   ( 1 + scalar @{$tree} ) <= $length_limit
        && exists $lookup{'iff'}
        && exists $lookup{'FALSE'}
        && exists $lookup{'not'}
        && $tree->[0] == $lookup{'not'} )
    {
        prove_and_add(
            [
                $lookup{'iff'}, $lookup{'FALSE'},
                ( map { $tree->[$_]; } ( 1 .. ( ( scalar @{$tree} - 1 ) ) ) )
            ],
            $label . 'B4',
            undef, undef, undef,
            $new_proofs
        );
    }

    # a1i ⊢ 𝜑    ⇒   ⊢ (𝜓 → 𝜑)
    if ( exists $lookup{'implies'}
        && $max_var + 1 < $n )
    {
        prove_and_add(
            [
                $lookup{'implies'}, 0,
                map { ( $_ >= 0 ) ? 1 + $_ : $_; } @{$tree}
            ],
            $label . 'D',
            undef, undef, undef,
            $new_proofs
        );
    }

    #  ⊢ (𝜑 → 𝜓)    ⇒   ⊢ (¬ 𝜓 → ¬ 𝜑)
    if (   ( 2 + scalar @{$tree} ) <= $length_limit
        && exists $lookup{'implies'}
        && $tree->[0] == $lookup{'implies'}
        && exists $lookup{'not'} )
    {
        my ( $index, $want ) = ( 1, 1 );
        while ($want) {
            if ( $tree->[$index] < 0 ) {
                $want += $logical_ops[ $tree->[$index] ]->{'nsl'};
            }
            $want--;
            $index++;
        }
        my @new_tree = @{$tree};
        my @first_clause = splice @new_tree, $index;
        splice @new_tree, 1, 0, $lookup{'not'}, @first_clause, $lookup{'not'};
        my %variable_map;
        my $next_variable = 0;
        foreach my $node (@new_tree) {
            if ( $node >= 0 ) {
                if ( !exists $variable_map{$node} ) {
                    $variable_map{$node} = $next_variable;
                    $next_variable++;
                }
            }
        }
        @new_tree = map { $_ < 0 ? $_ : $variable_map{$_}; } @new_tree;
        prove_and_add( \@new_tree, $label . 'C2',
            undef, undef, undef, $new_proofs );
    }

    # notnoti ⊢ 𝜑    ⇒   ⊢ ¬ ¬ 𝜑
    if ( ( 2 + scalar @{$tree} ) <= $length_limit && exists $lookup{'not'} ) {
        prove_and_add(
            [ $lookup{'not'}, $lookup{'not'}, @{$tree} ],
            $label . 'N2',
            undef, undef, undef, $new_proofs
        );
    }

    #
    if (   ( 2 + scalar @{$tree} ) <= $length_limit
        && exists $lookup{'or'}
        && $max_var + 1 < $n )
    {
        prove_and_add(
            [ $lookup{'or'}, @{$tree}, $max_var + 1 ],
            $label . 'O2',
            undef, undef, undef, $new_proofs
        );
    }

    #
    if (   ( 2 + scalar @{$tree} ) <= $length_limit
        && exists $lookup{'and'}
        && exists $lookup{'TRUE'} )
    {

# prove_and_add( [ $lookup{'and'}, $lookup{'TRUE'}, @{$tree}], $label . 'A', undef, undef, undef, $new_proofs );
    }
    if (   ( 2 + scalar @{$tree} ) <= $length_limit
        && exists $lookup{'iff'}
        && exists $lookup{'TRUE'} )
    {

# prove_and_add( [ $lookup{'iff'}, $lookup{'TRUE'}, @{$tree}], $label . 'B3', undef, undef, undef, $new_proofs );
    }

    #
    if (   ( 2 + scalar @{$tree} ) <= $length_limit
        && exists $lookup{'or'}
        && $max_var + 1 < $n )
    {
        prove_and_add(
            [ $lookup{'or'}, 0, map { ( $_ >= 0 ) ? 1 + $_ : $_; } @{$tree} ],
            $label . 'O',
            undef, undef, undef, $new_proofs
        );
    }

    #
    if (   ( 3 + scalar @{$tree} ) <= $length_limit
        && exists $lookup{'and'}
        && exists $lookup{'FALSE'}
        && exists $lookup{'not'} )
    {
        prove_and_add(
            [ $lookup{'and'}, $lookup{'not'}, $lookup{'FALSE'}, @{$tree} ],
            $label . 'A2',
            undef, undef, undef, $new_proofs
        );
    }

    # pm2.24i ⊢ 𝜑    ⇒   ⊢ (¬ 𝜑 → 𝜓)
    if (   ( 3 + scalar @{$tree} ) <= $length_limit
        && exists $lookup{'implies'}
        && exists $lookup{'not'}
        && $max_var + 1 < $n )
    {
        prove_and_add(
            [ $lookup{'implies'}, $lookup{'not'}, @{$tree}, $max_var + 1 ],
            $label . 'D2',
            undef, undef, undef, $new_proofs
        );
    }

    #
    if (   ( 4 + scalar @{$tree} ) <= $length_limit
        && exists $lookup{'and'}
        && exists $lookup{'TRUE'}
        && exists $lookup{'not'} )
    {
        prove_and_add(
            [
                $lookup{'and'},  $lookup{'not'}, $lookup{'not'},
                $lookup{'TRUE'}, @{$tree}
            ],
            $label . 'A3',
            undef, undef, undef,
            $new_proofs
        );
    }

    #  ⊢ 𝜑    ⇒   ⊢ ( ( 𝜑 → 𝜓 ) → 𝜓 )
    if (   ( 4 + scalar @{$tree} ) <= $length_limit
        && exists $lookup{'implies'}
        && $max_var + 1 < $n )
    {
        prove_and_add(
            [
                $lookup{'implies'}, $lookup{'implies'}, @{$tree},
                $max_var + 1,       $max_var + 1
            ],
            $label . 'I2',
            undef, undef, undef,
            $new_proofs
        );
    }

    #
    if (   ( 5 + scalar @{$tree} ) <= $length_limit
        && exists $lookup{'and'}
        && exists $lookup{'FALSE'}
        && exists $lookup{'not'} )
    {
        prove_and_add(
            [
                $lookup{'and'}, $lookup{'not'},   $lookup{'not'},
                $lookup{'not'}, $lookup{'FALSE'}, @{$tree}
            ],
            $label . 'A4',
            undef, undef, undef,
            $new_proofs
        );
    }

    return;
}

__DATA__

##
# These propositions are specified one per line with a label followed
# by the syntax in prefix long-name notation, even though the infix
# asc (ASCII) format is used in metamath files and the infix utf
# (UTF-8 based on uni UNICODE format) is used for most display.
##

# 1
tru TRUE # ⊤

# 2
fal not FALSE # ¬ ⊥

# 3
biid iff phi phi #  ( 𝜑 ↔ 𝜑 )
# falim implies FALSE phi # ( ⊥ → 𝜑 )
# id implies phi phi # ( 𝜑 → 𝜑 )
# found28 and TRUE TRUE # truA : ( ⊤ ∧ ⊤ )

# 4
exmid or phi not phi
# found1 or not phi phi
found27 not and FALSE phi
# found29 and not FALSE TRUE
found30 iff not FALSE TRUE
found31 iff not TRUE FALSE
found44 not iff TRUE FALSE
found45 not or FALSE FALSE
found46 not implies TRUE FALSE



# 5
# idd implies phi implies psi psi
ax-1 implies phi implies psi phi # ( 𝜑 → ( 𝜓 → 𝜑 ) )
# notnot1 implies phi not not phi
# notnot2 implies not not phi phi
# orc implies phi or phi psi # ( 𝜑 → ( 𝜑 ∨ 𝜓 ) )
# olc implies phi or psi phi # ( 𝜑 → ( 𝜓 ∨ 𝜑 ) )
# simpl implies and phi psi phi # ( ( 𝜑 ∧ 𝜓 ) → 𝜑 )
# simpr implies and phi psi psi # ( ( 𝜑 ∧ 𝜓 ) → 𝜓 )
found3 not and not phi phi
# found4 not and phi not phi
# found5 iff not not phi phi
found6 iff phi not not phi
found7 not iff phi not phi
# found8 not iff not phi phi
found19 or phi implies phi psi
# found26 not and phi FALSE
# found32 and not FALSE not FALSE
# found33 and not not TRUE TRUE # truN2AC : ( ¬ ¬ ⊤ ∧ ⊤ )
found40 iff phi iff phi TRUE
found41 iff phi implies TRUE phi
found42 iff phi or phi phi
found43 iff phi and phi phi
found47 iff phi and phi TRUE
found48 iff phi and TRUE phi
found49 iff phi or FALSE phi
found50 iff phi or phi FALSE
found51 iff phi iff TRUE phi
found52 iff phi iff phi TRUE
found53 or phi iff phi FALSE
found54 or phi iff FALSE phi
found27a not and not TRUE phi
found30a iff not not TRUE TRUE
found31a iff not TRUE not TRUE
found44a not iff TRUE not TRUE
found46a not implies TRUE not TRUE
found45a not or not TRUE FALSE

# 6
# pm2.21 implies not phi implies phi psi # ( ¬ 𝜑 → ( 𝜑 → 𝜓 ) )
# pm2.24 implies phi implies not phi psi # ( 𝜑 → ( ¬ 𝜑 → 𝜓 ) )
# pm2.18 implies implies not phi phi phi
# simplim implies not implies phi psi phi
# found34 and not not TRUE not FALSE
# found35 and not not not FALSE TRUE
found45aa not or not TRUE not TRUE
found55 iff phi implies not phi phi

# 7
# foundA implies and phi psi and phi phi
# foundB implies and phi psi and psi phi
# foundC implies and phi psi and psi psi
# pm2.27 implies phi implies implies phi psi psi
# simprim implies not implies phi not psi psi
# pm2.01 implies implies phi not phi not phi
# peirce implies implies implies phi psi phi phi
# orcom iff or phi psi or psi phi # ( ( 𝜑 ∨ 𝜓 ) ↔ ( 𝜓 ∨ 𝜑 ) )
# ancom iff and phi psi and psi phi # ( ( 𝜑 ∧ 𝜓 ) ↔ ( 𝜓 ∧ 𝜑 ) )
# found9 implies phi implies psi implies chi phi
# found20 implies phi implies psi or chi phi
# found23 implies phi implies psi or phi chi
# found36 and not not TRUE not not TRUE
# found37 and not not not FALSE not FALSE

# 8
# df-or iff or phi psi implies not phi psi
# pm2.521 implies not implies phi psi implies psi phi
# found38 and not not not FALSE not not TRUE

# 9
# pm2.43 implies implies phi implies phi psi implies phi psi
# found22 implies phi implies implies implies psi chi psi psi
# found27 implies implies implies psi phi psi implies chi psi
# found29 implies implies implies phi implies psi chi psi psi
ax-3 implies implies not phi not psi implies psi phi
# con3 implies implies phi psi implies not psi not phi
# mth8 implies phi implies not psi not implies phi psi
# pm3.2im implies phi implies psi not implies phi not psi
# pm2.5 implies not implies phi psi implies not phi psi
# pm2.51 implies not implies phi psi implies phi not psi
# pm5.18 iff iff phi psi not iff phi not psi
# df-an iff and phi psi not implies phi not psi
# found10 implies phi implies psi implies chi implies theta phi
# found21 implies phi implies psi implies chi or theta phi
# found24 implies phi implies psi implies chi or phi theta
# found39 and not not not FALSE not not not FALSE

# 10
# pm2.52 implies not implies phi psi implies not phi not psi
# jarl   implies implies implies phi psi chi implies not phi chi
# pm2.6  implies implies not phi psi implies implies phi psi psi
# pm2.61 implies implies phi psi implies implies not phi psi psi

# 11
# pm2.04 implies implies phi implies psi chi implies psi implies phi chi
# imim1 implies implies phi psi implies implies psi chi implies phi chi
# imim2 implies implies phi psi implies implies chi phi implies chi psi
# loolin implies implies implies phi psi implies psi phi implies psi phi
# pm2.65 implies implies phi psi implies implies phi not psi not phi
# dfbi2 iff iff phi psi and implies phi psi implies psi phi
# found11 implies phi implies psi implies chi implies theta implies tau phi
# found22 implies phi implies psi implies chi implies theta or tau phi
# found25 implies phi implies psi implies chi implies theta or phi tau

# 13
ax-2 implies implies phi implies psi chi implies implies phi psi implies phi chi
# pm2.86 implies implies implies phi psi implies phi chi implies phi implies psi chi
# expt implies implies not implies phi not psi chi implies phi implies psi chi
# impt implies implies phi implies psi chi implies not implies phi not psi chi
# found12 implies phi implies psi implies chi implies theta implies tau implies eta phi

# 15
# prth implies and implies phi psi implies chi theta implies and phi chi and psi theta
# loowoz implies implies implies phi psi implies phi chi implies implies psi phi implies psi chi
# found13 implies phi implies psi implies chi implies theta implies tau implies eta implies zeta phi

# 17
# pm2.83 implies implies phi implies psi chi implies implies phi implies chi theta implies phi implies psi theta
# found14 implies phi implies psi implies chi implies theta implies tau implies eta implies zeta implies sigma phi

# 19
# found15 implies phi implies psi implies chi implies theta implies tau implies eta implies zeta implies sigma implies rho phi

# 21
# consensus iff or or and phi psi and not phi chi and psi chi or and phi psi and not phi chi
# found16 implies phi implies psi implies chi implies theta implies tau implies eta implies zeta implies sigma implies rho implies mu phi

# 23 
# found17 implies phi implies psi implies chi implies theta implies tau implies eta implies zeta implies sigma implies rho implies mu implies lamda phi

# 25
# found18 implies phi implies psi implies chi implies theta implies tau implies eta implies zeta implies sigma implies rho implies mu implies lamda implies kappa phi

# 41
# bijust not implies implies not implies implies phi psi not implies psi phi not implies implies phi psi not implies psi phi not implies not implies implies phi psi not implies psi phi not implies implies phi psi not implies psi phi

# vim: set ai sw=4
