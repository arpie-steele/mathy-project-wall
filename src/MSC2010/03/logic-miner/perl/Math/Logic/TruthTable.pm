package Math::Logic::TruthTable;

use strict;
use warnings;
use Math::Logic::TruthTable::Environment;

our $VERSION = 1;

sub new_environment {
    my $value = Math::Logic::TruthTable::Environment->new();
    return $value;
}

1;
