package GenCompare;

use strict;
use warnings;

use Scalar::Util qw(blessed);

our $VERSION = '1.0';

sub compare_gen {
    my ($this, $that) = @_;
    if ( $this->can('compare') ) {
	if ( $that->can('compare') ) {
	    return $this->compare($that);
	} else {
	    return 1;
	}
    } else {
	if ( $that->can('compare') ) {
	    return -1;
	} else {
	    return $this cmp $that;
	}
    }
}

sub compare_array {
    my ($this, $that) = @_;
    my $n = scalar @{$this};
    my $m = scalar @{$that};
    my $top = ( $n < $m ) ? $n - 1 : $m - 1 ;
    foreach my $i ( 0..$top ) {
        my $result = compare($this->[$i], $that->[$i]);
        if ( $result ) {
	    return $result;
	}
    }
    return $n <=> $m;
}

sub compare_hash {
    my ($this, $that) = @_;
    my @n = keys %{$this};
    my @m = keys %{$that};
    my %union = map { ( $_ => 1 ); } ( @n, @m );
    foreach my $k ( sort keys %union ) {
        if ( exists $this->{$k} ) {
	    if ( exists $that->{$k} ) {
		next;
	    } else {
		return 1;
	    }
        } else {
	    if ( exists $that->{$k} ) {
		return -1;
	    } else {
		next; # Should never reach
	    }
        }
    }
    foreach my $k ( sort keys %union ) {
        my $left = ( exists $this->{$k} ) ? $this->{$k} : undef;
        my $right = ( exists $that->{$k} ) ? $that->{$k} : undef;
        my $result = compare($left, $right);
        if ( $result ) {
	    return $result;
	}
    }
    return 0;
}

sub compare_obj {
    my ($this, $that) = @_;
    if ( blessed $this ) {
	if ( blessed $that ) {
	    return compare_gen($this, $that);
	} else {
	    return 1;
	}
    } else {
	if ( blessed $that ) {
	    return -1;
	} else {
	    if ( 'ARRAY' eq ref $this ) {
		if ( 'ARRAY' eq ref $that ) {
		    return compare_array($this, $that);
		} else {
		    return 1;
		}
	    } else {
		if ( 'ARRAY' eq ref $that ) {
		    return -1;
		} else {
		    if ( 'HASH' eq ref $this ) {
			if ( 'HASH' eq ref $that ) {
			    return compare_hash($this, $that);
			} else {
			    return 1;
			}
		    } else {
			if ( 'HASH' eq ref $that ) {
			    return -1;
			} else {
			    return $this cmp $that;
			}
		    }
		}
	    }
	}
    }
}

sub compare_refs {
    my ($this, $that) = @_;
    if ( ref $this ) {
	if ( ref $that ) {
	    return compare_obj($this, $that);
	} else {
	    return 1;
	}
    } else {
	if ( ref $that ) {
	    return -1;
	} else {
	    return $this cmp $that;
	}
    }
}

sub compare {
    my ($this, $that) = @_;
    if ( defined $this ) {
	if ( defined $that ) {
	    return compare_refs($this, $that);
	} else {
	    return 1;
	}
    } else {
	if ( defined $that ) {
	    return -1;
	} else {
	    return 0;
	}
    }
}
