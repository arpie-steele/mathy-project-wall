package Metamath::Options;

use strict;
use warnings;

# strict options are options more restrictive than the spec.
# loose options are options less restrictive than the spec.

sub new {
    my ($class_or_ref, %more_options) = @_;
    my $class = ref $class_or_ref || $class_or_ref;
    my %options = $class->default_options() ;
    if ( ref $class_or_ref ) {
	foreach my $key ( keys %{$class_or_ref} ) {
	    my $value = $class_or_ref->{$key};
	    if ( $value && $value eq 'UNSET' ) { delete $options{$key} ; next; }
	    $options{$key} = $value;
	}
    }
    foreach my $key ( keys %more_options ) {
        my $value = $more_options{$key};
        if ( $value && $value eq 'UNSET' ) { delete $options{$key} ; next; }
        $options{$key} = $value;
    }
    return bless { %options }, $class;
}

sub default_options {
    my ($class_or_ref) = @_;
    my %options = (
    );
    return %options;
}

1;
