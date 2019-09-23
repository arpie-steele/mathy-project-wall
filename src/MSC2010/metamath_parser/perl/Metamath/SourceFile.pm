package Metamath::SourceFile;

use strict;
use warnings;
use Carp;
use English qw(-no_match_vars);
use Metamath::Options;
use Metamath::Token;

sub new {
    my ($class_or_ref, $options, $filename, $optional_fh) = @_;
    my $obj = bless { }, ref $class_or_ref || $class_or_ref;
    if ( defined $options ) {
	$obj->set_options($options);
    }
    if ( defined $filename ) {
	$obj->set_filename($filename);
	if ( defined $optional_fh ) {
	    $obj->set_fh($optional_fh);
	}
    }
    return $obj;
}

sub set_options {
    my ($self, $options) = @_;
    $self->{'options'} = $options;
    return $self;
}

sub get_options {
    my ($self) = @_;
    my $options;
    if ( exists $self->{'options'} && defined $self->{'options'} ) {
	$options = $self->{'options'};
    } else {
        $options = Metamath::Options->new();
	$self->set_options($options);
    }
    return $options;
}

sub set_line_number {
    my ($self, $line_number) = @_;
    $self->{'ln'} = $line_number;
    return $self;
}

sub get_line_number {
    my ($self) = @_;
    my $line_number;
    if ( exists $self->{'ln'} && defined $self->{'ln'} ) {
	$line_number = $self->{'ln'};
    } else {
        $line_number = 0;
	$self->set_line_number($line_number);
    }
    return $line_number;
}

sub inc_line_number {
    my ($self) = @_;
    my $line_number = 1 + $self->get_line_number();
    $self->set_line_number($line_number);
    return $line_number;
}

sub set_filename {
    my ($self, $filename) = @_;
    $self->{'fn'} = $filename;
    return $self;
}

sub get_filename {
    my ($self) = @_;
    my $filename;
    if ( exists $self->{'fn'} && defined $self->{'fn'} ) {
	return $self->{'fn'};
    }
    croak 'filename unset in object';
}

sub set_eof {
    my ($self) = @_;
    $self->{'eof'} = 1;
    return $self;
}

sub get_eof {
    my ($self) = @_;
    my $filename;
    if ( exists $self->{'eof'} && $self->{'eof'} ) {
	return $self->{'eof'};
    }
    return;
}

sub set_can_close {
    my ($self, $can_close) = @_;
    $self->{'can_close'} = $can_close;
    return $self;
}

sub get_can_close {
    my ($self) = @_;
    my $can_close;
    if ( exists $self->{'can_close'} && $self->{'can_close'} ) {
	return $self->{'can_close'};
    }
    return;
}

sub set_fh {
    my ($self, $fh) = @_;
    $self->{'fh'} = $fh;
    return $self;
}

sub peek_fh {
    my ($self) = @_;
    my $fh;
    if ( exists $self->{'fh'} && defined $self->{'fh'} ) {
	$fh = $self->{'fh'};
    }
    return $fh;
}

sub get_fh {
    my ($self) = @_;
    my $fh;
    if ( exists $self->{'fh'} && defined $self->{'fh'} ) {
	$fh = $self->{'fh'};
    } else {
        my $fn = $self->get_filename();
        open $fh, '<', $fn or croak "$fh: open: $OS_ERROR";
	$self->set_fh($fh);
	$self->set_can_close(1);
    }
    return $fh;
}

sub close_fh {
    my ($self) = @_;
    if ( exists $self->{'fh'} && defined $self->{'fh'}  ) {
	my $fn = $self->get_filename();
	my $fh = $self->peek_fh();
        if ( $self->get_can_close() ) {
		close $fh or croak "$fn: close: $OS_ERROR";
        }
    }
    return $self;
}

sub DESTROY {
    my ($self) = @_;

    $self->close_fh();
}

sub tokenize {
    my ($self) = @_;
    while ( defined (my $token = $self->grab_next_token() ) ) {
    }
    return;
}

sub grab_next_line {
    my ($self) = @_;
    if ( $self->get_eof() ) { return; }
    my $fn = $self->get_filename();
    my $fh = $self->get_fh();
    my $line = <$fh>;
    if ( ! defined $line ) {
	$self->set_eof();
        return;
    }
    my $line_number = $self->inc_line_number();
    my @tokens =
map { Metamath::Token->new($_, $fn, $line_number); }
grep { 0 < length $_ }
split /((?:\s+)|(?:(?:[\$]{2})+)|(?:[\$][^\s\$]))/xms, $line, -1;
    if ( $tokens[0]->is_ws()
&& $self->token_cache_count() > 0
&& $self->token_cache_peek_last()->is_ws() ) {
        $self->token_cache_peek_last()->glue( shift @tokens );
    }
    $self->token_cache_push( @tokens );
    return 1;
}

sub grab_next_token {
    my ($self) = @_;
    if ( $self->get_eof() ) { return; }
    while ( $self->token_cache_count() < 2 ) {
	if ( ! $self->grab_next_line() ) {
	    last;
	}
    };
    if ( $self->token_cache_count() > 0 ) {
	return $self->shift_from_token_cache();
    }
    return;
}

sub token_cache_count {
    my ($self) = @_;
    if ( ! exists $self->{'token_cache'} ) {
	$self->{'token_cache'} = [ ];
    }
    return scalar @{$self->{'token_cache'}};
}

sub token_cache_push {
    my ($self, @tokens) = @_;
    if ( ! exists $self->{'token_cache'} ) {
	$self->{'token_cache'} = [ ];
    }
    push @{$self->{'token_cache'}}, @tokens;
    return scalar @{$self->{'token_cache'}};
}

sub shift_from_token_cache {
    my ($self) = @_;
    if ( ! exists $self->{'token_cache'} ) {
	$self->{'token_cache'} = [ ];
    }
    if ( ! scalar @{$self->{'token_cache'}} ) {
	carp "Unexpected shift of empty token cache";
        return;
    }
    return shift @{$self->{'token_cache'}};
}

sub token_cache_peek_last {
    my ($self) = @_;
    if ( ! exists $self->{'token_cache'} ) {
	$self->{'token_cache'} = [ ];
    }
    if ( ! scalar @{$self->{'token_cache'}} ) {
	croak "Unexpected peek of empty token cache";
    }
    return $self->{'token_cache'}->[-1];
}

sub dump_stats {
    my ($self) = @_;
    # TODO
    return;
}

1;
