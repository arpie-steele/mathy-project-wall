#!/usr/bin/perl

use strict;
use warnings;

use Metamath::Options;
use Metamath::SourceFile;

our $VERSION = 1.0;

my $file_options = Metamath::Options->new();

if ( !scalar @ARGV ) {
    my $file = Metamath::SourceFile->new( $file_options, 'STDIN', \*STDIN );
    $file->tokenize();
    $file->dump_stats( \*STDOUT );
    exit 0;
}

foreach my $filename (@ARGV) {
    my $file = Metamath::SourceFile->new( $file_options, $filename );
    $file->tokenize();
    $file->dump_stats( \*STDOUT );
}

exit 0;
