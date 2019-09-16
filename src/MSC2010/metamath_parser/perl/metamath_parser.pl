#!/usr/bin/perl

use strict;
use warnings;

use Metamath::Database;
use Metamath::SourceFile;
use Metamath::Characters;
use Metamath::TokenKinds;

our $VERSION = 1.0;

# Metamath::Characters::display_statistics();

Metamath::TokenKinds::tokenize_stream( \*STDIN, 'STDIN' );

exit 0;
