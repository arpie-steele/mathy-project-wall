#!/usr/bin/perl

use strict;
use warnings;

use Metamath::Characters;
use Metamath::Database;
use Metamath::Options;
use Metamath::SourceFile;
use Metamath::TokenKinds;

our $VERSION = 1.0;

# Metamath::Characters::display_statistics();

Metamath::TokenKinds::tokenize_stream( \*STDIN, 'STDIN' );

exit 0;
