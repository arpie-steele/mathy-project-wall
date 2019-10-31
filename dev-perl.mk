REQUIREDPACKAGES = perl-Data-Dumper perl-Perl-Critic
PERL = /usr/bin/perl
PERLCHECKFLAGS = -c -w -T $(shell perl -MFile::Find -MFile::Spec -e ' \
find( \
    sub { \
        if (/^(.+)[.]pm$$/) { \
            my $$pkg = $$1; \
            if ( open my $$fh, q(<), $$_ ) { \
                while ( defined( my $$line = <$$fh> ) ) { \
                    if ( $$line =~ /^\s*package\s+((?:\w+[:][:])*\Q$$pkg\E)\s*;/ ) \
                    { \
                        my $$count = scalar split /[:][:]/, $$1; \
                        @dirs = File::Spec->splitdir($$File::Find::dir); \
                        if ( $$count > 1 ) { splice @dirs, ( 1 - $$count ); } \
                        my $$dir = File::Spec->catdir(@dirs); \
                        $$libs{$$dir}++; \
                        last; \
                    } \
                } \
                close $$fh; \
            } \
        } \
    }, \
    q(.) \
); \
print map { "-I $$_\n"; } sort keys %libs; \
')

FINDSKIPNOTPERL = $(shell perl -e ' \
    print map {"! -iname \x27$$_\x27\n";} sort { (lc $$a) cmp (lc $$b ) } @ARGV; \
' \
'.??*' '*~[1-9]' '*.[1-9]' '*.am' '*.BAK' '*.bbcode' '*.body' '*.c' 'Changes' \
'*.cmd' '*.conf' 'configure.ac' '*.crt' '*.css' '*.dec' '*.enc' '*.gz' '*.h' \
'*.header' '*.html' '*.inc' '*.ini' '*.java' '*.jpg' '*.js' '*.json' '*.key' \
'*.keydb' '*.lck' 'ldaprc' '*.ldif' 'LICENSE' 'log' 'Makefile' '*.md' '*.m' '*.mk' \
'*.mm' '*.mmts' '*.ora' '*.p12' '*.patch' '*.pem' '*.php' 'phpab' 'phpdoc' \
'phpunit' '*.png' '*.py' '*.rb' '*README' '*.sh' '*.sso' '*.sty' '*.svg' \
'*.tex' '*.tgz' 'theorems' 'theorems?' 'TODO' '*.txt' 'Vagrantfile' '*.yicf' \
)
FINDNOTSRCDIR = $(shell perl -e ' \
    print map {"-name \x27$$_\x27 -prune -o\n";} sort { (lc $$a) cmp (lc $$b ) } @ARGV; \
' \
.git .vagrant docs output \
)

PERLCRITIC = /usr/bin/perlcritic
PERLCRITICFLAGS = --verbose=9 -1

.PHONY: perlcritic

perlcritic:
	@find . $(FINDNOTSRCDIR) -type f $(FINDSKIPNOTPERL) -print \
	| xargs file | egrep -i perl | cut -d: -f1 | sort \
	| while read file ; do \
		echo $(PERL) $(PERLCHECKFLAGS) $$file ; \
		if $(PERL) $(PERLCHECKFLAGS) $$file ; then \
			: ; \
		else \
			grep -n '^use' $$file ; \
			exit 1 ; \
		fi ; \
	        if [ -x $(PERLCRITIC) ] ; then \
		echo $(PERLCRITIC) $(PERLCRITICFLAGS) $$file ; \
			if $(PERLCRITIC) $(PERLCRITICFLAGS) $$file ; then \
				: ; \
			else \
				exit 1 ; \
			fi ; \
		else \
			echo Skipping $(PERLCRITIC) $(PERLCRITICFLAGS) $$file; \
		fi ; \
	done
	@if [ -x $(PERLCRITIC) ] ; then \
		: ; \
	else \
		echo Please install perl-Perl-Critic with package manager ; \
	fi

