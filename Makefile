REQUIREDPACKAGES = perl-Data-Dumper perl-Perl-Critic

all: metamath perlcritic

metamath : submodules/metamath-exe/*.c submodules/metamath-exe/*.h
	gcc -I submodules/metamath-exe -O3 -funroll-loops -finline-functions -fomit-frame-pointer -Wall -pedantic -o $@ submodules/metamath-exe/m*.c

dev-install:
	@if [ -x /usr/bin/yum ] ; then \
		echo sudo yum install $(REQUIREDPACKAGES) ; \
		sudo yum install $(REQUIREDPACKAGES) ; \
	else \
		echo "I don't know how to install packages on your system" ; \
		exit 1; \
	fi

include dev-perl.mk
