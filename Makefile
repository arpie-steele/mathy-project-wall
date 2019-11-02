TOP = .
MACCC = /usr/bin/gcc
MACCFLAGS = -O3 -funroll-loops -finline-functions -fomit-frame-pointer -Wall -pedantic
MMDIR = submodules/metamath-exe
MMMISSING = Makefile.in aclocal.m4 autom4te.cache config.h.in configure depcomp install-sh missing
REQUIREDPACKAGES = perl-Data-Dumper perl-Perl-Critic automake autoconf
SUBDIRS = src/MSC2010

all: metamath all-subdirs

metamath : $(MMDIR)/*.c $(MMDIR)/*.h
	@if [ "`uname -s`" = Darwin ] ; then \
		echo $(MACCC) -I $(MMDIR) $(MACCFLAGS) -o $@ $(MMDIR)/m*.c ; \
		$(MACCC) -I $(MMDIR) $(MACCFLAGS) -o $@ $(MMDIR)/m*.c ; \
	elif [ "`uname -s`" = Linux ] ; then \
		echo cd submodules/metamath-exe ; \
		cd submodules/metamath-exe \
			&& echo aclocal \
			&& aclocal \
			&& echo autoheader \
			&& autoheader \
			&& echo automake --add-missing \
			&& automake --add-missing \
			&& echo autoconf \
			&& autoconf \
			&& echo ./configure \
			&& ./configure \
			&& echo make metamath \
			&& make metamath \
			&& echo mv metamath ../.. \
			&& mv metamath ../.. \
			&& echo make distclean \
			&& make distclean \
			&& echo rm -rf $(MMMISSING) \
			&& rm -rf $(MMMISSING) ; \
	else \
		echo "I'm not sure how to build $@ for your system." ; \
		exit 1; \
	fi

dev-install:
	@if [ -x /usr/bin/yum ] ; then \
		echo sudo yum install $(REQUIREDPACKAGES) ; \
		sudo yum install $(REQUIREDPACKAGES) ; \
	else \
		echo "I don't know how to install packages on your system" ; \
		exit 1; \
	fi

include $(TOP)/dev-subdirs.mk
