include mmdef.mk

PERL = /usr/bin/perl
METAMATH=$(TOP)/metamath
METAMATHCMDS='verify proof *' 'write theorem_list/show_lemmas/alt_html/no_versioning/theorems_per_page 1000000' 'quit'
SUBMODULES=$(TOP)/submodules

clean-mm :
	rm -f iset.mm nf.mm set.mm mmtheorems.html mmtheorems1.html

$(MMHTML) : | mmdef.mk

mmdef.mk : $(MMHTML:.html=.mm)
	$(PERL) -e 'foreach $$fn (@ARGV) { $$htm = $$fn; $$htm =~ s/[.]mm$$/.html/; $$out{$$htm}->{$$fn} = 1; if ( open $$fh, q(<), $$fn ) { while (<$$fh>) { if (/\$$\[\s+(\S+)\s+\$$\]/) { $$out{$$htm}->{$$1} = 1; } } } } foreach $$htm ( sort keys %out ) { print "$$htm mmdef.mk: @{[sort keys %{$$out{$$htm}}]}\n"; }' $(MMHTML:.html=.mm) > $@

%.html : %.mm
	@if [ ! -x $(METAMATH) ] ; then \
		echo Please cd to $TOP and type make metamath ; \
		exit 1 ; \
	fi
	@firststatement="`$(PERL) -ne ' \
	if ( /\\s*(\\S+)\s+\\$$[pa]\\s+/ ) { print qq($$1\\n); last; } \
	' $<`" ; \
	if [ "$$firststatement" = "" ] ; then \
		echo "No proofs or axioms found in $<. Skipping." ; \
		exit 0; \
	fi ; \
	echo $(METAMATH) '"read $<"' "$(METAMATHCMDS)" ; \
	if $(METAMATH) "read $<" $(METAMATHCMDS) \
		| grep 'All proofs in the database were verified' \
		> /dev/null ; then \
	        rm -f mmtheorems.html ; \
	else \
		echo "Not all proofs in the file $< were proven" ; \
	        rm -f mmtheorems.html mmtheorems1.html ; \
		exit 1; \
	fi ; \
	blank1=`$(PERL) -ne ' \
	$$l++; \
	if (/<TR BGCOLOR=white><TD/) { $$a = $$l; } \
	if ( $$a && $$a + 1 == $$l && /^$$/ ) { $$b = $$l } \
	if (/NAME="mm1h"/) { print qq($$b\n); last; } \
	' mmtheorems1.html` ; \
	if [ "$$blank1" = "" ] ; then \
		echo Could not find mm1h in mmtheorems1.html \
		exit 1 ; \
	fi ; \
	blank2=`$(PERL) -ne ' \
	$$l++; \
	if (/<TR BGCOLOR=white><TD/) { $$a = $$l; } \
	if ( $$a && $$a + 1 == $$l && /^$$/ ) { $$b = $$l } \
	if (/NAME="\Q'"$$firststatement"'\E"/) { print qq($$b\n); last; } \
	' mmtheorems1.html` ; \
	if [ "$$blank2" = "" ] ; then \
		echo Could not find $$firststatement in mmtheorems1.html \
		exit 1 ; \
	fi ; \
	echo -E -e 42,114d -e "$$blank1","$$blank2"d -e '/<HR NOSHADE/,/<HR NOSHADE/d' -e "'/<TABLE BORDER=0 WIDTH="100%">/,/<\/TABLE>/d' < mmtheorems1.html > $@" ; \
	sed -E -e 42,114d -e "$$blank1","$$blank2"d -e '/<HR NOSHADE/,/<HR NOSHADE/d' -e '/<TABLE BORDER=0 WIDTH="100%">/,/<\/TABLE>/d' < mmtheorems1.html > $@ ; \
	rm -f mmtheorems1.html

iset.mm nf.mm set.mm :
	@if [ -f $(SUBMODULES)/set.mm/$@ ] ; then \
		echo ln -s $(SUBMODULES)/set.mm/$@ . ; \
		ln -s $(SUBMODULES)/set.mm/$@ . ; \
	else \
		echo The submodule $(SUBMODULES)/set.mm does not \
			appear to be initialized. ; \
		exit 1 ; \
	fi
