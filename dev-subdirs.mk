
all-subdirs :
	for dir in $(SUBDIRS) ; do \
		( cd $$dir &&  make all ) ; \
	done

.PHONY : all-subdirs
