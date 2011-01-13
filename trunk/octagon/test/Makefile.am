AUTOMAKE_OPTIONS = 1.4

lib_suffix = @lib_suffix@

AUTOHEADER = echo ""

SUBDIRS=.

# octtest

AM_CFLAGS=-I.. -I../clib @CFLAGS@ @EXTRA_DEFS@

bin_PROGRAMS = octtest
octtest_SOURCES = oct_test.c

octtest_LDADD = ../clib/liboct_LIBSUFFIX.la


# clean

clean-local:
	rm -f *~ *.tmp \#*


# dist

distclean-local:
	rm -f Makefile

