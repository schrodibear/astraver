AUTOMAKE_OPTIONS = 1.4

lib_suffix = @lib_suffix@

AUTOHEADER = echo ""

SUBDIRS=.

# flags

AM_CFLAGS=-I.. @CFLAGS@ @EXTRA_DEFS@

# installed headers

configincludedir = $(includedir)/oct
liboctincludedir = $(includedir)/oct
liboctinclude_HEADERS = oct_num.h oct_private.h oct.h 


# liboct

lib_LTLIBRARIES = liboct.la liboct_LIBSUFFIX.la

liboct_la_SOURCES = oct_polka.c oct_sem.c oct_util.c
liboct_LIBSUFFIX_la_SOURCES = oct_polka.c oct_sem.c oct_util.c


# clean

clean-local:
	rm -f *~ *.tmp \#*
	rm -f liboct_*.la

# dist

distclean-local:
	rm -f Makefile

EXTRA_DIST=README


# uninstall

uninstall-local:
	rm -f $(DESTDIR)$(libdir)/liboct_*



