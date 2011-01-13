AUTOMAKE_OPTIONS = 1.4

AUTOHEADER = echo ""

#SUBDIRS = . @SUBDIRS@
SUBDIRS = . clib test ocamllib 

# installed binaries

bin_SCRIPTS = oct-config oct-config-LIBSUFFIX

# installed headers

configincludedir = $(includedir)/oct
liboctincludedir = $(includedir)/oct
liboctinclude_HEADERS = oct_config_2.h


# clean

clean-local:
	rm -f *~ *.tmp \#*
#	rm -f oct-config oct-config-* oct_config*.h


# dist

distclean-local:
	rm -f Makefile configure.cache


# uninstall

uninstall-local:
	rm -f $(DESTDIR)$(bindir)/oct-config-*


oct_config_2.h:
	touch oct_config_2.h

