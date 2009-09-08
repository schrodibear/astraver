/*
@PPC_OPTIONS: -cpp-extra-args='-I minix3_include'
 */
/*
 * (c) copyright 1987 by the Vrije Universiteit, Amsterdam, The Netherlands.
 * See the copyright notice in the ACK home directory, in the file "Copyright".
 */
/* $Header: /users/demons/filliatr/ARCHIVE/caml/why/frama-c-plugin/tests/jessie/minix3_strlen.c,v 1.1 2009-09-08 11:11:46 monate Exp $ */

#include <jessie_prolog.h>
#include	<string.h>

size_t
strlen(const char *FRAMA_C_STRING org)
{
	register const char *s = org;

	while (*s++)
		/* EMPTY */ ;

	return --s - org;
}

/* 
Local Variables:
compile-command: "./run_test.sh minix3_strlen.c"
End:
*/
