/**************************************************************************/
/*                                                                        */
/*  This file is part of Frama-C.                                         */
/*                                                                        */
/*  Copyright (C) 2007-2009                                               */
/*    INRIA (Institut National de Recherche en Informatique et en         */
/*           Automatique)                                                 */
/*                                                                        */
/*  you can redistribute it and/or modify it under the terms of the GNU   */
/*  Lesser General Public License as published by the Free Software       */
/*  Foundation, version 2.1.                                              */
/*                                                                        */
/*  It is distributed in the hope that it will be useful,                 */
/*  but WITHOUT ANY WARRANTY; without even the implied warranty of        */
/*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the         */
/*  GNU Lesser General Public License for more details.                   */
/*                                                                        */
/*  See the GNU Lesser General Public License version 2.1                 */
/*  for more details (enclosed in the file licenses/LGPLv2.1).            */
/*                                                                        */
/**************************************************************************/

/* $Id: strings.h,v 1.1 2009-09-08 11:11:43 monate Exp $ */

#ifndef _STRINGS_H_
#define _STRINGS_H_

/*@ requires valid_string(s1) && valid_string(s2);
  @ assigns \nothing;
  @ ensures \true;
  @*/
extern int strcasecmp(const char *s1, const char *s2);

/*@ requires \valid(((char*)dest)+(0..n - 1))
  @          && \valid(((char*)src)+(0..n - 1));
  @ assigns ((char*)dest)[0..n - 1];
  @ ensures memcmp((char*)dest,(char*)src,n) == 0;
  @*/
extern void bcopy(const void *src, void *dest, size_t n);

#endif /* _STRINGS_H_ */
