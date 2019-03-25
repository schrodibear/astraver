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

/* $Id: astraver_spec_prolog.h,v 1.1 2013-11-28 16:06:45 mandrykin Exp $ */

#ifndef _JESSIE_SPEC_PROLOG_H_
#define _JESSIE_SPEC_PROLOG_H_

#ifndef _SIZE_T
#ifdef __kernel_size_t
#define _SIZE_T
typedef __kernel_size_t size_t;
#else
#include <stddef.h>
#define _SIZE_T
#endif
#endif

typedef char _type;

/*@ axiomatic memcpy__type {
  @   predicate memcmp__type{L1, L2}(_type *p1, _type *p2, size_t n) =
  @     n % (sizeof (_type)) == 0 &&
  @     \let _n = n / sizeof (_type);
  @     \valid{L1}(((_type *) p1)+(0 .. _n - 1)) &&
  @     \valid{L2}(((_type *) p2)+(0 .. _n - 1)) &&
  @     \forall integer k; 0 <= k < _n ==> \at(p1[k], L1) == \at(p2[k], L2);
  @   predicate separated__type{L1, L2}(_type *p1, _type *p2, size_t n) =
  @      n % (sizeof (_type)) == 0 &&
  @      \let _n = n / sizeof (_type);
  @      \valid{L1}(((_type *) p1)+(0 .. _n - 1)) && \valid{L2}(((_type *) p2)+(0 .. _n - 1)) &&
  @      (\base_addr{L1}(p1) != \base_addr{L2}(p2) || \separated(p1+(0.._n-1), p2) && \separated(p2+(0.._n-1), p1));
  @ }
  @ */

/*@ requires n >= 0 &&
  @          n % (sizeof (_type)) == 0 &&
  @          \let _n = n / sizeof (_type);
  @          \valid(((_type *) dest)+(0 .. _n - 1)) &&
  @          \valid(((_type *) src)+(0 .. _n - 1)) &&
  @          separated__type{Pre, Pre}((_type *) dest,(_type *) src, n);
  @ assigns ((_type *) dest)[0 .. (n / sizeof (_type)) - 1] \from ((_type *) src)[0 .. (n / sizeof (_type)) - 1];
  @ allocates \nothing;
  @ ensures memcmp__type{Here, Here}((_type *) dest, (_type *) src, n) && \result == dest;
  @*/
extern _type *memcpy__type(_type *restrict dest, const _type *restrict src, size_t n);

//@ assigns ((char *) dest)[0 .. n - 1];
void *memcpy(void *dest, const void *src, size_t n);

/*@ requires n >= 0 &&
  @          n % (sizeof (_type)) == 0 &&
  @          \let _n = n / sizeof (_type);
  @          \valid(((_type *) dest)+(0 .. _n - 1)) &&
  @          \valid(((_type *) src)+(0 .. _n - 1)) &&
  @          separated__type{Pre, Pre}((_type *) dest,(_type *) src, n);
  @ assigns ((_type *) dest)[0 .. (n / sizeof (_type)) - 1] \from ((_type *) src)[0 .. (n / sizeof (_type)) - 1];
  @ allocates \nothing;
  @ ensures memcmp__type{Here, Here}((_type *) dest, (_type *) src, n) && \result == dest;
  @*/
extern _type *__memcpy__type(_type *restrict dest, const _type *restrict src, size_t n);

//@ assigns ((char *) dest)[0 .. n - 1];
void *__memcpy(void *dest, const void *src, size_t n);

/*@ requires n >= 0 &&
  @          n % (sizeof (_type)) == 0 &&
  @          \let _n = n / sizeof (_type);
  @          \valid(((_type *) dest)+(0 .. _n - 1)) &&
  @          \valid(((_type *) src)+(0 .. _n - 1));
  @ assigns ((_type *) dest)[0 .. (n / sizeof (_type)) - 1] \from ((_type *) src)[0 .. (n / sizeof (_type)) - 1];
  @ allocates \nothing;
  @ ensures memcmp__type{Here, Pre}((_type *) dest, (_type *) src, n) && \result == dest;
  @*/
extern _type *memmove__type(_type *dest, const _type *src, size_t n);

//@ assigns ((char *) dest)[0 .. n - 1];
void *memmove(void *dest, const void *src, size_t n);

/*@ requires n >= 0 &&
  @          n % (sizeof (_type)) == 0 &&
  @          \let _n = n / sizeof (_type);
  @          \valid(((_type *) dest)+(0 .. _n - 1)) &&
  @          \valid(((_type *) src)+(0 .. _n - 1));
  @ assigns \nothing;
  @ allocates \nothing;
  @ ensures \result == 0 <==> memcmp__type{Here, Here}((_type *) dest, (_type *) src, n);
  @*/
extern int memcmp__type(const _type *dest, const _type *src, size_t n);

//@ assigns \nothing;
int memcmp(const void *dest, const void *src, size_t n);

/*@ requires n >= 0 &&
  @          n % (sizeof (_type)) == 0 &&
  @          \let _n = n / sizeof (_type);
  @          \valid(((_type *) dest)+(0 .. _n - 1));
  @ assigns ((_type *) dest)[0 .. (n / sizeof (_type)) - 1] \from val;
  @ allocates \nothing;
  @ ensures \let _n = n / sizeof (_type);
  @           val == 0 ==>
  @             ((\forall integer k; 0 <= k < _n ==> dest[k] == (_type) (unsigned  char) val) &&
  @              (_n >= 1 ==> *dest == (_type) (unsigned char) val));
  @*/
extern void *memset__type(_type *dest, int val, size_t n);

//@ assigns ((char *) dest)[0 .. n - 1];
void *memset(void *dest, int val, size_t n);

#endif /* _JESSIE_SPEC_PROLOG_H_ */
