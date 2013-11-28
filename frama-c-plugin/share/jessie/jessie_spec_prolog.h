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

/* $Id: jessie_spec_prolog.h,v 1.1 2013-11-28 16:06:45 mandrykin Exp $ */

#ifndef _JESSIE_SPEC_PROLOG_H_
#define _JESSIE_SPEC_PROLOG_H_

#include <stddef.h>

typedef char _type;

/*@ axiomatic memcpy_for_spec {
  @   predicate memcmp__type{L1, L2}(_type *p_type1, _type *p_type2, size_t n) =
  @     n % (sizeof (_type)) == 0 &&
  @     \let _n = n / sizeof (_type);
  @     \valid{L1}(((_type *) p_type1)+(0 .. _n - 1)) &&
  @     \valid{L2}(((_type *) p_type2)+(0 .. _n - 1)) &&
  @     \forall integer k; 0 <= k < _n ==> \at(p_type1[k], L1) == \at(p_type2[k], L2);
  @   predicate separated__type{L1, L2}(_type *p_type1, _type *p_type2, size_t n) =
  @      n % (sizeof (_type)) == 0 &&
  @      \let _n = n / sizeof (_type);
  @      \valid{L1}(((_type *) p_type1)+(0 .. _n - 1)) && \valid{L2}(((_type *) p_type2)+(0 .. _n - 1)) &&
  @      (\base_addr{L1}(p_type1) != \base_addr{L2}(p_type2) ||
  @       \offset_max{L1}(p_type1) < \offset_min{L2}(p_type2) ||
  @       \offset_max{L2}(p_type2) < \offset_min{L1}(p_type1));
  @ }
  @ */

/*@ requires n > 0 &&
  @          n % (sizeof (_type)) == 0 &&
  @          \let _n = n / sizeof (_type);
  @          \valid(((_type *) dest)+(0 .. _n - 1)) &&
  @          \valid(((_type *) src)+(0 .. _n - 1)) &&
  @          separated__type{Pre, Pre}((_type *) dest,(_type *) src, n);
  @ assigns ((_type *) dest)[0 .. (n / sizeof (_type)) - 1] \from ((_type *) src)[0 .. (n / sizeof (_type)) - 1];
  @ ensures memcmp__type{Here, Here}((_type *) dest, (_type *) src, n) && \result == dest;
  @*/
_type *memcpy__type(_type *restrict dest, const _type *restrict src, size_t n);




#endif /* _JESSIE_SPEC_PROLOG_H_ */