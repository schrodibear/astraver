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

/* $Id: stddef.h,v 1.1 2009-09-08 11:11:43 monate Exp $ */

#ifndef _STDDEF_H_
#define _STDDEF_H_

#ifndef NULL
# define NULL ((void*)0)
#endif

#ifndef _WCHAR_T
# define _WCHAR_T
typedef unsigned short wchar_t;
#endif

#ifndef _SIZE_T
# define _SIZE_T
typedef unsigned int size_t;
#endif

#endif /* _STDDEF_H_ */
