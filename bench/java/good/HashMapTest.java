/**************************************************************************/
/*                                                                        */
/*  The Why platform for program certification                            */
/*                                                                        */
/*  Copyright (C) 2002-2011                                               */
/*                                                                        */
/*    Jean-Christophe FILLIATRE, CNRS & Univ. Paris-sud 11                */
/*    Claude MARCHE, INRIA & Univ. Paris-sud 11                           */
/*    Yannick MOY, Univ. Paris-sud 11                                     */
/*    Romain BARDOU, Univ. Paris-sud 11                                   */
/*                                                                        */
/*  Secondary contributors:                                               */
/*                                                                        */
/*    Thierry HUBERT, Univ. Paris-sud 11  (former Caduceus front-end)     */
/*    Nicolas ROUSSET, Univ. Paris-sud 11 (on Jessie & Krakatoa)          */
/*    Ali AYAD, CNRS & CEA Saclay         (floating-point support)        */
/*    Sylvie BOLDO, INRIA                 (floating-point support)        */
/*    Jean-Francois COUCHOT, INRIA        (sort encodings, hyps pruning)  */
/*    Mehdi DOGGUY, Univ. Paris-sud 11    (Why GUI)                       */
/*                                                                        */
/*  This software is free software; you can redistribute it and/or        */
/*  modify it under the terms of the GNU Lesser General Public            */
/*  License version 2.1, with the special exception on linking            */
/*  described in file LICENSE.                                            */
/*                                                                        */
/*  This software is distributed in the hope that it will be useful,      */
/*  but WITHOUT ANY WARRANTY; without even the implied warranty of        */
/*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  */
/*                                                                        */
/**************************************************************************/

import java.util.HashMap;

/*

- ajout du source dans le repertoire de l'API Java de krakatoa

  cd .../lib/java_api
  unzip src.zip java/util/HashMap.java

- resol pb syntaxe dans HashMap.java

  commenté (avec //KML) 4 occurrences de
 
    HashMap.this.expr ...

  dans le code (pb support inner classes par Krakatoa)

  de toute facon: le code des methodes de l'API n'est pas utilise par Krakatoa, seulement les spec

- HashMap etend AbstractMap: besoin de

  unzip src.zip java/util/AbstractMap.java

- de nouveau 4 occurrences de 

    AbstractMap.this.... 

  commentees avec //KML

- import explicite de java.util.Map.Entry dans AbstractMap: commenté

- AbstractMap implemente Map -> ajouter Map

  unzip src.zip java/util/Map.java

- Map utilise Set et Collection ->

  unzip src.zip java/util/Set.java
  unzip src.zip java/util/Collection.java

- HashMap: champ transient Entry[] table; commente

- HashMap: methode getEntry commentee

- HashMap: methode removeEntryForKey commentee

- HashMap: methode removeMapping commentee

- ajout de Iterator

  unzip src.zip java/util/Iterator.java

- methodes de serialization commentees

*/

class HashMapTest {

    public static void main(String argv[]) {

	HashMap m = new HashMap();

	Integer zero = new Integer(0);

	Integer one = new Integer(1);

	m.put(zero,one);

	Object o = m.get(zero);

	//@ assert o instanceof Integer ; 
	// && o == 1;
	
	// System.out.println("o = " + o);

    }

}
	