package java.lang;

public class System {

    /**Copies an array from the specified source array, beginning at the
 specified position, to the specified position of the destination array.
 A subsequence of array components are copied from the source
 array referenced by <code>src</code> to the destination array
 referenced by <code>dest</code>. The number of components copied is
 equal to the <code>length</code> argument. The components at
 positions <code>srcPos</code> through
 <code>srcPos+length-1</code> in the source array are copied into
 positions <code>destPos</code> through
 <code>destPos+length-1</code>, respectively, of the destination
 array.
 <p>

 If the <code>src</code> and <code>dest</code> arguments refer to the
 same array object, then the copying is performed as if the
 components at positions <code>srcPos</code> through
 <code>srcPos+length-1</code> were first copied to a temporary
 array with <code>length</code> components and then the contents of
 the temporary array were copied into positions
 <code>destPos</code> through <code>destPos+length-1</code> of the
 destination array.
 <p>

 If <code>dest</code> is <code>null</code>, then a
 <code>NullPointerException</code> is thrown.
 <p>
 If <code>src</code> is <code>null</code>, then a
 <code>NullPointerException</code> is thrown and the destination
 array is not modified.
 <p>

 Otherwise, if any of the following is true, an
 <code>ArrayStoreException</code> is thrown and the destination is
 not modified:
 <ul>
 <li>The <code>src</code> argument refers to an object that is not an
     array.
 <li>The <code>dest</code> argument refers to an object that is not an
     array.
 <li>The <code>src</code> argument and <code>dest</code> argument refer
     to arrays whose component types are different primitive types.
 <li>The <code>src</code> argument refers to an array with a primitive
    component type and the <code>dest</code> argument refers to an array
     with a reference component type.
 <li>The <code>src</code> argument refers to an array with a reference
    component type and the <code>dest</code> argument refers to an array
     with a primitive component type.
 </ul>

 <p>
 Otherwise, if any of the following is true, an
 <code>IndexOutOfBoundsException</code> is
 thrown and the destination is not modified:
 <ul>
 <li>The <code>srcPos</code> argument is negative.
 <li>The <code>destPos</code> argument is negative.
 <li>The <code>length</code> argument is negative.
 <li><code>srcPos+length</code> is greater than
     <code>src.length</code>, the length of the source array.
 <li><code>destPos+length</code> is greater than
     <code>dest.length</code>, the length of the destination array.
 </ul>

 <p>
 Otherwise, if any actual component of the source array from
 position <code>srcPos</code> through
 <code>srcPos+length-1</code> cannot be converted to the component
 type of the destination array by assignment conversion, an
 <code>ArrayStoreException</code> is thrown. In this case, let
 <b><i>k</i></b> be the smallest nonnegative integer less than
 length such that <code>src[srcPos+</code><i>k</i><code>]</code>

 cannot be converted to the component type of the destination
 array; when the exception is thrown, source array components from
 positions <code>srcPos</code> through
 <code>srcPos+</code><i>k</i><code>-1</code>
 will already have been copied to destination array positions
 <code>destPos</code> through
 <code>destPos+</code><i>k</i><code>-1</code> and no other
 positions of the destination array will have been modified.
 (Because of the restrictions already itemized, this
 paragraph effectively applies only to the situation where both
 arrays have component types that are reference types.)

<p>
    */
    /* public normal_behavior
      @  requires src != null &&  srcPos >= 0 &&
      @    srcPos+length <= src.length && dst != null && 
      @    dstPos >= 0 && dstPos+length <= dst.length &&
      @    length >= 0;
      @  modifiable dst[dstPos..dstPos+length-1];
      @     ensures (\forall int i ; 0 <= i && i < length ;
      @                    dst[dstPos+i] == \old(src[srcPos+i]));
      @*/
    /* INCOMPLETE : exceptional_behavior
     */
    /*
static void arraycopy(Object src, int srcPos, Object dst, int dstPos, int length);
    */
 
    /*@ public normal_behavior
      @  requires src != null &&  srcPos >= 0 &&
      @    srcPos+length <= src.length && dst != null && 
      @    dstPos >= 0 && dstPos+length <= dst.length &&
      @    length >= 0;
      @  modifiable dst[dstPos..dstPos+length-1];
      @     ensures (\forall int i ; 0 <= i && i < length ;
      @                    dst[dstPos+i] == \old(src[srcPos+i]));
      @*/
    /* INCOMPLETE : exceptional_behavior
     */
    static void arraycopy(int[] src, int srcPos, int[] dst, int dstPos, int length);
 
}
