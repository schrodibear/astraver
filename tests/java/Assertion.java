public class Assertion {
         /*@
           @ ensures \result == 5;
           @*/
         public static int max(int x) {
                 /*@ assert x == 5; @*/
                 return x;
         }
} 