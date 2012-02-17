/* Read about this function at:

   http://sna-projects.com/blog/2010/06/beating-binary-search/

   The function that follows is a translation to C
*/


/*@ 
  requires 0 < array_length ;
  requires \forall integer i, j ; 
     (0 <= i <= j < array_length ==> array[i] <= array[j]) ;
  requires \valid(array+(0..array_length-1)) ;
*/
int 
interpolationSearch(int key, int array[], int array_length) 
{
    int low = 0;
    int high = array_length - 1;
    int min = array[0];
    int max = array[high];
    /*@ 
      loop invariant 0 <= low < array_length ;
      loop invariant 0 <= high < array_length ;
    */
    while(1) {
        if(low > high || key < min || key > max)
            return -1;

        // make a guess of the location
        int guess;
        if(high == low) {
            guess = high;
        } else {
            int size = high - low;
            int offset = (((size - 1) * ((long long)key - min)) / ((long long)max - min));
            guess = low + offset;
        }

        // maybe we found it?
        if(array[guess] == key)
            return guess;

        // if we didn't find it and we are out of space to look, give up
        if(guess == 0 || guess == array_length - 1)
            return -1;

        // if we guessed to high, guess lower or vice versa
        if(array[guess] > key) {
            high = guess - 1;
            max = array[guess-1];
        } else {
            low = guess + 1;
            min = array[guess + 1];
        }
    }
}

int main()
{
  int ar[5]={1,1,1,1,1};
  return interpolationSearch(1, ar, 5);
}  

