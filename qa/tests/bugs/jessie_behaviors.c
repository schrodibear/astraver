typedef int Elem;

#define SIZE 5
Elem queue[SIZE];

typedef int RC;

size_t first = 0;
size_t length = 0;

/*@
    global invariant queue_memory_validness:
        \valid(queue + (0 .. SIZE - 1));
 */

/*@
    global invariant first_index_bound:
        0 <= first < SIZE;
 */

/*@
    global invariant length_bound:
        0 <= length <= SIZE;
 */

/*@
    predicate elements_preserved{LPre, LPost}(integer offset, integer len) =
        \forall integer i; 0 <= i < len ==>
            \at( queue[(first + i) % SIZE], LPost ) ==
            \at( queue[(first + offset + i) % SIZE], LPre );
 */

/*@
    assigns length, first, queue[0 .. SIZE - 1];

    allocates \nothing;
    frees \nothing;

    ensures elements_preserved{Pre, Post}(0, \old(length));

    behavior non_full:
      assumes length < SIZE;

      ensures \result == 0;
      ensures length == \old(length) + 1;

      ensures queue[\old(first + length) % SIZE] == e;

    behavior full:
      assumes length == SIZE;

      ensures \result == -1;
      ensures length == \old(length);

    disjoint behaviors;
    complete behaviors;
 */
RC my_add (Elem e) {
    if (length == SIZE) {
        return -1;
    }
    queue[(first + length) % SIZE] = e;
    length++;
    return 0;
}

/*@
    assigns length, first, queue[0 .. SIZE - 1], *e;

    allocates \nothing;
    frees \nothing;

    behavior non_empty:
      assumes length > 0;

      requires \valid(e);

      ensures \result == 0;
      ensures length == \old(length) - 1;

      ensures *e == \old(queue[first]);

      ensures elements_preserved{Pre, Post}(1, length);

    behavior empty:
      assumes length == 0;

      ensures \result == -1;
      ensures length == \old(length);

      ensures elements_preserved{Pre, Post}(0, length);

    complete behaviors;
    disjoint behaviors;
 */
RC my_remove (Elem *e) {
    if (length == 0) {
        return -1;
    }
    *e = queue[first];
    first = ++first % SIZE;
    length--;
    return 0;
}

/*@
    predicate elem_in_queue{L}(Elem e) =
        \exists integer i; 0 <= i < length && queue[(first + i) % SIZE] == e;
 */

/*@
    assigns first, queue[0 .. SIZE - 1];
    allocates \nothing;
    frees \nothing;

    ensures elements_preserved{Pre, Post}(0, length);

    ensures \result <==> elem_in_queue{Pre}(e);
 */
RC exists (Elem e) {
    size_t i = first;
    int count;
    if (length == 0) {
        return 0;       // false
    }
    /*@
        loop invariant 0 <= count <= length;
        loop invariant i == (first + count) % SIZE;

        loop invariant \forall integer j; 0 <= j < count ==> queue[(first + j) % SIZE] != e;

        loop variant length - count;
     */
    for (count=0; (count<length); ++count) {
        if (queue[i] == e) {
            return 1;   // true
        } // end if
        i = (i + 1) % SIZE;
    } // end for
    return 0;

}

/*@
    assigns first, queue[0 .. SIZE - 1];
    allocates \nothing;
    frees \nothing;

    ensures elements_preserved{Pre, Post}(0, length);

    behavior in_queue:
        assumes elem_in_queue(e) && length < SIZE;
        ensures \result == 0;

    behavior not_in_queue:
        assumes !elem_in_queue(e) && length == SIZE;
        ensures \result == -1;

    disjoint behaviors;
 */
RC ready (Elem e) {
    if ((length == SIZE) && !(exists (e))) {
        return -1;
    }
    return 0;
}

int main () {
    return 0;
}
