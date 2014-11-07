
struct inode;

struct dentry {
   struct {
      int count;
   } d_lockref;

   struct inode *d_inode;
};

struct inode {
   int test;
};

/*@ axiomatic inode_dentry {
    logic struct dentry * d_find_alias{L}(struct inode *i);

    axiom bind{L}:
       \forall struct inode *i;
          \valid(i) &&
             \let d =  d_find_alias{L}(i);
                \valid(d) ==> d->d_inode == i;

    }
 */

/*@ requires \valid(i);
    assigns  d_find_alias{Pre}(\at(i, Pre))->d_lockref.count;
    ensures \let d = d_find_alias{Pre}(\at(i, Pre)); d->d_lockref.count == \old(d->d_lockref.count) + 1;
    ensures \result == d_find_alias{Pre}(\at(i, Pre));
 */
extern struct dentry *d_find_alias(struct inode *i);

