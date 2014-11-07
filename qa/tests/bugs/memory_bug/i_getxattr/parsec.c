#include "kernel.h"
#include "extern.h"
#include "module.h"
#include "spec_lib.h"

/*@ axiomatic inode_dentry {
    logic struct dentry * d_find_alias{L}(struct inode *i);

    axiom bind{L}:
       \forall struct inode *i;
          \valid(i) &&
             \let d =  d_find_alias{L}(i);
                \valid(d) ==> d->d_inode == i;

    }
 */

//@ predicate d_inc{L1,L2}(struct dentry *d) = \at(d->d_lockref.count, L1) + 1 == \at(d->d_lockref.count, L2);
//@ predicate d_dec{L1,L2}(struct dentry *d) = \at(d->d_lockref.count, L1) - 1 == \at(d->d_lockref.count, L2);

// ghost struct dentry *ghost_d;
// logic struct dentry * d_find_alias{L}(struct inode *i) = ghost_d;

/*@ requires \valid(i);
    assigns d_find_alias(\at(i, Pre))->d_lockref.count;
    ensures d_inc{Pre, Post}(d_find_alias{Pre}(\at(i, Pre)));
    ensures \result == d_find_alias{Pre}(\at(i, Pre)) && \valid(\result) && \result->d_inode == i || \result == \null;
 */
extern struct dentry *d_find_alias(struct inode *i);


/*@ requires \valid(dentry) || dentry == \null;
    ensures \result == dentry;

    behavior DENTRY_EQ_NULL:
        assumes dentry == \null;
        assigns \nothing;
    behavior DENTRY_NE_NULL:
        assumes dentry != \null;
        assigns dentry->d_lockref.count;
        ensures d_inc{Pre, Post}(dentry);
    complete behaviors;
    disjoint behaviors;
 */
extern /*static inline*/ struct dentry *dget(struct dentry *dentry);

/*@ requires \valid(dentry) || dentry == \null;
    behavior DENTRY_EQ_NULL:
        assumes dentry == \null;
        assigns \nothing;
    behavior DENTRY_NE_NULL:
        assumes dentry != \null;
        assigns dentry->d_lockref.count;
        ensures dentry == \null || dentry == \old(dentry);
        ensures dentry == \old(dentry) ==> d_dec{Pre, Post}(dentry);
    complete behaviors;
    disjoint behaviors;
 */
extern void dput(struct dentry *dentry);


//------------------------------------------------------------------------------

	#define T(fmt,arg...) do{ }while(0)


//------------------------------------------------------------------------------

/*@ requires valid_string(name);
    requires \valid(d);
    requires \valid(d->d_inode);
 */
ssize_t getxattr_spec(struct dentry *d, const char *name, void *value, size_t size);

//@ ghost enum {FAILURE, SUCCESS} outcome_i_getxattr;
//@ ghost struct dentry *_fake_d = 0;
/*@ requires \valid(i);
    requires \valid(name);
    requires d == \null || \valid(d);
    requires \valid(i->i_op) ==> i->i_op->getxattr == &getxattr_spec;

    behavior RET_EQ_ENOSYS:
        assumes i->i_op == \null || i->i_op->getxattr == \null;
        assigns \nothing;
        ensures \result == -ENOSYS;
    behavior RET_EQ_ENOMSG:
        assumes d == \null;
        assumes d_find_alias(i) == \null;
        assigns \nothing;
        ensures \result == -ENOMSG;
    behavior RET_EQ_ENOMEM:
        assumes \valid(d) || \valid(d_find_alias(i));
        assumes \valid(i->i_op) && i->i_op->getxattr == &getxattr_spec;
        assumes outcome_i_getxattr == FAILURE;
        assigns \nothing;
        ensures \let d = d_find_alias(i); d->d_lockref.count == \old(d->d_lockref.count);
        ensures d_find_alias(i) == _fake_d;
        ensures \result == -ENOMEM;
 */
int i_getxattr(struct dentry *d, struct inode *i, const char *name, void **val, int f)
{
    int rc;
    struct dentry *fake_d;

    T("Enter name(%s)",name);

    if( (!i->i_op) || (!i->i_op->getxattr) ) { return -ENOSYS; }

    fake_d=d?dget(d):d_find_alias(i);
    //@ ghost  _fake_d = fake_d;
    //@ assert d == \null ==> fake_d == d_find_alias(i);

    if(unlikely(!fake_d))
    {
        D("Can't find dentry alias - return -ENOSYS, attr name(%s),filename(%pd),ino(%lu)",name,d,i->i_ino);
        dump_stack();
        return -ENOMSG;
    }

    rc=i->i_op->getxattr(fake_d,name,NULL,0);
    T("getxattr returned rc=%d",rc);

    if(rc<=0) goto dput_fake_d;

    *val=kmalloc(rc,GFP_KERNEL);
    if(!*val){ /*@ ghost outcome_i_getxattr = FAILURE; */ T("return ENOMEM"); rc=-ENOMEM; goto dput_fake_d; }
    //@ ghost outcome_i_getxattr = SUCCESS;

    rc=i->i_op->getxattr(fake_d,name,*val,rc);
    T("getxattr: name(%s),size(NULL),filename(%pd),ino(%lu) returned rc=%d",name,d,i->i_ino,rc);

dput_fake_d:
    dput(fake_d);
    return rc;
}


