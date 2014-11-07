#include "kernel.h"
#include "extern.h"
#include "module.h"


//@ ghost struct dentry *d;
/*@ requires \valid(i);
    assigns \nothing;
    ensures \result == \null || \result == d;
 */
extern struct dentry *d_find_alias(struct inode *i);

/*@ requires \valid(dentry) || dentry == \null;
    behavior DENTRY_EQ_NULL:
        assumes dentry == \null;
        assigns \nothing;
    behavior DENTRY_NE_NULL:
        assumes dentry != \null;
        assigns dentry->d_lockref.count;
        ensures dentry->d_lockref.count == \old(dentry->d_lockref.count) + 1;
    complete behaviors;
    disjoint behaviors;
 */
extern /*static inline*/ struct dentry *dget(struct dentry *dentry) ;

/*@ requires \valid(dentry) || dentry == \null;
    behavior DENTRY_EQ_NULL:
        assumes dentry == \null;
        assigns \nothing;
    behavior DENTRY_NE_NULL:
        assumes dentry != \null;
        assigns dentry->d_lockref.count;
        ensures dentry == \null || dentry == \old(dentry);
        ensures dentry == \old(dentry) ==> dentry->d_lockref.count == \old(dentry->d_lockref.count) - 1;
    complete behaviors;
    disjoint behaviors;
 */
extern void dput(struct dentry *dentry);


//------------------------------------------------------------------------------

	#define T(fmt,arg...) do{ }while(0)


//------------------------------------------------------------------------------

/*
 */
ssize_t getxattr_spec(struct dentry *, const char *, void *, size_t);

//@ ghost enum {FAILURE, SUCCESS} outcome_i_getxattr;
/*@ requires \valid(i);
    requires \valid(name);
    requires d == \null || \valid(d);

    behavior RET_EQ_ENOSYS:
        assumes i->i_op == \null || i->i_op->getxattr == \null;
        assigns \nothing;
        ensures \result == -ENOSYS;
    behavior RET_EQ_ENOMEM:
        assumes \valid(i->i_op) && \valid(i->i_op->getxattr);
        //assigns ;
        ensures \result == -ENOSYS;
   complete behaviors;
   disjoint behaviors;
 */
static int i_getxattr(struct dentry *d, struct inode *i, const char *name, void **val, int f)
{
    int rc;
    struct dentry *fake_d;

    T("Enter name(%s)",name);

    if( (!i->i_op) || (!i->i_op->getxattr) ) { return -ENOSYS; }

    fake_d=d?dget(d):d_find_alias(i);

    if(unlikely(!fake_d))
    {
        T("Can't find dentry alias");
        rc=-ENOSYS;/// other code
        goto dput_fake_d;
    }

    //rc=i->i_op->getxattr(fake_d,name,NULL,0);
    T("getxattr returned rc=%d",rc);

    if(rc<=0) goto dput_fake_d;

    *val=kmalloc(rc,GFP_KERNEL);
    if(!*val){ /*@ ghost outcome_i_getxattr = FAILURE;*/ T("return ENOMEM"); rc=-ENOMEM; goto dput_fake_d; }
    //@ ghost outcome_i_getxattr = SUCCESS;

    //rc=i->i_op->getxattr(fake_d,name,*val,rc);
    T("getxattr: name(%s),size(NULL),filename(%pd),ino(%lu) returned rc=%d",name,d,i->i_ino,rc);

dput_fake_d:
    dput(fake_d);
    return rc;
}

