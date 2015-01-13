typedef struct {
	int a;
} parsec_sb_security_t;

struct super_block {
	void *s_security;
};


/*@	requires \valid(sb);
  	requires \typeof(sb->s_security) <: \type(parsec_sb_security_t *);
	assigns \nothing;
	ensures \result == (parsec_sb_security_t *) sb->s_security;
*/
extern inline parsec_sb_security_t* SB_SEC(const struct super_block* sb) { return (parsec_sb_security_t*)(sb->s_security); }

struct inode {
	void *i_security;
};

typedef struct {
	int a;
} parsec_inode_security_t;

/*@	requires \valid(i);
  	requires \typeof(i->i_security) <: \type(parsec_inode_security_t *);
	assigns \nothing;
	ensures \result == (parsec_inode_security_t *) i->i_security;
*/
extern inline parsec_inode_security_t* INODE_SEC(const struct inode* i) { return (parsec_inode_security_t*)(i->i_security); }

