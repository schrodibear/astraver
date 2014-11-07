typedef unsigned int uint32_t;
typedef unsigned char uint8_t;
typedef unsigned long long uint64_t;

typedef uint32_t ignoremask_t;

typedef struct __mac_t {
        uint8_t         level;
        uint64_t        category;
} _mac_t; // for subjects

typedef struct _mac_label {
        ignoremask_t    type;
        _mac_t    mac;
} _mac_label_t; // for objects


#define MAC_ATTR_IGNORE_LVL    0x08
#define MAC_ATTR_IGNORE_CAT    0x01

/*@
        axiomatic Y {
	  logic boolean check_category(_mac_t *s, _mac_t *m); 
	  logic boolean check_level(_mac_t *s, _mac_t *m); 
	}
	
	predicate is_readable(_mac_t *s, _mac_label_t *o) =
        	((o->type & MAC_ATTR_IGNORE_LVL) || check_level(s, &o->mac)) &&
	        ((o->type & MAC_ATTR_IGNORE_CAT) || check_category(s, &o->mac));
 */

void f(_mac_t *s, _mac_label_t *o) {
  //@ assert is_readable(s, o);
}
  
