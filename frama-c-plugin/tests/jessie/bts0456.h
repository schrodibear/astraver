typedef value_type;

/*@
 axiomatic GoodNumberProcessor
 {
  logic integer bsp_p;
  axiom good_bsp_p: 0<bsp_p;
 }
*/

/*@
 ensures \result==bsp_p;
*/
int bsp_nprocs();

/*@
 ensures 0<=\result<bsp_p;
*/
int bsp_pid();

int bsp_l();

int bsp_g();

int bsp_r();

/*@
 assigns \nothing;
*/
void bsplib_init(int* argc, char*** argv);

void bsplib_done();

double bsp_time();

void bsp_sync();

/* void bsp_push_reg(void* ident, int size); */

/*@
 assigns \nothing;
*/
void bsp_push_reg(value_type* ident, int n);

/* void bsp_pop_reg(void* ident); */

/*@
 assigns \nothing;
*/
void bsp_pop_reg(value_type* ident);

/* void bsp_put(int destPID, void* src, void* dest, int offset, int nbytes); */
/*@
 assigns \nothing;
*/
void bsp_put(int destPID, value_type* src, value_type* dest, int offset, int nbytes);

/* void bsp_get(int srcPID, value_type* src, int offset, value_type* dest, int nbytes); */
/*@
 assigns \nothing;
*/
void bsp_get(int srcPID, value_type* src, int offset, void* dest, int nbytes);

/* void bsp_send(int dest, void* buffer, int size); */
/*@
 assigns \nothing;
*/
void bsp_send(int dest, value_type* buffer, int size);

/* void* bsp_getmsg(int proc_id, int index); */
/*@
 assigns \nothing;
*/
value_type *bsp_getmsg(int proc_id, int index);

/*@
 assigns \nothing;
*/
int bspmsg_size(int proc_id, int index);

/*@
 assigns \nothing;
*/
int bsp_nmsgs(int proc_id);
