//@ assigns \nothing;
void f1() {};

//@ assigns \nothing;
void f2(void) {};

/*@ requires arg > 0;
  @ assigns \nothing;
 */
void f3(int arg) {};

/*@ requires arg < 0;
  @ assigns \nothing;
 */
void f33(int arg) {};

// Auto-conversions *f <--> f <--> &f aren't currently supported in annotations (by Frama-C frontend)
/*@ requires f == &f3 || f == &f33;
  @ ensures \result == 0;
 */
extern int f4(void (*f) (int));

/*@ axiomatic function_address_inequality {
  @     logic boolean always_true{L} = \true;
  @     axiom diff_f3_f33: f3 != f33 && always_true;
  @ }
*/
// (void (*) ()) and (void (*) (void)) are regarded as different types in annotations (by the Frama-C frontend)
// But the types are compatible in code
/*@ requires (f == (void (*) ())&f1 || f == (void (*) ())&f2) && (g == &f1 || g == &f2);
  @ ensures \result == &f3 && \old(n) > 0 || \result == &f33 && \old(n) <= 0;
 */
void (*f5(void (*f) (), void (*g) (void), int n/*, ...*/)) (int)
{
  f();
  g();
  if (n > 0) {
    return *f3;
  } else {
    return f33;
  }
}

struct fps {
    int member;
    void (*f)();
    void (*g)(void);
    int (*h) (void (*) (int));
    void (* (*k) (void (*) (), void (*) (void), int/*, ...*/)) (int);
    int l[];
} fps, *pfps, afps[5];

void (*gs[5])(void);

typedef unsigned long size_t;

extern void *malloc(const size_t size);

//@ ensures \result == 0;
int main(int argc, char **argv)
{
    int result = 0;
    gs[4] = f1;
    fps.f = f2;
    fps.g = **f1;
    fps.f = f1;
    fps.g = **f2;
    fps.h = *f4;
    
    fps.k = &f5;
    fps.k = *&f5;
    fps.k = &*f5;
    fps.k = **f5;
    fps.k = **********************f5;
    fps.k = &*&*&*&*&*&*f5;
    fps.k = &******&f5;
    // Surprisingly, this "&&" does work in Frama-C as well (!),
    // being treated as "(void (*(*)(void (*)(), void (*)(void), int ))(int ))((void *)0)".
    // Meanwhile in GCC && means takng address of a local label...
    
    //fps.k = &&f5;
        
    pfps = malloc((sizeof(struct fps) + sizeof(int) * 4) * 5);
    pfps[0] = fps;
    pfps[4] = fps;
    pfps[0].f(); // f1
    result += pfps[4].h(&f33); // f4
    pfps[4].h(f3); //f4
    afps[4] = fps;
    afps[0] = *pfps;
    (*afps[4].k((&afps[0])->f, afps[4].g, 1))(result + 1); // f5(f1, f2) --> f3(1)
    afps[4].k(fps.g, fps.f, -1)(pfps->h(f33) - 1); // f5(f2, f1) --> f33(f4(f33) /*== 0*/ - 1)
    //@ assert result == 0;
    gs[4]();
    if (pfps[0].g == f2) {
      return result;
    } else {
      return -1;
    }
}