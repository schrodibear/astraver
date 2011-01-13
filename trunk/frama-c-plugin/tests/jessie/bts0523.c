
// uncomment to demonstrate crash:
#define loopAssignsStruct

typedef int timeT;
typedef int speedT;
typedef int bool;

#define true		((bool)1)
#define false		((bool)0)

#define endOfTime	0x000fffff



/*@ ensures *sp < \old(*sp);
    assigns \nothing;
    //assigns *sp;
*/
extern void doBrake(speedT *sp);



/*@ ensures \result == true || \result == false;
    assigns \nothing;
*/
extern bool boolSensorValue(void);


/*@ 
    requires \valid(emState);
    requires \valid(sp);
    assigns *emState;
    ensures emButton ==> *emState;
    ensures !emButton && *sp == 0 ==> !*emState;
*/
void handleEmergency(
    bool emButton,
    bool *emState,
    speedT *sp)
{
    if (emButton) {
	*emState = true;
    } else if (*sp == 0) {
	*emState = false;
    }
    if (*emState)
	doBrake(sp);
}


struct _state {
    speedT speed;
    bool emState;
    bool emButton;
};

struct _state hist[endOfTime];

/*@ ensures \forall timeT t1; hist[t1].emButton
	==> \exists timeT t2; t2 >= t1 && hist[t2].speed == 0;
*/
void main(void)
{
    timeT t;
    speedT speed;
    bool emState;
    bool emButton;

    emState = false;
#ifdef loopAssignsStruct
    /*@ loop invariant 0 <= t <= endOfTime;
	loop invariant emButton ==> emState;
	loop assigns emButton,emState,speed,hist[t];
        loop variant endOfTime - t;
    */
#else
    /*@ loop invariant 0 <= t <= endOfTime;
	loop invariant emButton ==> emState;
	loop assigns emButton,emState,speed,
	     hist[t].speed,hist[t].emState,hist[t].emButton;
        loop variant endOfTime - t;
    */
#endif
    for (t=0; t<endOfTime; ++t) {
	emButton = boolSensorValue();
	handleEmergency(emButton,&emState,&speed);
	hist[t].speed = speed;
	hist[t].emState = emState;
	hist[t].emButton = emButton;
    }
}

