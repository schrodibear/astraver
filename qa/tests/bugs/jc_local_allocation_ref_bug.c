#include <stdlib.h>
#include <limits.h>

struct ports_t {
    int *states;
    int count;
    int max_state;
};

/*@ predicate valid_ports(struct ports_t *ports) =
        \valid(ports) &&
        (0 <= ports->count <= ports->max_state/2) &&
        (ports->max_state % 2 == 0) &&
        \valid(ports->states + (0..ports->count-1)) &&
        (\forall integer i; 0 <= i < ports->count ==>
                -1 <= ports->states[i] < ports->count + ports->max_state/2) &&
        (\forall integer i; 0 <= i < ports->count ==>
                ports->states[i] >= ports->max_state/2 ==>
                    0 <= ports->states[ports->states[i] - ports->max_state/2]
                        < ports->max_state/2);
*/

struct ports_t *ports;

//@ global invariant ports_v: \valid(ports) && valid_ports(ports);

/*@ logic integer port_value{L}(integer port) =
        ports->states[port] >= ports->max_state/2
            ? ports->states[ports->states[port] - ports->max_state/2]
            : ports->states[port];
*/

/*@ assigns \nothing;
    ensures \result <==> \exists integer port;
                                0 <= port < ports->count &&
                                x == port_value(port); */
int has_value(int x) {
    int *v = malloc(sizeof(*v) * ports->count);
    /*@ loop invariant 0 <= i <= ports->count;
        loop invariant \forall integer k; 0 <= k < i ==> v[k] != x;
        loop assigns v[i];
        loop variant ports->count - i; */
    for(int i = 0; i < ports->count; i++) {
        if (v[i] == x) {
            return 1;
        }
    }
    return 0;
}

