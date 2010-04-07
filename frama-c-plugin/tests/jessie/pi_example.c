#pragma JessieFloatModel(full)

/*@
requires \is_finite(radius) && radius > 0 && radius <= 3;
ensures \is_finite(\result) && \abs(\result - 3.141592654*2.0*radius) <= 0.01;
*/
float Perimeter(float radius) {
    return 6.28f*radius;
}
