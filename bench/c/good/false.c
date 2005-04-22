
/* these programs _are_ incorrect
   they are here to test the consistence of the theory */

int x[4];
int y[5];

/*@ ensures \false */
void false1() {
  x[-1] = 1;
  y[5] = 2;
}
