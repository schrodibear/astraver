typedef struct {
	int level;
	int category;
} parsec_mac_t;

/*@ requires \valid(tm);
    requires \valid(sm); //valid_read;
    assigns *tm \from *sm;
  */
void mac_cpy(parsec_mac_t *tm, const parsec_mac_t *sm)
{
	tm->level = sm->level;
	tm->category = sm->category;
}

