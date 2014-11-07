typedef int gifconf_func_t(struct net_device * dev, char * bufptr, int len);

int gifconf_func(struct net_device * dev, char * bufptr, int len)
{
}

extern int register_gifconf(unsigned int family, gifconf_func_t * gifconf);

int main()
{
  register_gifconf(0, gifconf_func);
}