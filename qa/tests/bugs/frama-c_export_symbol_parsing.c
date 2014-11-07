#define __used			__attribute__((__used__))

#define __VMLINUX_SYMBOL(x) _##x
#define __VMLINUX_SYMBOL_STR(x) "_" #x

/* Indirect, so macros are expanded before pasting. */
#define VMLINUX_SYMBOL(x) __VMLINUX_SYMBOL(x)
#define VMLINUX_SYMBOL_STR(x) __VMLINUX_SYMBOL_STR(x)

struct kernel_symbol
{
	unsigned long value;
	const char *name;
};

#define __CRC_SYMBOL(sym, sec)					\
	extern void *__crc_##sym __attribute__((weak));		\
	static const unsigned long __kcrctab_##sym		\
	__used							\
	__attribute__((section("___kcrctab" sec "+" #sym), unused))	\
	= (unsigned long) &__crc_##sym;

/* For every exported symbol, place a struct in the __ksymtab section */
#define __EXPORT_SYMBOL(sym, sec)				\
	extern typeof(sym) sym;					\
	__CRC_SYMBOL(sym, sec)					\
	static const char __kstrtab_##sym[]			\
	__attribute__((section("__ksymtab_strings"), aligned(1))) \
	= VMLINUX_SYMBOL_STR(sym);				\
	static const struct kernel_symbol __ksymtab_##sym	\
	__used							\
	__attribute__((section("___ksymtab" sec "+" #sym), unused))	\
	= { (unsigned long)&sym, __kstrtab_##sym }

#define EXPORT_SYMBOL(sym)					\
	__EXPORT_SYMBOL(sym, "")

#define EXPORT_SYMBOL_GPL(sym)					\
	__EXPORT_SYMBOL(sym, "_gpl")


int test(void)
{
	return 0;
}
EXPORT_SYMBOL(test);

