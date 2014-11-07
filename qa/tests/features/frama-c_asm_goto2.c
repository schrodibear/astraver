typedef _Bool bool;
typedef unsigned short u16;
typedef unsigned char u8;

#define true 1
#define false 0

u16 X86_FEATURE_ALWAYS;

#define CC_HAVE_ASM_GOTO
#define CONFIG_X86_DEBUG_STATIC_CPU_HAS

static __attribute__((__always_inline, __pure)) bool __static_cpu_has(u16 bit)
 {
 #ifdef CC_HAVE_ASM_GOTO
 
 #ifdef CONFIG_X86_DEBUG_STATIC_CPU_HAS
 
                 /*
                  * Catch too early usage of this before alternatives
                  * have run.
                  */
                 asm volatile goto("1: jmp %l[t_warn]\n"
                          "2:\n"
                          ".section .altinstructions,\"a\"\n"
                          " .long 1b - .\n"
                          " .long 0\n"           /* no replacement */
                          " .word %P0\n"         /* 1: do replace */
                          " .byte 2b - 1b\n"     /* source len */
                          " .byte 0\n"           /* replacement len */
                          ".previous\n"
                          /* skipping size check since replacement size = 0 */
                          : : "m" (X86_FEATURE_ALWAYS) : : t_warn);
 
 #endif
 
                 asm volatile goto("1: jmp %l[t_no]\n"
                          "2:\n"
                          ".section .altinstructions,\"a\"\n"
                          " .long 1b - .\n"
                          " .long 0\n"           /* no replacement */
                          " .word %P0\n"         /* feature bit */
                          " .byte 2b - 1b\n"     /* source len */
                          " .byte 0\n"           /* replacement len */
                          ".previous\n"
                          /* skipping size check since replacement size = 0 */
                          : : "i" (bit) : : t_no);
                 return true;
         t_no:
                 return false;
 
 #ifdef CONFIG_X86_DEBUG_STATIC_CPU_HAS
         t_warn:
                 warn_pre_alternatives();
                 return false;
 #endif
 
 #else /* CC_HAVE_ASM_GOTO */
 
                 u8 flag;
                 /* Open-coded due to __stringify() in ALTERNATIVE() */
                 asm volatile("1: movb $0,%0\n"
                              "2:\n"
                              ".section .altinstructions,\"a\"\n"
                              " .long 1b - .\n"
                              " .long 3f - .\n"
                              " .word %P1\n"             /* feature bit */
                              " .byte 2b - 1b\n"         /* source len */
                              " .byte 4f - 3f\n"         /* replacement len */
                              ".previous\n"
                              ".section .discard,\"aw\",@progbits\n"
                              " .byte 0xff + (4f-3f) - (2b-1b)\n" /* size check */
                              ".previous\n"
                              ".section .altinstr_replacement,\"ax\"\n"
                              "3: movb $1,%0\n"
                              "4:\n"
                              ".previous\n"
                              : "=m" (flag) : "m" (bit));
                 return flag;
 
 #endif /* CC_HAVE_ASM_GOTO */
 }


 //@ assigns \nothing;
 int main() {
   bool b = __static_cpu_has(1);
   return b ? 1 : 0;
 }
