#include <inttypes.h>
#include <sys/types.h>

extern void main(void);

ssize_t write(int fd, const void *buf, size_t size) {
    register int64_t rax __asm__ ("rax") = 1;
    register int rdi __asm__ ("rdi") = fd;
    register const void *rsi __asm__ ("rsi") = buf;
    register size_t rdx __asm__ ("rdx") = size;
    __asm__ __volatile__ (
        "syscall"
        : "+r" (rax)
        : "r" (rdi), "r" (rsi), "r" (rdx)
        : "rcx", "r11", "memory"
    );
    return rax;
}

extern void putint(unsigned long long d) {
  char buf[21] = {};
  char* cur = &buf[20];

  *cur = '\n';
  size_t len = 1;

  if (d == 0) {
    cur--;
    *cur = '0';
    len++;
  } else while (d > 0) {
    cur--;
    *cur = '0' + (d % 10);
    d /= 10;
    len++;
  }

  write(0, cur, len);
}

// Tell the compiler incoming stack alignment is not RSP%16==8 or ESP%16==12
__attribute__((force_align_arg_pointer))
extern void _start(void) {
    main();

    /* exit system call */
    asm("movl $1,%eax;"
        "xorl %ebx,%ebx;"
        "int  $0x80"
    );
    __builtin_unreachable();  // tell the compiler to make sure side effects are done before the asm statement
}
