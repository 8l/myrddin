.globl std$syscall
std$syscall:
	pushl %ebp
	movl %esp,%ebp
	movl 12(%ebp),%eax #count
        shl  $2,%eax
	/*
	   hack: 6 args uses %ebp, so we index
	   relative to %esp.

           hack: We load 6 args regardless of
           how many we actually have. This may
           load junk values, but if the syscall
           doesn't use them, it's going to be
           harmless.
	 */
	movl 32(%esp),%ebp
	movl 28(%esp),%edi
	movl 24(%esp),%esi
	movl 20(%esp),%edx
	movl 16(%esp),%ecx
	movl 12(%esp),%ebx
	movl 8(%esp),%eax
        int $0x80
	movl %ebp,%esp
	popl %ebp
	ret

.globl _std$syscall
_std$syscall:
        popl %ecx	/* return address */
	popl %eax       /* call num */
	pushl %ecx
        int $0x80
	pushl %ecx	/* put the return address back */
	ret
