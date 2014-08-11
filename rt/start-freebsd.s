.data
/* std._environment : byte[:][:] */
.globl std$_environment
std$_environment:
.envbase:
.quad 0 /* env size */
.envlen:
.quad 0 /* env ptr */

.globl std$__cenvp
std$__cenvp:
.quad 0

.text
/*
 * The entry point for the whole program.
 * This is called by the OS. In order, it:
 *  - Sets up all argc entries as slices
 *  - Sets up all envp entries as slices
 *  - Converts argc/argv to a slice
 *  - Stashes envp in std._environment
 *  - Stashes a raw envp copy in __cenvp (for syscalls to use)
 *  - Calls main()
 */
.globl _start
_start:
	/* stack allocate sizeof(byte[:])*(argc + len(envp)) */
	movq	(%rdi),%rax
	leaq	16(%rdi,%rax,8), %rbx	/* argp = argv + 8*argc + 8 */
        call    count
	addq	%r9,%rax
	imulq	$16,%rax
	subq	%rax,%rsp
	movq	%rsp, %rdx	/* saved args[:] */

	/* convert envp to byte[:][:] for std._environment */
	movq	(%rdi),%rax
	leaq	16(%rdi,%rax,8), %rbx	/* envp = argv + 8*argc + 8 */
        /* store envp for some syscalls to use without spurious conversion. */
        movq    %rbx,std$__cenvp(%rip)
	movq	%r9,%rax
	movq	%rsp, %rcx
	movq	%r9,.envlen
	movq	%rdx,.envbase
	call cvt
	movq	%rcx,%rdx

        /* convert argc, argv to byte[:][:] for args. */
	movq	(%rdi), %rax	/* argc */
	leaq	8(%rdi), %rbx	/* argv */
	movq	(%rdi), %rsi	/* saved argc */
        call    cvt
	pushq   %rsi
	pushq   %rdx

	/* enter the main program */
	call	main
	/* exit(0) */
        xorq	%rdi,%rdi
	movq	$1,%rax
	syscall

