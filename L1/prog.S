	.text
	.globl go
go:
	pushq %rbx
	pushq %rbp
	pushq %r12
	pushq %r13
	pushq %r14
	pushq %r15

	call _main


	popq %r15
	popq %r14
	popq %r13
	popq %r12
	popq %rbp
	popq %rbx

	retq
_main:
	subq $0, %rsp
_entry:
	movq $1, %rdx
	imulq $8, %rdx
	movq %rdx, %r8
	addq $16, %r8
	movq 0(%rcx), %rdx
	movq %rdx, %rcx
	addq %r8, %rcx
	addq $0, %rsp
	retq
