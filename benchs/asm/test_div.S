.text
.globl _start
_start:
li  a1, 11;
li  a2, 12;
li  a3, 13;
li  a4, 14;
li  a5, 15;

mul	a5,a2,a5
mul	a3,a1,a3
div	s1,a1,a2
div	s3,a4,a1
divu	s2,a5,a3

1: j 1b