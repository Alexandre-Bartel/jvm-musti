; @Harness: disassembler
; @Result: PASS
  section .text  size=0x00000042 vma=0x00000000 lma=0x00000000 offset=0x00000034 ;2**0 
  section .data  size=0x00000000 vma=0x00000000 lma=0x00000000 offset=0x00000076 ;2**0 

start .text:

label 0x00000000  ".text":
      0x0: 0x05 0x90  lpm  r0,  Z+
      0x2: 0x15 0x90  lpm  r1,  Z+
      0x4: 0x25 0x90  lpm  r2,  Z+
      0x6: 0x35 0x90  lpm  r3,  Z+
      0x8: 0x45 0x90  lpm  r4,  Z+
      0xa: 0x55 0x90  lpm  r5,  Z+
      0xc: 0x65 0x90  lpm  r6,  Z+
      0xe: 0x75 0x90  lpm  r7,  Z+
     0x10: 0x85 0x90  lpm  r8,  Z+
     0x12: 0x95 0x90  lpm  r9,  Z+
     0x14: 0xa5 0x90  lpm  r10,  Z+
     0x16: 0xb5 0x90  lpm  r11,  Z+
     0x18: 0xc5 0x90  lpm  r12,  Z+
     0x1a: 0xd5 0x90  lpm  r13,  Z+
     0x1c: 0xe5 0x90  lpm  r14,  Z+
     0x1e: 0xf5 0x90  lpm  r15,  Z+
     0x20: 0x05 0x91  lpm  r16,  Z+
     0x22: 0x15 0x91  lpm  r17,  Z+
     0x24: 0x25 0x91  lpm  r18,  Z+
     0x26: 0x35 0x91  lpm  r19,  Z+
     0x28: 0x45 0x91  lpm  r20,  Z+
     0x2a: 0x55 0x91  lpm  r21,  Z+
     0x2c: 0x65 0x91  lpm  r22,  Z+
     0x2e: 0x75 0x91  lpm  r23,  Z+
     0x30: 0x85 0x91  lpm  r24,  Z+
     0x32: 0x95 0x91  lpm  r25,  Z+
     0x34: 0xa5 0x91  lpm  r26,  Z+
     0x36: 0xb5 0x91  lpm  r27,  Z+
     0x38: 0xc5 0x91  lpm  r28,  Z+
     0x3a: 0xd5 0x91  lpm  r29,  Z+
     0x3c: 0xe5 0x91  lpm  r30,  Z+  ;  undefined
     0x3e: 0xf5 0x91  lpm  r31,  Z+  ;  undefined
     0x40: 0x05 0x90  lpm  r0,  Z+

start .data:

