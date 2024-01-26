
uppercase.bin:     file format elf32-littleriscv


Disassembly of section .text:

00010074 <_start>:
   10074:	ffff2517          	auipc	a0,0xffff2
   10078:	f8c50513          	addi	a0,a0,-116 # 2000 <__DATA_BEGIN__>

0001007c <begin_uppercase_loop>:
   1007c:	00050083          	lb	ra,0(a0)
   10080:	02008263          	beqz	ra,100a4 <end_program>
   10084:	06100113          	li	sp,97
   10088:	0020ea63          	bltu	ra,sp,1009c <already_uppercase>
   1008c:	07a00113          	li	sp,122
   10090:	00116663          	bltu	sp,ra,1009c <already_uppercase>
   10094:	fe008093          	addi	ra,ra,-32
   10098:	00150023          	sb	ra,0(a0)

0001009c <already_uppercase>:
   1009c:	00150513          	addi	a0,a0,1
   100a0:	fddff06f          	j	1007c <begin_uppercase_loop>

000100a4 <end_program>:
   100a4:	0000006f          	j	100a4 <end_program>
