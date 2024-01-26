        .section .data
input_string:   .asciz "waSSup LabsS123987@jdKWs"

        # tohost/fromhost are data locations used by Spike
        .align 8
tohost: .byte 0
        .align 8
fromhost: .byte 0
        
        .section .text
        .globl _start
_start:
        # Load the address of the input string into a0
        la a0, input_string
        
        # Load value of the first letter into x1
        begin_uppercase_loop:
        lb x1, 0(a0) 

        # Check if at end of memory
        beq x1, zero, end_program

        # Check conditional if already uppercased
        # If letter < 97 or > 122, then skip
        addi x2, x0, 97
        bltu x1, x2, already_uppercase
        addi x2, x0, 122
        bltu x2, x1, already_uppercase

        addi x1, x1, -32 # Conversion from lower to uppercase ASCII
        sb x1, 0(a0) # Store x1 (new LETTER) into a0

        already_uppercase:

        # Increment to the next letter in memory
        addi a0, a0, 1

        # Go to the top of the loop
        j begin_uppercase_loop
end_program:
        # jump here when you're done
        j end_program

