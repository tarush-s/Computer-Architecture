        .section .data
input_string:   .asciz "Hello world!"

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

        # Your code here!
        loop: 
                #code for inverting lower case to upper case characters 
                
                lb a1, 0(a0) #load byte from string  
                beq a1, 0, end_program  #check for terminating null character
                blt a1, 97, goto  #already an upper case character
                bgt a1, 122, goto # not a character 
                sub a1, a1, 32 #convert t0 uppercase 
                sb a1, 0(a0)

                goto: addi a0, a0, 1
                j loop

end_program:
        # jump here when you're done
        j end_program

