(* Includes all example programs for the different semantics as well as 
an initial state*)


From spec Require Import notations.
Require Import String.
(* Note that because of limitation of this Poc code, we need to jump to bottom at the end of 
the program to correctly terminate a program
Furthermore the sp register grows upwards instead of downwards
*)

(* Example of Spectector. First instruction not here because there boolean comparisons right now
Furthermore, we need to set real values in the config if we want to  execute the program *)
(* 
r 0 = x
r 1 = y
r 2= z
r 3 = A
r 4 = w
r 5 = B
r 6 = temp
*)
(* Example from spectector*)
Definition x := r 0.
Definition y := r 1.
Definition z := r 2.
Definition val_B := r 3.
Definition val_A := r 4.
Definition B := r 5.
Definition A := r 6.
Definition temp := r 7.

Definition prog_b := 
    {{
        0 : ( skip ) ;
        1 : ( beqz y, ⊥  );
        2 : ( load val_A , < A + y > ) ;
        3 : (x <- < val_A >);
        4 : (z <- < x *  512 > );
        5 : (load val_B, < B + z > );
        5 : (temp <- < temp + (r 4) > );
        6:  (jmp ⊥) (* Used to set the PC to bottom.*)
    }}.

Definition public := r 59.
Definition secret := r 58.
Definition p := 0.

Definition prog_s := 
    {{
        0 : (store secret, < p >);
        1 : (store public, < p > );
        2 : (load z, < p >); 
        3 : (z <- < z * 512 > );
        4 : (load val_B, < B + z >);
        5 : (temp <- < temp + val_B > );
        6 : (jmp ⊥)
    }}.


Definition eax := r 8.

Definition edi := r 9.
Definition prog_r := {{
    0 : ( sp <- < sp - 4 > ); (* Manip_stack address*)
    1 : ( ret );
    2 : ( call "Manip_Stack" ); (* Speculate address*)
    3 : ( load eax, < secret > );
    4 : ( load edi, < eax > );
    5 : ( spbarr ); (* Makes the trace nicer becasue ret in ln6. returns to 0 which resulst in a loop that clutters the trace*)
    6 : ( ret );
    7 : ( call "Speculate" ); (* Main address *)
    8 : (jmp ⊥)
}}.


Definition prog_sr := 
    {{
    0 : ( sp <- < sp - 4 > ); (* Manip_stack address*)
    1 : ( ret );
    2 : ( call "Manip_Stack" ); (* Speculate address*)
    3 : (store secret, < p >); (* Main address *)
    4 : (store public, < p > );
    5 : ( load eax, < p > );
    6 : ( load edi, < eax > );
    (* 7 : (spbarr);  Leaving out the spbarr to show effect of it in trace *)
    7 : ( ret );
    8 : ( call "Speculate" ); 
    9 : (jmp ⊥)
}}.


Definition prog_bs := 
    {{
        0 : (x <- <0 >);
        1 : (store secret, < p >);
        2 : (store public, < p > );
        3 : (beqz x, ⊥  );
        4 : (load z, < p >); 
        5 : (load val_A, < A + z> );
        6 : (temp <- < temp + val_A > );
        7 :  (jmp ⊥)
    }}.


Definition prog_br := 
{{
    0 : ( sp <- < sp - 4 > ); (* Manip_stack address*)
    1 : ( ret );
    2 : ( call "Manip_Stack" ); (* Speculate address*)
    3 : ( x <- < 0 > );
    4 : (beqz x, 7);
    5 : ( load eax, < secret > );
    6 : ( load edi, < eax > );
    7 : (spbarr);
    8 : ( ret );
    9 : ( call "Speculate" ); (* Main address *)
    10 : (jmp ⊥)
}}.

Definition prog_bsr := 
{{
    0 : ( sp <- < sp - 4 > ); (* Manip_stack address*)
    1 : ( ret );
    2 : ( call "Manip_Stack" ); (* Speculate address*)
    3 : ( x <- < 0 > );
    4 : (beqz x, 7);
    5 : ( load eax, < p > );
    6 : ( load edi, < eax > );
    7 : ( spbarr ); (* Here to make trace more readable*)
    8 : ( ret );
    9 : (store secret, < p >); (* Main address *)
    10 : (spbarr);
    11 : (store public, < p > );
    12 : ( call "Speculate" );
    13 : (jmp ⊥)
}}.