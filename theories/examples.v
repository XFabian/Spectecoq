
From spec Require Import Maps.
From spec Require Import Lang.
From spec Require Import programs.
From spec Require Import semantics.
Require Import List.
Require Import String.
Import ListNotations.



(* Initial Memory should be bottom t_empty ⊥. Jumps to other locations not in the program 
and are not bottom are not correctly handled. But it works for bottom
*)
(*|
================
Simple Examples
================

Here, we include the examples for each of the speculative semanitcs: for branch instructions,
for store instructions and for return instructions.
|*)
Definition init_state (st : state): SState :=
     [ {|
    State := st;
    Ctr := 0;
    RhoStack := [];
    Rsb := [];
    Id := none;
    Window := ⊥  (* Should be bottom but window is a nat right now* Since it is 0 riht now *)
    |} ].

(* sp needs to be set to somethign that has to be high, since memory written with sp can be overwritten*)
Definition exampl_b := {|Program := prog_b;
Config := {|Pc := 0;
            Mem := 1000 !-> 53; N 5000 !-> 2; t_empty ⊥; (* Need one N constructor for correct type inference*)
            Regs := y !-> 0; A !-> 1000; t_empty 0
        |} 
|}.


Definition empty_F : (Functions) := t_empty None.
(*The program speculatively leaks 53 * 512 *)
Compute (S_execute_tr empty_F (init_state exampl_b) semanticV1 100). (* 53 * 512 = 27136*)

Definition exampl_s := {|Program := prog_s;
Config := {|Pc := 0;
            Mem := 1000 !-> 53; N 5000 !-> 2; t_empty ⊥; (* Need one N constructor for correct type inference*)
            Regs := public !-> 0; secret !-> 53; t_empty 0
        |} 
|}.

(* The program speculatively leaks 53 * 512 *)
Compute (S_execute_tr empty_F (init_state exampl_s) semanticV4 1000). (* 53 * 512 = 27136*)

Definition exampl_r := {|Program := prog_r;
Config := {|Pc := 7;
            Mem := 1000 !-> 53; N 5000 !-> 2; t_empty ⊥ ; (* Need one N constructor for correct type inference*)
            Regs := sp !-> 100; public !-> 0; secret !-> 53; t_empty 0
        |} 
|}.
Print Functions.
Definition F_map : (Functions) := "Manip_Stack" !-> Some 0; "Speculate" !-> Some 2; t_empty None.
(* Leaks 53*)
Compute (S_execute_tr F_map (init_state exampl_r) semanticV5 1000).


(*|
=============================
Composed Examples (Section 5)
=============================

We always give the traces of the source semantics first to show that they do not leak
the secret value. Then, we show the trace under the combined semantics of the respective version.

|*)


(*|
Combination B + R
=================
|*)
Definition exampl_br := {|Program := prog_br;
Config := {|Pc := 9;
            Mem := 1000 !-> 53; N 5000 !-> 2; t_empty ⊥; (* Need one N constructor for correct type inference*)
            Regs := sp !-> 100; public !-> 0; secret !-> 53; t_empty 0
        |} 
|}.

Definition F_map_br : (Functions) := F_map.

(*|
The traces of the source semantics for branch and return speculation.
Under these semantics the program prog_br is secure because the secret is not leaked
|*)
Compute (S_execute_tr F_map_br (init_state exampl_br) semanticV1 1000).
Compute (S_execute_tr F_map_br (init_state exampl_br) semanticV5 1000).
(* Leaks secret with value 53 *)
Compute (S_execute_tr F_map_br (init_state exampl_br) semanticV15 1000).


(*|
Combination B + S
=================
|*)
Definition exampl_bs := {|Program := prog_bs;
Config := {|Pc := 0;
            Mem := 1000 !-> 53; N 5000 !-> 2; t_empty 0; (* Need one N constructor for correct type inference*)
            Regs := sp !-> 100; public !-> 0; secret !-> 53; t_empty 0
        |} 
|}.

Compute (S_execute_tr F_map (init_state exampl_bs) semanticV1 100). 
Compute (S_execute_tr F_map (init_state exampl_bs) semanticV4 100). 
(* Leaks the secret 53 *)
Compute (S_execute_tr F_map (init_state exampl_bs) semanticV14 100). 



(*|
Combination S + R
=================
|*)
Definition exampl_sr := {|Program := prog_sr;
Config := {|Pc := 8;
            Mem := t_empty ⊥ ; (* Need one N constructor for correct type inference*)
            Regs := sp !-> 100; public !-> 0; secret !-> 53; t_empty 0
        |} 
|}.

Definition F_map_sr : (Functions) := F_map.

Compute (S_execute_tr F_map_sr (init_state exampl_sr) semanticV4 100).
Compute (S_execute_tr F_map_sr (init_state exampl_sr) semanticV5 100).

(* Leaks 53 *)
Compute (S_execute_tr F_map_sr (init_state exampl_sr) semanticV45 100).


(*|
Combination B + S + R
======================
|*)
Definition exampl_bsr := {|Program := prog_bsr;
Config := {|Pc :=9;
            Mem := 1000 !-> 53; N 5000 !-> 2; t_empty ⊥; (* Need one N constructor for correct type inference*)
            Regs := sp !-> 100; public !-> 0; secret !-> 53; t_empty 0
        |} 
|}.

Definition F_map_bsr : (Functions) := F_map.

Compute (S_execute_tr F_map_bsr (init_state exampl_bsr) semanticV1 200). 
Compute (S_execute_tr F_map_bsr (init_state exampl_bsr) semanticV4 200). 
Compute (S_execute_tr F_map_bsr (init_state exampl_bsr) semanticV5 200). 
(* Leaks secret value 53 in the trace *)
Compute (S_execute_tr F_map_bsr (init_state exampl_bsr) semanticV145 200). 
