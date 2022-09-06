
Require Import spec.Maps.
Require Import Arith.
From Coq Require Import Unicode.Utf8.
Require Import Lia.
Require Import Coq.Strings.String.
Require Import List.
Import ListNotations.
(* see https://stackoverflow.com/questions/19212951/coq-error-when-trying-to-use-case-example-from-software-foundations-book *)
Open Scope string_scope.
Open Scope list_scope.
Open Scope nat_scope.

(* Memory and registers *)


(* pc should be a value so it can jump to bottom. Since pc is not writeable we pull it out *)
Inductive reg : Type :=
| sp 
| r (n : nat)
.

Inductive val : Type :=
| N (n : nat)
| Bottom
.


Notation "⊥" := (Bottom).
Coercion N : nat >-> val.


Definition val_eqb (v1 v2 : val) : bool :=
    match v1, v2 with
    | N n1, N n2 => Nat.eqb n1 n2
    | ⊥ , ⊥  => true 
    | _, _ => false
    end. 

Definition min (v1 v2 : val) : val :=
    match v1, v2 with 
    | N n1, N n2 => Nat.min n1 n2
    | ⊥, n | n, ⊥ => n 
end.


Definition add' (v v' : val) : val :=
match v, v' with
    | ⊥ , _ => ⊥
    | _ , ⊥ => ⊥
    | N n, N n' => N (n + n')
end.

Definition minus' (v v' : val) : val :=
match v, v' with
    | ⊥ , _ => ⊥
    | _ , ⊥ => ⊥
    | N n, N n' => N (n - n')
end.



Infix "+'" := add' (at level 100). 
Infix "-'" := minus' (at level 100). 
Definition pc : val := 0.


Definition eqb_reg (r1 r2 : reg) : bool :=
match r1, r2 with
    | sp, sp => true 
    | r n, r n' => if n =? n' then true else false 
    | _, _ => false 
end.

#[refine] Instance reg_EqDec : EqDec reg := {eqb := eqb_reg }.
Proof.
- intros [] [] H; auto; try inversion H. destruct (Nat.eqb n n0) eqn:H3.
    + apply beq_nat_true in H3. rewrite H3. reflexivity.
    + discriminate.
- intros [] [] H; try inversion H; try discriminate. destruct (Nat.eqb n n0) eqn:H3.
    + discriminate.
    + rewrite Nat.eqb_neq in H3. injection. intros H5. apply H3. auto.
Defined.

Definition reg_bank := total_map reg val.


Notation mem := nat.
#[refine] Instance val_EqDec : EqDec val := {eqb := val_eqb }.
Proof.
- intros [] [] H; auto; try inversion H. destruct (Nat.eqb n n0) eqn:H3.
    + apply beq_nat_true in H3. rewrite H3. reflexivity.
    + discriminate.
- intros [] [] H; try inversion H; try discriminate. destruct (Nat.eqb n n0) eqn:H3.
    + discriminate.
    + rewrite Nat.eqb_neq in H3. injection. intros H5. apply H3. auto.
Defined.


Definition memory := total_map val val.


(* Syntax of the language *)


Inductive label : Type :=
| Loc : val -> label.

Coercion Loc : val >-> label.

Inductive exp : Type :=
| Const (n : nat)
| Reg (r : reg)
| Add (e1 e2 : exp)
| Sub (e1 e2 : exp)
| Mul (e1 e2 : exp)
.


Inductive instr : Type :=
| Skip
| Barr
| Store (rg : reg) (e : exp)
| Load  (rg : reg) (e : exp)
| Assign (rg : reg) (e : exp)
| Jmp (l : label)
| JmpZ (cond : reg) (l : label)
| Call (f_name : string)
| Ret
.

#[refine] Instance string_EqDec : EqDec string := {eqb := String.eqb }.
Proof.
- intros [] [] H; auto; try inversion H. apply String.eqb_eq in H. auto. 
- intros [] [] H; try inversion H; try discriminate. apply String.eqb_neq. auto. 
Defined.

(* Mapping for function names*)
Definition Functions := (partial_map string nat)%type.
Print Functions. 

(* partial Map from  nats to isntruciton *)
Inductive program : Type :=
| Seq (p1 p2 : program) 
| Block (n : nat) (i : instr)
.



From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.
Record configuration := mkConf {
    Pc : val;
    Regs : reg_bank;
    Mem : memory
}.
Global Instance etaConf : Settable _ := settable! mkConf <Pc; Regs; Mem>.

Record state := mkState {
    Program : program;
    Config : configuration
}.
Global Instance etaState : Settable _ := settable! mkState <Program; Config>.



Inductive Obs : Type :=
| pcObs (l : label)
| storeObs (n : nat)
| loadObs (n : nat)
| callObs (n : nat)
| retObs (n: val)
| emptyObs
.

Definition Trace := list Obs.



Fixpoint getBlock (pr : program) (n : nat) : option instr :=
    match pr with
    | Block m i => if n =? m then Some i else None
    | Seq p1 p2 => match getBlock p1 n with
                    | Some i => Some i
                    | None => getBlock p2 n 
                    end
    end. 


Definition nextInstr (st : state) : option instr := 
 match st.(Config).(Pc) with 
    | N n => getBlock st.(Program) n 
    | ⊥ => None
 end.

Fixpoint eval_expr (c : configuration) (e : exp) : nat :=
    match e with
    | Const n => n
    | Reg rg =>  match c.(Regs) rg with | N n => n | ⊥ => 0 end(* TODO not very nice*)
    | Add e1 e2 => eval_expr c e1 + eval_expr c e2 
    | Sub e1 e2 => eval_expr c e1 - eval_expr c e2
    | Mul e1 e2 => eval_expr c e1 * eval_expr c e2
    end.

 


Definition update_pc (c : configuration) : configuration :=
    let n' :=  c.(Pc) +' 1 in c <| Pc := n' |>.


Definition execute_instr (F : Functions )(c : configuration) (i : instr) :  option (configuration * Obs) :=
match i with
| Skip => Some (update_pc c, emptyObs)
| Barr =>  Some (update_pc c, emptyObs)
| Store rg e => let v :=  c.(Regs) rg in
                Some (update_pc (c <|Mem := eval_expr c e !-> v ; (Mem c) |>)
                    , storeObs (eval_expr c e) )
| Load rg e =>  let v := (Mem c) (eval_expr c e) in (* load value from memory *)
                Some (update_pc (c <|  Regs := rg !-> v ; (Regs c) |>), 
                loadObs (eval_expr c e))
| Assign rg e => Some (update_pc (c <| Regs := rg !-> eval_expr c e;c.(Regs)|>),
                 emptyObs)
| Jmp (Loc n) => Some ( c <| Pc := n |>, 
                pcObs n)
| JmpZ cond (Loc n)  => match Regs c cond with
                        | 0 => Some (c <| Pc := n |>,
                                 pcObs n)
                        | (S n') => Some (update_pc c, pcObs (c.(Pc) +' 1))
                        | ⊥ => Some (update_pc c, pcObs (c.(Pc) +' 1))
                        end
| Call f => match F f with 
            | None => None 
            | Some n => Some (c <| Pc := n |> <|Mem := (Regs c sp) !-> c.(Pc) +' 1; Mem c|>
                 <|Regs := sp !-> (Regs c sp) +' 4; Regs c  |>, callObs n) (* Reduce stack by number*)
            end
| Ret => let ret_addr_loc := Regs c sp -' 4 in let ret_val := Mem c ret_addr_loc in
    Some (c <| Pc := ret_val |> <|Regs := sp !-> ret_addr_loc; Regs c  |>, retObs (ret_val))
end.

Notation "'LETOPT' '(' x ',' y ')' <== e1 'IN' e2"
   := (match e1 with
         | Some (x, y) =>  e2
         | None =>  None
       end)
   (right associativity, at level 60).


Definition stepE (F : Functions) (st : state) : option (state * Obs) :=
    match nextInstr st with
        | Some i => LETOPT (c, tr') <==  execute_instr F st.(Config) i IN
                    Some (st <| Config:= c |>, tr')
        | None => None
    end. 



Definition finState (st : state):= Pc (Config st) = ⊥.

Lemma finStateDec (st : state) : {finState st} + {¬ finState st}.
Proof.
    unfold finState. decide equality. decide equality.
Defined. (* has to be defined, otherwise opaque and not reduced.*)

Print finState.




Fixpoint execute (F : Functions) (st : state) (t : Trace) (i : nat) : option (state * Trace) :=    
    if finStateDec st then Some (st, t)
    else match i with 
        | 0 => None
        | S n => LETOPT (st', tr') <== stepE F st IN
                execute F st' (tr'::t) n
    end.


Fixpoint execute_tr (F : Functions) (st : state) (i : nat) : option Trace :=    
    if finStateDec st then Some nil
    else match i with 
        | 0 => None
        | S n => LETOPT (st', tr') <== stepE F st IN
                match execute_tr F st' n with
                    | Some t => Some (tr' :: t) 
                    | None => None
                end
    end.
Fixpoint execute_st (F : Functions) (st : state) (i : nat) : option state :=    
    if finStateDec st then Some st 
    else match i with 
        | 0 => None
        | S n => LETOPT (st', tr') <== stepE F st IN
                 execute_st F st' n
                    
    end.
