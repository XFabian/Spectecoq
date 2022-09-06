Require Import spec.Lang.


From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.
Require Import spec.Maps.
Require Import Lia.
Require Import spec.notations.
Import List.
Import ListNotations.
Open Scope list_scope.


Inductive eObs : Type :=
| obs (o : Obs)
| skipObs (n : val) (* Careful for now Pc is a val. but when we use it it should be a nat*)
| start4 (n : nat)
| rlb4 (n : nat)
| start1 (n : nat)
| rlb1 (n : nat)
| start5 (n : nat)
| rlb5 (n : nat)
.

Coercion obs : Obs >-> eObs.

Check obs emptyObs.
Definition eTrace := list eObs.


Inductive Cmd : Type :=
| CSkip
| CBarr 
| CStore 
| CLoad 
| CAssign 
| CJmp
| CJmpZ
| CCall 
| CRet
.

Definition eqb_Cmd (c1 c2 : Cmd) : bool :=
match c1, c2 with 
| CSkip, CSkip => true 
| CBarr, CBarr => true 
| CStore, CStore => true 
| CLoad, CLoad => true 
| CAssign, Cassign => true 
| CJmp ,CJmp => true 
| CJmpZ, CJmpZ => true 
| CCall, CCall => true 
| CRet, CRet => true 
| _ , _ => false
end.

Definition instr_to_cmd (i : instr) : Cmd :=
match i with 
| Skip => CSkip 
| Barr => CBarr
| Store rg e => CStore
| Load  rg e => CLoad 
| Assign rg e => CAssign 
| Jmp l => CJmp 
| JmpZ cond l => CJmpZ 
| Call f_name => CCall 
| Ret => CRet 
end.





Inductive VId :=
| V1 
| V4
| V5
| none
.
(* Added Identifier to distinguish how the state was created when misprediction happen.
    This is done so that we can discharge the correct rlb observation
*)

(* The limit of the RSB *)
Definition Rsb_limit := 10.
(* The max speculation window. For these exampkes set to a small number to not clutter the trace in V5*)
Definition omega := 30.

Record instance := mkInstance{
    State : state;
    Ctr : nat;
    Window : val;
    RhoStack : eTrace;
    Rsb : list val;
    Id : VId
}.



Global Instance etaInstance : Settable _ := settable! mkInstance <State; Ctr; Window; RhoStack; Rsb; Id>.
Definition setTest (x : instance) := x <| State; Config; Pc := 2|>.



Definition SState := list instance. (* speculative state *)


Definition SfinState (st : SState) := match st with 
                                    | nil => False 
                                    | x::nil => finState (State x)
                                    | _ => False
                                    end.

Locate  "¬".
Lemma SfinStateDec (st : SState) : {SfinState st} + {not (SfinState st)}.
Proof.
    unfold SfinState. destruct st as [| x xs]; try auto.
    destruct xs; try auto.
    apply finStateDec.
Defined.






Notation "'LETOPT' '(' x ',' y ')' <== e1 'IN' e2"
   := (match e1 with
         | Some (x, y) =>  e2
         | None =>  None
       end)
   (right associativity, at level 60).

Definition base_case (F : Functions) (i : instr) (inta : instance) : option (SState * eObs):= 
    match i with 
    | Barr => LETOPT (st', tr ) <== stepE F (State inta) IN  (* Barrier case *)
                                        let new_win := if val_eqb (Window inta) ⊥ then ⊥ else 0 in
                                        Some ([inta <| State := st' |> <| Window := new_win|>] (* can be bottoms as well !*)        
                                        , obs tr) 

    | _ => LETOPT (st', tr ) <== stepE F (State inta) IN (* No Branching case*)
        Some ([inta <|State := st'|> <| Window := (Window inta) -' 1 |>], obs tr) 
    end.

Definition mispred_fun := Functions -> instr -> instance -> option (SState * eObs).

Print min.

Definition mispredict_branch (F : Functions) (i : instr) (inta : instance) : option (SState * eObs) :=
    LETOPT (_, l) <== match i with | JmpZ rg l => Some (rg, l) | _ => None end IN
    LETOPT (st', t') <== stepE F (State inta) IN (* We do the normal branch step*)
    let lval := match l with | Loc v => v end  
    in  
    let misPcVal := if val_eqb (Pc (Config st')) lval then (Pc (Config (State inta))) +' 1 else lval in  
    Some (inta <|State; Config; Pc:=misPcVal|> <|Ctr := Ctr inta + 1|> 
    <|Window := min (Window inta) omega|> 
    <|RhoStack := start1 (Ctr inta)::[obs (pcObs misPcVal)] |> <|Id := V1 |>
    ::[inta <|State := st' |> <|Window := (Window inta) -' 1 |>], obs t')
    (* Create a new state and update the old one. Note the order
    The new one comes first.*)
    .

Definition mispredict_skip (F : Functions) (i : instr) (inta : instance)  : option (SState * eObs) :=
    LETOPT (st', t') <== stepE F (State inta) IN
    let skipPc := (Pc (Config (State inta))) in  
    Some (inta <|State; Config; Pc:=skipPc +' 1|> <|Ctr := Ctr inta + 1|>
     <|Window := min (Window inta) omega|>
     <|RhoStack := start4 (Ctr inta)::[skipObs skipPc ] |> <|Id := V4 |>
    ::[inta <|State := st' |> <|Window := (Window inta) -' 1 |>], obs t')
    .

    
Definition callV5 (F : Functions) (i : instr) (inta : instance)  : option (SState * eObs) :=
    LETOPT (_, f) <== match i with | Call f => Some (f, f) | _ => None end IN
    LETOPT (st', t') <== stepE F (State inta) IN
    let ret_address := Pc (inta.(State).(Config)) +' 1 in
    if length (inta.(Rsb)) =? Rsb_limit 
        then Some ([inta <|State := st' |> <|Window := (Window inta) -' 1 |>], obs t')(* Call Full *)
        else Some ([inta <|State := st' |> <|Window := (Window inta) -' 1 |> <|Rsb := ret_address::Rsb inta |>], obs t')
.
 
Definition get_ra_from_stack (inta : instance) :=
    Mem inta.(State).(Config) ((Regs inta.(State).(Config)) sp -' 4). (* Minus 4 of the way we push and pop from*)

Definition retV5 (F : Functions) (i : instr) (inta : instance)  : option (SState * eObs) :=
    LETOPT (st', t') <== stepE F (State inta) IN
    match inta.(Rsb) with 
    | nil => Some ([inta <|State := st' |> <|Window := (Window inta) -' 1 |>], obs t')(* Ret Empty *)
    | l::rs => let ret_add := get_ra_from_stack (inta) in (* Compare with value in stack  *)
                if val_eqb l ret_add 
                then Some ([inta <|State := st' |> <|Window := (Window inta) -' 1 |> <| Rsb := rs |>], obs t') (* pop top of RSB*)
                else Some (inta <|State :=  st' <|Config; Pc:= l|> |> (* Return speculation bz using l*)
                        <|Ctr := Ctr inta + 1|>
                        <|Window := min (Window inta) omega |>
                        <|RhoStack := start5 (Ctr inta)::[ obs (retObs l) ] |> 
                        <|Id := V5 |> <| Rsb := rs |>
                        ::[inta <|State := st' |> <|Window := (Window inta) -' 1 |> <| Rsb := rs |>]
                        , obs t')
    end
.
(* Check if Rsb contains entry. If it has entry compare if its the same as the return address. If it is different we mispredict*)


Fixpoint get_func_from_Z (Z : list (Cmd * mispred_fun)) (c : Cmd) : option (mispred_fun) :=
    match Z with 
        |nil => None 
        |  (x, f)::xs => if eqb_Cmd x c then Some f else get_func_from_Z xs c
    end.


Definition semantic_fun := Functions -> instr -> instance -> SState -> option (SState * eObs).

(* Partiall instantiate the semantic for Z parameter to get the semantics of V1 V4 etc *)
Definition semantic (Z : list (Cmd * mispred_fun)) (F : Functions)  (i : instr) 
                    (inta: instance) (xs : SState) : option (SState * eObs):=
let c := instr_to_cmd i in 
    LETOPT (st', t) <== match get_func_from_Z Z c with 
                    | None => base_case F i inta 
                    | Some f => f F i inta (*Apply the corresponding mispreditc function*)
                    end 
IN Some (st' ++ xs , t).


(* Main definitions of the compositions *)
Definition V1_list := [(CJmpZ, mispredict_branch)].
Definition V4_list := [(CStore , mispredict_skip)].
Definition V5_list := [ (CCall, callV5); (CRet, retV5)].


Definition semanticV1 := semantic V1_list.
Definition semanticV4 := semantic V4_list.
Definition semanticV5 := semantic V5_list.
Definition semanticV14 := semantic (V1_list ++ V4_list).
Definition semanticV15 := semantic (V1_list ++ V5_list).
Definition semanticV45 := semantic (V4_list ++ V5_list).
Definition semanticV145 := semantic (V1_list ++ V4_list ++ V5_list).






Definition rlb_fun (vid : VId) : (nat -> eObs) :=
    match vid with 
    | V1 => rlb1
    | V4 => rlb4 
    | V5  => rlb5 
    | _ => rlb1 (* Error *)
    end.

Definition reset_window (s : instance) (xs: SState) :=
    match xs with 
    | nil => s <| Window := ⊥  |> 
    | _ => s <| Window := 0 |>
    end.
Definition SstepE (F : Functions) (st : SState) (semantic : semantic_fun)  : option (SState * eObs) :=
match st with 
| nil => None (* Error*)
| s::xs => match (RhoStack s) with 
          | rho::ls => Some (s <|RhoStack := ls|>::xs, rho )(* Check for RhoStack*) 
          | nil =>
                let s:= if finStateDec (State s) then reset_window s xs else s in (* Ok becase whole state is not finsihed because of check in step function SFinStaeDec but that relies on this comment and is not so nice. its not encoded in the function but iin my brain*)
                match Window s with (* Rollback case*)
                | 0 => match xs with 
                        | nil =>  None
                        | s1::xs' => 
                                Some (s1 <|Ctr := Ctr s |>::xs', (rlb_fun s.(Id) )  (Ctr s1))
                        end
                | S _ | ⊥  => match nextInstr (State s) with 
                        | Some i => semantic F i s xs
                        | None => None
                        end
                end
        end
end.


Fixpoint S_execute (F : Functions) (st : SState) (t : eTrace) (semantic : semantic_fun)  (i : nat) : option (SState * eTrace) :=    
    if SfinStateDec st then Some (st, t)
    else match i with 
        | 0 => None
        | S n => LETOPT (st', tr') <== SstepE F st semantic IN
                S_execute F st' (tr'::t) semantic n
    end.

Fixpoint S_execute_tr (F : Functions) (st : SState) (semantic : semantic_fun) (i : nat) : option eTrace :=
    if SfinStateDec st then Some nil 
    else match i with 
    | 0 => None 
    | S n => LETOPT (st', tr') <== SstepE F st semantic IN
                        match S_execute_tr F st' semantic n with
                        | Some t => Some (tr' :: t) 
                        | None => None
                    end
    end. 
