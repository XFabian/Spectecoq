(* Include all notations from the language here.*)
From spec Require Export Lang.


Declare Scope expr_scope.
Declare Scope val_scope.
Delimit Scope expr_scope with E.
Delimit Scope val_scope with V.
Bind Scope expr_scope with exp. 
Bind Scope val_scope with val.


Declare Custom Entry spectector.
Declare Scope spec_scope.
Delimit Scope spec_scope with S.
Notation "'{{' e '}}'" := e (at level 0, e custom spectector at level 99) : spec_scope.
Notation "n ':' ( i )" := (Block n i) (in custom spectector at level 30) : spec_scope.
Notation "x ; y" := (Seq x y) (in custom spectector at level 90, right associativity) : spec_scope.



Notation "'skip'" := (Skip) (in custom spectector): spec_scope.
Notation "'spbarr'" := (Barr) (in custom spectector): spec_scope.
Notation "'ret'" := (Ret) (in custom spectector): spec_scope.
Notation "'store' x ',' < e >" := (Store x e) (in custom spectector at level 50): spec_scope.
Notation "'load' x ',' < e >" := (Load x e) (in custom spectector at level 50): spec_scope.
Notation "'jmp' l" := (Jmp l) (in custom spectector at level 50): spec_scope.
Notation "'beqz' c , l" := (JmpZ c l) (in custom spectector at level 50): spec_scope.
Notation "'call' f" := (Call f) (in custom spectector at level 50): spec_scope.
Notation "r '<-' < e >" := (Assign r e) (in custom spectector at level 50): spec_scope.
Notation "x" := x (in custom spectector at level 1, x constr at level 1): spec_scope. (* Needed for solo numbers for example*)

Coercion Const : nat >-> exp.
Coercion Reg : reg >-> exp.
Notation "x + y" := (Add x%E y%E) (in custom spectector at level 60, left associativity): spec_scope. 
Notation "x - y" := (Sub x y) (in custom spectector at level 60, left associativity): spec_scope.
Notation "x * y" := (Mul x y) (in custom spectector at level 55, left associativity): spec_scope.

Locate exp.
Print Grammar constr.
Open Scope expr_scope.
Print Reg.

Open Scope spec_scope.

Check (2 + 5)%E.
Locate Add.
Print Add.
Definition prog5 := 
    {{
        0 : ( skip );
        1 : ( beqz (r 1), ⊥  );
        1 : ((r 1) <- < 1 >);
        1 : ((r 1) <- < (r 1) + 5 > );
        2 : (store (r 1) , <  (r 2) > )
    }}.
Print prog5.
(*
Definition prog3 := 
{{
    0 : ( skip ) ;
    1 : ( beqz (r 1), ⊥  );
    2 : ( load (r 3) ,  ( (r 3) + (r 1)) ) ;
    3 : ( (r 2) <- (spec.Lang.Mul (r 2) 512 ) );
    4 : ( load (r 4), (spec.Lang.Add (r 5) (r 2)) );
    5 : ( (r 5) <- (spec.Lang.Add (r 5)  (r 4)) );
    6:  (jmp Lang.Bottom ) (* Used to set the PC to bottom. SHould add that automatically*)
}}.  
*)