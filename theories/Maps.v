Require Import Lia.
Require Import Arith.
From Coq Require Import Unicode.Utf8.

Class EqDec (A : Type) :=
{
    eqb : A -> A -> bool;
    eqb_leibniz : forall x y, eqb x y = true -> x = y; 
    beq_nat_false : forall x y, eqb x y = false -> x <> y
}.
Notation "x =? y" := (eqb x y) (at level 70).

Definition total_map (A B: Type) `{EqDec A} := A -> B.

(* Default value *)
Definition t_empty {A B : Type} `{EqDec A}  (v : B) :=
    (fun _ : A => v).

Definition t_update {A B : Type} `{EqDec A} (m : total_map A B)
                    (x : A) (v : B) :=
    fun y => if eqb x y then v else m y.

Notation "'_' ':' A '!->' v" := (@t_empty A _ _ v) (at level 100, right associativity).

Example empt (A : Type ) `{EqDec A} :=  _ : A !-> false.

Notation "x '!->' v ';' m" := (t_update m x v) 
                              (at level 100, v at next level, right associativity).



#[refine] Instance nat_EqDec : EqDec nat := {eqb := Nat.eqb }.
Proof.
    - intros [] [] H; auto; try inversion H. apply beq_nat_true in H1. rewrite H1. 
    reflexivity.
    - intros x y H. rewrite Nat.eqb_neq in H. auto.
Defined.


Definition examplemap :=
    (1 !-> 0 ;
     2 !-> 1 ;
     @t_empty nat _ nat_EqDec 4
    ).
(* We can leave out the annotations. Coq infers all of them *)
Definition examplemap' :=
    (1 !-> 0 ;
    2 !-> 1 ;
    t_empty 4
    ).

Check (t_empty 4). 

Print examplemap'.

Section list_test.
Print list.
Check list.

Inductive total_map' (A B : Type) (H : EqDec A) : Type :=
| T_empty : total_map' A B H
| T_update : forall (x : A) (v : B) (m : total_map' A B H),
            total_map' A B H          
.

Arguments T_empty : default implicits.
Arguments T_update : default implicits.
Print Implicit T_empty.
Check (T_update 2 3 (@T_empty nat _ _) ).


End list_test.


Section t_map_lemmas.

Context {A B : Type} (x : A) (v : B).
Context `{EqDec A}.
Context (m : total_map A B ).
Lemma t_apply_empty : (t_empty v) x = v.
Proof.
     cbn. simpl. unfold t_empty. auto.
Qed.
Print Instances EqDec.

Lemma t_update_eq : (x !-> v ; m) x = v.
Proof.
    unfold t_update. destruct (x =? x) eqn:H2; try auto. Search Nat.eqb. 
    apply beq_nat_false in H2. exfalso. apply H2. reflexivity.
Qed.

Lemma t_update_neq : ∀ y, x <> y -> (x !-> v ; m) y = m y.
Proof.
    intros y Heq. unfold t_update. destruct (x =? y) eqn:H3; try auto.
    apply eqb_leibniz in H3. congruence.
Qed.

(* careful here  *)
Require Import Coq.Logic.FunctionalExtensionality.
Lemma t_update_shadow : ∀ v1, 
  (x !-> v ; x !-> v1 ; m) = (x !-> v ; m).
Proof.
    intros v1. unfold t_update. 
    apply functional_extensionality. intros a.
    destruct (x =? a) eqn:H3; try auto.
Qed.

Theorem t_update_same :
  (x !-> m x ; m) = m.
Proof.
    unfold t_update. apply functional_extensionality. intros y.
    destruct (x =? y) eqn:H3; try auto.
    apply eqb_leibniz in H3. now rewrite H3.
Qed.

Theorem t_update_permute : ∀ v' y,
  x ≠ y →
  (x !-> v ; y !-> v' ; m)
  =
  (y !-> v' ; x !-> v ; m).
Proof.
    intros v' y H1. apply functional_extensionality. unfold t_update. intros z.
    destruct (x =? z) eqn:H3; try auto. apply eqb_leibniz in H3. 
    destruct (y =? z) eqn:H4; try auto.
    apply eqb_leibniz in H4. rewrite <- H3 in H4. symmetry in H4. congruence.
Qed.


End t_map_lemmas.
Definition partial_map (A B : Type) `{EqDec A}:= total_map A (option B).