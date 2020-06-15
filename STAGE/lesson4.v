From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Check nat : Type.

Definition zero : nat := 0.

Lemma zero_bis : nat.
Proof.
apply: 0.
Qed.

Print zero.
Print zero_bis.

Check nat -> nat : Type.

Definition silly : nat -> nat := fun x => x.

Lemma sillier : nat -> nat.
Proof.
move => x.
apply: x.
Qed.

Print silly.
Print sillier.

Section DependentFunction.

Variable P : nat -> Type.
Variable p1 : P 1.

Check forall x, P x.
Check forall x : nat, P 1.

Check fun x : nat => p1.

Check factorial.
Check factorial 2.

Variable px1 : forall x, P x.+1.

Check px1.
Check px1 3.

End DependentFunction.

Print True.

Definition trivial1 : True := I.

Definition trivial2 : True -> nat :=
  fun t => 
    match t with I => 3 end.

Lemma trivial3 : True -> nat.
Proof.
move => t.
case: t.
apply: 3.
Qed.

Print False.

Definition ex_falso A : False -> A :=
  fun abs => match abs with end.

Lemma ex_falso2 A : False -> A.
Proof.
move => abs.
case: abs.
Qed.

Section Connectives.

Print and.

Variable A : Prop.
Variable B : Prop.
Variable C : Prop.

Variable a : A.
Variable b : B.

Check conj a b.

Definition and_elim_left : and A B -> A :=
  fun ab => match ab with conj a b => a end.

Lemma and_elim_left2 : and A B -> A.
Proof.
case => l r.
apply l.
Qed.

Print or.

Check or_introl a : or A B.

End Connectives.







