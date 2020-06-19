From mathcomp Require Import all_ssreflect.
From Equations Require Import Equations.

Section wfrel.

Variable T : finType.

Variable rel : T -> T -> bool.

Hypothesis rel_trans :
  forall (t1 t2 t3 : T), rel t1 t2 -> rel t2 t3 -> rel t1 t3.

Hypothesis rel_anti_refl :
  forall (t : T), ~ rel t t.

Hypothesis rel_anti_sym :
  forall (t1 t2 : T), rel t1 t2 -> rel t2 t1 -> t1 = t2.

Definition subSetRel (t : T) := [set t2| rel t2 t].

Lemma decrease_card :
  forall (t1 t2 : T),
  t2 \in subSetRel t1 -> #|subSetRel t2| < #|subSetRel t1|.
Proof.
have proper t1 t2 : t2 \in subSetRel t1 -> subSetRel t2 \proper subSetRel t1.

Abort.
Lemma wf_rel : forall t : T, t \in set -> Acc rel t.
Proof.
Admitted.


