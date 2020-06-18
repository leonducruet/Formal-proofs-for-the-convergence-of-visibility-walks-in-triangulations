From mathcomp Require Import all_ssreflect.
From Equations Require Import Equations.

Section wfrel.

Variable T : finType.

Variable set : {set T}.

Variable rel : T -> T -> Prop.

Hypothesis rel_trans :
  forall (t1 t2 t3 : T), rel t1 t2 -> rel t2 t3 -> rel t1 t3.

Hypothesis rel_anti_refl :
  forall (t : T), ~ rel t t.

Hypothesis rel_anti_sym :
  forall (t1 t2 : T), rel t1 t2 -> ~ rel t2 t1.

Lemma wf_rel : forall t : T, t \in set -> Acc rel t.
Proof.
Admitted.


