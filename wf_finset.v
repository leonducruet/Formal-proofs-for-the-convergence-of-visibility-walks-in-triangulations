From mathcomp Require Import all_ssreflect.
From Equations Require Import Equations.

Section wfrel.

Variable T : finType.

Variable rel : T -> T -> bool.

Hypothesis rel_trans :
  forall (t1 t2 t3 : T), rel t1 t2 -> rel t2 t3 -> rel t1 t3.

Hypothesis rel_anti_refl :
  forall (t : T), ~ rel t t.

(* Hypothesis rel_anti_sym :
  forall (t1 t2 : T), rel t1 t2 -> rel t2 t1 -> t1 = t2. 
hypothèse inutile ?*)

Lemma rel_anti_sym :
  forall (t1 t2 : T), rel t1 t2 -> ~ rel t2 t1.
Proof.
move => t1 t2 h h_inv.
apply: (rel_anti_refl t2).
by apply: (rel_trans t2 t1 t2).
Qed.

Definition rel_inv (t1 t2 : T) := rel t2 t1.
 
Definition subSetRel (t : T) := finset (rel_inv t).

Lemma decrease_card :
  forall (t1 t2 : T),
  t2 \in subSetRel t1 -> #|subSetRel t2| < #|subSetRel t1|.
Proof.
move => t1 t2 h.
rewrite /subSetRel in_set /rel_inv in h.
have proper : subSetRel t2 \proper subSetRel t1.
  have subset : subSetRel t2 \subset subSetRel t1.
    apply /subsetP.
    rewrite /subSetRel /sub_mem.
    move => x in1.
    rewrite in_set /rel_inv in in1.
    rewrite in_set /rel_inv.
    by apply: (rel_trans x t2 t1).
  have diff : subSetRel t2 != subSetRel t1.
    rewrite eqEsubset.
    apply /nandP.
    rewrite subset /=.
    apply /orP.
    rewrite /=.
    apply /subsetPn.
    exists t2.
      by rewrite in_set.
    rewrite in_set /rel_inv.
    apply/negP.
    by apply: rel_anti_refl.
  by rewrite properEneq subset diff.
rewrite properEcard in proper.
move/andP: proper.
move => proper.
destruct proper.
by apply: H0.
Qed.
