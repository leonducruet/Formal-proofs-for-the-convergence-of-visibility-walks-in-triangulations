From mathcomp Require Import all_ssreflect.
From Equations Require Import Equations.
Require Import Arith.
Import Wellfounded.

Section wf_rel.

Variable T : finType.

Variable rel : T -> T -> bool.

Hypothesis rel_trans :
  transitive rel.

Hypothesis rel_irreflexive :
  irreflexive rel.

Definition rel_inv (t1 t2 : T) := rel t2 t1.
 
Definition subSetRel (t : T) := finset (rel_inv t).

Lemma increase_subSetRel (t1 t2 : T):
  rel t2 t1 -> subSetRel t2 \subset subSetRel t1.
Proof.
move=> h.
apply/subsetP.
rewrite/subSetRel/sub_mem=>t.
rewrite !in_set/rel_inv=>in1.
by apply: (rel_trans t2 t t1).
Qed.

Lemma decrease_card (t1 t2 : T):
  t2 \in subSetRel t1 -> #|subSetRel t2| < #|subSetRel t1|.
Proof.
rewrite /subSetRel in_set /rel_inv=> h.
apply: proper_card.
rewrite properEneq.
apply/andP.
split; last by apply: increase_subSetRel.
rewrite eqEsubset.
apply/nandP.
right.
apply/subsetPn.
exists t2; first by rewrite in_set.
by rewrite in_set rel_irreflexive.
Qed.

Definition f (t : T) : nat := #|subSetRel t|.

Definition rel_in_nat (t1 t2 : T) :=  lt (f t1) (f t2).

Lemma rel_to_nat : Relation_Definitions.inclusion T rel rel_in_nat.
Proof.
rewrite /Relation_Definitions.inclusion.
move => t1 t2 h.
rewrite /rel_in_nat /f.
apply /ltP.
apply: decrease_card.
by rewrite in_set /rel_inv.
Qed.

Lemma wf_rel_in_nat : well_founded rel_in_nat.
Proof.
rewrite /rel_in_nat.
apply: (wf_inverse_image T nat lt f).
by apply: lt_wf.
Qed.

Lemma wf_rel : well_founded rel.
Proof.
apply: wf_incl.
apply: rel_to_nat.
by apply : wf_rel_in_nat.
Qed.

End wf_rel.

Section wf_lexi.

Variables T1 T2 : finType.

Variable rel1 : rel T1.

Variable rel2 : rel T2.

Hypothesis rel1_trans : transitive rel1.

Hypothesis rel2_trans : transitive rel2.

Hypothesis rel1_irrefl : irreflexive rel1.

Hypothesis rel2_irrefl : irreflexive rel2.

Definition rel_lexi (a b : T1 * T2) :=
  (rel1 a.1 b.1) || ((a.1 == b.1) && (rel2 a.2 b.2)).

Lemma rel_lexi_trans : transitive rel_lexi.
Proof.
move=> [y1 y2] [x1 x2] [z1 z2].
rewrite/rel_lexi=>/=/orP[h1/orP[h2|/andP[/eqP h2 h3]]|
            /andP[/eqP h1 h2/orP[h3|/andP[/eqP h3 h4]]]].
      by apply/orP; left; apply: (rel1_trans y1).
    by apply/orP; left; rewrite -h2.
  by apply/orP; left; rewrite h1.
apply/orP; right; apply/andP; split; first by rewrite h1 h3.
by apply: (rel2_trans y2).
Qed.

Lemma rel_lexi_irrefl : irreflexive rel_lexi.
Proof.
move=> [x1 x2].
rewrite/rel_lexi/=.
apply:negbTE.
apply/negP=>/orP[h|/andP[_ h]]; apply:Bool.diff_true_false.
  by rewrite -(rel1_irrefl x1).
by rewrite -(rel2_irrefl x2).
Qed.

Lemma wf_rel_lexi : well_founded rel_lexi.
Proof.
apply: wf_rel.
  exact: rel_lexi_trans.
exact: rel_lexi_irrefl.
Qed.

End wf_lexi.