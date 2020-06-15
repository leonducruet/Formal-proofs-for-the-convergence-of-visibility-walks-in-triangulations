From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Lemma foldl_cat T R f (z0 : R) (s1 s2 : seq T) :
  foldl f z0 (s1 ++ s2) = foldl f (foldl f z0 s1) s2.
Proof.
move: z0.
elim: s1.
  by [].
move=> x xs IH.
move=> acc.
rewrite /=.
by rewrite IH.
Qed.