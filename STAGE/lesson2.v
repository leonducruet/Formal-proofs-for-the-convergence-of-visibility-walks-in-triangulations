From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Goal 2 + 2 = 4.
Proof. by []. Qed.

Lemma andbC (b1 b2 : bool) : b1 && b2 = b2 && b1.
Proof.
by case: b1; case: b2.
Qed.

Lemma orbN b : b || ~~ b.
Proof.
by case: b.
Qed.

Lemma leqn0 n : (n <= 0) = (n == 0).
Proof.
case: n => [|p].
  by [].
by [].
Qed.

Lemma muln_eq0 m n :
  (m * n == 0) = (m == 0) || (n == 0).
Proof.
case: m => [|p].
  by [].
case: n => [|q].
  rewrite muln0.
  by [].
by [].
Qed.

