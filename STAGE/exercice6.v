From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Implicit Type p q r : bool.
Implicit Type m n a b c : nat.

About modnMml.
Search _ modn addn.
Search _ modn muln.
Lemma ex1 x y : 8 * y != 6 * x + 1.
Proof.
apply /negP => /eqP /(congr1 (modn^~ 2)).
rewrite -modnMml.
rewrite mul0n.
rewrite -modnDml.
rewrite -modnMml.
by [].
Qed.

Definition sol n a b := [&& a > 0, b > 0 & 2 ^ n == a ^ 2 + b ^ 2].

About ltnP.
About ltn_eqF.
About leq_add.
Lemma sol0 a b : ~~ sol 0 a b.
Proof.
rewrite /sol.
have [a_l0/=|//] := ltnP.
have [b_l0/=|//] := ltnP.
rewrite ltn_eqF.
  by [].
rewrite (@leq_add 1 1);
by rewrite ?expn_gt0 ?a_l0 ?b_l0.
Qed.

Lemma sol1 a b : sol 1 a b = (a == 1) && (b == 1).
Proof.
case: a b => [|[|a]] [|[|b]] //; rewrite /sol ltn_eqF //= (@leq_add 2) //=.
Qed.

Lemma mod4Dsqr_even a b : (a ^ 2 + b ^ 2) %% 4 = 0 -> (~~ odd a) && (~~ odd b).
Proof.
have lemme0 x y : (x * 2 + y) ^ 2 = y ^ 2 %[mod 4].
  rewrite sqrnD addnAC.
  rewrite mulnAC [2 * _]mulnC -mulnA -[2 * 2]/4.
  rewrite expnMn -[2 ^ 2]/4.
  by rewrite -mulnDl -modnDml modnMl.
rewrite (@divn_eq a 2) (@divn_eq b 2).
rewrite -modnDm !lemme0 modnDm -!divn_eq !modn2.
case: odd; case: odd; rewrite //=.
Qed.

About congr1.
Lemma sol_are_even n a b : n > 1 -> sol n a b -> (~~ odd a) && (~~ odd b).
Proof.
rewrite /sol.
case: n => [|[|n]]//.
move => n_g0.
have [a_g0/=|//] := ltnP.
have [b_g0/=|//] := ltnP.
rewrite expnSr expnSr -mulnA -[2 * 2]/4.
move /eqP /(congr1 (modn^~ 4)).
rewrite modnMl.
move => h.
by rewrite mod4Dsqr_even.
Qed.

Lemma solSS n a b : sol n.+2 a b -> sol n a./2 b./2.
Proof.
move=> soln2ab. 
have [//|a_even b_even] := andP (sol_are_even _ soln2ab).
rewrite -[a]odd_double_half -[b]odd_double_half in soln2ab.
rewrite /sol (negPf a_even) (negPf b_even) ?add0n ?double_gt0 in soln2ab.
rewrite /sol. 
move: soln2ab => /and3P[-> -> /=].
rewrite -(addn2 n) expnD -!muln2 !expnMn -mulnDl -[2 ^ 2]/4.
move /eqP /(congr1 (divn^~ 4)).
rewrite !mulnK //.
by move => -> .
Qed.

Lemma sol_even a b n : ~~ sol (2 * n) a b.
Proof.


