From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Print andb.
Print and.

Print orb.
Print or.

Check true ==> false.
Check True -> False.

Lemma test_and (P : bool) :
  True /\ P -> P.
Proof.
move => t_p.
case: t_p => t p.
apply: p.
Qed.

Lemma test_orb (P Q R : bool) :
  P \/ Q -> R.
Proof.
move => p_q.
case: p_q.
Abort.

About iffP.
About idP.

Lemma eqnP {n m : nat} :
  reflect (n = m) (eqn n m).
Proof.
apply: iffP.
apply: idP.
  elim: n m => [|n IHn] m;
  case: m => // m Hm.
  by rewrite (IHn m Hm).
move => ->.
by elim: m.
Qed.

About andP.

Lemma example n m k : k <= n -> 
  (n <= m) && (m <= k) -> n = k.
Proof.
move => lekn /andP [lenm lemk].
Abort.

Lemma leq_total m n : (m <= n) || (m >= n).
Proof.
About implyNb.
About ltnNge.
rewrite -implyNb -ltnNge.
About implyP.
apply /implyP.
About ltnW.
by apply: ltnW.
Qed.

Lemma leq_max m n1 n2 :
  (m <= maxn n1 n2) = (m <= n1) || (m <= n2).
Proof.
About orP.
case /orP: (leq_total n2 n1) => [le_n21 | le_n12].
Abort.

Print Bool.reflect.
About andP.

Lemma example_spec a b : a && b ==> (a == b).
Proof.
by case: andP => [[-> ->] | //].
Qed.

Print or.
About leqP.
Print leq_xor_gtn.

Lemma example_spec2 a b : (a <= b) || (b < a).
Proof.
case: leqP.
Abort.

About ltngtP.
Print compare_nat.

Lemma example_spec3 a b : (a <= b) || (b < a) || (b == a).
Proof.
by case: ltngtP.
Qed.

About prime_gt1.

Lemma example_2 x y : prime x -> odd y -> 2 < y + x.
Proof.
move /prime_gt1 /ltnW.
Abort.

Lemma example_3 A B (V: A <-> B): B -> A.
Proof.
move=>b.
apply /V.
by [].
Qed.
