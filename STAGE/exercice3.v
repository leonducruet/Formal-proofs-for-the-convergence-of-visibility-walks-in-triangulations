From mathcomp Require Import all_ssreflect.

Implicit Type p q r : bool.
Implicit Type m n a b c : nat.

Lemma iterSr A n (f : A -> A) x : iter n.+1 f x = iter n f (f x).
Proof.
rewrite /=.
elim: n x => [|n IH] x.
  by [].
by rewrite /= IH.
Qed.

Lemma iter_predn m n : iter n predn m = m - n.
Proof.
elim: n m => [|n IHn] m.
  by rewrite subn0.
by rewrite /= IHn subnS.
Qed.

Definition add2list s := map (fun x => x.+2) s.
Definition odds n := iter n (fun s : seq nat => 1 :: add2list s) [::].
Definition suml := foldl addn 0.

Lemma foldl_addE n s : foldl addn n s = n + suml s.
Proof.
elim: s n => [|x xs IH] n.
  by rewrite /suml /= addn0.
by rewrite /suml /= add0n !IH addnA.
Qed.

Lemma suml_cons n s : suml (n :: s) = n + suml s.
Proof.
by rewrite /suml /= add0n foldl_addE -/suml.
Qed.

Lemma suml_add2list s : suml (add2list s) = suml s + 2 * size s.
Proof.
elim: s => [|x xs IH].
  by [].
rewrite /= !suml_cons IH.
by rewrite !mulnS !addnS addnA.
Qed.

Lemma size_add2list s : size (add2list s) = size s.
Proof.
by rewrite size_map.
Qed.

Lemma size_odds n : size (odds n) = n.
Proof.
elim: n => [|n IH].
  by [].
by rewrite /odds /= size_add2list IH.
Qed.

Lemma eq_suml_odds n : suml (odds n) = n ^ 2.
Proof.
elim: n => [|n IH].
  by [].
rewrite suml_cons suml_add2list size_odds IH.
rewrite addnCA addnA.
by rewrite -(addn1 n) sqrnD muln1.
Qed.

Search iota.

Lemma iota_add2list n k : 
  add2list [seq 2 * i + 1 | i <- iota k n] = [seq 2 * i + 1 | i <- iota k.+1 n].
Proof.
elim: n k => [| n IHn] k.
  by [].
rewrite //=.
rewrite IHn.
congr(_ :: _).
by rewrite !mulnS -addn2 addnC addnA.
Qed.

Lemma oddsE n : odds n = [seq 2 * i + 1 | i <- iota 0 n].
Proof.
elim: n => [|n IHn].
  by [].
rewrite //=.
rewrite -iota_add2list.
rewrite IHn.
by congr(_ :: _).
Qed.

Search iota.

Lemma nth_odds n i : i < n -> nth 0 (odds n) i = 2 * i + 1.
Proof.
move => l_in.
rewrite oddsE.
rewrite (nth_map 0).
rewrite nth_iota.
rewrite add0n //=.
  by rewrite l_in.
by rewrite size_iota l_in.
Qed.

Definition mysum m n F := (foldr (fun i a => F i + a) 0 (iota m (n - m))).

Notation "\mysum_ ( m <= i < n ) F" := (mysum m n (fun i => F))
  (at level 41, F at level 41, i, m, n at level 50,
           format "'[' \mysum_ ( m  <=  i  <  n ) '/  '  F ']'").

Lemma mysum_recl m n F : m <= n ->
  \mysum_(m <= i < n.+1) F i = \mysum_(m <= i < n) F i + F n.
Proof.
move => leq_mn.
rewrite /mysum.
rewrite subSn //.
rewrite -addn1 iota_add.
rewrite subnKC //=.
rewrite foldr_cat /=.
rewrite addn0.
elim: (iota _ _) (F n) => [|x s IH] k.
  by [].
by rewrite /= IH addnA.
Qed.

Lemma sum_odds n : \mysum_(0 <= i < n) (2 * i + 1) = n ^ 2.
Proof.
elim: n => [|n IHn].
  by [].
rewrite mysum_recl // IHn.
rewrite addnCA addnC.
by rewrite -(addn1 n) sqrnD muln1.
Qed.





