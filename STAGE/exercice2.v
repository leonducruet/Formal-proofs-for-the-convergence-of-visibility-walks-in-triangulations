From mathcomp Require Import all_ssreflect.

Implicit Type p q r : bool.
Implicit Type m n a b c : nat.

Lemma andTb p : true &&  p = p.
Proof. by []. Qed.

Lemma andbT p : p && true = p.
Proof.
by case: p.
Qed.

Lemma orbC p q : p || q = q || p.
Proof.
by case: p; case: q.
Qed.

Goal forall p q, (p && q) || ( p && ~~q) ||
              (~~ p && q) || (~~ p && ~~ q).
Proof.
by move=> p q; case: p; case: q.
Qed.

Goal forall p q r, (p || q) && r = r && (p || q).
Proof.
by move=> p q r; case: (p || q); case: r.
Qed.

(*Locate "==>".
Print implb. *)
Lemma implybE p q : p ==> q = ~~ p || q.
Proof.
by case: p.
Qed.

Lemma negb_imply p q : ~~ (p ==> q) = p && ~~ q.
Proof. by rewrite implybE negb_or negbK. Qed.

Lemma Peirce p q : ((p ==> q) ==> p) ==> p.
Proof. by rewrite implybE negb_imply implybE orbK orNb. Qed.

Lemma find_me p q : ~~ p = q -> p (+) q.
Proof. 
by move=> np_q; rewrite -np_q addbN negb_add. 
Qed.

(*Print maxn.
Search maxn in ssrnat.*)

Definition max3n a b c :=
   if a < b then maxn b c else maxn a c.

Lemma max3n3n a : max3n a a a = a.
Proof.
by rewrite /max3n if_same maxnn. Qed.

Lemma max3E a b c : max3n a b c = maxn (maxn a b) c.
Proof.
by rewrite /max3n /maxn; case: (a < b). Qed.

Lemma max3n_213 a b c : max3n a b c = max3n b a c.
Proof.
by rewrite max3E (maxnC a) -max3E. Qed.

Lemma max3n_132 a b c : max3n a b c = max3n a c b.
Proof.
by rewrite max3E -maxnA (maxnC b) maxnA -max3E. 
Qed.

Lemma max3n_231 a b c : max3n a b c = max3n b c a.
Proof.
by rewrite max3n_213 max3n_132.
Qed.

Definition order3n (T : Type) (r : rel T) x y z := (r x y) && (r y z).
Definition incr3n := order3n nat (fun x y => x <= y).
Definition decr3n := order3n nat (fun x y => y <= x).

Lemma incr3n_decr a b c : incr3n a b c = decr3n c b a.
Proof.
by rewrite /incr3n /order3n andbC.
Qed.

Lemma incr3_3n a : incr3n a a a.
Proof.
by rewrite /incr3n /order3n leqnn.
Qed.

Lemma decr3_3n a : decr3n a a a.
Proof.
by rewrite /decr3n /order3n leqnn.
Qed.

Lemma incr3n_leq12 a b c : incr3n a b c -> a <= b.
Proof.
by rewrite /incr3n /order3n; case (_ <= _).
Qed.

Lemma incr3n_leq23 a b c : incr3n a b c -> b <= c.
Proof.
by rewrite /incr3n /order3n; case (_ <= _).
Qed.

Lemma incr3n_eq a b c : incr3n a b a = (a == b).
Proof.
by rewrite /incr3n /order3n eqn_leq. Qed.




