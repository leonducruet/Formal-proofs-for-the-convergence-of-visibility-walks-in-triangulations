From mathcomp Require Import all_ssreflect.

Module  easy.

Implicit Type p q r : bool.
Implicit Type m n a b c : nat.

Lemma bool_gimmics1 a : a != a.-1 -> a != 0.
Proof.
apply: contra.
by move /eqP => -> .
Qed.

Lemma view_gimmics1 p a b :
  p -> (p ==> (a == b.*2)) -> a./2 = b.
Proof.
move => -> /eqP ->.
by rewrite doubleK.
Qed.

Lemma maxn_idPl m n :
  reflect (maxn m n = m) (m >= n).
Proof.
apply: (iffP idP); rewrite /maxn.
  by case: leqP.
move => <-.
by case: leqP.
Qed.

Lemma maxn_idPl_bis m n :
  reflect (maxn m n = m) (m >= n).
Proof.
rewrite /leq -(eqn_add2l m) -maxnE addn0.
by apply: eqP.
Qed.

End easy.

Module reflect1.

Inductive reflectl (P : Prop) b :=
  | RT (p : P) (e : b = true)
  | RF (p : ~ P) (e : b = false).

Lemma andP (b1 b2 : bool) :
  reflectl (b1 /\ b2) (b1 && b2).
Proof.
by case: b1; case b2;
  [ left | right => //= [][l r] ..]. 
Qed.

Lemma orP (b1 b2 : bool) : 
  reflectl (b1 \/ b2) (b1 || b2).
Proof.
case: b1; case: b2;
  [ left; by [|left | right] .. | by right => //= [][ | ] ].
Qed.

Lemma implyP (b1 b2 : bool) :
  reflectl (b1 -> b2) (b1 ==> b2).
Proof.
by case: b1; case: b2;
  [ left | right | left ..] => //= /(_ isT). 
Qed.

End reflect1.

Set Nested Proofs Allowed.

Definition bool_Prop_equiv (P : Prop) (b : bool) :=
  b = true <-> P.

Lemma test_bool_Prop_equiv b P :
  bool_Prop_equiv P b -> P \/ ~ P.
Proof.
rewrite /bool_Prop_equiv.
case: b; case => a b.
  left.
  by apply: a.
right => h.
by move: (b h).
Qed.

Lemma iffP_lr (P : Prop) (b : bool) :
  (P -> b) -> (b -> P) -> reflect P b.
Proof.
case: b; move => p_b b_p;
by apply: (iffP idP).
Qed.

Lemma iffP_rl (P : Prop) (b : bool) :
  reflect P b -> ((P -> b) /\ (b -> P)).
Proof.
by case: b; case => p; split.
Qed.

Lemma eqnP {n m : nat} :
  reflect (n = m) (eqn n m).
Proof.
apply: (iffP idP) => [|->].
  elim: n m => [[]|n IH [//|m]] //= /IH -> //=.
by elim: m.
Qed.

Lemma nat_inj_eq T (f : T -> nat) x y :
  injective f -> 
    reflect (x = y) (eqn (f x) (f y)).
Proof.
move => f_inj.
by apply (iffP eqnP) => [/f_inj|-> //].
Qed.

Lemma leq_max m n1 n2 :
  (m <= maxn n1 n2) = (m <= n1) || (m <= n2).
Proof.
wlog leq12: n1 n2 / n1 <= n2 => [n_ord|].
  case/orP: (leq_total n2 n1) => /n_ord;
  by rewrite maxnC orbC.
Abort.

Goal forall (P Q : Prop), (P <-> Q) -> P -> Q.
Proof.
move => P Q h hp.
by move/h : hp => hp.
Qed.
  
Goal forall (P : nat -> Prop) (Q : Prop),
  (P 0 -> Q)
    -> (forall n, P n.+1 -> P n)
    -> P 4 -> Q.
Proof.
move => P Q.
move => h0 IH.
by move/IH/IH/IH/IH.
Qed.

Goal forall (b b1 b2 : bool),
  (b1 -> b) -> (b2 -> b) -> b1 || b2 -> b.
Proof.
move => b b1 b2.
move => hb1 hb2 hor.
case/orP : hor.
  by move/hb1.
by move/hb2.
Qed.

Goal forall (Q : nat -> Prop) (p1 p2 : nat -> bool) x,
  ((forall y, Q y -> p1 y /\ p2 y) /\ Q x) -> p1 x && p2 x.
Proof.
move => Q p1 p2 x h.
case: h.
move => /(_ x) h qx.
move/h : qx.
by move/andP.
Qed.

Goal forall (Q : nat -> Prop) (p1 p2 : nat -> bool) x,
  ((forall y, Q y -> p1 y \/ p2 y) /\ Q x) -> p1 x || p2 x.
Proof.
move => Q p1 p2 x h.
case: h.
move => /(_ x) h qx.
move/h: qx.
by move/orP.
Qed.

About Bool.ReflectT.
Lemma myidP: forall (b : bool), reflect b b.
Proof.
move => b.
case: b;
  [exact: ReflectT | exact: ReflectF].
Qed.

Lemma mynegP: forall (b : bool),
  reflect (~ b) (~~ b).
Proof.
move => b.
case: b.
  exact: ReflectF.
  exact: ReflectT.
Qed.

Lemma myandP: forall (b1 b2 : bool),
  reflect (b1 /\ b2) (b1 && b2).
Proof.
move => b1 b2.
case: b1; case: b2;
  [ exact: ReflectT |
  apply: ReflectF;
    move=> h;
    by case: h ..].
Qed.

Lemma myiffP:
  forall (P Q: Prop) (b : bool),
    reflect P b -> (P -> Q) -> (Q -> P) -> reflect Q b.
Proof.
move => P Q b.
move => Pb PQ QP.  
move: Pb. case: b.
  move => h. case:h.
    move/PQ => hp. by apply:ReflectT.
  move=> hNp. apply: ReflectF. move/QP=> hp.
  by move/hNp: hp.
move => h. case: h.
  move/PQ => hp. by apply: ReflectT.
move => hNp. apply: ReflectF. move/QP=> hp.
by move/hNp: hp.  
Qed.

Fixpoint len (n m : nat) : bool :=
  match n, m with
  | 0, _ => true
  | n'.+1, 0 => false  
  | n'.+1, m'.+1 => len n' m'
  end.

Lemma lenP: forall n m, 
  reflect (exists k, k + n = m) (len n m).
Proof.
  move => n; elim: n.
  move => m. apply: (iffP idP).
  move => _. exists m.
Abort.





