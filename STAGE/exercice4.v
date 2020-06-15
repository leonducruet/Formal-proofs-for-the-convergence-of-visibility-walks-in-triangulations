From mathcomp Require Import all_ssreflect.

Implicit Type P Q R : Prop.

Definition not P :=
  P -> False.

Lemma exo P : not (P /\ not P).
Proof.
by case => [p np].
Qed.

Inductive iff P Q :=
  iff_intro (p2q : P -> Q) (q2p : Q -> P).

Definition iff1 P Q : iff P Q -> P -> Q :=
  fun (iff_p_q : iff P Q) => 
    match iff_p_q with 
      iff_intro p2q _ => p2q
    end.

Inductive xor P Q : Prop :=
  | xorL (p : P) (nq : not Q)
  | xorR (np : not P) (q : Q).

Lemma xorC P Q : iff (xor P Q) (xor Q P).
Proof.
apply: iff_intro;
case => [p nq| np q]; 
by [apply: xorL| apply: xorR].
Qed.

Lemma xor1 P Q : (xor P Q) -> not Q -> P.
Proof.
case => [p nq| np q]; by [].
Qed.  

Lemma xor2 P Q Z : (xor P Q) -> (xor Q Z) -> iff P Z.
Proof.
case => [p nq0| np q0];
case => [q1 nz| nq1 z];
apply: iff_intro; by [].
Qed.

Inductive ex2 T (P Q : pred T) : Prop :=
  ex2_intro (x : T) (p : P x) (q : Q x).

Lemma ex2T T (P : pred T) : (exists x, P x) -> (ex2 T P P).
Proof.
case => x px.
apply: (ex2_intro _ _ _ x); by [].
Qed.

Definition induction_seq A (P : seq A -> Prop) :
  P nil -> (forall a l, P l -> P (a :: l)) -> forall l, P l :=
    fun (p0 : P nil) (pl : forall a l, P l -> P (a :: l)) =>
      fix IH l :=
        match l with
        | nil => p0
        | a :: l1 => pl a l1 (IH l1)
        end.

About prime_gt1.
About dvdn_leq.

Lemma ex_view p : prime p -> p %| 7 -> 1 < p <= 7.
Proof.
by move => /prime_gt1 -> /dvdn_leq ->.
Qed.
 
Inductive cherryt : bool -> Type :=
  | Flower : cherryt true
  | Bud : cherryt false
  | Node f (l : cherryt f) (d : cherryt f) : cherryt f.




