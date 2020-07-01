From mathcomp Require Import all_ssreflect all_algebra finfun.

Require Import parameters.
Require Import determinant.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Import GRing.Theory Num.Theory Order.Theory. *)

(* Open Scope ring_scope. *)

(* ffune *)

Section implementation.

Variable R : realFieldType.

Variable P : finType.

Variable coords : P -> R * R.

Hypothesis inj_coords : 
  forall (p1 p2 : P), (coords p1) == (coords p2) -> p1 == p2.

Definition E := [finType of {dffun 'I_2 -> P}].

Lemma elimI2 (P' : 'I_2 -> Prop): P' 0 -> P' 1 -> forall i, P' i.
Proof.
move=> p0 p1 [[ | [ | [ | ?]]] ci] //.
    by have /eqP -> : Ordinal ci == 0.
  by have /eqP -> : Ordinal ci == 1.
Qed.

Definition oppos_edge (e : E) : E := 
  [ffun i : 'I_2 => e (i + 1)].

Lemma p1p1_I2 : 
  forall (i : 'I_2), (i + 1 + 1 : 'I_2) = i.
Proof.
apply: elimI2; by apply /eqP.
Qed.

Lemma inv_oppos_edge (e : E) : (oppos_edge (oppos_edge e)) = e.
Proof.
rewrite -ffunP.
apply: elimI2; by rewrite /oppos_edge ?ffunE p1p1_I2.
Qed.

Definition T :=  [finType of {dffun 'I_3 -> P}].

Definition edge_tr (t : T) : {ffun 'I_3 -> E} :=
  [ffun i : 'I_3 => [ffun j : 'I_2 => if val j == 0%N then t i else t (i + 1)]].

Definition edge_in (e : E) (t : T) :=
  exists (i : 'I_3), (edge_tr t i) == e.

Variable tr : triangulation T.

(* Definition is_Delaunay :=
  forall (t1 t2 : T), 
    t1 \in tr -> t2 \in tr -> 
      forall (i : 'I_3), dist t1 (coord (pt_tr t2 i)) > 0. *)

Variable target_pt : P.


(* Lemma eq_dffun (g1 g2 : ∀ x, rT x) :
   (∀ x, g1 x = g2 x) → finfun g1 = finfun g2. *)

(* Hypothesis involution_opposite_edge : 
  forall (e : E), opposite_edge (opposite_edge e) = e.

Variable separating_edge : T -> option E.

Definition target_in (t : T) :=
  separating_edge t == None.

Hypothesis separating_edge_in_triangle : 
  forall (e : E) (t : T),
  separating_edge t = Some e -> edge_in e t.

Variable find_triangle_of_edge : E -> option T.

Hypothesis correction_find_triangle :
  forall (e : E) (t : T),
  find_triangle_of_edge e = Some t <-> edge_in e t.

Variable triangle_measure : T -> R.

Hypothesis positive_measure :
  forall (t : T), triangle_measure t >= 0. *)



