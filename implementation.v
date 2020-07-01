From mathcomp Require Import all_ssreflect all_algebra.

Require Import parameters.
Require Import determinant.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(* Import GRing.Theory Num.Theory Order.Theory. *)

Open Scope ring_scope.

Section implementation.

Variable R : realFieldType.

Variable P : finType.

Variable coords : P -> R * R.

Hypothesis inj_coords : 
  forall (p1 p2 : P), (coords p1) == (coords p2) -> p1 == p2.

Definition E := 'I_2 -> P.

Definition edge_eq (e1 e2 : E) :=
  forall (i : 'I_2), e1 i = e2 i.

Lemma elimI2 (P' : 'I_2 -> Prop): P' 0 -> P' 1 -> forall i, P' i.
Proof.
move=> p0 p1 [[ | [ | [ | ?]]] ci] //.
    by have /eqP -> : Ordinal ci == 0.
  by have /eqP -> : Ordinal ci == 1.
Qed.

(* Notation "e1 == e2" := (@edge_eq (e1 : E) (e2 : E)). *)

Definition oppos_edge (e : E) : E := 
  fun (i : 'I_2) => e (i + 1).

Lemma inv_oppos_edge (e : E) : edge_eq (oppos_edge (oppos_edge e)) e.
Proof.
rewrite /oppos_edge /edge_eq.
apply: elimI2.
  have zero : (0 + 1 + 1 : 'I_2) = 0.
    by apply /eqP.
  by rewrite zero.
have one : (1 + 1 + 1 : 'I_2) = 1.
  by apply /eqP.
by rewrite one.
Qed.

Definition T := 'I_3 -> P.

Definition edges_tr (t : T) (i : 'I_3) : E :=
  fun (j : 'I_2) => if val j == 0%N then t i else t (i + 1).

Definition edge_in (e : E) (t : T) :=
  exists (i : 'I_3), edge_eq (edges_tr t i) e.

Variable tr : triangulation T.

(* Definition is_Delaunay :=
  forall (t1 t2 : T), 
    t1 \in tr -> t2 \in tr -> 
      forall (i : 'I_3), dist t1 (coord (pt_tr t2 i)) > 0. *)

Variable target_pt : P.
  

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



