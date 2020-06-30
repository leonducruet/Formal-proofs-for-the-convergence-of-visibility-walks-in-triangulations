From mathcomp Require Import all_ssreflect all_algebra.

Require Import parameters.
Require Import determinant.

Import GRing.Theory Num.Theory Order.Theory.

Open Scope ring_scope.

Section implementation.

Variable R : realFieldType.

Variable P : finType.

Variable coords : P -> R * R.

Definition pt_eq (p1 p2 : P) :=
  ((coords p1).1 == (coords p2).1) && ((coords p1).2 == (coords p2).2).

Notation " p1 == p2 " := (pt_eq p1 p2).

Variable E : finType.

Variable edge : E -> P * P.

Definition edge_eq (e1 e2 : E) :=
  ((edge e1).1 == (edge e2).1) && ((edge e1).2 == (edge e2).2).

Notation " e1 == e2 " := (edge_eq e1 e2).

Definition opposite_edge (e : E) :=

Variable T : finType.

Variable edges_tr : T -> 'I_3 -> E.

Variable points_tr : T -> 'I_3 -> P.

Definition edge_in (e : E) (t : T) :=
  exists (i : 'I_3), (edges_tr t i) == e.

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



