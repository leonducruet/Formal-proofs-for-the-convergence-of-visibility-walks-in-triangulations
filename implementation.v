From mathcomp Require Import all_ssreflect all_algebra.
From Equations Require Import Equations.

Require Import parameters.
Require Import determinant.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Num.Theory.

Section implementation.

Variable R : realFieldType.

Variable P : finType.

Variable coords : P -> R * R.

Hypothesis inj_coords : 
  forall (p1 p2 : P), (coords p1) == (coords p2) -> p1 == p2.

Definition E := {ffun 'I_2 -> P}.

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

Definition T := {ffun 'I_3 -> P}.

Definition edges_tr (t : T) : {ffun 'I_3 -> E} :=
  [ffun i : 'I_3 => [ffun j : 'I_2 => if val j == 0%N then t i else t (i + 1)]].

Definition edge_in (e : E) (t : T) :=
  ((edges_tr t 0) == e) || ((edges_tr t 1) == e) || ((edges_tr t (1 + 1)) == e).

Lemma edge_in_exists (e : E) (t : T) :
  (edge_in e t) -> exists (i : 'I_3), (edges_tr t i) = e.
Proof.
rewrite /edge_in.
move /orP => h.
destruct h as [h2 | h1].
  move: h2.
  move /orP => h2.
  destruct h2 as [h3 | h2].
    exists 0.
    by apply /eqP : h3.
  exists 1.
  by apply /eqP : h2.
exists (1 + 1).
by apply /eqP : h1.
Qed.

Lemma elimI3 (P' : 'I_3 -> Prop): P' 0 -> P' 1 -> P' (1 + 1) -> forall i, P' i.
Proof.
move=> p0 p1 p2 [[ | [ | [ | ?]]] ci] //.
    by have /eqP -> : Ordinal ci == 0.
  by have /eqP -> : Ordinal ci == 1.
by have /eqP -> : Ordinal ci == (1 + 1).
Qed.

Lemma p1p1_I3 : 
  forall (i : 'I_3), (i + 1 + 1 + 1 : 'I_3) = i.
Proof.
apply: elimI3; by apply /eqP.
Qed.

Definition tr_dist (t : T) (p : P) :=
  out_circle R (coords (t 0)) (coords (t 1)) (coords (t (1 + 1))) (coords p).

Lemma starter_pt_dist (i : 'I_3) (t : T) (p : P) :
  forall (i : 'I_3), 
  tr_dist t p = out_circle R (coords (t i)) (coords (t (i + 1))) (coords (t (i + 1 + 1))) (coords p).
Proof.
Admitted.

Definition is_DelaunayT (t1 t2 : T) (i : 'I_3) :=
  ( ~ edge_in (edges_tr t2 i) t1) -> 0 < tr_dist t1 (t2 i).

Definition is_Delaunay (tr' : triangulation [finType of T]) :=
  forall (t1 t2 : T), t1 \in tr' -> t2 \in tr' ->
  forall (i : 'I_3), is_DelaunayT t1 t2 i.

Variable tr : triangulation [finType of T].

Fixpoint find_triangle_in_list (p : T -> bool) (tr_enum : list T) : option T :=
  match tr_enum with
  | nil => None
  | t :: tail => if (p t) then Some t else find_triangle_in_list p tail
  end.

(* Equations find_triangle_in_list (p : T -> bool) (tr_enum : list T) : option T :=
  find_triangle_in_list p nil := None;
  find_triangle_in_list p (cons t tail) 
    with find_triangle_in_list p tail => { |opt := if p t then Some t else opt}.
 *)

Definition find_triangle_of_edge (e : E) : option T :=
  find_triangle_in_list (edge_in e) (enum tr).

Lemma correc_find_triangle (e : E) (t : T) :
  find_triangle_of_edge e = Some t <-> edge_in e t.
Proof.
Admitted.

Variable target_pt : P.

Definition triangle_area (t : T) :=
  tr_area R (coords (t 0)) (coords (t 1)) (coords (t (1 + 1))).

Lemma starter_pt_triangle_area (i : 'I_3) (t : T) :
  triangle_area t = tr_area R (coords (t i)) (coords (t (i +1))) (coords (t (i + 1 + 1))).
Proof.
Admitted.

Hypothesis tr_orientation :
  forall (t : T), 0 < triangle_area t.
(* Hypothesis non_empty_triangles :
  forall (t : T), triangle_area t != 0. *)

(* Definition is_separating_edge (e : E) :=
  tr_area (coords (e 0)) (coords (e 1)) (coords target_pt). *)

Definition is_separating_edge (t : T) (i : 'I_3) :=
  0 < tr_area R (coords (t i)) (coords target_pt) (coords (t (i + 1))).

Definition separating_edge (t : T) :=
  if (is_separating_edge t 0) then Some (edges_tr t 0) 
    else if (is_separating_edge t 1) then Some (edges_tr t 1)
    else if (is_separating_edge t (1 + 1)) then Some (edges_tr t (1 + 1))
    else None.

Lemma separating_edge_is_separating_edge :
  forall (e : E) (t : T) (i : 'I_3),
  separating_edge t = Some e -> edges_tr t i = e -> is_separating_edge t i.
Proof.
Admitted.

Lemma separating_edge_in_triangle :
  forall (e : E) (t : T),
  separating_edge t = Some e -> edge_in e t.
Proof.
move => e t.
rewrite /separating_edge.
case: (is_separating_edge t).
  rewrite /edge_in.
  move => h.
  apply /orP.
  left.
  apply /orP.
  left.
  apply /eqP.
  by apply: Some_inj h.
case: (is_separating_edge t).
  rewrite /edge_in.
  move => h.
  apply /orP.
  left.
  apply /orP.
  right.
  apply /eqP.
  by apply: Some_inj h.
case: (is_separating_edge t).
  rewrite /edge_in.
  move => h.
  apply /orP.
  right.
  apply /eqP.
  by apply: Some_inj h.
by [].
Qed.

(* Definition tr_dist (t : T) (p : P) := 
  power R (coords (t 0)) (coords (t 1)) (coords (t (1 + 1))) (coords p).

Lemma starter_pt_dist (i : 'I_3) (t : T) (p : P) :
  tr_dist t p = power R (coords (t i)) (coords (t (i + 1))) (coords (t (i + 1 + 1))) (coords p).
Proof.
Admitted. *)

Definition triangle_measure (t : T) :=
  power R (coords (t 0)) (coords (t 1)) (coords (t (1 + 1))) (coords target_pt).

Lemma starter_pt_measure (i : 'I_3) (t : T) (p : P) :
  triangle_measure t = power R (coords (t i)) (coords (t (i + 1))) (coords (t (i + 1 + 1))) (coords target_pt).
Proof.
Admitted.

Lemma is_Delaunay_tr :
  is_Delaunay tr.
Proof.
Admitted.

Lemma decrease_condition :
  forall (e : E) (t t' : T),
  separating_edge t = Some e -> 
    find_triangle_of_edge (oppos_edge e) = Some t' -> walk_lt R [finType of T] triangle_measure t' t.
Proof.
move => e t1 t2 h1 h2.
have neighbours : exists (i j : 'I_3), 
  (t1 i = t2 (j + 1)) /\ (t1 (i + 1) = t2 j) /\ 
  (is_separating_edge t1 i) /\ ( ~ edge_in (edges_tr t2 (j + 1 + 1)) t1).
  have e_in_t1: exists (i : 'I_3), edges_tr t1 i = e.
    apply: edge_in_exists.
    by apply: separating_edge_in_triangle h1.
  have oppos_e_in_t2: exists (i : 'I_3), edges_tr t2 i = oppos_edge e.
    apply: edge_in_exists.
    rewrite -correc_find_triangle.
    by apply: h2.
  destruct e_in_t1 as [i].
  have edge_is_separating : is_separating_edge t1 i.
    apply: separating_edge_is_separating_edge.
      by apply: h1.
    by apply: H.
  destruct oppos_e_in_t2 as [j].

  rewrite -H in H0.
  move: H0.
  rewrite -ffunP .
  move => H'.
  move: (H' 0).
  move: (H' 1).
  move => H0 H1.
  rewrite !ffunE /= in H0.
  rewrite !ffunE /= in H1.
  exists i.
  exists j.
  split; by [].
rewrite /walk_lt -subr_gt0.
destruct neighbours as [i h].
destruct h as [j].
rewrite (starter_pt_measure i t1 target_pt) (starter_pt_measure (j + 1) t2 target_pt).
rewrite p1p1_I3.
destruct H as [H1 H2].
destruct H2 as [H2 H3].
rewrite -H1 -H2.
apply: (power_decrease R).
      rewrite -(starter_pt_triangle_area i t1).
      by apply: tr_orientation.
    rewrite H1 H2.
    rewrite (inv_cycle_tr_area R).
    rewrite -(starter_pt_triangle_area j t2).
    by apply: tr_orientation.
  by apply: H3.
rewrite -(starter_pt_dist i t1).
have 
apply: (is_DelaunayT t1 t2 (j + 1 + 1)).

(* Definition is_DelaunayT (t1 t2 : T) (i : 'I_3) :=
  ( ~ edge_in (edges_tr t2 i) t1) -> 0 < tr_dist t1 (t2 i). *)
apply: (is_Delaunay tr).

rewrite starter_pt_dist.




