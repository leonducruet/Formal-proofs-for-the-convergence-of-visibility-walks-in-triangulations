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

(* Hypothesis inj_coords : 
  forall (p1 p2 : P), (coords p1) == (coords p2) -> p1 == p2. *)

Definition E := {ffun 'I_2 -> P}.

Lemma elimI2 (P' : 'I_2 -> Prop): P' 0 -> P' 1 -> forall i, P' i.
Proof.
move=> p0 p1 [[ | [ | [ | ?]]] ci] //.
    by have /eqP -> : Ordinal ci == 0.
  by have /eqP -> : Ordinal ci == 1.
Qed.

Lemma elimI3 (P' : 'I_3 -> Prop): P' 0 -> P' 1 -> P' (1 + 1) -> forall i, P' i.
Proof.
move=> p0 p1 p2 [[ | [ | [ | ?]]] ci] //.
    by have /eqP -> : Ordinal ci == 0.
  by have /eqP -> : Ordinal ci == 1.
by have /eqP -> : Ordinal ci == (1 + 1).
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

(*
1/ pqr -> qrp
2/ pqr -> ~ prq
3/ p!=q -> q!=r -> p!=r -> pqr \/ prq
4/ tqr /\ ptr /\ pqt -> pqr
5/ tsp /\ tsq /\ tsr /\ tpq /\ tqr -> tpr 
*)

Hypothesis inj_triangles : 
  forall (t : T), forall (i j : 'I_3), (t i) == (t j) -> i == j.

Definition triangle_area (t : T) :=
  tr_area R (coords (t 0)) (coords (t 1)) (coords (t (1 + 1))).

Hypothesis tr_orientation :
  forall (t : T), 0 < triangle_area t.

Definition edges_tr (t : T) : {ffun 'I_3 -> E} :=
  [ffun i : 'I_3 => [ffun j : 'I_2 => if val j == 0%N then t i else t (i + 1)]].

Lemma inj_edges_tr :
  forall (t : T), forall (i j : 'I_3), 
    (edges_tr t i) == (edges_tr t j) -> i == j.
Proof.
move => t i j /eqP h.
rewrite !ffunE in h.
move: h.
rewrite -ffunP.
move => h.
move : (h 0).
rewrite !ffunE /=.
move => /eqP H.
apply: inj_triangles.
by apply: H.
Qed.

Definition point_in (p : P) (t : T) : bool :=
  [exists i : 'I_3, (t i) == p].

Lemma point_in_exists (p : P) (t : T) :
  (point_in p t) -> exists (i : 'I_3), (t i) = p.
Proof.
rewrite /point_in.
by apply : exists_eqP.
Qed.

Definition edge_in (e : E) (t : T) : bool :=
  [exists i : 'I_3, (edges_tr t i) == e].

Lemma edge_in_exists (e : E) (t : T) :
  (edge_in e t) -> exists (i : 'I_3), (edges_tr t i) = e.
Proof.
rewrite /edge_in.
by apply : exists_eqP.
Qed.

Lemma common_points (t1 t2 : T) :
  forall (i j : 'I_3), 
  t1 i = t2 (j + 1) -> t1 (i + 1) = t2 j -> ~ point_in (t2 (j + 1 + 1)) t1.
Proof.
move => i j h1 h2.
rewrite /point_in.
move /existsP => h3.
destruct h3 as [x].
move : H.
case : x.

Admitted.

Lemma p1p1p1_I3 : 
  forall (i : 'I_3), (i + 1 + 1 + 1 : 'I_3) = i.
Proof.
apply: elimI3; by apply /eqP.
Qed.

Lemma p10 : (0 + 1 : 'I_3) = 1.
Proof.
by [].
Qed.

Lemma p1p10 : (0 + 1 + 1 : 'I_3) = (1 + 1).
Proof.
by [].
Qed.

Lemma p1p11 : (1 + 1 + 1 : 'I_3) = 0.
Proof.
by apply /eqP.
Qed.

Definition tr_dist (t : T) (p : P) :=
  out_circle R (coords (t 0)) (coords (t 1)) (coords (t (1 + 1))) (coords p).

Lemma starter_pt_dist (i : 'I_3) (t : T) (p : P) : 
  tr_dist t p = out_circle R (coords (t i)) (coords (t (i + 1))) (coords (t (i + 1 + 1))) (coords p).
Proof.
move: i.
apply : elimI3.
    by rewrite p10 p1p10.
  by rewrite p1p11 (inv_cycle_out_circle R).
by rewrite p1p11 p10 -(inv_cycle_out_circle R).
Qed.

Variable tr : triangulation [finType of T].

Lemma unique_edge :
  forall (t : T) (e : E), (t \in (enum tr)) -> (edge_in e t) -> 
    forall (t' : T), t != t' -> ~ (edge_in e t').
Proof.
Admitted.

Fixpoint find_triangle_in_list (p : T -> bool) (tr_enum : list T) : option T :=
  match tr_enum with
  | nil => None
  | t :: tail => if (p t) then Some t else find_triangle_in_list p tail
  end.

Lemma correc_find_triangle_in_list (p : T -> bool) (tr_enum : list T) :
  forall (t : T), 
  find_triangle_in_list p tr_enum = Some t -> (p t) /\ (t \in tr_enum).
Proof.
move => t.
elim: tr_enum.
  by [].
move => a l HR.
rewrite /find_triangle_in_list.
case_eq (p a).
  move => h0.
  move /Some_inj => h1.
  rewrite -h1.
  split.
    by [].
  rewrite in_cons.
  apply /orP.
  by left.
move => npa H.
have Pl : p t /\ t \in l.
  by apply: HR.
destruct Pl as [H1 H2].
have t_in_al : t \in a :: l.
  rewrite in_cons.
  apply /orP.
  by right.
by split.
Qed.

Lemma unique_result (p : T -> bool) (tr_enum : list T) :
  forall (t1 : T),
  (p t1) -> (forall (t2 : T), t1 != t2 -> ~ (p t2)) ->
    (find_triangle_in_list p (tr_enum) = Some t1) \/ ~~ (t1 \in tr_enum).
Proof.
move => t1 h1 h2.
elim : tr_enum.
  right.
  by rewrite in_nil.
move => a l.
case_eq (t1 == a).
move => a_eq_t1_bool HR.
  left.
  have a_eq_t1 : t1 = a.
    by apply /eqP.
  by rewrite -a_eq_t1 /find_triangle_in_list h1.
move => a_diff_t1_bool HR.
have a_diff_t1 : t1 != a.
    by rewrite a_diff_t1_bool.
case_eq (p a).
  have not_pa : ~ p a.
    by apply: h2.
  move => not_pa2.
  move : not_pa.
  by rewrite not_pa2.
move => npa.
rewrite /find_triangle_in_list npa.
have not_in (x y : T) (s : list T) : ((x == y) = false) -> ((x \in y :: s) = (x \in s)).
  move => H1.
  by rewrite in_cons H1 /=.
by rewrite (not_in t1 a l a_diff_t1_bool).
Qed.

Definition find_triangle_of_edge (e : E) : option T :=
  find_triangle_in_list (edge_in e) (enum tr).

Lemma correc_find_triangle (e : E) (t : T) :
  find_triangle_of_edge e = Some t <-> (edge_in e t) /\ (t \in (enum tr)).
Proof.
split.
  rewrite /find_triangle_of_edge.
  by apply: correc_find_triangle_in_list.
move => H.
destruct H as [H1 H2].
have uni_edge : forall (t' : T), t != t' -> ~ (edge_in e t').
  by apply: unique_edge.
have aux : (find_triangle_in_list (edge_in e) (enum tr) = Some t) \/ (~~ (t \in (enum tr))).
  by apply: unique_result.
rewrite H2 /= in aux.
rewrite /find_triangle_of_edge.
by destruct aux.
Qed.

Variable target_pt : P.

Lemma starter_pt_triangle_area (i : 'I_3) (t : T) :
  triangle_area t = tr_area R (coords (t i)) (coords (t (i +1))) (coords (t (i + 1 + 1))).
Proof.
move: i.
apply : elimI3.
    by rewrite p10 p1p10.
  by rewrite p1p11 (inv_cycle_tr_area R).
by rewrite p1p11 p10 -(inv_cycle_tr_area R).
Qed.

Definition is_separating_edge (t : T) (i : 'I_3) :=
  0 < tr_area R (coords (t i)) (coords target_pt) (coords (t (i + 1))).

Definition separating_edge_i (t : T) (i : 'I_3) :=
  if (is_separating_edge t i) then Some (edges_tr t i) 
    else if (is_separating_edge t (i + 1)) then Some (edges_tr t (i + 1))
    else if (is_separating_edge t (i + 1 + 1)) then Some (edges_tr t (i + 1 + 1))
    else None.

Definition separating_edge (t : T) :=
  separating_edge_i t 0.

Lemma separating_edge_is_separating_edge :
  forall (t : T) (i : 'I_3),
  separating_edge t = Some (edges_tr t i) -> is_separating_edge t i.
Proof.
have with_i (t : T) : 
  forall (i : 'I_3),
  separating_edge_i t i = Some (edges_tr t i) -> is_separating_edge t i.
  rewrite /separating_edge_i.
  apply: elimI3.
      rewrite !p10 !p1p10.
      case: (is_separating_edge t 0).
        by [].
      case: (is_separating_edge t 1).
        move /eqP.
        by apply: inj_edges_tr.
      case: (is_separating_edge t (1 + 1)).
        move /eqP.
        by apply: inj_edges_tr.
      by [].
    rewrite p1p11.
    case: (is_separating_edge t 1).
      by [].
    case: (is_separating_edge t (1 + 1)).
      move /eqP.
      by apply: inj_edges_tr.
    case: (is_separating_edge t 0).
      move /eqP.
      by apply: inj_edges_tr.
    by [].
  rewrite p1p11 p10.
  case: (is_separating_edge t (1 + 1)).
    by [].
  case: (is_separating_edge t 0).
    move /eqP.
    by apply: inj_edges_tr.
  case: (is_separating_edge t 1).
    move /eqP.
    by apply: inj_edges_tr.
  by [].
move => t.
apply : elimI3.
    have i_0 : separating_edge t = separating_edge_i t 0.
      by [].
    rewrite i_0.
    apply: (with_i t 0).
  have i_1 : 
    separating_edge t = Some (edges_tr t 1) -> 
      separating_edge_i t 1 = Some (edges_tr t 1).
    rewrite /separating_edge /separating_edge_i.
    case : (is_separating_edge t 0).
      move /eqP.
      by move => /inj_edges_tr.
    rewrite p10.
    case: (is_separating_edge t 1).
      by [].
    case: (is_separating_edge t (1 + 1)).
      move /eqP.
      by move => /inj_edges_tr.
    by [].
  move => h.
  apply: (with_i t 1).
  by apply: i_1.
have i_2 : 
  separating_edge t = Some (edges_tr t (1 + 1)) -> 
    separating_edge_i t (1 + 1) = Some (edges_tr t (1 + 1)).
  have i_2_sub : 
    separating_edge_i t 1 = Some (edges_tr t (1 + 1)) -> 
      separating_edge_i t (1 + 1) = Some (edges_tr t (1 + 1)).
    rewrite /separating_edge /separating_edge_i.
    case : (is_separating_edge t 1).
      move /eqP.
      by move => /inj_edges_tr.
    case : (is_separating_edge t (1 + 1)).
      by [].
    rewrite p1p11.
    case : (is_separating_edge t 0).
      move /eqP.
      by move => /inj_edges_tr.
    by [].
  have sub_i_2 : 
    separating_edge t = Some (edges_tr t (1 + 1)) -> 
      separating_edge_i t 1 = Some (edges_tr t (1 + 1)).
    rewrite /separating_edge /separating_edge_i.
    rewrite p10.
    case : (is_separating_edge t 0).
      move /eqP.
      by move => /inj_edges_tr.
    case : (is_separating_edge t 1).
      move /eqP.
      by move => /inj_edges_tr.
    case : (is_separating_edge t (1 + 1)).
      by [].
    by [].
  move => h.
  apply: i_2_sub.
  by apply: sub_i_2.
move => h.
apply: (with_i t (1 + 1)).
by apply: i_2.
Qed.

Lemma separating_edge_in_triangle :
  forall (e : E) (t : T),
  separating_edge t = Some e -> edge_in e t.
Proof.
move => e t h.
rewrite /edge_in.
apply /existsP.
rewrite /separating_edge /separating_edge_i in h.
move: h.
case: (is_separating_edge t).
  move => h.
  exists 0.
  apply /eqP.
  by apply : Some_inj h.
case: (is_separating_edge t).
  move => h.
  exists 1.
  apply /eqP.
  by apply : Some_inj h.
case: (is_separating_edge t).
  move => h.
  exists (1 + 1).
  apply /eqP.
  by apply : Some_inj h.
by [].
Qed.

Definition triangle_measure (t : T) :=
  power R (coords (t 0)) (coords (t 1)) (coords (t (1 + 1))) (coords target_pt).

Lemma starter_pt_measure (i : 'I_3) (t : T) (p : P) :
  triangle_measure t = power R (coords (t i)) (coords (t (i + 1))) (coords (t (i + 1 + 1))) (coords target_pt).
Proof.
move: i.
apply : elimI3.
    by rewrite p10.
  by rewrite p1p11 (inv_cycle_power R).
by rewrite p1p11 p10 -(inv_cycle_power R).
Qed.

Hypothesis is_Delaunay_tr :
  forall (t1 t2 : T) (i : 'I_3), (* t1 \in tr -> t2 \in tr -> *)
  ( ~ point_in (t2 i) t1) -> 0 < tr_dist t1 (t2 i).

Lemma decrease_condition :
  forall (e : E) (t t' : T), 
  separating_edge t = Some e -> 
    find_triangle_of_edge (oppos_edge e) = Some t' -> walk_lt R [finType of T] triangle_measure t' t.
Proof.
move => e t1 t2 h1 h2.
have neighbours : exists (i j : 'I_3), 
  (t1 i = t2 (j + 1)) /\ (t1 (i + 1) = t2 j) /\ 
  (is_separating_edge t1 i) /\ ~ point_in (t2 (j + 1 + 1)) t1.
  have e_in_t1: exists (i : 'I_3), edges_tr t1 i = e.
    apply: edge_in_exists.
    by apply: separating_edge_in_triangle h1.
  have oppos_e_in_t2: exists (i : 'I_3), edges_tr t2 i = oppos_edge e.
    apply: edge_in_exists.
    have aux : (edge_in (oppos_edge e) t2) /\ (t2 \in (enum tr)) -> edge_in (oppos_edge e) t2.
      move => H.
      by destruct H as [H1 H2].
    apply: aux.  
    rewrite -correc_find_triangle.
    by apply: h2.
  destruct e_in_t1 as [i].
  have edge_is_separating : is_separating_edge t1 i.
    apply: separating_edge_is_separating_edge.
      rewrite H.
      by apply: h1.
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
  have diff_point :
    ~ point_in (t2 (j + 1 + 1)) t1.
    apply: common_points.
      by rewrite H0.
    by rewrite H1.
    rewrite /edge_in.
  exists i.
  exists j.
  split; by [].
rewrite /walk_lt -subr_gt0.
destruct neighbours as [i h].
destruct h as [j].
rewrite (starter_pt_measure i t1 target_pt) (starter_pt_measure (j + 1) t2 target_pt).
rewrite p1p1p1_I3.
destruct H as [H1 H2].
destruct H2 as [H2 H3].
destruct H3 as [H3 H4].
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
by apply: is_Delaunay_tr.
Qed.





