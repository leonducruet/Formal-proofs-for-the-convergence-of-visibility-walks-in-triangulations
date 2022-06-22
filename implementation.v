From mathcomp Require Import all_ssreflect all_algebra.

Require Import determinant.
Require Import parameters.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Num.Theory GRing.Theory.

Close Scope order_scope.

Section finite_lemmas.

Lemma elimI2 (P' : 'I_2 -> Prop): P' 0 -> P' 1 -> forall i, P' i.
Proof.
move=> p0 p1 [[|[|]] ci] //.
    by have /eqP -> : Ordinal ci == 0.
  by have /eqP -> : Ordinal ci == 1.
Qed.

Lemma elimI3 (P' : 'I_3 -> Prop): P' 0 -> P' 1 -> P' (1 + 1) -> forall i, P' i.
Proof.
move=> p0 p1 p2 [[|[|[|]]] ci] //.
    by have /eqP -> : Ordinal ci == 0.
  by have /eqP -> : Ordinal ci == 1.
by have /eqP -> : Ordinal ci == (1 + 1).
Qed.

Lemma p1p1_I2 : 
  forall (i : 'I_2), (i + 1 + 1 : 'I_2) = i.
Proof.
apply: elimI2; by apply /eqP.
Qed.

Lemma p1p11 : (1 + 1 + 1 : 'I_3) = 0.
Proof.
by apply /eqP.
Qed.

Lemma p1p1p1_I3 : 
  forall (i : 'I_3), (i + 1 + 1 + 1 : 'I_3) = i.
Proof.
apply: elimI3; by apply /eqP.
Qed.

End finite_lemmas.

Section implementation.

Variable R : realFieldType.

Variable P : finType.

Variable coords : P -> R * R.

Definition E := {ffun 'I_2 -> P}.

Definition oppos_edge (e : E) : E := 
  [ffun i : 'I_2 => e (i + 1)].

Lemma inv_oppos_edge (e : E) : (oppos_edge (oppos_edge e)) = e.
Proof.
rewrite -ffunP.
apply: elimI2; by rewrite /oppos_edge ?ffunE p1p1_I2.
Qed.

Definition T := {ffun 'I_3 -> P}.

Definition t_make (p0 p1 p2 : P) : T :=
  [ffun i : 'I_3 => 
    if val i == 0%nat then p0 else if val i == 1%nat then p1 else p2].

Hypothesis inj_triangles : 
  forall (t : T), forall (i j : 'I_3), (t i) == (t j) -> i == j.

Definition triangle_area (t : T) :=
  tr_area R (coords (t 0)) (coords (t 1)) (coords (t (1 + 1))).

Definition edges_tr (t : T) : {ffun 'I_3 -> E} :=
  [ffun i : 'I_3 => [ffun j : 'I_2 => if val j == 0%N then t i else t (i + 1)]].

Lemma inj_edges_tr :
  forall (t : T), forall (i j : 'I_3), 
    (edges_tr t i) == (edges_tr t j) -> i == j.
Proof.
move => t i j.
rewrite !ffunE=>/eqP.
rewrite -ffunP=>/(_ 0).
rewrite !ffunE=>/=/eqP.
by apply: inj_triangles.
Qed.

Definition point_in (p : P) (t : T) : bool :=
  [exists i : 'I_3, (t i) == p].

Lemma point_in_exists (p : P) (t : T) :
  (point_in p t) -> exists (i : 'I_3), (t i) = p.
Proof.
rewrite /point_in.
by apply: exists_eqP.
Qed.

Definition edge_in (e : E) (t : T) : bool :=
  [exists i : 'I_3, (edges_tr t i) == e].

Lemma edge_in_exists (e : E) (t : T) :
  (edge_in e t) -> exists (i : 'I_3), (edges_tr t i) = e.
Proof.
rewrite /edge_in.
by apply : exists_eqP.
Qed.

Lemma starter_pt_triangle_area (i : 'I_3) (t : T) :
  triangle_area t = tr_area R (coords (t i)) (coords (t (i +1))) (coords (t (i + 1 + 1))).
Proof.
move: i.
apply : elimI3; first by rewrite add0r.
  by rewrite p1p11 (inv_cycle_tr_area R).
by rewrite p1p11 add0r -(inv_cycle_tr_area R).
Qed.

Lemma triangle_area_no_dup (t : T) (i : 'I_3):
  t i = t (i + 1) -> triangle_area t = 0.
Proof.
move => abs.
by rewrite (starter_pt_triangle_area i) abs dupl_tr_area.
Qed.

Definition tr_dist (t : T) (p : P) :=
  out_circle R (coords (t 0)) (coords (t 1)) (coords (t (1 + 1))) (coords p).

Lemma starter_pt_dist (i : 'I_3) (t : T) (p : P) : 
  tr_dist t p = out_circle R (coords (t i)) (coords (t (i + 1))) (coords (t (i + 1 + 1))) (coords p).
Proof.
move: i.
apply : elimI3; first by rewrite add0r.
  by rewrite p1p11 (inv_cycle_out_circle R).
by rewrite p1p11 add0r -(inv_cycle_out_circle R).
Qed.


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
elim: tr_enum; first by[].
move => a l HR.
rewrite /find_triangle_in_list.
case_eq (p a).
  move => h0.
  move /Some_inj => h1.
  rewrite -h1.
  split; first by[].
  rewrite in_cons.
  apply /orP.
  by left.
move => npa H.
destruct HR as [H1 H2]=>//.
split; first by[].
rewrite in_cons.
apply /orP.
by right.
Qed.

Lemma unique_result (p : T -> bool) (tr_enum : list T) :
  forall (t1 : T),   
  (p t1) -> (forall (t2 : T), (t2 \in (tr_enum)) ->  t2 != t1 -> ~ (p t2)) ->
    (find_triangle_in_list p (tr_enum) = Some t1) \/ ~~ (t1 \in tr_enum).
Proof.
move => t1 h0.
elim : tr_enum; first by right; rewrite in_nil.
move => a l.
case_eq (t1 == a).
  move => a_eq_t1_bool HR.
  left.
  have -> : a = t1 by apply/eqP; rewrite eq_sym.
  by rewrite /find_triangle_in_list h0.
move => a_diff_t1_bool HR.
have a_diff_t1 : t1 != a.
    by rewrite a_diff_t1_bool.
case_eq (p a).
  move => h1 h2.
  have not_pa : ~ p a.
    apply: h2; first by rewrite in_cons eq_refl.
    by rewrite eq_sym.
  move : not_pa.
  by rewrite h1.
move => npa H.
rewrite /find_triangle_in_list npa.
have not_in (x y : T) (s : list T) : ((x == y) = false) -> ((x \in y :: s) = (x \in s)).
  move => H1.
  by rewrite in_cons H1 /=.
rewrite (not_in t1 a l a_diff_t1_bool).
apply : HR.
move => t2.
case_eq (t2 == a).
  move => t2a h1 h2.
  have ta : t2 = a.
    by apply /eqP.
  by rewrite ta npa.
move => nta.
rewrite -(not_in t2 a l nta).
by apply: H.
Qed.

Variable target_pt : P.

Definition is_separating_edge (t : T) (i : 'I_3) :=
  0 < tr_area R (coords (t i)) (coords target_pt) (coords (t (i + 1))).

Definition separating_edge_i (t : T) (i : 'I_3) :=
  if (is_separating_edge t i) then Some (edges_tr t i) 
    else if (is_separating_edge t (i + 1)) then Some (edges_tr t (i + 1))
    else if (is_separating_edge t (i + 1 + 1)) then Some (edges_tr t (i + 1 + 1))
    else None.

Definition separating_edge (t : T) :=
  separating_edge_i t 0.

Section triangulation.

Variable tr : triangulation [finType of T].

Hypothesis tr_orientation :
  forall (t : T), t \in tr -> 0 < triangle_area t.

Hypothesis tr_triangulation :
  forall (t t' : T) (i j : 'I_3),
  t \in tr -> t' \in tr -> t i == t' j -> t (i + 1) == t' (j + 1) -> t == t'.

Lemma common_points (t1 t2 : T) :
  forall (i j : 'I_3),  t1 \in tr -> t2 \in tr -> 
  t1 i = t2 (j + 1) -> t1 (i + 1) = t2 j -> ~ point_in (t2 (j + 1 + 1)) t1.
Proof.
move => i j t1_in t2_in h1 h2.
rewrite /point_in.
move /existsP => [] x.
rewrite -(subrK i x).
elim/elimI3: (x - i).
    rewrite add0r h1 => /eqP h3.
    have := tr_orientation t2_in.
    rewrite (triangle_area_no_dup h3).
    by rewrite Order.POrderTheory.ltxx.
  rewrite addrC h2 eq_sym -[X in (_ == t2 X)]addr0 -p1p11 !addrA=> /eqP h3. 
  have := tr_orientation t2_in.
  rewrite (triangle_area_no_dup h3).
  by rewrite Order.POrderTheory.ltxx.
rewrite addrC addrA => /eqP h3.
have := tr_orientation t1_in.
rewrite (starter_pt_triangle_area i) h1 h2 h3 -(inv_cycle_tr_area R) 
  (flipr_tr_area R) -(starter_pt_triangle_area j) oppr_gt0.
rewrite Order.POrderTheory.lt_gtF; first by[].
by apply: (tr_orientation t2_in).
Qed.

Lemma unique_edge :
  forall (t : T) (e : E), (t \in tr) -> (edge_in e t) -> 
    forall (t' : T), (t' \in tr) -> t' != t -> ~ (edge_in e t').
Proof.
move => t e t_in.
rewrite /edge_in.
move /existsP => [] i.
move /eqP => h1.
move => t' t'_in h2.
move /existsP => [] j.
move /eqP.
rewrite -h1 /edges_tr !ffunE.
move /ffunP => H.
move : (H 0).
rewrite !ffunE /=.
move: (H 1).
rewrite !ffunE /=.
move /eqP => H1.
move /eqP => H2.
have aux : t' = t.
  apply /eqP.
  by rewrite (tr_triangulation t'_in t_in H2 H1).
rewrite -aux in h2.
move : h2.
by rewrite eq_refl.
Qed.

Definition find_triangle_of_edge (e : E) : option T :=
  find_triangle_in_list (edge_in e) (enum tr).

Lemma correc_find_triangle (e : E) (t : T) :
  find_triangle_of_edge e = Some t <-> (edge_in e t) /\ (t \in tr).
Proof.
split.
  rewrite /find_triangle_of_edge.
  move=> /correc_find_triangle_in_list [] -> tenum.
  by rewrite -(set_enum tr) inE.
move => H.
destruct H as [H1 H2].
have uni_edge : forall (t' : T), (t' \in tr) -> t' != t -> ~ (edge_in e t').
  by apply: unique_edge H2 H1. 
have aux : (find_triangle_in_list (edge_in e) (enum tr) = Some t) \/ (~~ (t \in tr)).
  rewrite (_ : (t \notin tr) = (t \notin (enum tr))); last first.
    by rewrite -[in LHS](set_enum tr) inE.
  apply: unique_result => //.
  by move=> t2 t2in t2nt; apply: uni_edge=> //; rewrite -(set_enum tr) inE.
rewrite H2 /= in aux.
rewrite /find_triangle_of_edge.
by destruct aux.
Qed.

Lemma invariant_find_triangle_of_edge :
  forall (e : E) (t : T),
    find_triangle_of_edge e = Some t -> t \in tr.
Proof.
move => e t.
have aux : (edge_in e t) /\ (t \in tr) -> t \in tr.
  by move => [H1 H2].
move => h.
apply: aux.
by apply (correc_find_triangle e t).
Qed.

Lemma separating_edge_is_separating_edge :
  forall (t : T) (i : 'I_3),
  separating_edge t = Some (edges_tr t i) -> is_separating_edge t i.
Proof.
have with_i (t : T) : 
  forall (i : 'I_3),
  separating_edge_i t i = Some (edges_tr t i) -> is_separating_edge t i.
  rewrite /separating_edge_i.
  apply: elimI3.
      rewrite add0r.
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
  rewrite p1p11 add0r.
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
    rewrite add0r.
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
    rewrite add0r.
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
    by rewrite add0r.
  by rewrite p1p11 (inv_cycle_power R).
by rewrite p1p11 add0r -(inv_cycle_power R).
Qed.

End triangulation.

Section delaunay_walk.

Variable tr : triangulation [finType of T].

Hypothesis tr_orientation :
  forall (t : T), t \in tr -> 0 < triangle_area t.

Hypothesis tr_triangulation :
  forall (t t' : T) (i j : 'I_3),
  t \in tr -> t' \in tr -> t i == t' j -> t (i + 1) == t' (j + 1) -> t == t'.

Hypothesis is_Delaunay_tr :
  forall (t1 t2 : T) (i : 'I_3), t1 \in tr -> t2 \in tr ->
  ( ~ point_in (t2 i) t1) -> 0 < tr_dist t1 (t2 i).

Lemma decrease_condition :
  forall (e : E) (t t' : T), (t \in tr) -> 
  separating_edge t = Some e -> 
    find_triangle_of_edge tr (oppos_edge e) = Some t' -> walk_lt R [finType of T] triangle_measure t' t.
Proof.
move => e t1 t2 t1_tr h1 h2.
have t2_tr : t2 \in tr.
  have aux : (edge_in (oppos_edge e) t2) /\ (t2 \in tr) -> (t2 \in tr).
    move => H.
    by destruct H as [H1 H2].
  apply: aux.
  rewrite -correc_find_triangle//.
have neighbours : exists (i j : 'I_3), 
  (t1 i = t2 (j + 1)) /\ (t1 (i + 1) = t2 j) /\ 
  (is_separating_edge t1 i) /\ ~ point_in (t2 (j + 1 + 1)) t1.
  have e_in_t1: exists (i : 'I_3), edges_tr t1 i = e.
    apply: edge_in_exists.
    by apply: separating_edge_in_triangle h1.
  have oppos_e_in_t2: exists (i : 'I_3), edges_tr t2 i = oppos_edge e.
    apply: edge_in_exists.
    have aux : (edge_in (oppos_edge e) t2) /\ (t2 \in tr) -> edge_in (oppos_edge e) t2.
      move => H.
      by destruct H as [H1 H2].
    apply: aux. 
    rewrite -correc_find_triangle//.
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
    apply common_points with tr i=>//.
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

Definition walk_impl :=
  walk R [finType of E] [finType of T] edge_in tr
 oppos_edge separating_edge
  (find_triangle_of_edge tr) (correc_find_triangle tr_triangulation) triangle_measure decrease_condition.

Lemma walk_impl_result_edge :
  forall (e : E) (t : {t : T | t \in tr}),
  walk_impl t = inr e -> (exists (t1 : T), edge_in (oppos_edge e) t1) /\
    (forall (t2 : T), t2 \in tr -> ~~ edge_in e t2).
Proof.
apply: walk_result_edge.
apply: inv_oppos_edge.
apply: separating_edge_in_triangle.
Qed.

Definition target_in_impl :=
  target_in [finType of E] [finType of T] separating_edge.

Lemma walk_impl_result_triangle :
  forall (t1 : {t : T | t \in tr}) (t2 : T),
  walk_impl t1 = inl t2 -> target_in_impl t2.
Proof.
by apply: walk_result_triangle.
Qed.

End delaunay_walk.

End implementation.