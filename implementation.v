From mathcomp Require Import all_ssreflect all_algebra.

Require Import determinant.
Require Import parameters.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Num.Theory GRing.Theory Order.POrderTheory.

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
by have /eqP -> : Ordinal ci == (-1).
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

Definition E := {ffun 'I_2 -> P}.

Definition T := {ffun 'I_3 -> P}.

Definition t_make (p0 p1 p2 : P) : T :=
  [ffun i : 'I_3 => 
    if val i == 0%nat then p0 else if val i == 1%nat then p1 else p2].

Variable coords : P -> R * R.

Notation tr_area := (tr_area R).

Definition triangle_area (t : T) :=
  tr_area (coords (t 0)) (coords (t 1)) (coords (t (-1))).

Lemma triangle_area_invariant (t : T) :
  forall i : 'I_3,
  triangle_area t = tr_area (coords (t i)) (coords (t (i + 1))) (coords (t (i - 1))).
Proof.
apply: elimI3; first by[].
  by rewrite inv_cycle_tr_area subrr.
by rewrite -inv_cycle_tr_area subrr -addrA subrr addr0.
Qed.

Variable target_pt : P.

Notation power := (power R).

Definition triangle_dist (t : T) (p : P) :=
  power (coords (t 0)) (coords (t 1)) (coords (t (-1))) (coords p).

Lemma triangle_dist_invariant (t : T) (p : P) :
  forall i : 'I_3,
  triangle_dist t p =
    power (coords (t i)) (coords (t (i + 1))) (coords (t (i - 1))) (coords p).
Proof.
apply: elimI3; first by[].
  by rewrite inv_cycle_power addrN.
by rewrite -inv_cycle_power subrr -addrA subrr addr0.
Qed.

Definition triangle_measure (t : T) :=
  triangle_dist t target_pt.

Definition relT (t t' : T) := triangle_measure t < triangle_measure t'.

Lemma relT_trans : transitive relT.
Proof.
move=> y x z.
rewrite/relT.
exact: lt_trans.
Qed.

Lemma relT_irreflexive : irreflexive relT.
Proof.
move=> x.
rewrite/relT.
exact: lt_irreflexive.
Qed.

Definition edges_tr (t : T) : {ffun 'I_3 -> E} :=
  [ffun i : 'I_3 => [ffun j : 'I_2 => if val j == 0%N then t i else t (i + 1)]].

Definition edge_in (e : E) (t : T) : bool :=
  [exists i : 'I_3, (edges_tr t i) == e].

Definition opposite_edge (e : E) : E := 
  [ffun i : 'I_2 => e (i + 1)].

Lemma involution_opposite_edge : involutive opposite_edge.
Proof.
move=> e.
rewrite -ffunP.
by apply: elimI2; rewrite /opposite_edge ?ffunE p1p1_I2.
Qed.

Definition is_separating_edge (t : T) (i : 'I_3) :=
  0 < tr_area (coords (t i)) (coords target_pt) (coords (t (i + 1))).

Definition separating_edge_i (t : T) (i : 'I_3) :=
  if (is_separating_edge t i) then Some (edges_tr t i) 
    else if (is_separating_edge t (i + 1)) then Some (edges_tr t (i + 1))
    else if (is_separating_edge t (i - 1)) then Some (edges_tr t (i - 1))
    else None.

Definition separating_edge (t : T) : option E :=
  separating_edge_i t 0.

Lemma separating_edge_is_separating_edge (t : T) (e : E) :
  separating_edge t = Some e -> is_separating_edge t 0.
Proof.
Abort.


Lemma separating_edge_in_triangle : 
  forall (e : E) (t : T),
  separating_edge t = Some e -> edge_in e t.
Proof.
move=> e t.
rewrite/separating_edge/separating_edge_i.
case : ifP=>[_ [<-]|_].
  by rewrite /edge_in; apply/existsP; exists 0.
case: ifP=>[_ [<-]|_].
  by rewrite /edge_in; apply/existsP; exists 1.
case: ifP=>[_ [<-]|//].
by rewrite /edge_in; apply/existsP; exists (1+1).
Qed.

Notation triangulation_ := (triangulation_ [finType of T]).

(*TODO orientation -> injective;retirer injective des hypothèses et écrire lemme*)

Definition injective_triangles (tr : triangulation_) :=
  [forall t : T, forall i : 'I_3, forall j : 'I_3,
    (t \in tr) ==> ((t i) == (t j)) ==> (i == j)].

Definition orientation (tr : triangulation_) :=
  [forall t : T, (t \in tr) ==> (0 < triangle_area t)].

Definition is_triangulation (tr : triangulation_) :=
  [forall t : T, forall t' : T, forall i : 'I_3, forall j : 'I_3,
  (t \in tr) ==> (t' \in tr) ==> (t i == t' j) ==> (t (i + 1) == t' (j + 1)) ==>
    (t == t')].

Definition is_tr (tr : triangulation_) : bool :=
  (injective_triangles tr) &&
  (orientation tr) &&
  (is_triangulation tr).

Notation triangulation := (triangulation [finType of T] is_tr).

Notation tr_measure := (tr_measure R).

Definition triangulation_measure (t : T) :=
  tr_measure (coords (t 0)) (coords (t 1)) (coords (t (1 + 1))).

Definition measure_triangulation (tr : triangulation) :=
  \sum_(t <- enum (proj1_sig tr)) triangulation_measure t.

Definition rel_tr (tr tr' : triangulation) :=
  measure_triangulation tr < measure_triangulation tr'.

Lemma rel_tr_trans : transitive rel_tr.
Proof.
move=> y x z.
rewrite/rel_tr.
exact: lt_trans.
Qed.

Lemma rel_tr_irreflexive : irreflexive rel_tr.
Proof.
move=> x.
rewrite/rel_tr.
exact: lt_irreflexive.
Qed.

Fixpoint find_triangle_in_list (p : T -> bool) (tr_enum : list T) :option T :=
  match tr_enum with
  | nil => None
  | t :: tail => if (p t) then Some t else find_triangle_in_list p tail
  end.

Definition find_triangle_of_edge (tr : triangulation) (e : E) : option T :=
  find_triangle_in_list (edge_in e) (enum (proj1_sig tr)).

Lemma correct_find_triangle_in_list (p : T -> bool) (l : list T) (t : T) :
  find_triangle_in_list p l = Some t -> (p t) /\ (t \in l).
Proof.
elim : l=>[//|t0 l H].
rewrite/find_triangle_in_list.
case: ifP=> [h [<-]|h1 h2].
  split; first by[].
  rewrite in_cons.
  by apply/orP; left.
move: (H h2)=>[].
split; first by[].
by rewrite in_cons; apply/orP; right.
Qed.

Lemma unique_result_find_triangle_in_list (p : T -> bool) (l : list T) (t : T) :
  p t -> (forall t2 : T, t2 \in l -> p t2 -> t2 = t) ->
    (t \in l /\ find_triangle_in_list p l = Some t) \/ t \notin l.
Proof.
move=> h1.
elim: l; first by right.
move=> t' l Hind h2.
case: Hind.
    move=> t2 h3 h4.
    apply: h2; last by[].
    rewrite in_cons.
    by apply/orP; right.
  move=>[h3 h4].
  left.
  split; first by rewrite in_cons; apply/orP; right.
  rewrite /find_triangle_in_list.
  case: ifP; last by move=> _; apply: h4.
  move=> h5.
  rewrite (h2 t')=>//.
  by rewrite in_cons; apply/orP; left.
move=> h3.
case_eq (t == t')=>[/eqP <-|h4].
  left; split; first by rewrite in_cons; apply/orP; left.
  rewrite/find_triangle_in_list.
  case:ifP; last by rewrite h1.
  by[].
right.
rewrite in_cons h4.
by apply/norP.
Qed.

Lemma correction_find_triangle :
  forall (tr : triangulation) (e : E) (t : T),
  find_triangle_of_edge tr e = Some t <-> (edge_in e t) /\ (t \in (proj1_sig tr)).
Proof.
move=> [tr p_tr] e t/=.
rewrite/find_triangle_of_edge/=.
split.
  move=> H.
  rewrite -(set_enum tr) inE.
  by apply: correct_find_triangle_in_list.
case=> H1 H2.
case: (@unique_result_find_triangle_in_list
              (fun t0 => (edge_in e t0)) (enum tr) t).
      by [].
    move: p_tr H1.
    rewrite/is_tr/is_triangulation/edge_in/edges_tr=>/andP[_ /forallP/= triangulation_tr].
    move=>/existsP[i].
    rewrite ffunE=>/eqP <- t2 h/existsP[i'].
    rewrite ffunE=>/eqP.
    rewrite -ffunP=> H1.
    move: (H1 0) (H1 1).
    rewrite !ffunE=>/=/eqP eqtt2 /eqP eqtt2'.
    move: (triangulation_tr t2)=>/forallP /(_ t)/forallP/(_ i')/forallP/(_ i)
            /implyP.
    by rewrite -{1}(set_enum tr) inE=>/(_ h)/implyP/(_ H2)/implyP/(_ eqtt2)
                                    /implyP/(_ eqtt2')/eqP.
  by case.
by move:H2; rewrite -{1}(set_enum tr) inE=> ->.
Qed.

Definition point_in (p : P) (t : T) : bool :=
  [exists i : 'I_3, (t i) == p].

Variable tr_ : triangulation_.

Hypothesis tr_is_triangulation : is_tr tr_.

Definition tr : triangulation := (exist _ tr_ tr_is_triangulation).

Section delaunay_walk.

Hypothesis delaunay :
  forall (t1 t2 : T) (i : 'I_3), t1 \in tr_ -> t2 \in tr_ ->
  ( ~ point_in (t2 i) t1) -> 0 < triangle_dist t1 (t2 i).

Notation walk_lt := (walk_lt [finType of T] relT is_tr tr).

Notation power_decrease := (power_decrease R).

Lemma decrease_condition :
  forall (e : E) (t t' : T),
  t \in tr_ ->
  separating_edge t = Some e -> 
    find_triangle_of_edge tr (opposite_edge e) = Some t' -> relT t' t.
Proof.
move=> e t t' t_in_tr_ sep_edge_t_e find_tr_e_t'.
rewrite/relT/triangle_measure -subr_gt0.
move:tr_is_triangulation.
rewrite/is_tr/injective_triangles/orientation=>
    /andP[]/andP[]/forallP/=inj/forallP/= oriented/forallP/= is_triang.
move:(separating_edge_in_triangle sep_edge_t_e).
rewrite/edge_in=>/existsP[i/eqP edge_t_i_e].
move:(iffLR (correction_find_triangle tr (opposite_edge e) t') find_tr_e_t')=>/=[].
rewrite/edge_in -edge_t_i_e/opposite_edge=>/existsP/=[j/eqP].
rewrite-ffunP=> common_edge t'_in_tr_.
rewrite (triangle_dist_invariant t target_pt i).
rewrite (triangle_dist_invariant t' target_pt (j+1)).
move: (common_edge 0).
rewrite !ffunE/= -!addrA subrr addr0=> eq1.
move: (common_edge 1).
rewrite !ffunE=>/= eq2.
rewrite eq1 eq2.
apply: power_decrease.
      rewrite -triangle_area_invariant.
      by move:(oriented t)=>/implyP/(_ t_in_tr_).
    rewrite -eq1 -eq2 addrA.
    have -> : (t' j = t' ((j+1)-1)) by rewrite -addrA subrr addr0.
    rewrite -triangle_area_invariant.
    by move: (oriented t')=>/implyP/(_ t'_in_tr_).
  move: sep_edge_t_e.
  rewrite/separating_edge/separating_edge_i -edge_t_i_e.
  case: ifP=>[H[]|_].
    rewrite/edges_tr !ffunE -ffunP=>/(_ 0).
    rewrite !ffunE=>/=/eqP h.
    by move:(inj t)=>/forallP/(_ 0)/forallP/(_ i)/implyP/(_ t_in_tr_)
                    /implyP/(_ h)/eqP <-.
  case: ifP=>[H[]|_].
    rewrite add0r/edges_tr !ffunE -ffunP=>/(_ 0).
    rewrite !ffunE=>/=/eqP h.
    by move:(inj t)=>/forallP/(_ 1)/forallP/(_ i)/implyP/(_ t_in_tr_)
                    /implyP/(_ h)/eqP <-.
  case: ifP=>[H[]|//].
    rewrite /edges_tr !ffunE -ffunP=>/(_ 0).
    rewrite !ffunE=>/=/eqP h.
    by move:(inj t)=>/forallP/(_ (-1))/forallP/(_ i)/implyP/(_ t_in_tr_)
                    /implyP/(_ h)/eqP <-.
have not_in : ~ point_in (t' (j - 1)) t.
  rewrite/point_in=>/existsP/=[] i0.
  rewrite -(subrK i i0).
  elim/elimI3: (i0 - i).
      rewrite add0r -eq2=> h.
      move:(inj t')=>/forallP/(_ (j+1))/forallP/(_ (j-1))/implyP/(_ t'_in_tr_)
                      /implyP/(_ h).


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

Lemma starter_pt_dist (i : 'I_3) (t : T) (p : P) : 
  tr_dist t p = out_circle R (coords (t i)) (coords (t (i + 1))) (coords (t (i + 1 + 1))) (coords p).
Proof.
move: i.
apply : elimI3; first by rewrite add0r.
  by rewrite p1p11 (inv_cycle_out_circle R).
by rewrite p1p11 add0r -(inv_cycle_out_circle R).
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



Section triangulation.



Variable tr : triangulation_ [finType of T].

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