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
by have /eqP -> : Ordinal ci == (1 + 1).
Qed.

Lemma I2_2_is_0 : (1 + 1 : 'I_2) = 0.
Proof.
by apply/eqP.
Qed.

Lemma I3_3_is_0 : (1 + 1 + 1 :'I_3) = 0.
Proof.
by apply/eqP.
Qed.

End finite_lemmas.

Section implementation.

Variable R : realFieldType.

Variable P : finType.

Definition E := {ffun 'I_2 -> P}.

Definition T := {ffun 'I_3 -> P}.

Variable coords : P -> R * R.

Notation tr_area := (tr_area R).

Definition triangle_area (t : T) :=
  tr_area (coords (t 0)) (coords (t 1)) (coords (t (1 + 1))).

Lemma triangle_area_invariant (t : T) :
  forall i : 'I_3,
  triangle_area t =
    tr_area (coords (t i)) (coords (t (i + 1))) (coords (t (i + 1 + 1))).
Proof.
apply: elimI3; first by[].
  by rewrite inv_cycle_tr_area subrr.
by rewrite -inv_cycle_tr_area I3_3_is_0 add0r.
Qed.

Variable target_pt : P.

Notation power := (power R).

Definition triangle_dist (t : T) (p : P) :=
  power (coords (t 0)) (coords (t 1)) (coords (t (1 + 1))) (coords p).

Lemma triangle_dist_invariant (t : T) (p : P) :
  forall i : 'I_3,
  triangle_dist t p =
    power (coords (t i)) (coords (t (i + 1))) (coords (t (i + 1 + 1))) (coords p).
Proof.
apply: elimI3; first by[].
  by rewrite inv_cycle_power addrN.
by rewrite -inv_cycle_power I3_3_is_0 add0r.
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
by apply: elimI2; rewrite /opposite_edge ?ffunE I2_2_is_0 ?add0r.
Qed.

Definition is_separating_edge (t : T) (i : 'I_3) :=
  0 < tr_area (coords (t i)) (coords target_pt) (coords (t (i + 1))).

Definition separating_edge_i (t : T) (i : 'I_3) :=
  if (is_separating_edge t i) then Some (edges_tr t i) 
    else if (is_separating_edge t (i + 1)) then Some (edges_tr t (i + 1))
    else if (is_separating_edge t (i - 1)) then Some (edges_tr t (i + 1 + 1))
    else None.

Definition separating_edge (t : T) : option E :=
  separating_edge_i t 0.

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

Definition orientation (tr : triangulation_) :=
  [forall t : T, (t \in tr) ==> (0 < triangle_area t)].

Definition is_triangulation (tr : triangulation_) :=
  [forall t : T, forall t' : T, forall i : 'I_3, forall j : 'I_3,
  (t \in tr) ==> (t' \in tr) ==> (t i == t' j) ==> (t (i + 1) == t' (j + 1)) ==>
    (t == t')].

Definition is_tr (tr : triangulation_) : bool :=
  (orientation tr) &&
  (is_triangulation tr).

Notation triangulation := (triangulation [finType of T] is_tr).

Lemma injective_triangles :
  forall (tr : triangulation) (t : T) (i j : 'I_3),
  t \in (proj1_sig tr) -> t i = t j -> i = j.
Proof.
move=> [tr_ p_tr] t i j/= t_in_tr_.
move: p_tr.
rewrite/is_tr/orientation=>/andP[]/forallP/(_ t)/implyP/(_ t_in_tr_).
rewrite (triangle_area_invariant t i)=> area _ ti_tj.
move: area; rewrite ti_tj -(subrK i j).
elim/elimI3 : (j - i); first by rewrite add0r.
  by rewrite addrC dupl_tr_area lt_irreflexive.
by rewrite addrC addrA flipr_tr_area dupl_tr_area oppr0 lt_irreflexive.
Qed.

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

Fixpoint find_in_list {T : Type} (p : T -> bool) (tr_enum : list T) :option T :=
  match tr_enum with
  | nil => None
  | t :: tail => if (p t) then Some t else find_in_list p tail
  end.

Definition find_triangle_of_edge (tr : triangulation) (e : E) : option T :=
  find_in_list (edge_in e) (enum (proj1_sig tr)).

Lemma correct_find_in_list (p : T -> bool) (l : list T) (t : T) :
  find_in_list p l = Some t -> (p t) /\ (t \in l).
Proof.
elim : l=>[//|t0 l H].
rewrite/find_in_list.
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
    (t \in l /\ find_in_list p l = Some t) \/ t \notin l.
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
  rewrite /find_in_list.
  case: ifP; last by move=> _; apply: h4.
  move=> h5.
  rewrite (h2 t')=>//.
  by rewrite in_cons; apply/orP; left.
move=> h3.
case_eq (t == t')=>[/eqP <-|h4].
  left; split; first by rewrite in_cons; apply/orP; left.
  rewrite/find_in_list.
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
  by apply: correct_find_in_list.
case=> H1 H2.
case: (@unique_result_find_triangle_in_list
              (fun t0 => (edge_in e t0)) (enum tr) t).
      by [].
    move: p_tr H1.
    rewrite/is_tr/is_triangulation/edge_in/edges_tr=>
              /andP[_ /forallP/= triangulation_tr].
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
rewrite/is_tr/orientation=>
    /andP[]/forallP/= oriented _.
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
      rewrite addrA -triangle_area_invariant.
      by move:(oriented t)=>/implyP/(_ t_in_tr_).
    rewrite -eq1 -eq2 addrA -[X in _ < tr_area _ _ (coords (t' X))]addr0
              -I3_3_is_0 !addrA -triangle_area_invariant.
    by move: (oriented t')=>/implyP/(_ t'_in_tr_).
  move: sep_edge_t_e.
  rewrite/separating_edge/separating_edge_i -edge_t_i_e.
  case: ifP=>[H[]|_].
    rewrite/edges_tr !ffunE -ffunP=>/(_ 0).
    rewrite !ffunE=>/=h.
    by rewrite -(@injective_triangles tr t 0 i t_in_tr_ h).
  case: ifP=>[H[]|_].
    rewrite add0r/edges_tr !ffunE -ffunP=>/(_ 0).
    rewrite !ffunE=>/=h.
    by rewrite -(@injective_triangles tr t 1 i t_in_tr_ h).
  case: ifP=>[H[]|//].
  rewrite /edges_tr !ffunE -ffunP=>/(_ 0).
  rewrite !ffunE add0r=>/=h.
  by rewrite -(@injective_triangles tr t (1 + 1) i t_in_tr_ h).
have not_in : ~ point_in (t' (j + 1 + 1)) t.
  rewrite/point_in=>/existsP/=[i0]/eqP.
  rewrite -(subrK i i0) addrC.
  elim/elimI3: (i0 - i).
      rewrite addr0 -eq2=>h.
      move:(@injective_triangles tr t' (j + 1) (j + 1 + 1) t'_in_tr_ h).
      rewrite -{1}(addr0 (j + 1))=> H.
      by move: (addrI (j + 1) H).
    rewrite -eq1=>h.
    move:(@injective_triangles tr t' j (j + 1 + 1) t'_in_tr_ h).
    rewrite -{1}(addr0 j) -addrA=> H.
    by move: (addrI j H).
  rewrite addrA=>h.
  move:(oriented t)=>/implyP/(_ t_in_tr_).
  rewrite (triangle_area_invariant t i) -eq1 -eq2 h.
  rewrite inv_cycle_tr_area inv_cycle_tr_area flipr_tr_area
          -triangle_area_invariant oppr_gt0=> area_t'.
  apply: Bool.diff_false_true.
  rewrite -(@lt_asym _ _ (triangle_area t') 0).
  apply/andP.
  split; first by[].
  by move:(oriented t')=>/implyP/(_ t'_in_tr_).
move:(delaunay t_in_tr_ t'_in_tr_ not_in).
rewrite (triangle_dist_invariant _ _ i)/power.
move: (oriented t)=>/implyP/(_ t_in_tr_).
rewrite (triangle_area_invariant _ i)=>h.
rewrite -(pmulr_lgt0 _ h) -mulrA [X in 0 < _ * X]mulrC mulfV;
  first by rewrite mulr1 !addrA.
apply/negP=>/eqP H.
by move: h; rewrite H lt_irreflexive.
Qed.

Definition delaunay_walk :=
  walk _ _ _ relT_trans relT_irreflexive _ _ _ _ _ correction_find_triangle
          tr decrease_condition.

Lemma delaunay_walk_result_edge :
  forall (e : E) (t : {t : T | t \in (proj1_sig tr)}),
  delaunay_walk t = inr e -> (exists (t1 : T), edge_in (opposite_edge e) t1) /\
    (forall (t2 : T), t2 \in tr_ -> ~~ edge_in e t2).
Proof.
apply: walk_result_edge.
  exact:involution_opposite_edge.
apply: separating_edge_in_triangle.
Qed.

Definition target_in_impl :=
  target_in [finType of E] [finType of T] separating_edge.

Lemma walk_impl_result_triangle :
  forall (t1 : {t : T | t \in (proj1_sig tr)}) (t2 : T),
  delaunay_walk t1 = inl t2 -> target_in_impl t2.
Proof.
by apply: walk_result_triangle.
Qed.

End delaunay_walk.

Section general_walk.

Definition delaunay_criterion (t1 t2 : T) :=
  [forall i : 'I_3, ( ~~ point_in (t2 i) t1) ==> (0 < triangle_dist t1 (t2 i))].

Hypothesis test : forall t : triangulation_, is_tr t.

Definition not_in_edge (t : T) (e : E) : 'I_3 :=
  if t 0 == e 0 then 1 + 1 else if t 0 == e 1 then 1 else 0. 

Notation find_triangle_inspect := (find_triangle_inspect _ _ is_tr
                                                find_triangle_of_edge).

Notation delaunay_inspect := (delaunay_inspect _ delaunay_criterion).

Definition flip_t (e : E) (tr : triangulation) (t : T) : T :=
  if find_triangle_of_edge tr (opposite_edge e) is Some t' then
    if delaunay_criterion t t' then t else
    let i := not_in_edge t e in
    let j := not_in_edge t' (opposite_edge e) in
    [ffun i0 : 'I_3 => if i0 == i then t i else
                        if i0 == i + 1 then t' j else t' (j + 1)]
  else t.

Definition flip_tr_ (e : E) (tr : triangulation) (t t' : T) :=
  (flip_t e tr t) |: ((flip_t e tr t')|: (proj1_sig tr)) :\ t :\t'.

Lemma correct_flip_t :
  forall (e : E) (tr : triangulation) (t t' : T),
    find_triangle_of_edge tr e = Some t ->
    find_triangle_of_edge tr (opposite_edge e) = Some t' ->
    delaunay_criterion t t' = false ->
    is_tr (flip_tr_ e tr t t').
Proof.
move=> e [tr'_ is_tr_tr'_] t t' find_e_t find_oppe_t' not_del.
rewrite/flip_tr_/=/flip_t find_oppe_t' not_del/=.
rewrite/is_tr/orientation/is_triangulation.
apply/andP; split.
  apply/forallP=>/= t1.
  apply/implyP=>/setU1P[eqt1|/setD1P[t1_not_t']/setD1P[t1_not_t]/setU1P[]].
      rewrite eqt1/triangle_area.

Search "set" "U" "1" outside finmap.



Definition flip_tr (e : E) (tr : triangulation) :=
  if find_triangle_inspect tr e is exist (Some t1) eq1 then
    if find_triangle_inspect tr (opposite_edge e) is exist (Some t2) eq2 then
      if delaunay_inspect t1 t2 is exist false eq3 then
        exist _ (flip_tr_ e tr t1 t2) (correct_flip_t eq1 eq2 eq3)
      else tr
    else tr
  else tr.

End general_walk.

End implementation.