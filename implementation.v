From mathcomp Require Import all_ssreflect all_algebra.

Require Import determinant.
Require Import parameters.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Num.Theory GRing.Theory Order.POrderTheory Order.TotalTheory.

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

Notation out_circle := (out_circle R).

Hypothesis not_concyclic :
  forall A B C D : P,
  tr_area (coords A) (coords B) (coords C) != 0 ->
  out_circle (coords A) (coords B) (coords C) (coords D) = 0 ->
  D \in [set A; B; C].

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

Variable intersection : T -> T -> option (R * R).

Definition contains (t : T) (p : R * R) : bool :=
  [forall i : 'I_3, tr_area (coords (t i)) (coords (t (i+1))) p > 0].

Hypothesis correct_intersection :
  forall (t1 t2 : T),
  (intersection t1 t2 = None) <->
  (forall p, ~ (contains t1 p /\ contains t2 p)).

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

Definition empty_intersections (tr : triangulation_) :=
  [forall t1 : T, forall t2 : T, (t1 \in tr) ==> (t2 \in tr) ==>
    (t1 != t2) ==> (intersection t1 t2 == None)].

Definition point_in (p : P) (t : T) : bool :=
  [exists i : 'I_3, (t i) == p].

Definition delaunay_criterion (t1 t2 : T) :=
  [forall i : 'I_3, ( ~~ point_in (t2 i) t1) ==> (0 < triangle_dist t1 (t2 i))].

Definition not_in_edge (t : T) (e : E) : 'I_3 :=
  if t 0 == e 0 then 1 + 1 else if t 0 == e 1 then 1 else 0.

Fixpoint find_in_list {T : Type} (p : T -> bool) (tr_enum : list T) :option T :=
  match tr_enum with
  | nil => None
  | t :: tail => if (p t) then Some t else find_in_list p tail
  end.

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

Definition find_triangle_of_edge (tr : triangulation_) (e : E) : option T :=
  find_in_list (edge_in e) (enum tr).

Definition flip_t_ (e : E) (tr : triangulation_) (t : T) : T :=
  if find_triangle_of_edge tr (opposite_edge e) is Some t' then
    if delaunay_criterion t t' then t else
    let i := not_in_edge t e in
    let j := not_in_edge t' (opposite_edge e) in
    [ffun i0 : 'I_3 => if i0 == 0 then t i else
                        if i0 == 1 then t' j else e 1]
  else t.

Definition flip_tr_ (e : E) (tr : triangulation_) (t t' : T) :=
  (flip_t_ e tr t) |: ((flip_t_ (opposite_edge e) tr t')|: tr) :\ t :\t'.

Definition is_tr (tr : triangulation_) : bool :=
  (orientation tr) &&
  (empty_intersections tr).

Notation triangulation := (triangulation [finType of T] is_tr).

Definition flip_t (e : E) (tr : triangulation) := (flip_t_ e (proj1_sig tr)).

Lemma oriented_triangles (tr : triangulation) (t : T) :
  t \in (proj1_sig tr) -> 0 < triangle_area t.
Proof.
move=>t_in_tr.
by move: (proj2_sig tr)=>/andP[]/forallP/(_ t)/implyP/(_ t_in_tr).
Qed.

Lemma empty_tr (tr : triangulation) (t1 t2 : T) :
  t1 \in (proj1_sig tr) -> t2 \in (proj1_sig tr) -> t1 <> t2 ->
    intersection t1 t2 = None.
Proof.
move=>t1_in_tr t2_in_tr/eqP t1_not_t2.
by move: (proj2_sig tr)=>/andP[_]/forallP/(_ t1)/forallP/(_ t2)/implyP
                        /(_ t1_in_tr)/implyP/(_ t2_in_tr)/implyP/(_ t1_not_t2)/eqP.
Qed.

Axiom common_edge_intersection :
  forall (t1 t2 : T) (tr : triangulation) (i j : 'I_3),
    t1 \in (proj1_sig tr) -> t2 \in (proj1_sig tr) -> t1 i = t2 j ->
      t1 (i+1) = t2 (j+1) -> t1 (i+1+1) != t2 (j+1+1) ->
      (exists p, intersection t1 t2 = Some p).

Notation middle := (middle R).

Definition middle_t (t : T) :=
  middle (coords (t 0)) (coords (t 1)) (coords (t (1+1))).

Lemma invariant_middle (t : T) (i : 'I_3) :
  middle_t t = middle (coords (t i)) (coords (t (i+1))) (coords (t (i+1+1))).
Proof.
move: i.
apply: elimI3;
rewrite ?I3_3_is_0 ?add0r/middle_t/middle;
move: (coords (t 0)) (coords (t 1)) (coords (t (1+1)))=>[a0 a1][b0 b1][c0 c1]//.
  by rewrite -addrA addrC -(addrA a1) (addrC a1).
by rewrite addrC addrA (addrC _ c1) addrA.
Qed.

Lemma contains_middle :
  forall (tr : triangulation) (t : T),
  t \in (proj1_sig tr) -> contains t (middle_t t).
Proof.
move=>tr t t_in_tr.
apply/forallP=>i.
rewrite (invariant_middle _ i).
rewrite -middle_area mulr_gt0//.
  by rewrite -triangle_area_invariant (oriented_triangles t_in_tr).
rewrite invr_gt0 ltr_spsaddl?ltr01//.
by rewrite ltr_spsaddl?ltr01.
Qed.

Lemma uniq_triangles (tr : triangulation) (t t' : T) (i j : 'I_3) :
  t \in (proj1_sig tr) ->
  t' \in (proj1_sig tr) ->
  t i = t' j ->
  t (i+1) = t' (j+1) ->
  t (i+1+1) = t' (j+1+1) ->
  t = t'.
Proof.
move=>t_in_tr t'_in_tr ti tip tipp.
apply: (@contra_not_eq _ (intersection t t' = None)).
  move=>/eqP ?.
  exact: (@empty_tr tr).
move=>/correct_intersection/(_ (middle_t t))[].
split.
  exact: (contains_middle t_in_tr).
rewrite (invariant_middle _ i) ti tip tipp -invariant_middle.
exact: (contains_middle t'_in_tr).
Qed.

Lemma injective_triangles :
  forall (tr : triangulation) (t : T) (i j : 'I_3),
  t \in (proj1_sig tr) -> t i = t j -> i = j.
Proof.
move=> tr t i j t_in_tr.
move: (oriented_triangles t_in_tr).
rewrite (triangle_area_invariant t i)=> area ti_tj.
move: area; rewrite ti_tj -(subrK i j).
elim/elimI3 : (j - i); first by rewrite add0r.
  by rewrite addrC dupl_tr_area lt_irreflexive.
by rewrite addrC addrA flipr_tr_area dupl_tr_area oppr0 lt_irreflexive.
Qed.

Lemma uniq_tr (tr : triangulation) (t t' : T) (i j : 'I_3) :
  t \in (proj1_sig tr) -> t' \in (proj1_sig tr) ->
  t i = t' j -> t (i+1) = t' (j+1) -> t = t'.
Proof.
move=>t_in_tr t'_in_tr eq1 eq2.
apply: (uniq_triangles t_in_tr t'_in_tr eq1 eq2).
apply/eqP.
apply/negP=>/negP h.
move: (common_edge_intersection t_in_tr t'_in_tr eq1 eq2 h)=>[p].
rewrite (empty_tr t_in_tr t'_in_tr)//.
rewrite -ffunP.
move: eq1 eq2 h.
rewrite -(addrNK j i).
elim/elimI3: (i-j); rewrite ?add0r -?(addrA 1) -?(addrA j 1) ?(addrC j) ?addrA
                              ?I3_3_is_0 ?add0r.
    by move=>_ _/eqP h/(_ (1+1+j)).
  move=>h _ _/(_ j).
  rewrite -h=>/(injective_triangles t_in_tr)/eqP.
  by rewrite eq_sym -subr_eq0 -addrA subrr.
move=>_ h _/(_ j).
rewrite h=>/(injective_triangles t'_in_tr)/eqP.
by rewrite -subr_eq0 -addrA subrr.
Qed.

Notation tr_measure := (tr_measure R).

Definition triangulation_measure (t : T) :=
  tr_measure (coords (t 0)) (coords (t 1)) (coords (t (1 + 1))).

Lemma triangulation_measure_invariant (t : T) (i : 'I_3) :
  triangulation_measure t =
  tr_measure (coords (t i)) (coords (t (i+1))) (coords (t (i+1+1))).
Proof.
elim/elimI3: i; first by[].
  by rewrite I3_3_is_0 inv_cycle_measure.
by rewrite I3_3_is_0 -inv_cycle_measure.
Qed.

Definition measure_triangulation (tr : triangulation) :=
  \sum_(t in (proj1_sig tr)) triangulation_measure t.

Definition rel_tr (tr tr' : triangulation) :=
  measure_triangulation tr > measure_triangulation tr'.

Lemma rel_tr_trans : transitive rel_tr.
Proof.
move=> y x z.
rewrite/rel_tr=>yx zy.
apply: (lt_trans zy yx).
Qed.

Lemma rel_tr_irreflexive : irreflexive rel_tr.
Proof.
move=> x.
rewrite/rel_tr.
exact: lt_irreflexive.
Qed.

Lemma rel_anti : antisymmetric rel_tr.
Proof.
move=>x y p.
apply: (@contraPeq _ (rel_tr x y && rel_tr y x)); last by[].
move=>_; apply/negP.
rewrite Bool.negb_andb/rel_tr -!leNgt.
exact: le_total.
Qed.

Lemma correction_find_triangle :
  forall (tr : triangulation) (e : E) (t : T),
  find_triangle_of_edge (proj1_sig tr) e = Some t <->
    (edge_in e t) /\ (t \in (proj1_sig tr)).
Proof.
move=> tr e t/=.
rewrite/find_triangle_of_edge/=.
split.
  move=> H.
  rewrite -(set_enum (proj1_sig tr)) inE.
  by apply: correct_find_in_list.
case=> H1 H2.
case: (@unique_result_find_triangle_in_list
              (fun t0 => (edge_in e t0)) (enum (proj1_sig tr)) t).
      by [].
    move: H1=>/existsP[i].
    rewrite ffunE=>/eqP <- t2 h/existsP[i'].
    rewrite ffunE=>/eqP.
    rewrite -ffunP=> H1.
    move: (H1 0) (H1 1).
    rewrite !ffunE=>/=eqtt2 eqtt2'.
    move: (@uniq_tr tr t2 t i' i).
    by rewrite -{1}(set_enum (proj1_sig tr)) inE=>
                  /(_ h)/(_ H2)/(_ eqtt2)/(_ eqtt2').
  by case.
by move:H2; rewrite -{1}(set_enum (proj1_sig tr)) inE=> ->.
Qed.

Section delaunay_walk.

Variable tr_ : triangulation_.

Hypothesis tr_is_triangulation : is_tr tr_.

Definition tr : triangulation := (exist _ tr_ tr_is_triangulation).

Hypothesis delaunay :
  forall (t1 t2 : T) (i : 'I_3), t1 \in tr_ -> t2 \in tr_ ->
  ( ~ point_in (t2 i) t1) -> 0 < triangle_dist t1 (t2 i).

Notation walk_lt := (walk_lt [finType of T] relT is_tr tr).

Notation power_decrease := (power_decrease R).

Lemma decrease_condition_ :
  forall (e : E) (t t' : T),
  (forall i : 'I_3, (~ point_in (t' i) t) -> 0 < triangle_dist t (t' i)) ->
  t \in tr_ ->
  separating_edge t = Some e -> 
    find_triangle_of_edge tr_ (opposite_edge e) = Some t' -> relT t' t.
Proof.
move=> e t t' del t_in_tr_ sep_edge_t_e find_tr_e_t'.
rewrite/relT/triangle_measure -subr_gt0.
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
      exact: (@oriented_triangles tr t t_in_tr_).
    rewrite -eq1 -eq2 addrA -[X in _ < tr_area _ _ (coords (t' X))]addr0
              -I3_3_is_0 !addrA -triangle_area_invariant.
    exact: (@oriented_triangles tr t' t'_in_tr_).
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
  move:(@oriented_triangles tr t t_in_tr_).
  rewrite (triangle_area_invariant t i) -eq1 -eq2 h.
  rewrite inv_cycle_tr_area inv_cycle_tr_area flipr_tr_area
          -triangle_area_invariant oppr_gt0=> area_t'.
  apply: Bool.diff_false_true.
  rewrite -(@lt_asym _ _ (triangle_area t') 0).
  apply/andP.
  split; first by[].
  exact: (@oriented_triangles tr t').
move:(del (j+1+1) not_in).
rewrite (triangle_dist_invariant _ _ i)/power.
move: (@oriented_triangles tr t t_in_tr_).
rewrite (triangle_area_invariant _ i)=>h.
rewrite -(pmulr_lgt0 _ h) -mulrA [X in 0 < _ * X]mulrC mulfV;
  first by rewrite mulr1 !addrA.
apply/negP=>/eqP H.
by move: h; rewrite H lt_irreflexive.
Qed.

Lemma decrease_condition :
  forall (e : E) (t t' : T),
  t \in tr_ ->
  separating_edge t = Some e -> 
    find_triangle_of_edge tr_ (opposite_edge e) = Some t' -> relT t' t.
Proof.
move=>e t t' t_in_tr sep find.
apply: (@decrease_condition_ e t t')=>//.
move=>i.
apply: delaunay; first by[].
by move: (iffLR (correction_find_triangle tr (opposite_edge e) t') find)=>[].
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

Lemma not_in_edge_invariant (tr : triangulation) (t : T) (e : E) (i : 'I_3) :
  t \in (proj1_sig tr) ->
  t i = e 0 -> t (i + 1) = e 1 ->
  not_in_edge t e = i + 1 + 1.
Proof.
rewrite/not_in_edge=>t_in_tr.
elim/elimI3 : i=>[<- _|<-<-|<-<-].
    by rewrite eq_refl add0r.
  case: ifP=>[/eqP/(injective_triangles t_in_tr)<-|_].
    by rewrite !addr0.
  case: ifP=>[/eqP/(injective_triangles t_in_tr)<-|_].
    by rewrite add0r.
  by rewrite I3_3_is_0.
case: ifP=>[/eqP/(injective_triangles t_in_tr)eq011|_].
  by rewrite -!eq011.
by rewrite I3_3_is_0 eq_refl add0r.
Qed.

Lemma oriented_flip (t t' : T) (tr : triangulation) (i j : 'I_3) :
  t i = t' (j + 1) -> t (i + 1) = t' j ->
  t \in (proj1_sig tr) -> t' \in (proj1_sig tr) ->
  delaunay_criterion t t' = false ->
  0 < tr_area (coords (t' j)) (coords (t (i + 1 + 1))) (coords (t' (j + 1 + 1))).
Proof.
move=>tit'jp tipt'j t_in_tr t'_in_tr/forallP not_del.
apply: (ccw_flip _ _ _ (coords (t' (j + 1)))).
    rewrite -tipt'j -tit'jp inv_cycle_tr_area -triangle_area_invariant.
    exact: (oriented_triangles t_in_tr).
  rewrite -triangle_area_invariant.
  exact: (oriented_triangles t'_in_tr).
rewrite -tipt'j -tit'jp leNgt.
apply/negP=>H.
move: not_del; apply=>i0.
apply/implyP.
rewrite -(addrNK j i0).
elim/elimI3: (i0 - j).
    rewrite add0r=>/existsP[].
    exists (i + 1).
    by apply/eqP.
  rewrite addrC=>/existsP[].
  exists i.
  by apply/eqP.
rewrite addrC addrA (triangle_dist_invariant _ _ i) pmulr_rgt0 ?invr_gt0.
  rewrite -triangle_area_invariant=>_.
  exact: (oriented_triangles t_in_tr).
by rewrite -inv_cycle_out_circle.
Qed.

Lemma delaunay_flip (t t' : T) (tr : triangulation) (i j : 'I_3) :
  t \in (proj1_sig tr) ->
  t' \in (proj1_sig tr) ->
  t i = t' (j + 1) -> t (i + 1) = t' j ->
  delaunay_criterion t t' -> delaunay_criterion t' t.
Proof.
move=>t_in_tr t'_in_tr tit'jp tipt'j/forallP del.
apply/forallP=>/= i0.
apply/implyP=>/negP.
rewrite -(addrNK i i0) addrC.
elim/elimI3: (i0 - i).
    rewrite addr0 tit'jp=>-[].
    by apply/existsP; exists (j+1).
  rewrite tipt'j=>-[].
  by apply/existsP; exists j.
rewrite (triangle_dist_invariant _ _ j)/power=> not_in.
rewrite pmulr_rgt0 ?invr_gt0.
  rewrite -triangle_area_invariant.
  exact: (oriented_triangles t'_in_tr).
rewrite -flip_out_circle -tit'jp -tipt'j addrA -(@pmulr_rgt0 _ (
    (tr_area (coords (t i)) (coords (t (i+1))) (coords (t (i+1+1))))^-1));
    first last.
  rewrite invr_gt0 -triangle_area_invariant.
  exact: (oriented_triangles t_in_tr).
rewrite mulrC inv_cycle_out_circle -/(power _ _ _ _) -triangle_dist_invariant.
move: (del (j + 1 + 1))=>/implyP.
apply.
apply/existsP=>-[i1].
rewrite -(addrNK i i1) addrC.
elim/elimI3: (i1 - i); rewrite ?addr0=>/eqP h.
    apply: not_in.
    move: (@uniq_tr tr t t' i (j+1+1) t_in_tr t'_in_tr h).
    rewrite -!addrA (addrA 1) I3_3_is_0 addr0=>/(_ tipt'j) ->.
    by apply/existsP; exists (i + (1+1)).
  apply: not_in.
  move: (uniq_tr t_in_tr t'_in_tr tit'jp h)=>->.
  by apply/existsP; exists (i + (1+1)).
apply: not_in.
rewrite h.
by apply/existsP; exists (j+1+1).
Qed.

Lemma delaunay_eq (t t' : T) (tr : triangulation) (i j : 'I_3) :
  t \in (proj1_sig tr) ->
  t' \in (proj1_sig tr) ->
  t i = t' (j + 1) -> t (i + 1) = t' j ->
  delaunay_criterion t t' = delaunay_criterion t' t.
Proof.
move=> t_in_tr t'_in_tr tit'jp tipt'j.
apply: Bool.eq_true_iff_eq.
split=>del.
  exact: (delaunay_flip t_in_tr t'_in_tr tit'jp tipt'j del).
exact: (@delaunay_flip t' t tr j i).
Qed.

Lemma different_neightboors (t1 t2 : T) (tr : triangulation) (e : E) :
  find_triangle_of_edge (proj1_sig tr) e = Some t1 ->
  find_triangle_of_edge (proj1_sig tr) (opposite_edge e) = Some t2 ->
  t1 <> t2.
Proof.
move=>/correction_find_triangle[]/existsP[i]/eqP.
rewrite -ffunP=>coords_t1.
move: (coords_t1 0) (coords_t1 1).
rewrite !ffunE=>/=t1i t1ip t1_in_tr/correction_find_triangle[]/existsP[j]/eqP.
rewrite -ffunP=>coords_t2.
move: (coords_t2 0) (coords_t2 1).
rewrite !ffunE add0r I2_2_is_0=>/=t2j t2jp t2_in_tr eq.
move: t2j.
rewrite -eq -t1ip=>/(injective_triangles t1_in_tr).
move: t2jp.
rewrite -eq -t1i=>/(injective_triangles t1_in_tr)<-/eqP.
by rewrite eq_sym addrC addrA addrC addrA -subr_eq0 -addrA subrr.
Qed.

Axiom contains_flip :
  forall (tr : triangulation) (t1 t2 : T) (e : E) (p : R * R),
  find_triangle_of_edge (proj1_sig tr) e = Some t1 ->
  find_triangle_of_edge (proj1_sig tr) (opposite_edge e) = Some t2 ->
  delaunay_criterion t1 t2 = false ->
  contains (flip_t e tr t1) p ->
  contains t1 p \/ contains t2 p.

Lemma flip_empty (tr : triangulation) (e : E) (t t' : T) :
  find_triangle_of_edge (proj1_sig tr) e = Some t ->
  find_triangle_of_edge (proj1_sig tr) (opposite_edge e) = Some t' ->
  delaunay_criterion t t' = false ->
  empty_intersections (flip_tr_ e (proj1_sig tr) t t').
Proof.
move=> find_e_t find_oppe_t' not_del.
rewrite /flip_tr_/={1}/is_tr/orientation/uniq_triangles.
move: (iffLR (correction_find_triangle _ _ _) find_e_t)=>/=[].
rewrite/edge_in=>/existsP[i]/eqP.
rewrite/edges_tr ffunE -ffunP=>/= e_x t_in_tr.
move: (iffLR (correction_find_triangle _ _ _) find_oppe_t')=>/=[].
rewrite/edge_in=>/existsP[j]/eqP.
rewrite/edges_tr ffunE -ffunP=>/= oppe_x t'_in_tr.
move: (e_x 0) (e_x 1) (oppe_x 0) (oppe_x 1).
rewrite 2!ffunE=>/=tie0 tipe1.
rewrite ffunE=>/=t'joppe0.
rewrite ffunE=>/=t'jpoppe1.
rewrite/opposite_edge !ffunE  add0r I2_2_is_0 in t'joppe0 t'jpoppe1.
move:(tie0); rewrite -t'jpoppe1=>tit'jp.
move:(tipe1); rewrite -t'joppe0=>tipt'j.
apply/forallP=>t1.
apply/forallP=>t2.
rewrite/flip_t_ involution_opposite_edge find_e_t find_oppe_t'
      -(delaunay_eq t_in_tr t'_in_tr tit'jp tipt'j) not_del
      (not_in_edge_invariant t_in_tr tie0 tipe1)
      (@not_in_edge_invariant _ _ (opposite_edge e) j t'_in_tr)
      !ffunE ?I2_2_is_0//.
apply/implyP=>/setU1P[eq1|/setD1P[t1_not_t']
            /setD1P[t1_not_t]/setU1P[eq1|t1_in_tr]];
apply/implyP=>/setU1P[eq2|/setD1P[t2_not_t']
            /setD1P[t2_not_t]/setU1P[eq2|t2_in_tr]];
apply/implyP=>/eqP t1_not_t2; apply/eqP.
                exfalso; apply: t1_not_t2.
                by rewrite eq1 eq2.
              apply/eqP; apply/negP=>/negP/eqP/correct_intersection[p]
                [/forallP p_in_t1/forallP p_in_t2].
              move: (p_in_t1 0) (p_in_t2 0).
              rewrite eq1 eq2 !ffunE/= -inv_cycle_tr_area flipr_tr_area
                      oppr_gt0=>/ltW.
              by rewrite leNgt=>/Bool.negb_true_iff->.
            apply: (iffRL (@correct_intersection t1 t2))=>p[p_in_t1 p_in_t2].
            move: (@contains_flip _ _ _ _ p find_e_t find_oppe_t' not_del).
            rewrite/flip_t/flip_t_ find_oppe_t' not_del
                (not_in_edge_invariant t_in_tr tie0 tipe1)
                (@not_in_edge_invariant _ _ (opposite_edge e) j t'_in_tr)
                  ?ffunE ?I2_2_is_0//-eq1=>/(_ p_in_t1)[]contains_p.
              by move: t2_not_t (empty_tr t2_in_tr t_in_tr)=>/eqP h/(_ h)
                          /correct_intersection/(_ p)[].
            by move: t2_not_t' (empty_tr t2_in_tr t'_in_tr)=>/eqP h/(_ h)
                          /correct_intersection/(_ p)[].
          apply/correct_intersection=>p[/forallP/(_ 0)].
          rewrite eq1 !ffunE/= =>contains_t1/forallP/(_ 0).
          rewrite eq2 !ffunE/= flipr_tr_area inv_cycle_tr_area oppr_gt0 ltNge=>
                    /negP[].
          by apply/ltW.
        move: t1_not_t2.
        by rewrite eq1 eq2.
      apply/correct_intersection=>p[p_in_t1 p_in_t2].
      move: (@contains_flip _ _ t _ p find_oppe_t').
      rewrite involution_opposite_edge=>/(_ find_e_t).
      move: (not_del).
      rewrite (delaunay_eq t_in_tr t'_in_tr tit'jp tipt'j)=>->/(_ erefl).
      rewrite /flip_t/flip_t_ involution_opposite_edge find_e_t
              -(delaunay_eq t_in_tr t'_in_tr tit'jp tipt'j) not_del
              (@not_in_edge_invariant _ _ (opposite_edge e) j t'_in_tr)
              ?ffunE ?I2_2_is_0//(not_in_edge_invariant t_in_tr tie0 tipe1)-eq1=>
              /(_ p_in_t1)[]contains_p.
        by move: t2_not_t' (empty_tr t2_in_tr t'_in_tr)=>/eqP h/(_ h)
                          /correct_intersection/(_ p)[].
      by move: t2_not_t (empty_tr t2_in_tr t_in_tr)=>/eqP h/(_ h)
                        /correct_intersection/(_ p)[].
    apply/correct_intersection=>p[p_in_t1 p_in_t2].
    move: (@contains_flip _ _ _ _ p find_e_t find_oppe_t' not_del).
    rewrite/flip_t/flip_t_ find_oppe_t' not_del
          (not_in_edge_invariant t_in_tr tie0 tipe1)
          (@not_in_edge_invariant _ _ (opposite_edge e) j t'_in_tr)?ffunE
          ?I2_2_is_0//-eq2=>/(_ p_in_t2)[]contains_p.
      by move: t1_not_t (empty_tr t1_in_tr t_in_tr)=>/eqP h/(_ h)
                  /correct_intersection/(_ p)[].
    by move: t1_not_t' (empty_tr t1_in_tr t'_in_tr)=>/eqP h/(_ h)
                  /correct_intersection/(_ p)[].
  apply/correct_intersection=>p[p_in_t1 p_in_t2].
  move: (@contains_flip _ _ t _ p find_oppe_t').
  rewrite/flip_t/flip_t_ involution_opposite_edge find_e_t
         -(delaunay_eq t_in_tr t'_in_tr tit'jp tipt'j) not_del
         (not_in_edge_invariant t_in_tr tie0 tipe1)
          (@not_in_edge_invariant _ _ (opposite_edge e) j t'_in_tr)?ffunE
          ?I2_2_is_0//-eq2=>/(_ erefl)/(_ erefl)/(_ p_in_t2)[]contains_p.
    by move: t1_not_t' (empty_tr t1_in_tr t'_in_tr)=>/eqP h/(_ h)
              /correct_intersection/(_ p)[].
  by move: t1_not_t (empty_tr t1_in_tr t_in_tr)=>/eqP h/(_ h)
              /correct_intersection/(_ p)[].
exact: (@empty_tr tr).
Qed.

Lemma correct_flip_t :
  forall (e : E) (tr : triangulation) (t t' : T),
    find_triangle_of_edge (proj1_sig tr) e = Some t ->
    find_triangle_of_edge (proj1_sig tr) (opposite_edge e) = Some t' ->
    delaunay_criterion t t' = false ->
    is_tr (flip_tr_ e (proj1_sig tr) t t').
Proof.
move=> e tr t t' find_e_t find_oppe_t' not_del.
rewrite /flip_tr_/={1}/is_tr/orientation/uniq_triangles.
move: (iffLR (correction_find_triangle _ _ _) find_e_t)=>/=[].
rewrite/edge_in=>/existsP[i]/eqP.
rewrite/edges_tr ffunE -ffunP=>/= e_x t_in_tr.
move: (iffLR (correction_find_triangle _ _ _) find_oppe_t')=>/=[].
rewrite/edge_in=>/existsP[j]/eqP.
rewrite/edges_tr ffunE -ffunP=>/= oppe_x t'_in_tr.
move: (e_x 0) (e_x 1) (oppe_x 0) (oppe_x 1).
rewrite 2!ffunE=>/=tie0 tipe1.
rewrite ffunE=>/=t'joppe0.
rewrite ffunE=>/=t'jpoppe1.
rewrite/opposite_edge !ffunE  add0r I2_2_is_0 in t'joppe0 t'jpoppe1.
move:(tie0); rewrite -t'jpoppe1=>tit'jp.
move:(tipe1); rewrite -t'joppe0=>tipt'j.
apply/andP; split.
  apply/forallP=>/= t1.
  rewrite/flip_t_ find_oppe_t' not_del involution_opposite_edge find_e_t
        -(delaunay_eq t_in_tr t'_in_tr tit'jp tipt'j) not_del !ffunE I2_2_is_0
        (not_in_edge_invariant t_in_tr tie0 tipe1)
        (@not_in_edge_invariant tr t' (opposite_edge e) j t'_in_tr); first last.
      by rewrite ffunE I2_2_is_0.
    by rewrite ffunE.
  apply/implyP=>/setU1P[->|/setD1P[/negP t1_not_t']
                    /setD1P[/negP t1_not_t]/setU1P[|t1_in_tr]].
      rewrite/triangle_area !ffunE/= inv_cycle_tr_area -t'joppe0.
      exact: (@oriented_flip _ _ tr).
    move=>->.
    rewrite/triangle_area !ffunE/=-tie0 inv_cycle_tr_area.
    apply: (@oriented_flip _ _ tr)=>//.
    by rewrite -(delaunay_eq t_in_tr t'_in_tr tit'jp tipt'j).
  exact : (oriented_triangles t1_in_tr)=>/(_ erefl)/(_ erefl)
            /(_ p_in_t2)[]contains_p.
exact: flip_empty.
Qed.

Notation find_triangle_inspect := (find_triangle_inspect _ _ is_tr
          find_triangle_of_edge).

Notation delaunay_inspect := (delaunay_inspect _ delaunay_criterion).

Definition flip_tr (e : E) (tr : triangulation) :=
  if find_triangle_inspect tr e is @exist _ _ (Some t1) eq1 then
    if find_triangle_inspect tr (opposite_edge e) is
           exist (Some t2) eq2 then
      if delaunay_inspect t1 t2 is exist false eq3 then
        exist _ (flip_tr_ e (proj1_sig tr) t1 t2)
            (@correct_flip_t e tr t1 t2 eq1 eq2 eq3)
      else tr
    else tr
  else tr.

Notation tr_T := (tr_T _ is_tr).

Lemma correct_flip :
  forall (e : E) (tr : triangulation) (t : T),
  t \in (proj1_sig tr) ->
  edge_in e t ->
  flip_t e tr t \in
        proj1_sig (flip_tr e tr).
Proof.
move=>e tr t t_in_tr e_in_t.
rewrite/flip_tr.
case: find_triangle_inspect=>-[t1|] find_e.
  move: (iffRL (correction_find_triangle tr e t) (conj e_in_t t_in_tr)).
  rewrite find_e=>-[eqt1_t].
  case: find_triangle_inspect=>-[t2|] find_oppe.
    move: (iffLR (correction_find_triangle tr (opposite_edge e) t2) find_oppe)=>
              [/existsP[i2]/eqP].
    rewrite/edges_tr-ffunP !ffunE=>coords_t2 t2_in_tr.
    case: delaunay_inspect=>-[del|not_del].
      by rewrite -eqt1_t/flip_t/flip_t_ find_oppe del eqt1_t.
    rewrite/flip_tr_.
    apply/setU1P; left.
    by rewrite eqt1_t.
  by rewrite/flip_t/flip_t_ find_oppe.
move: (iffRL (correction_find_triangle tr e t) (conj e_in_t t_in_tr)).
by rewrite find_e.
Qed.

Lemma flip_not_in_tr (tr : triangulation) (e : E) (t1 t2 : T) :
  find_triangle_of_edge (proj1_sig tr) e = Some t1 ->
  find_triangle_of_edge (proj1_sig tr) (opposite_edge e) = Some t2 ->
  ~~ delaunay_criterion t1 t2 ->
  flip_t e tr t1 \notin (proj1_sig tr).
Proof.
move=>find_e find_oppe/Bool.negb_true_iff not_del.
move: (find_e) (find_oppe)=>/correction_find_triangle[]/existsP[i]/eqP.
rewrite ffunE-ffunP=>coords_t1 t1_in_tr/correction_find_triangle[]/existsP[j]/eqP.
rewrite ffunE-ffunP=>coords_t2 t2_in_tr.
move: (coords_t1 0) (coords_t1 1) (coords_t2 0) (coords_t2 1).
rewrite !ffunE/= I2_2_is_0 add0r=>t1i t1ip t2j t2jp.
move: (t1i) (t1ip).
rewrite -t2j -t2jp=>t1_t2p t1p_t2.
set ft := flip_t _ _ _.
apply/negP=>ft_in_tr.
move: (@uniq_tr tr t1 ft (i+1) (1+1) t1_in_tr ft_in_tr).
rewrite/ft/flip_t/flip_t_ find_oppe not_del !ffunE
        (not_in_edge_invariant t1_in_tr t1i t1ip)=>/=/(_ t1ip)/(_ erefl).
rewrite -ffunP (@not_in_edge_invariant _ _ (opposite_edge e) j t2_in_tr);
          first last=>[||/(_ i)].
    by rewrite ffunE I2_2_is_0.
  by rewrite ffunE.
move: coords_t1 t1i t1ip t1_t2p t1p_t2=>_.
elim/elimI3: i; rewrite ffunE/= ?add0r ?I3_3_is_0.
    by move=>_ _ _ _/(injective_triangles t1_in_tr).
  move=>_ _ -> _/(injective_triangles t2_in_tr)/eqP.
  by rewrite eq_sym addrC -subr_eq0 -addrA subrr.
by move=> _ <- _ _/(injective_triangles t1_in_tr).
Qed.


Lemma non_delaunay_decrease :
  forall (t1 t2 : T) (tr : triangulation) (e : E),
  ~~ delaunay_criterion t1 t2 -> t1 \in (proj1_sig tr) -> t2 \in (proj1_sig tr) ->
  edge_in e t1 ->
  edge_in (opposite_edge e) t2 ->
  rel_tr (flip_tr e tr) tr.
Proof.
move=>t1 t2 tr e not_del t1_in_tr t2_in_tr e_in_t1 oppe_in_t2.
move: (e_in_t1) (oppe_in_t2)=>/existsP[i]/eqP.
rewrite -ffunP ffunE=>coords_t1/existsP[j]/eqP.
rewrite/opposite_edge -ffunP !ffunE=>coords_t2.
move:(coords_t1 0) (coords_t1 1) (coords_t2 0) (coords_t2 1).
rewrite !ffunE add0r I2_2_is_0=>/=t1i t1ip t2j t2jp.
move: (t1i) (t1ip).
rewrite -t2j -t2jp=>t1i_t2 t1ip_t2.
rewrite/rel_tr/measure_triangulation/flip_tr.
case: find_triangle_inspect=>-[t|] find_e.
  move: (iffRL (correction_find_triangle tr e t1) (conj e_in_t1 t1_in_tr)).
  rewrite find_e=>-[eq1].
  case: find_triangle_inspect=>-[t'|] find_oppe.
    move: (iffRL (correction_find_triangle tr (opposite_edge e) t2)
        (conj oppe_in_t2 t2_in_tr)).
    rewrite find_oppe=>-[eq2].
    case: delaunay_inspect=>-[del|ndel].
      by move: not_del; rewrite -eq1-eq2 del.
    rewrite/flip_tr_ big_setU1/=.
      rewrite -(addrNK (triangulation_measure t') (triangulation_measure _)) -addrA
              -big_setD1/=.
        rewrite -(addrNK (triangulation_measure t) (_-_))-addrA-big_setD1/=.
          rewrite big_setU1/=.
            rewrite-!/(measure_triangulation _)/flip_t_ find_oppe
              involution_opposite_edge find_e eq1 eq2
              -(delaunay_eq t1_in_tr t2_in_tr t1i_t2 t1ip_t2)
              (not_in_edge_invariant t1_in_tr t1i t1ip)
              (@not_in_edge_invariant tr t2 (opposite_edge e) j t2_in_tr)
              !ffunE ?I2_2_is_0=>//.
            rewrite -eq1 -eq2 ndel (triangulation_measure_invariant t i)
              (triangulation_measure_invariant t' j)/triangulation_measure !ffunE/=.
            rewrite -opprB addrA (addrC (-(_+_))) -opprB -(addrA _ (-(_ - _)))
              (opprD (_ _ _ (_ (e 1)))) !addrA opprK.
            rewrite eq1 eq2 t1i t1ip t2j t2jp-(addrA _ (-_))
              (addrC (-_ (_ (t1 _)) _ _)) addrA -3!addrA (addrC (-_) (-_)) 3!addrA.
            rewrite -(inv_cycle_measure _ (_ (e 0)))
                (inv_cycle_measure _ (_ (t2 _))) measure_sub_out_circle
                  flip_out_circle -t1i -t1ip.
            rewrite ltr_addr oppr_gt0 lt_def.
            apply/andP; split.
              apply/negP; rewrite eq_sym; apply/negP.
              move: (oriented_triangles t1_in_tr).
              rewrite (triangle_area_invariant t1 i)=>/lt0r_neq0
                /(@not_concyclic _ _ _ (t2 (j+1+1)))/contra_not_neq; apply.
              rewrite !inE=>/orP[/orP[]|]/eqP eq.
                  move: (@injective_triangles _ _ (j+1+1) (j+1) t2_in_tr).
                  rewrite eq t1i_t2=>/(_ erefl)/eqP.
                  by rewrite addrC-subr_eq0-addrA subrr.
                move: (@injective_triangles _ _ (j+1+1) j t2_in_tr).
                rewrite eq t1ip_t2=>/(_ erefl)/eqP.
                by rewrite addrC addrA addrC addrA -subr_eq0 -(addrA (1+1)) subrr.
              move: (oriented_triangles t2_in_tr).
              rewrite (triangle_area_invariant t2 j) -t1i_t2 -t1ip_t2 eq
                -inv_cycle_tr_area flipr_tr_area -triangle_area_invariant oppr_gt0
                ltNge.
              by move: (oriented_triangles t1_in_tr)=>/ltW->.
            rewrite leNgt; apply/negP=>h.
            move: not_del=>/negP[].
            apply/forallP=>j0.
            rewrite -(addrNK j j0) addrC.
            elim/elimI3: (j0 - j); apply/implyP=>/negP.
                rewrite addr0=>-[].
                by apply/existsP; exists (i+1); rewrite t1ip_t2.
              by case; apply/existsP; exists i; rewrite t1i_t2.
            rewrite (triangle_dist_invariant _ _ i)/power addrA pmulr_rgt0=>[_|//].
            rewrite invr_gt0 -triangle_area_invariant.
            exact: (oriented_triangles t1_in_tr).
          rewrite eq2; apply/negP=>flip_in_tr.
          move: (@flip_not_in_tr _ _ _ t1 find_oppe).
          rewrite involution_opposite_edge eq2 -{1}eq1=>/(_ find_e).
          rewrite -(delaunay_eq t1_in_tr t2_in_tr t1i_t2 t1ip_t2)=>/(_ not_del)
                                  /negP[].
          exact: flip_in_tr.
        apply/setU1P; right.
        by rewrite eq1.
      apply/setD1P; split.
        apply/negP=>/eqP.
        rewrite eq1 eq2=> eq.
        move: (oriented_triangles t1_in_tr).
        rewrite (triangle_area_invariant _ i) t1i_t2 t1ip_t2 -eq
                -(addrNK j (i+1+1)).
        elim/elimI3: (i+1+1-j).
            by rewrite add0r -inv_cycle_tr_area dupl_tr_area lt_irreflexive.
          by rewrite addrC inv_cycle_tr_area dupl_tr_area lt_irreflexive.
        rewrite (addrC (1+1)) addrA -inv_cycle_tr_area flipr_tr_area oppr_gt0
                -triangle_area_invariant ltNge.
        by move: (oriented_triangles t2_in_tr)=>/ltW->.
      apply/setU1P; right.
      by rewrite eq2.
    apply/negP=>/setD1P[flip_not_t']/setD1P[flip_not_t]/setU1P[].
      rewrite/flip_t_ find_oppe involution_opposite_edge find_e eq1 eq2
            -(delaunay_eq t1_in_tr t2_in_tr t1i_t2 t1ip_t2) -eq1-eq2 ndel-ffunP
            =>/(_ (1+1)).
      rewrite !ffunE/= I2_2_is_0=> eq.
      move: (@injective_triangles _ _ i (i+1) t1_in_tr).
      rewrite t1i t1ip eq=>/(_ erefl)/eqP.
      by rewrite eq_sym addrC -subr_eq0-addrA subrr.
    move=>flip_in_tr.
    move: (flip_not_in_tr find_e find_oppe).
    rewrite eq1 eq2=>/(_ not_del)/negP[].
    by rewrite/flip_t -eq1.
  move: (conj oppe_in_t2 t2_in_tr)=>/correction_find_triangle.
  by rewrite find_oppe.
move: (conj e_in_t1 t1_in_tr)=>/correction_find_triangle.
by rewrite find_e.
Qed.

Lemma delaunay_decrease :
  forall (t1 t2 : T) (e : E) (tr : triangulation),
  delaunay_criterion t1 t2 -> t1 \in (proj1_sig tr) ->
  separating_edge t1 = Some e ->
  find_triangle_of_edge (proj1_sig tr) (opposite_edge e) = Some t2 ->
  relT t2 t1.
Proof.
move=>t1 t2 e tr/forallP del t1_in_tr sep find_oppe.
apply: (@decrease_condition_ (proj1_sig tr) (proj2_sig tr) e t1 t2)=>//.
move=>i/negP not_point_in.
by move: (del i)=>/implyP/(_ not_point_in).
Qed.

Definition general_walk := walk2 _ _ _ relT_trans relT_irreflexive _ _ _
                            separating_edge_in_triangle _ _ rel_tr_trans
                            rel_tr_irreflexive _ correction_find_triangle _ _ _
                            correct_flip non_delaunay_decrease delaunay_decrease.

Lemma general_walk_result_edge :
  forall (e : E) (result_tr : triangulation)
    (start : {tr_T : triangulation * T | tr_T.2 \in (proj1_sig tr_T.1) }),
  general_walk start = (result_tr, inr e) ->
  (exists (t1 : T), edge_in (opposite_edge e) t1) /\
    (forall (t2 : T), t2 \in (proj1_sig result_tr) -> ~~ edge_in e t2).
Proof.
apply: walk2_result_edge.
exact: involution_opposite_edge.
Qed.

Notation target_in := (target_in _ _ separating_edge).

Lemma general_walk_result_triangle :
  forall (start : {tr_T : triangulation * T | tr_T.2 \in (proj1_sig tr_T.1) })
    (result_tr : triangulation) (t2 : T),
  general_walk start = (result_tr, inl t2) ->
  target_in t2.
Proof.
apply: walk2_result_triangle.
Qed.

End general_walk.

End implementation.