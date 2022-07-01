From mathcomp Require Import all_ssreflect all_algebra finmap.
From Equations Require Import Equations.

Require Import wf_finset.

Open Scope ring_scope.

Section parameters.

Variable E : finType.

Variable T : finType.

Variable relT : rel T.

Hypothesis relT_trans : transitive relT.

Hypothesis relT_irrefl : irreflexive relT.

Variable edge_in : E -> T -> bool.

Variable opposite_edge : E -> E.

Hypothesis involution_opposite_edge : 
  involutive opposite_edge.

Variable separating_edge : T -> option E.

Definition target_in (t : T) :=
  separating_edge t == None.

Hypothesis separating_edge_in_triangle : 
  forall (e : E) (t : T),
  separating_edge t = Some e -> edge_in e t.

Definition triangulation_ := { set T }.

Variable is_tr : pred triangulation_.

Definition triangulation := { tr : triangulation_ | is_tr tr}.

Variable rel_tr : rel triangulation.

Hypothesis rel_tr_trans : transitive rel_tr.

Hypothesis rel_tr_irrefl : irreflexive rel_tr.

Variable find_triangle_of_edge : triangulation_ -> E -> option T.

Hypothesis correction_find_triangle :
  forall (tr : triangulation) (e : E) (t : T),
  find_triangle_of_edge (proj1_sig tr) e = Some t <->
      (edge_in e t) /\ (t \in (proj1_sig tr)).

Lemma invariant_find_triangle_of_edge : forall (tr : triangulation) (e : E) (t : T),
   find_triangle_of_edge (proj1_sig tr) e = Some t -> t \in (proj1_sig tr).
Proof.
by move => tr e t; rewrite (correction_find_triangle tr); case.
Qed.

Section delaunay_walk_parameters.

Variable tr : triangulation.

Lemma relT_well_founded : well_founded relT.
Proof.
apply: wf_rel.
  apply: relT_trans.
apply: relT_irrefl.
Qed.

Instance relT_wf : WellFounded relT.
Proof.
rewrite /WellFounded; apply relT_well_founded.
Qed.

Definition walk_lt (t1 t2 : {t : T | t \in (proj1_sig tr)}) : bool := 
  relT (proj1_sig t1) (proj1_sig t2).

Instance walk_lt_wf : WellFounded walk_lt.
Proof.
rewrite /WellFounded.
apply: (Inverse_Image.wf_inverse_image _ T relT).
apply: relT_well_founded.
Qed.

Lemma edge_in_find_triangle_of_edge : forall (e : E) (t : T),
   t \in (proj1_sig tr) -> 
   edge_in e t -> find_triangle_of_edge (proj1_sig tr) e = Some t.
Proof.
move => e t h1 h2.
by apply (correction_find_triangle _ e t).
Qed.

Hypothesis decrease_condition :
  forall (e : E) (t t' : T),
  t \in (proj1_sig tr) ->
  separating_edge t = Some e -> 
    find_triangle_of_edge (proj1_sig tr) (opposite_edge e) = Some t' -> relT t' t.

Definition separating_inspect (t : T) :
  {e' : option E | separating_edge t = e'} :=
 exist _ (separating_edge t) erefl.

Definition find_triangle_inspect (e : E) :
  {t' : option T | find_triangle_of_edge (proj1_sig tr) e = t'} :=
  exist _ (find_triangle_of_edge (proj1_sig tr) e) erefl.

Equations walk (current_triangle : {t : T | t \in (proj1_sig tr)})
   : T + E by wf current_triangle walk_lt :=
walk current_triangle with
    separating_inspect (proj1_sig current_triangle) => { 
     | exist _ (Some edge) eq1
       with find_triangle_inspect (opposite_edge edge) => {
          | exist _ (Some new_triangle) eq2 :=
            walk
              (exist _ new_triangle
                 (invariant_find_triangle_of_edge _ _ _ eq2));
          | exist _ None eq2 := inr (opposite_edge edge)};
     | exist _ None eq1 := inl (proj1_sig (current_triangle))}.
Next Obligation.
by rewrite /walk_lt /=; apply: (decrease_condition edge).
Qed.

Lemma walk_result_edge :
  forall (e : E) (t : {t : T | t \in (proj1_sig tr)}),
  walk t = inr e -> (exists (t1 : T), edge_in (opposite_edge e) t1) /\
    (forall (t2 : T), t2 \in (proj1_sig tr) -> ~~ edge_in e t2).
Proof.
move => e t h; funelim (walk t); rewrite h in Heqcall; first by[].
  move: Heqcall.
  by apply: (H e).
move: Heqcall=> [heq].
split.
  rewrite -heq involution_opposite_edge.
  exists (proj1_sig current_triangle).
  by apply: separating_edge_in_triangle eq1.
move => t2 h2.
apply /negP => /(edge_in_find_triangle_of_edge e t2 h2).
by rewrite -heq eq2.
Qed.

Lemma walk_result_triangle :
  forall (t1 : {t : T | t \in (proj1_sig tr)}) (t2 : T),
  walk t1 = inl t2 -> target_in t2.
Proof.
move => t1 t2 h; funelim (walk t1); rewrite h in Heqcall; last by[];
  last by apply: H Heqcall.
move: Heqcall => [heq].
rewrite -heq /target_in.
apply/eqP.
by apply: eq1.
Qed.

End delaunay_walk_parameters.

Section non_delaunay_walk_parameters.

Definition tr_T := {ttr : triangulation * T | ttr.2 \in (proj1_sig ttr.1)}.

Variable delaunay_criterion : T -> T -> bool.

Variable flip_t : E -> triangulation -> T -> T.

Variable flip_tr : E -> triangulation -> triangulation.

Hypothesis correct_flip :
  forall (e : E) (tr : triangulation) (t : T),
  t \in (proj1_sig tr) ->
  edge_in e t ->
  flip_t e tr t \in
        proj1_sig (flip_tr e tr).

Hypothesis non_delaunay_decrease : forall (t1 t2 : T) (tr : triangulation) (e : E),
  ~~ delaunay_criterion t1 t2 -> t1 \in (proj1_sig tr) -> t2 \in (proj1_sig tr) ->
  edge_in e t1 ->
  edge_in (opposite_edge e) t2 ->
  rel_tr (flip_tr e tr) tr.

Hypothesis delaunay_decrease : forall (t1 t2 : T) (e : E) (tr : triangulation),
  delaunay_criterion t1 t2 -> t1 \in (proj1_sig tr) ->
  separating_edge t1 = Some e ->
  find_triangle_of_edge (proj1_sig tr) (opposite_edge e) = Some t2 ->
  relT t2 t1.

Notation rel_lexi := (rel_lexi [finType of triangulation] T rel_tr relT).

Definition walk_lt2 (tt1 tt2 : tr_T) := 
  rel_lexi (proj1_sig tt1) (proj1_sig tt2).

Lemma walk_lt2_well_founded : well_founded walk_lt2.
Proof.
rewrite/walk_lt2.
apply: wf_rel=>/=.
  move=> [t1 t1_proof] [t2 t2_proof] [t3 t3_proof].
  by apply: rel_lexi_trans.
move=> [t t_proof].
by apply rel_lexi_irrefl.
Qed.

Instance walk_lt2_wf : WellFounded walk_lt2.
Proof.
rewrite /WellFounded; apply walk_lt2_well_founded.
Qed.

Definition delaunay_inspect (t1 t2 : T) :
  {b : bool | delaunay_criterion t1 t2 = b} :=
  exist _ (delaunay_criterion t1 t2) erefl.

Equations walk2 (current : tr_T) :
  triangulation * (T + E)
  by wf current walk_lt2 :=
  walk2 current with
    separating_inspect (proj1_sig current).2 => {
      | exist _ (Some edge) eq1
        with find_triangle_inspect (proj1_sig current).1 (opposite_edge edge) => {
          | exist _ (Some t2) eq2
            with delaunay_inspect (proj1_sig current).2 t2 => {
              | exist _ false _ := walk2 (exist _
              (flip_tr edge (proj1_sig current).1,
                  flip_t edge (proj1_sig current).1 (proj1_sig current).2)
                   (correct_flip _ _ _ (proj2_sig current)
                            (separating_edge_in_triangle _ _ eq1)));
              | exist _ true _ := walk2 (exist _ ((proj1_sig current).1, t2)
                                         (invariant_find_triangle_of_edge _ _ _ eq2))};
          | exist _ None _ := ((proj1_sig current).1, inr (opposite_edge edge))};
      | exist _ None _ := ((proj1_sig current).1, inl (proj1_sig current).2)}.
Next Obligation.
rewrite/walk_lt2/rel_lexi/wf_finset.rel_lexi/=.
apply/orP.
right.
apply/andP.
split; first by apply/eqP.
apply: (delaunay_decrease _ _ edge (proj1_sig current).1)=>//=.
apply: (proj2_sig current).
Qed.
Next Obligation.
move:e eq2 eq1 walk2.
case: current=> [[tr t]/= p] e eq2 eq1 walk2.
rewrite/walk_lt2/rel_lexi/wf_finset.rel_lexi/=.
apply/orP.
left.
apply: (non_delaunay_decrease t t2)=>//.
      by rewrite e.
    by rewrite (correction_find_triangle _) in eq2; move:eq2=>[].
  by apply: separating_edge_in_triangle.
by rewrite (correction_find_triangle _) in eq2; move:eq2=>[].
Qed.

Lemma walk2_result_edge :
  forall (e : E) (result_tr : triangulation) (start : tr_T),
  walk2 start = (result_tr, inr e) ->
  (exists (t1 : T), edge_in (opposite_edge e) t1) /\
    (forall (t2 : T), t2 \in (proj1_sig result_tr) -> ~~ edge_in e t2).
Proof.
move => e result_tr [[tr t]/= p] h.
funelim (walk2 (exist _ (tr, t) p)); rewrite h in Heqcall.
      by[].
    move: Heqcall=>[tr_result opposite_e0].
    split.
      exists t.
      rewrite -opposite_e0 involution_opposite_edge.
      exact: separating_edge_in_triangle.
    move=> t2 t2_in_tr.
    apply /negP => /(edge_in_find_triangle_of_edge result_tr e0 t2 t2_in_tr).
    by rewrite -opposite_e0 -tr_result e.
  exact: H.
exact: H.
Qed.

Lemma walk2_result_triangle :
  forall (start : tr_T) (result_tr : triangulation) (t2 : T),
  walk2 start = (result_tr, inl t2) ->
  target_in t2.
Proof.
move=> [[tr t] p] result_tr t2 h.
rewrite/target_in.
funelim (walk2 (exist _ (tr, t) p)); rewrite h in Heqcall=>//.
    move:Heqcall=>[eq1 eq_t_t2].
    by apply/eqP; rewrite -eq_t_t2.
  exact: (H result_tr).
apply: (H result_tr)=>//=.
Qed.

End non_delaunay_walk_parameters.

End parameters.
