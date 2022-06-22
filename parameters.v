From mathcomp Require Import all_ssreflect all_algebra finmap.
From Equations Require Import Equations.

Require Import wf_finset.

Import GRing.Theory Num.Theory Order.Theory Order.POrderTheory.
Import DefaultProdLexiOrder.

Open Scope ring_scope.

Local Open Scope order_scope.

Section parameters.

Variable R : realDomainType.

Variable E : finType. 

Variable T : Type.

Variable triangle : Finite.class_of T.

Canonical T_eq := EqType T triangle.

Canonical T_choice := ChoiceType T (Choice.mixin triangle).

Canonical T_count := CountType T triangle.

Canonical T_fin := FinType T triangle.

Variable T_o : leOrderMixin [choiceType of T].

Canonical T_orderType := POrderType tt T T_o.

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

Definition triangulation := {set T}.

Variable finite_tr : Finite.class_of triangulation.

Canonical tr_eqType := EqType triangulation finite_tr.

Canonical tr_choiceType := ChoiceType triangulation (Choice.mixin finite_tr).

Canonical tr_countType := CountType triangulation finite_tr.

Canonical tr_finType := FinType triangulation finite_tr.

Variable tr_o : leOrderMixin [choiceType of triangulation].

Canonical tr_orderType := POrderType tt triangulation tr_o.

Variable find_triangle_of_edge : E -> option T.

Hypothesis correction_find_triangle :
  forall (tr : triangulation) (e : E) (t : T),
  find_triangle_of_edge e = Some t <-> (edge_in e t) /\ (t \in tr).

Lemma invariant_find_triangle_of_edge : forall (tr : triangulation) (e : E) (t : T),
   find_triangle_of_edge e = Some t -> t \in tr.
Proof.
by move => tr e t; rewrite (correction_find_triangle tr); case.
Qed.

Section delaunay_walk_parameters.

Variable tr : triangulation.

Definition walk_lt (t1 t2 : T) := t1 < t2.

Lemma walk_lt_well_founded : well_founded walk_lt.
Proof.
apply: wf_rel.
  move=>t1 t2 t3.
  apply: lt_trans.
apply: lt_irreflexive.
Qed.

Instance walk_lt_wf : WellFounded walk_lt.
Proof.
rewrite /WellFounded; apply walk_lt_well_founded.
Qed.

Definition walk_lt' (t1 t2 : {t : T | t \in tr}) : bool := 
  (proj1_sig t1) < (proj1_sig t2).

Instance walk'_lt_wf : WellFounded walk_lt'.
Proof.
rewrite /WellFounded.
apply: (Inverse_Image.wf_inverse_image _ T walk_lt).
apply: walk_lt_well_founded.
Qed.

Lemma edge_in_find_triangle_of_edge : forall (e : E) (t : T),
   t \in tr -> 
   edge_in e t -> find_triangle_of_edge e = Some t.
Proof.
move => e t h1 h2.
by apply (correction_find_triangle tr e t).
Qed.

Hypothesis decrease_condition :
  forall (e : E) (t t' : T),
  t \in tr ->
  separating_edge t = Some e -> 
    find_triangle_of_edge (opposite_edge e) = Some t' -> walk_lt t' t.

Definition separating_inspect (t : T) :
  {e' : option E | separating_edge t = e'} :=
 exist _ (separating_edge t) erefl.

Definition find_triangle_inspect (e : E) :
  {t' : option T | find_triangle_of_edge e = t'} :=
  exist _ (find_triangle_of_edge e) erefl.

Equations walk (current_triangle : {t : T | t \in tr})
   : T + E by wf current_triangle walk_lt' :=
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
by rewrite /walk_lt' /=; apply: (decrease_condition edge).
Qed.

Lemma walk_result_edge :
  forall (e : E) (t : {t : T | t \in tr}),
  walk t = inr e -> (exists (t1 : T), edge_in (opposite_edge e) t1) /\
    (forall (t2 : T), t2 \in tr -> ~~ edge_in e t2).
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
  forall (t1 : {t : T | t \in tr}) (t2 : T),
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

Definition tr_T := {ttr : triangulation * T | ttr.2 \in ttr.1}.

Variable delaunay_criterion : T -> T -> bool.

Variable flip_tr : E -> triangulation -> triangulation.

Variable flip_t : E -> T -> T.

Hypothesis correct_flip :
  forall (e : E) (ttr : tr_T),
  let (tr, t) := proj1_sig ttr in
  flip_t e t \in flip_tr e tr.

Variable common_edge : T -> T -> option E.

Definition contains_edge (tr : triangulation) (e : E) :=
  [exists t : {t : T | t \in tr}, edge_in e (proj1_sig t)].

Hypothesis non_delaunay : forall (t1 t2 : T) (tr : triangulation) (e : E),
  ~~ delaunay_criterion t1 t2 -> t1 \in tr -> t2 \in tr ->
  common_edge t1 t2 = Some e ->
  flip_tr e tr < tr.

Hypothesis delaunay : forall (t1 t2 : T) (e : E) (tr : triangulation),
  delaunay_criterion t1 t2 -> t1 \in tr ->
  separating_edge t1 = Some e ->
  find_triangle_of_edge (opposite_edge e) = Some t2 ->
  t2 < t1.

Hypothesis correct_common_edge :
  forall (t1 t2 : T) (e : E),
  common_edge t1 t2 = Some e -> edge_in e t1 /\ edge_in (opposite_edge e) t2.

Hypothesis common_edge_alternate : forall (t1 t2 : T) (e : E),
  common_edge t1 t2 = Some e <-> common_edge t2 t1 = Some (opposite_edge e).

Lemma invariant_separating_edge (e : E) :
  forall (ttr : tr_T),
  let (tr, t) := proj1_sig ttr in
  separating_edge t = Some e -> contains_edge tr e.
Proof.
move=> [[tr t]/= ttr] h.
apply/existsP=>/=.
exists (exist _ t ttr)=>/=.
exact: separating_edge_in_triangle.
Qed.

Definition walk_lt2 (tt1 tt2 : tr_T) := 
  proj1_sig tt1 < proj1_sig tt2.

Lemma walk_lt2_well_founded : well_founded walk_lt2.
Proof.
rewrite/walk_lt2.
apply: wf_rel=>/=.
  move=> [t1 t1_proof] [t2 t2_proof] [t3 t3_proof].
  apply: lt_trans.
move=> [t t_proof].
apply lt_irreflexive.
Qed.

Instance walk_lt2_wf : WellFounded walk_lt2.
Proof.
rewrite /WellFounded; apply walk_lt2_well_founded.
Qed.

Definition delaunay_inspect (t1 t2 : T) :
  {b : bool | delaunay_criterion t1 t2 = b} :=
  exist _ (delaunay_criterion t1 t2) erefl.

Definition flip_tr_inspect (e : E) (tr : triangulation) :
  {tr' : triangulation | flip_tr e tr = tr'} :=
  exist _ (flip_tr e tr) erefl.

Equations walk2 (current : {ttr : triangulation * T | ttr.2 \in ttr.1}) :
  tr_T + {etr : triangulation * E | contains_edge etr.1 etr.2}
  by wf current walk_lt2 :=
  walk2 current with
    separating_inspect (proj1_sig current).2 => {
      | exist _ (Some edge) eq1
        with find_triangle_inspect (opposite_edge edge) => {
          | exist _ (Some t2) eq2
            with delaunay_inspect (proj1_sig current).2 t2 => {
              | exist _ false _ := walk2 (exist _
              (flip_tr edge (proj1_sig current).1, flip_t edge (proj1_sig current).2)
                                              (correct_flip edge current));
              | exist _ true _ := walk2 (exist _ ((proj1_sig current).1, t2)
                                         (invariant_find_triangle_of_edge _ _ _ eq2))};
          | exist _ None _ := inr (exist _ (tr, edge)
                                      (invariant_separating_edge _ _ eq1))};
      | exist _ None _ := inl current}.

End non_delaunay_walk_parameters.

End parameters.
