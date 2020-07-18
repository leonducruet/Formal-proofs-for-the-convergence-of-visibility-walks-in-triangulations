From mathcomp Require Import all_ssreflect all_algebra finmap.
From Equations Require Import Equations.

Require Import wf_finset.

Import GRing.Theory Num.Theory Order.Theory.

Open Scope ring_scope.

Section parameters.

Variable R : realDomainType.

Variable P : finType.

Variable E : finType. 

Variable T : finType.

Variable edge_in : E -> T -> bool.

Definition triangulation := {set T}.

Variable is_Delaunay : triangulation -> bool.

Section walk_parameters.

Variable tr : triangulation.

Variable target_point : P.

Hypothesis tr_is_Delaunay : is_Delaunay tr.

Variable opposite_edge : E -> E.

Hypothesis involution_opposite_edge : 
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
  find_triangle_of_edge e = Some t <-> (edge_in e t) /\ (t \in enum tr).

Lemma invariant_find_triangle_of_edge : forall (e : E) (t : T),
   find_triangle_of_edge e = Some t -> t \in enum tr.
Proof.
move => e t.
have aux : (edge_in e t) /\ (t \in enum tr) -> t \in enum tr.
  by move => [H1 H2].
move => h.
apply: aux.
by apply (correction_find_triangle e t).
Qed.

Lemma edge_in_find_triangle_of_edge : forall (e : E) (t : T),
   t \in enum tr -> 
   (edge_in e t -> find_triangle_of_edge e = Some t).
Proof.
move => e t h1 h2.
by apply (correction_find_triangle e t).
Qed.

Variable triangle_measure : T -> R.

Definition walk_lt (t1 t2 : T) : Prop := 
  triangle_measure t1 < triangle_measure t2.

Definition walk_lt' (t1 t2 : {t : T | t \in enum tr}) : Prop := 
  triangle_measure (proj1_sig t1) < triangle_measure (proj1_sig t2).

Lemma walk_lt_trans : 
  forall (t1 t2 t3 : T),
  walk_lt t1 t2 -> walk_lt t2 t3 -> walk_lt t1 t3.
Proof.
rewrite /walk_lt.
move => t1 t2 t3.
by apply: lt_trans.
Qed.

Lemma walk_lt_anti_refl :
  forall (t : T), ~ (walk_lt t t).
Proof.
rewrite /walk_lt.
move => t.
by rewrite ltxx.
Qed.

Lemma walk_lt_well_founded : well_founded walk_lt.
Proof.
apply: wf_rel.
apply: walk_lt_trans.
by apply: walk_lt_anti_refl.
Qed.

Instance walk_lt_wf : WellFounded walk_lt.
Proof.
rewrite /WellFounded; apply walk_lt_well_founded.
Qed.

Instance walk'_lt_wf : WellFounded walk_lt'.
Proof.
rewrite /WellFounded.
apply (Inverse_Image.wf_inverse_image _ T walk_lt).
apply walk_lt_well_founded.
Qed.

Hypothesis decrease_condition :
  forall (e : E) (t t' : T),
  t \in enum tr ->
  separating_edge t = Some e -> 
    find_triangle_of_edge (opposite_edge e) = Some t' -> walk_lt t' t.

Definition separating_inspect (t : T) :
  {e' : option E | separating_edge t = e'} :=
 exist _ (separating_edge t) erefl.

Definition find_triangle_inspect (e : E) :
  {t' : option T | find_triangle_of_edge e = t'} :=
  exist _ (find_triangle_of_edge e) erefl.

Equations walk (current_triangle : {t : T | t \in enum tr})
   : T + E by wf (current_triangle) walk_lt' :=
walk current_triangle with
    separating_inspect (proj1_sig current_triangle) => { 
     | exist _ (Some edge) eq1
       with find_triangle_inspect (opposite_edge edge) => {
          | exist _ (Some new_triangle) eq2 :=
            walk
              (exist _ new_triangle
                 (invariant_find_triangle_of_edge _ _ eq2));
          | exist _ None eq2 := inr (opposite_edge edge)};
     | exist _ None eq1 := inl (proj1_sig (current_triangle))}.
Next Obligation.
rewrite /walk_lt' /=; apply: (decrease_condition edge) => //.
Qed.

Lemma walk_result_edge :
  forall (e : E) (t : {t : T | t \in enum tr}),
  walk t = inr e -> (exists (t1 : T), edge_in (opposite_edge e) t1) /\
    (forall (t2 : T), t2 \in enum tr -> ~~ edge_in e t2).
Proof.
move => e t h; funelim (walk t); rewrite h in Heqcall.
    by [].
  move: Heqcall.
  by apply: (H e1).
move: Heqcall=> [heq].
split.
  rewrite -heq involution_opposite_edge.
  exists (proj1_sig current_triangle).
  by apply: separating_edge_in_triangle e.
move => t2 h2.
apply /negP => /(edge_in_find_triangle_of_edge e1 t2 h2).
by rewrite -heq e0.
Qed.

Lemma walk_result_triangle :
  forall (t1 : {t : T | t \in enum tr}) (t2 : T),
  walk t1 = inl t2 -> target_in t2.
Proof.
move => t1 t2 h; funelim (walk t1); rewrite h in Heqcall.
    move: Heqcall => [heq].
    rewrite -heq /target_in.
    apply/eqP.
    by apply: e.
  by apply: H Heqcall.
by [].
Qed.

End walk_parameters.

End parameters.
