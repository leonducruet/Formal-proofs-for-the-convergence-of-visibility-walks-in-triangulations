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
  find_triangle_of_edge e = Some t <-> edge_in e t.

Variable triangle_measure : T -> R.

Hypothesis positive_measure :
  forall (t : T), triangle_measure t >= 0.

Definition walk_lt (t1 t2 : T) : Prop := 
  triangle_measure t1 < triangle_measure t2.

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

Instance walk_lt_wf : WellFounded walk_lt.
Proof.
rewrite /WellFounded.
apply: wf_rel.
apply: walk_lt_trans.
by apply: walk_lt_anti_refl.
Qed.

Hypothesis decrease_condition :
  forall (e : E) (t t' : T),
  separating_edge t = Some e -> 
    find_triangle_of_edge (opposite_edge e) = Some t' -> walk_lt t' t.

Definition separating_inspect (t : T) :
  {e' : option E | separating_edge t = e'} :=
 exist _ (separating_edge t) erefl.

Definition find_triangle_inspect (e : E) :
  {t' : option T | find_triangle_of_edge e = t'} :=
  exist _ (find_triangle_of_edge e) erefl.

Equations walk (current_triangle : T) 
   : T + E by wf (current_triangle) walk_lt :=
walk current_triangle with
    separating_inspect current_triangle => { 
     | exist _ (Some edge) eq1
       with find_triangle_inspect (opposite_edge edge) => {
          | exist _ (Some new_triangle) eq2 :=
             walk new_triangle;
          | exist _ None eq2 := inr (opposite_edge edge)};
     | exist _ None eq1 := inl (current_triangle)}.

Lemma walk_result_edge :
  forall (e : E) (t : T),
  walk t = inr e -> (exists (t1 : T), edge_in (opposite_edge e) t1) /\
    (forall (t2 : T), ~~ edge_in e t2).
Proof.
move => e t h; funelim (walk t); rewrite h in Heqcall.
    by [].
  move: Heqcall.
  by apply: (H e1).
move: Heqcall=> [heq].
split.
  rewrite -heq involution_opposite_edge.
  exists current_triangle.
  by apply: separating_edge_in_triangle e.
move => t2.
apply /negP => /correction_find_triangle.
by rewrite -heq e0.
Qed.

Lemma walk_result_triangle :
  forall (t1 t2 : T),
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
