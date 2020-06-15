From mathcomp Require Import all_ssreflect all_algebra.
From Equations Require Import Equations.

Section parameters.
  
  Variable R : realDomainType.

  Variable P : finType.
  
  Variable coord : P -> R ^ 2.

  Definition triangulation := {set (P ^ 3)}.
  
  Variable is_Delaunay : triangulation -> bool.

  Variable tr : triangulation.

  Definition Delaunay_tr := is_Delaunay tr.

  Variable target_point : P.

  Section hypothesis.
    
    Hypothesis tr_is_Delaunay : reflect True Delaunay_tr.

    Variable separating_edge : P ^ 3 -> option (P ^ 2).

    Variable opposite_edge : P ^ 2 -> P ^ 2.

    Variable find_triangle_of_edge : P ^ 2 -> option (P ^ 3).

    Variable walk_lt : P ^ 3 -> P ^ 3 -> Prop.

    Hypothesis walk_lt_wf : WellFounded walk_lt.

    Hypothesis  decrease_condition :
      forall e t t',
        separating_edge t = some e -> 
          find_triangle_of_edge (opposite_edge e) = some t' ->
            walk_lt t' t.

    Definition separating_inspect (t : P ^ 3) :
      {e' : option (P ^ 2) | separating_edge t = e'} :=
     exist _ (separating_edge t) erefl.

    Definition find_triangle_inspect (e : P ^ 2) :
      {t' : option (P ^ 3) | find_triangle_of_edge e = t'} :=
      exist _ (find_triangle_of_edge e) erefl.

    Equations walk (current_triangle : P ^ 3) 
       : (P ^ 3) + (P ^ 2) by wf (current_triangle) walk_lt :=
    walk current_triangle with
        separating_inspect current_triangle => { 
         | exist _ (Some edge) eq1
           with find_triangle_inspect (opposite_edge edge) => {
              | exist _ (Some new_triangle) eq2 :=
                 walk new_triangle;
              | exist _ None eq2 := inr (opposite_edge edge)};
         | exist _ None eq1 := inl (current_triangle)}.
    
    End hypothesis.

End parameters.


