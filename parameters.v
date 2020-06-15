From mathcomp Require Import all_ssreflect.
From Equations Require Import Equations.

Section parameters.

  Variable P : finType.
  
  Variable E : finType. 

  Variable T : finType.

  Definition triangulation := {set T}.
  
  Variable is_Delaunay : triangulation -> bool.

  Variable tr : triangulation.

  Variable target_point : P.

  Section hypothesis.

    Hypothesis tr_is_Delaunay : is_Delaunay tr.

    Variable separating_edge : T -> option E.

    Variable opposite_edge : E -> E.

    Variable find_triangle_of_edge : E -> option T.

    Variable walk_lt : T -> T -> Prop.

    Hypothesis walk_lt_wf : WellFounded walk_lt.

    Hypothesis  decrease_condition :
      forall (e : E) (t t' : T),
        separating_edge t = Some e -> 
          find_triangle_of_edge (opposite_edge e) = Some t' ->
            walk_lt t' t.

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
    
    End hypothesis.

End parameters.

