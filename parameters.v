From mathcomp Require Import all_ssreflect.
From Equations Require Import Equations.

Section parameters.

  Variable P : finType.
  
  Variable E : finType. 

  Variable T : finType.
  
  Variable edge_in_triangle : E -> T -> bool.

  Definition triangulation := {set T}.
  
  Variable is_Delaunay : triangulation -> bool.

  Variable tr : triangulation.

  Variable target_point : P.

  Section walk_parameters.

    Hypothesis tr_is_Delaunay : is_Delaunay tr.

    Variable opposite_edge : E -> E.
    
    Hypothesis involution_opposite_edge : 
      forall (e : E), opposite_edge (opposite_edge e) = e.

    Variable separating_edge : T -> option E.
    
    Hypothesis separating_edge_is_in_triangle : 
      forall (e : E) (t : T),
        separating_edge t = Some e -> 
          edge_in_triangle e t.

    Variable find_triangle_of_edge : E -> option T.

    Hypothesis edge_is_in_triangle_of_edge :
      forall (e : E) (t : T),
        find_triangle_of_edge e = Some t -> 
          edge_in_triangle e t.

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

    Lemma walk_result_edge :
      forall (e : E) (t : T),
      walk t = inr e -> (exists (t1 : T), edge_in_triangle (opposite_edge e) t1) /\
        (forall (t2 : T), ~~ edge_in_triangle e t2).
    Proof.
    move => e t h; split.
      exists t.
      funelim (walk t).
    Abort.

    
    End walk_parameters.

End parameters.

