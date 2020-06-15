From mathcomp Require Import all_ssreflect all_algebra.
From Equations Require Import Equations.

Section parameters.

Variable R : realDomainType.

Variable P : finType.

Variable coords : P -> R * R.

Definition triangulation := {set (P ^ 3)}.

Variable is_Delaunay : triangulation -> bool.

Variable separating_edge : P ^ 3 -> P -> option (P ^ 2).

(* look for documentation about Equations in Coq, for instance at:

https://github.com/mattam82/Coq-Equations

https://github.com/mattam82/Coq-Equations/blob/master/examples/Basics.v

*)


Equations filter {A} (l : list A) (p : A -> bool) : list A :=
filter nil p := nil ;
filter (cons a l) p with p a =>
filter (cons a l) p true := a :: filter l p;
filter (cons a l) p false := filter l p.

Variable opposite_edge : P ^ 2 -> P ^ 2.

Variable find_triangle_of_edge : triangulation -> P ^ 2 -> option (P ^ 3).

(* implicit design assumption: walk_lt (a, b, c) (a', b', c') can only
  hold if a satisfies the Delaunay criterion, and probably a' = a, and
  probably b \in a, and b' \in a, and probably c = c' *)

Variable walk_lt : (P ^ 3 * P) -> (P ^ 3 * P) -> Prop.

Hypothesis walk_lt_wf : WellFounded walk_lt.

Hypothesis  decrease_condition :
   forall e tr t t' p,
   separating_edge t p = Some e ->
   find_triangle_of_edge tr (opposite_edge e) = Some t' ->
   walk_lt (t', p) (t, p).

Equations walk (tr : triangulation) (trd : is_Delaunay tr)
   (target_point : P) (current_triangle : P ^ 3) 
   : (P ^ 3) + (P ^ 2) by wf (current_triangle, target_point) walk_lt :=
walk tr trd target_point current_triangle with
    separating_edge current_triangle target_point => { 
     | Some edge with find_triangle_of_edge tr (opposite_edge edge) => {
          | Some new_triangle := walk tr trd target_point new_triangle;
          | None := inr (opposite_edge edge)};
     | None := inl (current_triangle)}.

Next Obligation.
apply: decrease_condition.
       
Definition walk (tr : triangulation) (trd : is_Delaunay tr)
  (target_point : P) (current_triangle : P ^ 3) :=
    match triangulation with _ => 0 end.

End parameters.
