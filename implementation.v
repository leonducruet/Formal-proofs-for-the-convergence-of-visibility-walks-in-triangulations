From mathcomp Require Import all_ssreflect all_algebra finfun.

Require Import parameters.
Require Import determinant.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Import GRing.Theory Num.Theory Order.Theory. *)

(* Open Scope ring_scope. *)

(* ffune *)

Section implementation.

Variable R : realFieldType.

Variable P : finType.

Variable coords : P -> R * R.

Hypothesis inj_coords : 
  forall (p1 p2 : P), (coords p1) == (coords p2) -> p1 == p2.

Definition E := [finType of {ffun 'I_2 -> P}].

Lemma elimI2 (P' : 'I_2 -> Prop): P' 0 -> P' 1 -> forall i, P' i.
Proof.
move=> p0 p1 [[ | [ | [ | ?]]] ci] //.
    by have /eqP -> : Ordinal ci == 0.
  by have /eqP -> : Ordinal ci == 1.
Qed.

Definition oppos_edge (e : E) : E := 
  [ffun i : 'I_2 => e (i + 1)].

Lemma p1p1_I2 : 
  forall (i : 'I_2), (i + 1 + 1 : 'I_2) = i.
Proof.
apply: elimI2; by apply /eqP.
Qed.

Lemma inv_oppos_edge (e : E) : (oppos_edge (oppos_edge e)) = e.
Proof.
rewrite -ffunP.
apply: elimI2; by rewrite /oppos_edge ?ffunE p1p1_I2.
Qed.

Definition T :=  [finType of {ffun 'I_3 -> P}].

Definition edges_tr (t : T) : {ffun 'I_3 -> E} :=
  [ffun i : 'I_3 => [ffun j : 'I_2 => if val j == 0%N then t i else t (i + 1)]].

Definition edge_in (e : E) (t : T) :=
  exists (i : 'I_3), (edges_tr t i) == e.

Variable tr : triangulation T.

Fixpoint find_triangle_aux (e : E) (tr_enum : list T) : option T :=
  match tr_enum with
  | nil => None
  | t :: r => if (edge_in e t) then Some t else find_triangle_aux r
  end.

Definition find_triangle_of_edge (e : E) : option T :=
  
  let rec find_aux (tr' : list T) :=
    match tr' with
    | nil => None
    | t :: r => if (edge_in e t) then Some t else find_aux r
    end
  in
  find_aux (enum tr).
  
  

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

Variable target_pt : P.

Definition 
(* Definition is_Delaunay :=
  forall (t1 t2 : T), 
    t1 \in tr -> t2 \in tr -> 
      forall (i : 'I_3), dist t1 (coord (pt_tr t2 i)) > 0. *)

(*

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
  forall (t : T), triangle_measure t >= 0. *)



