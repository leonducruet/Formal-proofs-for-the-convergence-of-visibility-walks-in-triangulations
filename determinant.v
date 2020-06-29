From mathcomp Require Import all_ssreflect all_algebra. 

Import GRing.Theory Num.Theory.
 
Open Scope ring_scope. 

Section det.

Variable R : realDomainType. 

Definition det3x3 (a1 a2 a3
                  b1 b2 b3
                  c1 c2 c3 : R) := 
  a1 * b2 * c3 + a2 * b3 * c1 + a3 * b1 * c2 -
  a1 * b3 * c2 - a3 * b2 * c1 - a2 * b1 * c3.

Definition x_ (A : R * R) := let (a_x, _) := A in a_x.

Definition y_ (A : R * R) := let (_, a_y) := A in a_y.

Definition pt_norm (A : R * R) := 
  (x_ A) * (x_ A) + (y_ A) * (y_ A). 

Definition tr_area (A B C : R * R) := 
  det3x3 (x_ A) (y_ A) 1
         (x_ B) (y_ B) 1
         (x_ C) (y_ C) 1.

Definition out_circle (A B C D : R * R) :=
  (pt_norm A) * (tr_area B C D) - (pt_norm B) * (tr_area A C D) +
  (pt_norm C) * (tr_area A B D) - (pt_norm D) * (tr_area A B C).

Definition power (A B C D : R * R) :=
  if tr_area A B C != 0 then out_circle A B C D / tr_area A B C else 0.

Lemma out_circle_diff (A B C D E : R * R) :
  tr_area A D B * out_circle A B C E - tr_area A B C * out_circle A D B E =
    tr_area A E B * out_circle A B C D.
Proof.
move: A B C D E.
move => [a_x a_y][b_x b_y][c_x c_y][d_x d_y][e_x e_y].
rewrite /out_circle /pt_norm /tr_area /det3x3 /x_ /y_.
(* ring.
Qed. *)
Admitted.

Variable A : R * R.

Variable B : R * R.

Variable C : R * R.

Variable D : R * R.

Variable E : R * R.

Section decrease.

(*    +A
              +D
                    +E
  +C
          +B *)

Hypothesis ABC : tr_area A B C > 0.

Hypothesis ADB : tr_area A D B > 0.

Hypothesis AEB : tr_area A E B > 0.

Hypothesis delaunay : out_circle A B C D > 0.

Lemma power_decrease : power A B C E - power A D B E > 0.
Proof.
have power_diff : 
  (power A B C E - power A D B E) * tr_area A B C * tr_area A D B =
    out_circle A B C D * tr_area A E B.
  rewrite /power.
  have ABC_neq0 : tr_area A B C != 0.
    by apply: lt0r_neq0 ABC.
  have ADB_neq0 : tr_area A D B != 0.
    by apply: lt0r_neq0 ADB.
  rewrite ABC_neq0 ADB_neq0.
  rewrite mulrBl.
  rewrite mulrAC.
  About divrr.
  rewrite (divrr ABC_neq0).
  
Admitted.
    
End decrease.

End det.

