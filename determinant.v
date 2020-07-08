From mathcomp Require Import all_ssreflect all_algebra.

Require Import matrix.

Import GRing.Theory Num.Theory.
 
Open Scope ring_scope.

Section det.

Variable R : realFieldType.

Let R' := (R : Type).

Let mul : R' -> R' -> R' := @GRing.mul _.
Let add : R' -> R' -> R' := @GRing.add _.
Let sub : R' -> R' -> R' := (fun x y => x - y).
Let opp : R' -> R' := @GRing.opp _.
Let zero : R' := 0.
Let one : R' := 1.

Let R2_theory :=
  @mk_rt R' zero one add mul sub opp
   (@eq R')
   (@add0r R) (@addrC R) (@addrA R) (@mul1r R) (@mulrC R)
     (@mulrA R) (@mulrDl R) (fun x y : R => erefl (x - y)) (@addrN R).

Add Ring R2_Ring : R2_theory.

Ltac mc_ring :=
rewrite ?mxE /= ?(expr0, exprS, mulrS, mulr0n) -?[@GRing.add _]/add
   -?[@GRing.mul _]/mul
   -?[@GRing.opp _]/opp -?[1]/one -?[0]/zero;
match goal with |- @eq ?X _ _ => change X with R' end;
ring.

Definition pt_norm (A : R * R) := 
  A.1 * A.1 + A.2 * A.2.

Definition tr_area (A B C : R * R) :=
  \det (area_mx R pt_norm A B C).

Lemma inv_cycle_tr_area (A B C : R * R) :
  tr_area A B C = tr_area C A B.
Proof.
move: A B C.
move => [a_x a_y][b_x b_y][c_x c_y].
rewrite /tr_area.
repeat rewrite (expand_det_col _ ord0) /cofactor /row' /col' !big_ord_recr
   big_ord0 /= add0r !(mxE, ffunE, addn0, expr0, expr1, expr2, mxE, ffunE, 
   det_mx00, mul1r, mulNr, mulrN, opprK, mulr1, addrA) /=.
rewrite /pt_norm.
by mc_ring.
Qed.

Lemma flipr_tr_area (A B C : R * R) :
  tr_area A B C = - tr_area A C B.
Proof.
move: A B C.
move => [a_x a_y][b_x b_y][c_x c_y].
rewrite /tr_area.
repeat rewrite (expand_det_col _ ord0) /cofactor /row' /col' !big_ord_recr
   big_ord0 /= add0r !(mxE, ffunE, addn0, expr0, expr1, expr2, mxE, ffunE, 
   det_mx00, mul1r, mulNr, mulrN, opprK, mulr1, addrA) /=.
rewrite /pt_norm.
by mc_ring.
Qed.

Lemma flipl_tr_area (A B C : R * R) :
  tr_area A B C = - tr_area B A C.
Proof.
move: A B C.
move => [a_x a_y][b_x b_y][c_x c_y].
rewrite /tr_area.
repeat rewrite (expand_det_col _ ord0) /cofactor /row' /col' !big_ord_recr
   big_ord0 /= add0r !(mxE, ffunE, addn0, expr0, expr1, expr2, mxE, ffunE, 
   det_mx00, mul1r, mulNr, mulrN, opprK, mulr1, addrA) /=.
rewrite /pt_norm.
by mc_ring.
Qed.

Definition out_circle (A B C D : R * R) :=
  \det (circle_mx R pt_norm A B C D).

Lemma inv_cycle_out_circle (A B C D : R * R) :
  out_circle A B C D = out_circle C A B D.
Proof.
move: A B C D.
move => [a_x a_y][b_x b_y][c_x c_y][d_x d_y].
rewrite /out_circle /tr_area.
repeat rewrite (expand_det_col _ ord0) /cofactor /row' /col' !big_ord_recr
   big_ord0 /= add0r !(mxE, ffunE, addn0, expr0, expr1, expr2, mxE, ffunE, 
   det_mx00, mul1r, mulNr, mulrN, opprK, mulr1, addrA) /=.
rewrite /pt_norm.
by mc_ring.
Qed.

Definition power (A B C E: R * R) :=
  out_circle A B C E / tr_area A B C.

Lemma inv_cycle_power (A B C E : R * R) :
  power A B C E = power C A B E.
Proof.
by rewrite /power inv_cycle_out_circle inv_cycle_tr_area.
Qed.

Lemma out_circle_diff (A B C D E : R * R) :
  out_circle A B C E * tr_area A D B - out_circle A D B E * tr_area A B C =
    out_circle A B C D * tr_area A E B.
Proof.
move: A B C D E.
move => [a_x a_y][b_x b_y][c_x c_y][d_x d_y][e_x e_y].
rewrite /out_circle /tr_area.
repeat rewrite (expand_det_col _ ord0) /cofactor /row' /col' !big_ord_recr
   big_ord0 /= add0r !(mxE, ffunE, addn0, expr0, expr1, expr2, mxE, ffunE, 
   det_mx00, mul1r, mulNr, mulrN, opprK, mulr1, addrA) /=.
rewrite /pt_norm.
by mc_ring. 
Qed.

Section decrease.

Variable A : R * R.

Variable B : R * R.

Variable C : R * R.

Variable D : R * R.

Variable E : R * R.

Hypothesis ABC_lt0 : tr_area A B C > 0.

Hypothesis ADB_lt0 : tr_area A D B > 0.

Hypothesis AEB_lt0 : tr_area A E B > 0.

Hypothesis delaunay : out_circle A B C D > 0.

Lemma power_decrease : power A B C E - power A D B E > 0.
Proof.
have power_diff : 
  (power A B C E - power A D B E) * tr_area A B C * tr_area A D B =
    out_circle A B C D * tr_area A E B.
  rewrite /power.
  rewrite ?mulrBl mulfVK.
  rewrite mulrAC mulfVK.
  by apply: out_circle_diff.
    by apply: lt0r_neq0 ADB_lt0.
  by apply: lt0r_neq0 ABC_lt0.
have mul_decrease : 
  (power A B C E - power A D B E) * tr_area A B C * tr_area A D B > 0.
  rewrite power_diff.
  apply: mulr_gt0.
    by apply: delaunay.
  by apply: AEB_lt0.
have step1 : (power A B C E - power A D B E) * tr_area A B C * tr_area A D B / tr_area A D B > 0.
  by apply: divr_gt0 mul_decrease ADB_lt0.
rewrite mulfK in step1.
  have step2 : (power A B C E - power A D B E) * tr_area A B C / tr_area A B C > 0.
    by apply: divr_gt0 step1 ABC_lt0.
  rewrite mulfK in step2.
    by apply: step2.
  by apply: lt0r_neq0 ABC_lt0.
by apply: lt0r_neq0 ADB_lt0.
Qed.

End decrease.

End det.

