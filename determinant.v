From mathcomp Require Import all_ssreflect all_algebra.

Require Import matrix.

From mathcomp Require Import ring.
Import GRing.Theory Num.Theory Order.POrderTheory.
 
Open Scope ring_scope.

Section det.

Variable R : realFieldType.

Ltac expand_det :=
repeat rewrite (expand_det_col _ ord0) /cofactor /row' /col' !big_ord_recr
   big_ord0 /= add0r !(mxE, ffunE, addn0, expr0, expr1, expr2, mxE, ffunE, 
   det_mx00, mul1r, mulNr, mulrN, opprK, mulr1, addrA) /=.

Definition pt_norm (A : R * R) := 
  A.1 ^+2 + A.2 ^+2.

Definition tr_area (A B C : R * R) :=
  \det (area_mx R pt_norm A B C).

Lemma poly_area (A B C : R * R) :
  tr_area A B C =
    B.1 * C.2 - C.1 * B.2 - (A.1 * C.2 - C.1 * A.2) + A.1 * B.2 - B.1 * A.2.
Proof.
by rewrite/tr_area; expand_det.
Qed.

Lemma inv_cycle_tr_area (A B C : R * R) :
  tr_area A B C = tr_area C A B.
Proof.
by rewrite !poly_area; field.
Qed.

Lemma flipr_tr_area (A B C : R * R) :
  tr_area A B C = - tr_area A C B.
Proof.
by rewrite !poly_area; field.
Qed.

Lemma dupl_tr_area (A B : R * R) :
  tr_area A A B = 0.
Proof.
by rewrite !poly_area; field.
Qed.

Definition translation (A O : R * R) :=
  (A.1 - O.1, A.2 - O.2).

Lemma translation0 (A : R * R) : translation A A = (0, 0).
Proof.
by rewrite/translation !subrr.
Qed.

Lemma norm_translation :
  forall A B : R * R,
  A != B -> pt_norm (translation A B) > 0.
Proof.
move=> [Ax Ay] [Bx By].
rewrite xpair_eqE -(subr_eq0 Ax) -(subr_eq0 Ay)/pt_norm/translation=>/=/nandP[]h.
  apply: ltr_spaddl; last by apply: sqr_ge0.
  rewrite lt_def.
  apply/andP.
  split; last by apply: sqr_ge0.
  apply: (contra _ h).
  by rewrite  sqrf_eq0.
apply: ltr_spaddr; last by apply: sqr_ge0.
rewrite lt_def.
apply/andP.
split; last by apply: sqr_ge0.
apply: (contra _ h).
by rewrite sqrf_eq0.
Qed.

Lemma area_translation (A B C O : R * R) :
  tr_area A B C =
  tr_area (translation A O) (translation B O) (translation C O).
Proof.
by rewrite !poly_area/translation/=; field.
Qed.

Lemma area_add (A B C D : R * R) :
  (tr_area A B C) + (tr_area A D B) =
    (tr_area A D C) + (tr_area B C D).
Proof.
by rewrite !poly_area; field.
Qed.

Definition out_circle (A B C D : R * R) :=
  \det (circle_mx R pt_norm A B C D).

Lemma poly_out_circle (A B C D : R * R) :
  out_circle A B C D =
    B.1 * (C.2 * (D.1 * D.1 + D.2 * D.2) - D.2 * (C.1 * C.1 + C.2 * C.2)) -
C.1 * (B.2 * (D.1 * D.1 + D.2 * D.2) - D.2 * (B.1 * B.1 + B.2 * B.2)) +
D.1 * (B.2 * (C.1 * C.1 + C.2 * C.2) - C.2 * (B.1 * B.1 + B.2 * B.2)) -
(A.1 * (C.2 * (D.1 * D.1 + D.2 * D.2) - D.2 * (C.1 * C.1 + C.2 * C.2)) -
 C.1 * (A.2 * (D.1 * D.1 + D.2 * D.2) - D.2 * (A.1 * A.1 + A.2 * A.2)) +
 D.1 * (A.2 * (C.1 * C.1 + C.2 * C.2) - C.2 * (A.1 * A.1 + A.2 * A.2))) +
A.1 * (B.2 * (D.1 * D.1 + D.2 * D.2) - D.2 * (B.1 * B.1 + B.2 * B.2)) -
B.1 * (A.2 * (D.1 * D.1 + D.2 * D.2) - D.2 * (A.1 * A.1 + A.2 * A.2)) +
D.1 * (A.2 * (B.1 * B.1 + B.2 * B.2) - B.2 * (A.1 * A.1 + A.2 * A.2)) -
(A.1 * (B.2 * (C.1 * C.1 + C.2 * C.2) - C.2 * (B.1 * B.1 + B.2 * B.2)) -
 B.1 * (A.2 * (C.1 * C.1 + C.2 * C.2) - C.2 * (A.1 * A.1 + A.2 * A.2)) +
 C.1 * (A.2 * (B.1 * B.1 + B.2 * B.2) - B.2 * (A.1 * A.1 + A.2 * A.2))).
Proof.
by rewrite/out_circle/pt_norm; expand_det; field.
Qed.

Lemma inv_cycle_out_circle (A B C D : R * R) :
  out_circle A B C D = out_circle C A B D.
Proof.
move: A B C D.
move => [a_x a_y][b_x b_y][c_x c_y][d_x d_y].
by rewrite !poly_out_circle; field.
Qed.

Lemma flip_out_circle (A B C D : R * R) :
  out_circle A B C D = out_circle A C D B.
Proof.
by rewrite !poly_out_circle; field.
Qed.

Lemma out_circle_translation (A B C D O : R * R) :
  out_circle A B C D =
  out_circle (translation A O) (translation B O) (translation C O) (translation D O).
Proof.
by rewrite !poly_out_circle/translation/=; field.
Qed.

Lemma develop_out_circle (A B C D : R * R) :
  out_circle A B C D =
    - (pt_norm A) * (tr_area B C D) +
    (pt_norm B) * (tr_area A C D) -
    (pt_norm C) * (tr_area A B D) +
    (pt_norm D) * (tr_area A B C).
Proof.
by rewrite poly_out_circle !poly_area/pt_norm; field.
Qed.

Definition power (A B C E: R * R) :=
  out_circle A B C E / tr_area A B C.

Lemma inv_cycle_power (A B C E : R * R) :
  power A B C E = power C A B E.
Proof.
by rewrite /power inv_cycle_out_circle inv_cycle_tr_area.
Qed.

Lemma power_diff (A B C D E : R * R) :
  tr_area A B C != 0 ->
  tr_area A D B != 0 -> 
  power A B C E - power A D B E =
  -power A B C D * tr_area A B E / tr_area A D B.
Proof.
move: A B C D E.
move => [a_x a_y][b_x b_y][c_x c_y][d_x d_y][e_x e_y].
rewrite/power !poly_out_circle !poly_area/=.
move=> ABC ADB; field.
by apply/andP.
Qed.

Lemma poly_tetrahedron (A B C D : R * R * R) :
  (\det (tetrahedron_mx R A B C D)) =
    A.1.1 * (B.1.2 * (C.2 - D.2) - C.1.2 * (B.2 - D.2) + D.1.2 * (B.2 - C.2)) -
    B.1.1 * (A.1.2 * (C.2 - D.2) - C.1.2 * (A.2 - D.2) + D.1.2 * (A.2 - C.2)) +
    C.1.1 * (A.1.2 * (B.2 - D.2) - B.1.2 * (A.2 - D.2) + D.1.2 * (A.2 - B.2)) -
    D.1.1 * (A.1.2 * (B.2 - C.2) - B.1.2 * (A.2 - C.2) + C.1.2 * (A.2 - B.2)).
Proof.
by expand_det; field.
Qed.

Definition tr_measure (A B C : R * R) :=
  (\det (tetrahedron_mx R (A, 0) (B, 0) (C, 0) (A, pt_norm A))) +
  (\det (tetrahedron_mx R (B, 0) (A, pt_norm A) (B, pt_norm B) (C, pt_norm C))) +
  (\det (tetrahedron_mx R (A, pt_norm A) (C, 0) (C, pt_norm C) (B, 0))).

Lemma poly_measure (A B C : R * R) :
  tr_measure A B C = 
A.1 * (B.2 * - (A.1 * A.1 + A.2 * A.2) + C.2 * (A.1 * A.1 + A.2 * A.2)) -
B.1 * (A.2 * - (A.1 * A.1 + A.2 * A.2) + C.2 * (A.1 * A.1 + A.2 * A.2)) +
C.1 * (A.2 * - (A.1 * A.1 + A.2 * A.2) + B.2 * (A.1 * A.1 + A.2 * A.2)) +
B.1 *
(A.2 * (B.1 * B.1 + B.2 * B.2 - (C.1 * C.1 + C.2 * C.2)) -
 B.2 * (A.1 * A.1 + A.2 * A.2 - (C.1 * C.1 + C.2 * C.2)) +
 C.2 * (A.1 * A.1 + A.2 * A.2 - (B.1 * B.1 + B.2 * B.2))) -
A.1 *
(B.2 * (B.1 * B.1 + B.2 * B.2 - (C.1 * C.1 + C.2 * C.2)) -
 B.2 * - (C.1 * C.1 + C.2 * C.2) - C.2 * (B.1 * B.1 + B.2 * B.2)) +
B.1 *
(B.2 * (A.1 * A.1 + A.2 * A.2 - (C.1 * C.1 + C.2 * C.2)) -
 A.2 * - (C.1 * C.1 + C.2 * C.2) - C.2 * (A.1 * A.1 + A.2 * A.2)) +
C.1 *
(-(B.2 * (A.1 * A.1 + A.2 * A.2 - (B.1 * B.1 + B.2 * B.2)) -
  A.2 * - (B.1 * B.1 + B.2 * B.2) - B.2 * (A.1 * A.1 + A.2 * A.2))) +
A.1 * (C.2 * (C.1 * C.1 + C.2 * C.2) - B.2 * (C.1 * C.1 + C.2 * C.2)) -
C.1 *
(A.2 * (C.1 * C.1 + C.2 * C.2) - C.2 * (A.1 * A.1 + A.2 * A.2) +
 B.2 * (A.1 * A.1 + A.2 * A.2 - (C.1 * C.1 + C.2 * C.2))) +
C.1 * (- (C.2 * (A.1 * A.1 + A.2 * A.2)) + B.2 * (A.1 * A.1 + A.2 * A.2)) +
B.1 *
(-(A.2 * - (C.1 * C.1 + C.2 * C.2) -
  C.2 * (A.1 * A.1 + A.2 * A.2 - (C.1 * C.1 + C.2 * C.2)) +
  C.2 * (A.1 * A.1 + A.2 * A.2))).
Proof.
by rewrite/tr_measure/pt_norm !poly_tetrahedron/=; field.
Qed.

Lemma measure_sub_out_circle (A B C D : R * R) :
  (tr_measure A B C) + (tr_measure A D B) -
  (tr_measure A D C) - (tr_measure C D B) =
    out_circle A D B C.
Proof.
by rewrite !poly_measure !poly_out_circle; field.
Qed.

Lemma dupl_measure (A B : R * R) : tr_measure A A B = 0.
Proof.
by rewrite poly_measure; field.
Qed.

Lemma inv_cycle_measure (A B C : R * R) : tr_measure A B C = tr_measure C A B.
Proof.
by rewrite !poly_measure; field.
Qed.

Lemma flipr_measure (A B C : R * R) : tr_measure A B C = - tr_measure A C B.
Proof.
by rewrite !poly_measure; field.
Qed.

Section decrease.

Variable A : R * R.

Variable B : R * R.

Variable C : R * R.

Variable D : R * R.

Variable E : R * R.

Hypothesis ABC_gt0 : tr_area A B C > 0.

Hypothesis ADB_gt0 : tr_area A D B > 0.

Hypothesis AEB_gt0 : tr_area A E B > 0.

Hypothesis delaunay : out_circle A B C D > 0.

Lemma power_decrease : power A B C E - power A D B E > 0.
Proof.
rewrite power_diff; first last.
  by apply lt0r_neq0.
  by apply lt0r_neq0.
rewrite pmulr_rgt0; first by rewrite invr_gt0.
rewrite nmulr_lgt0; last by rewrite flipr_tr_area oppr_lt0.
rewrite oppr_lt0/power pmulr_lgt0//.
by rewrite invr_gt0.
Qed.

End decrease.

Section flip.

Variables A B C D : R * R.

Hypothesis ABC_gt0 : tr_area A B C > 0.

Hypothesis ACD_gt0 : tr_area A C D > 0.

Hypothesis in_circle : out_circle A B C D <= 0.

Lemma ccw_flip : tr_area A B D > 0.
Proof.
rewrite (area_translation _ _ _ A)
  -(@pmulr_lgt0 _ (pt_norm (translation C A)) _); last first.
  apply: norm_translation.
  apply/negP=>/eqP CA.
  move: ACD_gt0.
  by rewrite CA dupl_tr_area lt_irreflexive.
move: in_circle.
rewrite (out_circle_translation _ _ _ _ A) develop_out_circle/translation
          2!{1}subrr -!/(translation _ _) /pt_norm(expr2 0) mulr0 addr0 oppr0
          mul0r add0r -!/(pt_norm _) addrC addrA subr_le0 (mulrC (_ (_ C A))).
apply: lt_le_trans.
rewrite -!area_translation.
apply: addr_gt0; apply: mulr_gt0=>//; apply: norm_translation; apply/eqP=> h.
  move: ACD_gt0.
  by rewrite h flipr_tr_area dupl_tr_area oppr0 lt_irreflexive.
move: ABC_gt0.
by rewrite h dupl_tr_area lt_irreflexive.
Qed.

End flip.

End det.

