From mathcomp Require Import all_ssreflect all_algebra.

Section matrix.

Variable R : realDomainType.

Variable pt_norm : R * R -> R.

Definition select3 {T : Type} (A B C : T) :=
  fun (i : nat) => 
    match i with
    | 0 => A
    | 1 => B
    | _ => C
    end.

Definition select4 {T : Type} (A B C D : T) :=
  fun (i : nat) => 
    match i with
    | 0 => A
    | 1 => B
    | 2 => C
    | _ => D
    end.

Definition project (A : R * R) :=
  fun (i : nat) => 
    match i with
    | 0 => 1%R
    | 1 => A.1
    | 2 => A.2
    | _ => pt_norm A
    end.

Definition project2 (A : R * R * R) :=
  fun (i : nat) =>
    match i with
      | 0 => A.1.1
      | 1 => A.1.2
      | 2 => A.2
      | _ => 1%R
    end.

Definition area_mx (A B C : R * R) :=
  (\matrix_(i < 3, j < 3) project (select3 A B C i) j)%R.

Definition circle_mx (A B C D : R * R) :=
  (\matrix_(i < 4, j < 4) project (select4 A B C D i) j)%R.

Definition tetrahedron_mx (A B C D : R * R * R) :=
  (\matrix_(i < 4, j < 4) project2 (select4 A B C D i) j)%R.

End matrix.