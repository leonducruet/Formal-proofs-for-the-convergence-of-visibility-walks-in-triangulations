From mathcomp Require Import all_ssreflect all_algebra.

Section matrix.

Variable R : realDomainType.

Variable pt_norm : R * R -> R.

Definition select (A B C : R * R) :=
  [ffun i : 'I_3 => 
    if val i == 0 then A else if val i == 1 then B else C].

Definition select3 (A B C : R * R) :=
  fun (i : nat) => 
    match i with
    | 0 => A
    | 1 => B
    | _ => C
    end.

Definition select4 (A B C D : R * R) :=
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


Definition area_mx (A B C : R * R) :=
  (\matrix_(i < 3, j < 3) project (select3 A B C i) j)%R.

Definition circle_mx (A B C D : R * R) :=
  (\matrix_(i < 4, j < 4) project (select4 A B C D i) j)%R.

End matrix.