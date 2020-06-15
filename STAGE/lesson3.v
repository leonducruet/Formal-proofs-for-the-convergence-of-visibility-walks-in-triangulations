From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(*Search "contra".*)
Search gtn.

Lemma example m p : prime p -> p %| m ! + 1 -> m < p.
Proof.
move=> prime_p.
Qed.