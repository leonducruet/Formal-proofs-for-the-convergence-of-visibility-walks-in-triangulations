From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive option 
  A := Some (a : A) | None.
Arguments Some {_}.
Arguments None {_}.

Definition default 
  A (a : A) (s : option A) := if s is Some v then v else a.
Eval lazy in default 3 None.
Eval lazy in default 3 (Some 4).

Definition negb b := 
  if b then false else true. 
Notation "~~ x" := (negb x).

Eval lazy in ~~ true.
Eval lazy in ~~ false.

Fixpoint iter (T : Type) n op (x : T) := 
  if n is p.+1 then op (iter p op x) else x.
Arguments iter {T}.

Definition addn n m :=
  iter n (fun x => x + 1) m.

Eval lazy in addn 3 4.

Definition muln n m :=
  iter n (fun x => addn x m) 0.

Eval lazy in muln 3 4.

Fixpoint muln_rec n m :=
  match n with
  | p.+1 => addn (muln_rec p m) m
  | _ => 0
  end.

Eval lazy in muln_rec 3 4.

Definition add2list s :=
  map (fun x => x + 2) s.

Eval lazy in add2list [:: 1; 2; 3].

Definition odds n :=
  iter n (fun seq => 1 :: (add2list seq)) [::].

Eval lazy in odds 10.
  











