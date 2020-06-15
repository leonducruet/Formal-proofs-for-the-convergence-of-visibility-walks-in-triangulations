From mathcomp Require Import all_ssreflect.


(*Definition f (n : nat) := 1 + n + 1.
Print f.

Eval lazy in f 2.

Eval lazy delta [f] in f 2.
Eval lazy delta [f] beta in f 2.

Print bool.*)

(*Definition twoVtree (b : bool) := if b then 2 else 3.
Eval lazy in twoVtree true.
Eval lazy delta in twoVtree true.
Eval lazy delta beta in twoVtree true.
Eval lazy delta beta iota in twoVtree true.*)
(*
Definition andb (b1 b2 : bool) := if b1 then b2 else false.
Definition orb (b1 b2 : bool) := if b1 then true else b2.

Infix "&&" := andb.
Infix "||" := orb.

Check true && false || false.

Print nat

Check 3. *)
Check (fun x => (x + x).+2).
Eval lazy in (fun x => (x + x).+2) 1.

Definition pred (n : nat) :=
  if n is p.+1 then p else 0.

Eval lazy in pred 7.

Fixpoint addn n m := 
  if n is p.+1 then (addn p m).+1 else m.

Infix "+" := addn.
Eval lazy in 3 + 2.

Print addn.

Fixpoint eqn n m :=
  match n, m with
  | 0, 0 => true
  | p.+1, q.+1 => eqn p q
  | _, _ => false
  end.

Infix "==" := eqn.
Eval lazy in 3 == 4.

Fixpoint subn m n : nat :=
  match m, n with
  | p.+1, q.+1 => subn p q
  |_, _ => m
  end.

Infix "-" := subn.

Eval lazy in 3 - 2.
Eval lazy in 2 - 3.

Definition leq m n := m - n == 0.

Infix "<=" := leq.

Eval lazy in 4 <= 5.

Check nil.
Check cons 3 [:: 1; 8; 34].

Fixpoint size A (s : seq A) := 
  if s is _ :: tl then (size A tl).+1 else 0.

Eval lazy in size nat [:: 1; 8; 34].

Section symbols.
Variables v : nat.

Eval lazy in pred v.+1.
Eval lazy in pred v.

Variable f : nat -> nat -> nat.

Eval lazy in foldr f 3 [:: 1; 2 ].

Eval lazy in foldr addn 3 [:: 1; 2].

End symbols.

Fixpoint iota m n := if n is u.+1 then m :: iota m.+1 u else [::].

Eval lazy in iota 0 5.

Notation "\sum_ ( m <= i < n ) F" :=
  (foldr (fun i a => F + a) 0 (iota m (n-m))).

Check \sum_(1 <= x < 5) (x * 2 - 1).
Eval lazy in \sum_(1 <= x < 5) (x * 2 - 1).





