From mathcomp Require Import all_ssreflect all_algebra fingroup perm zmodp.
Require Import ProofIrrelevance.
Require Import Psatz.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Declare ML Module "paramcoq". *)

(* transforms a goal that is a boolean conjunction of comparisons into
  a collection of goals that are all coq_nat comparisons. *)
Ltac to_lia := repeat (apply/andP; split); apply/leP.

(* apply lia on a goal, after converting all arithmetic operations to
  operations that lia knows about. *)
Ltac ssr_lia := rewrite -?(plusE, minusE, multE, subn1); lia.

Lemma mem_iter_orbit (T : finType) (f : T -> T) p i :
  iter i f p \in orbit f p.
Proof. by rewrite -fconnect_orbit fconnect_iter. Qed.

Lemma iter_lt_order_neq (T : finType) f k l (x : T) :
  (k < l < fingraph.order f x)%N -> iter k f x != iter l f x.
Proof.
move => /andP [kl lo]; apply/eqP=> abs.
have ko : (k < fingraph.order f x)%N by apply: ltn_trans lo.
by move: (kl); rewrite ltn_neqAle -(findex_iter lo) -abs findex_iter // eqxx.
Qed.

Lemma subset_orbit (T : finType) (f : T -> T) (x y : T) :
   y \in orbit f x -> {subset (orbit f y) <= (orbit f x)}.
Proof.
move=> yo z; rewrite -!fconnect_orbit; apply: connect_trans.
by rewrite fconnect_orbit.
Qed.

Record cc_system (T : eqType) (ccw : T -> T -> T -> bool) := {
  Knuth_1 : forall a b c, ccw a b c -> ccw b c a;
  Knuth_2 : forall a b c, ccw a b c -> ~~ ccw b a c;
  Knuth_3 : forall a b c, uniq [:: a; b; c] -> ccw a b c \/ ccw b a c;
  Knuth_4 : forall a b c d, ccw a b d -> ccw b c d -> ccw c a d ->
      ccw a b c;
  Knuth_5 : forall a b c d e, ccw a b c -> ccw a b d -> ccw a b e ->
    ccw a c d -> ccw a d e -> ccw a c e;
  Knuth_5' : forall a b c d e, ccw a b c -> ccw a b d -> ccw a b e ->
    ccw b c d -> ccw b d e -> ccw b c e
}.

Record map_funs (T : Type) := {
  sort : Type;
  map0 : sort;
  eval : sort -> T -> T;
  update : sort -> T -> T -> sort;
  map_iter : forall A : Type, (T -> A -> A) -> A -> sort -> T -> A
}.

Record map_system (T : eqType) (funs : map_funs T) := {
  eval_update1 : forall (m : sort funs) x y, eval (update m x y) x = y;
  eval_update_dif : forall (m : sort funs) x x' y, x != x' ->
    eval (update m x y) x' = eval m x';
  map_iterP : 
    forall (A : Type) (f : T -> A -> A) (v : A) (m : sort funs) (x : T),
    exists n,
      map_iter f v m x = foldr f v (traject (eval m) x n) /\
      uniq (traject (eval m) x n) /\
      looping (eval m) x n;
  eval_map0 : forall x, eval (map0 funs) x = x
}.

Lemma nth_orbit (T : finType) (d : T) (f : T -> T) (e : T) (i : nat):
  i < size (orbit f e) -> nth d (orbit f e) i = iter i f e.
Proof.
rewrite size_orbit /orbit => ilt.
by rewrite (set_nth_default e) ?size_traject ?nth_traject.
Qed.

Lemma traject_looping_orbit (T : finType) (f : T -> T) (x : T) (n : nat):
  uniq (traject f x n) -> looping f x n -> traject f x n = orbit f x.
Proof.
move=> un lo; suff -> : n = fingraph.order f x by [].
have ns : n = #|traject f x n| by rewrite (card_uniqP un) size_traject.
apply: anti_leq; rewrite ns !subset_leq_card //; last first.
  by apply/subsetP=> y /trajectP; move=> [] k _ ->; apply: fconnect_iter.
apply/subsetP=> y /iter_findex <-; move: (findex _ _ _) => k.
have nn0 : n != 0 by move: lo; rewrite /looping; case: (n).
elim: k {-2}k (leqnn k) => [k' | k IH k' k'lek].
  by rewrite leqn0=> /eqP ->; move: nn0; case: (n)=> //= j _; rewrite inE eqxx.
have [k'ltn | ]:= boolP(k' < n); first by apply/trajectP; exists k'.
rewrite -leqNgt=> nlek'.
rewrite (_ : k' = (k' - n) + n); last by rewrite subnK.
have/trajectP [j jlt jq]:= (lo).
rewrite iter_add jq -iter_add; apply: IH.
by to_lia; move: (leP k'lek)(leP nlek') (leP jlt); ssr_lia.
Qed.

Section seq_algorithm.

Variables (P : Type) (p0 : P) (ccw : P -> P -> P -> bool)
  (mf : map_funs P).

Notation update := update.
Notation map0 := (map0 mf).

Definition seq3 (s : seq P) :=
   let a := nth p0 s 0 in
   let b := nth a s 1 in
   let c := nth b s 2 in
   if ccw a b c then [:: a; b; c] else [:: b; a; c].


Definition map_cycle3 (s : seq P) :=
  match s with
  | [:: a; b; c] => update (update (update map0 c a) b c) a b
  | _ => map0
  end.

Definition inside_triangle (trs : seq P) (p : P) :=
  match trs with
  | [:: a; b; c] => ccw a b p && ccw b c p && ccw c a p
  | _ => false
  end.

Fixpoint pick_triangle (trs : seq (seq P)) (p : P) :=
  match trs with
  | tr :: trs =>
    if inside_triangle tr p then Some(tr, trs)
    else
       match pick_triangle trs p with
       | Some (v, others) => Some (v, tr::others)
       | None => None
       end
  | _ => None
  end.

Definition inside_triangles tr (p : P):=
  match tr with
  | [:: a; b; c] => [:: [:: p; a; b]; [:: p; b; c]; [:: p; c; a]]
  | _ => [::]
  end.

Definition find_next_purple (p : P) (map : sort mf) side b :=
  map_iter (fun b' e =>
              if eqb (ccw b' (eval map b') p) side then b' else e)
     b map b.

Definition find_purple_points p (m : sort mf) (e : P) : P * P :=
  if ccw e (eval m e) p then
     let a := find_next_purple p m false (eval m e) in
       (a, find_next_purple p m true (eval m a))
  else 
     let b := find_next_purple p m true (eval m e) in
       (find_next_purple p m false (eval m b), b).

Definition add_red_triangles p (m : sort mf) b tr :=
  map_iter (fun b' ts =>
     if ccw b' (eval m b') p then
        tr
     else
        ([:: (eval m b'); b'; p] :: ts)) [::] m b.

Definition new_map (m : sort mf) (a b p : P) :=
  update (update m p b) a p.

Definition size_le_3 (T : Type) (s : seq T) : bool :=
  match s with
  | _ :: _ :: _ :: _ :: _ => false
  | _ => true
  end.

Fixpoint naive (s : seq P) :
   seq (seq P) * (sort mf) * P :=
   match  s with
    nil =>  (nil, update map0 p0 p0, p0)
  | p :: tl =>
    if size_le_3 s then
      let tr1 := seq3 s in
      ([:: tr1], map_cycle3 tr1, head p0 tr1)
    else
      let '(tr, map, bp) := naive tl in
      if pick_triangle tr p is Some (t, trmt) then
       (inside_triangles t p ++ trmt, map, bp)
      else
        let (a, b) := find_purple_points p map bp in
          (add_red_triangles p map a tr,
           new_map map a b p, p)
  end.

End seq_algorithm.

Section specifications_in_eqType.

Variables (P : eqType) (p0 : P) (ccw : P -> P -> P -> bool)
  (ccs : cc_system ccw) (mf : map_funs P) (ms: map_system mf).

Definition ccw_seq (s : seq P) :=
  match s with [:: a; b; c] => ccw a b c | _ => false end.

Definition inh' boundary x :=
  path.cycle (fun u v => ccw u v x) boundary.

Definition triangles_prop (tr : seq (seq P)) :=
  forall t, t \in tr -> size t = 3 /\ uniq t /\ ccw_seq t.

Definition hull_prop (inp boundary : seq P) :=
  0 < size boundary /\
  path.cycle
    (fun x y =>
       all (fun z => (z != x) ==> (z != y) ==> ccw x y z) inp)
    boundary.

Definition surface_props (inp : seq P) (tr : seq (seq P)) (boundary : seq P) :=
  (forall t1 t2 p, t1 \in tr -> t2 \in tr ->
    inside_triangle ccw t1 p ->
    inside_triangle ccw t2 p -> t1 = t2) /\
  (forall q, path.cycle (fun x y => ccw x y q) boundary ->
     (q \in inp \/ exists t, t \in tr /\ inside_triangle ccw t q)).

Definition correct_triangulation (inp : seq P) (tr : seq (seq P))
   (boundary : seq P) :=
  triangles_prop tr /\
  (flatten tr =i inp) /\
  {subset boundary <= inp} /\
  hull_prop inp boundary /\
  surface_props inp tr boundary /\
  uniq tr.

Definition surface_props2 (context inp : seq P) (tr : seq (seq P))
    (boundary : seq P) :=
  (forall t1 t2 p, p \in context -> t1 \in tr -> t2 \in tr ->
    inside_triangle ccw t1 p ->
    inside_triangle ccw t2 p -> t1 = t2) /\
  (forall q, q \in context -> path.cycle (fun x y => ccw x y q) boundary ->
     (q \in inp \/ exists t, t \in tr /\ inside_triangle ccw t q)).

Definition correct_triangulation2 (context inp : seq P) (tr : seq (seq P))
   (boundary : seq P) :=
  triangles_prop tr /\
  (flatten tr =i inp) /\
  (forall x, x \in boundary -> x \in inp) /\
  hull_prop inp boundary /\
  surface_props2 context inp tr boundary /\
  uniq tr /\
  uniq boundary.

End specifications_in_eqType.

Lemma mem_orbit1 (T : finType) (f : T -> T) (x y : T) :
  y \in orbit f x -> f y \in orbit f x.
Proof.
by rewrite -!fconnect_orbit => A; apply/(connect_trans A)/fconnect1.
Qed.

Lemma nthS (T : Type) (e a : T) (s : seq T) k :
  nth e (a :: s) k.+1 = nth e s k.
Proof.  by []. Qed.

Lemma cycle_orbit_injective (T : finType) (f : T -> T) (x : T) :
  fcycle f (orbit f x) -> {in orbit f x &, injective f}.
Proof.
move=> cyc y z.
wlog yz : y z / findex f x y <= findex f x z.
  move=> main yo zo.
  by have [yz | ] := boolP(findex f x y <= findex f x z);
      [ |rewrite -ltnNge ltn_neqAle => /andP[] _ zy;
         move/esym=> q; apply/esym]; apply: main=> //.
move=> yo zo ff; move: (yo) (zo).
rewrite -!fconnect_orbit =>/iter_findex ity /iter_findex itz.
move: yz; rewrite leq_eqVlt=> /orP[/eqP itq | yltz ].
  by rewrite -ity itq itz.
move: (zo); rewrite -fconnect_orbit=> /findex_max.
rewrite leq_eqVlt=> /orP[/eqP zmax | zin ].
  move: (cyc); rewrite /orbit -orderSpred trajectS /=.
  move/(pathP x)=> /(_ (findex f x z)).
  rewrite size_rcons size_traject zmax orderSpred leqnn=> /(_ isT).
  rewrite -(ltn_predK yltz) nthS nth_rcons size_traject (ltn_predK yltz).
  rewrite -zmax leqnn.
  rewrite (set_nth_default (f x)); last first.
    by rewrite (ltn_predK yltz) -ltnS zmax size_traject orderSpred leqnn.
  rewrite nth_traject; last by rewrite (ltn_predK yltz) leqnn.
  rewrite nth_rcons size_traject ltnn eqxx /= -iterSr (ltn_predK yltz).
  rewrite itz -ff => /eqP fyx.
  have/iter_lt_order_neq : 0 < (findex f x y).+1 < fingraph.order f x.
    by rewrite ltn0Sn -zmax ltnS.
  by rewrite iterS ity fyx eqxx.
have : (findex f x y).+1 < (findex f x z).+1 < fingraph.order f x.
  by rewrite ltnS yltz zin.
by move/iter_lt_order_neq; rewrite !iterS ity itz ff eqxx.
Qed.

Lemma iter_size (T : finType) (f : T -> T) (x : T) :
  fcycle f (orbit f x) ->
  {in orbit f x, forall y, iter (size (orbit f y)) f y = y}.
Proof.
move=> cyco.
have stb : {in (orbit f x), forall y, f y \in orbit f x}.
  by move=> y yo; apply: mem_orbit1.
move=> y yo; rewrite size_orbit.
by apply: (iter_order_in stb _ yo); apply: cycle_orbit_injective.
Qed.

Lemma cycle_findex_order (T : finType) (f : T -> T) (x : T) :
  fcycle f (orbit f x) -> (findex f (f x) x) = (fingraph.order f x).-1.
Proof.
move=> cyc.
have xin : x \in orbit f x by rewrite -fconnect_orbit connect0.
have ofx := order_cycle cyc (orbit_uniq _ _) (mem_orbit1 xin).
  have iterof : iter (fingraph.order f x).-1 f (f x) = x.
    by rewrite -iterSr orderSpred -size_orbit (iter_size cyc).
  suff /findex_iter : (fingraph.order f x).-1 < fingraph.order f (f x).
    by rewrite iterof.
  by rewrite orderSpred ofx size_orbit leqnn.
Qed.

Section proofs_in_eqType.

Variable (P : eqType) (ccw : P -> P -> P -> bool).

Notation pick_triangle := (@pick_triangle P ccw).
Notation inside_triangle := (@inside_triangle P ccw).

Lemma pick_triangle_someP (tr tr' : seq (seq P)) t (q : P) :
  pick_triangle tr q = Some (t, tr') ->
  inside_triangle t q && perm_eq (t :: tr') tr.
Proof.
elim: tr tr' t => [ | t1 trtl IH] tr' t //=.
have [ ins | nins] := boolP (inside_triangle t1 q).
  by move=> [<- <-]; rewrite ins perm_refl.
case cmp : (pick_triangle trtl q) => [[v1 vtr] |] //.
move=> [v1t t1vtrtr'].
have := IH _ _ cmp; rewrite -t1vtrtr' -v1t=> /andP[] -> peq.
by rewrite andTb (perm_catCA [:: v1] [:: t1] vtr) /= perm_cons.
Qed.

Lemma pick_triangle_noneP (tr : seq (seq P)) (q : P) :
  pick_triangle tr q = None ->
  forall t, t \in tr -> ~~inside_triangle t q.
Proof.
elim: tr q => [ | t1 trtl IH] q //=.
have [ ins | nins] := boolP (inside_triangle t1 q) => //.
case cmp : (pick_triangle trtl q) => [[v1 vtr] |] // _.
by move=> t; rewrite !inE => /orP [/eqP -> // | tin]; apply: IH.
Qed.

End proofs_in_eqType.

Section proofs_in_finType.

Variables (P : finType) (p0 : P) (ccw : P -> P -> P -> bool)
  (ccs : cc_system ccw) (mf : map_funs P) (ms: map_system mf).

Notation inside_triangle := (@inside_triangle P ccw).
Notation seq3 := (@seq3 P p0 ccw).
Notation map_cycle3 := (@map_cycle3 P mf).
Notation naive := (@naive P p0 ccw mf).
Notation pick_triangle := (@pick_triangle P ccw).
Notation inside_triangles := (@inside_triangles P).
Notation Knuth_1 := (Knuth_1 ccs).
Notation Knuth_2 := (Knuth_2 ccs).
Notation Knuth_3 := (Knuth_3 ccs).
Notation Knuth_4 := (Knuth_4 ccs).
Notation Knuth_5 := (Knuth_5 ccs).
Notation Knuth_5' := (Knuth_5' ccs).

Notation ccw_seq := (ccw_seq ccw).
Notation inh' := (inh' ccw).
Notation hull_prop := (hull_prop ccw).
Notation triangles_prop := (triangles_prop ccw).

Definition subE := (subUset, sub1set, inE, eqxx, orbT, andbT).

Definition inh f p x :=
  forall e, e \in orbit f p -> ccw e (f e) x.

Lemma order_stable (T : finType) (f : T -> T) (x : T) :
  (fingraph.order f x).-1 <= fingraph.order f (f x) <= fingraph.order f x.
Proof.
rewrite /fingraph.order.
have eqi : fconnect f x =i predU1 x (fconnect f (f x)).
  move=> z; apply/connectP/idP.
    case=> [ [ | e p]] /=; first by move=> _ ->; rewrite inE eqxx.
    move=> /andP[]/eqP -> pe lep; rewrite /predU1; apply/orP; right.
    by apply/connectP; exists p.
  move/orP=> [/eqP -> | ]; first by exists [::].
  by move/connectP=> [p pf lp]; exists (f x :: p); rewrite //= eqxx pf.
have [k fk] : exists k, #|fconnect f (f x)| = k.+1.
  case h : #|fconnect f (f x)| => [ | k]; last by exists k.
  have : (f x) \in fconnect f (f x) by rewrite inE connect0.
  by move/card0_eq: h => ->; rewrite inE.
rewrite (eq_card eqi) cardU1 -[X in _ + #|X|]/(fconnect f (f x)).
case: (_ \notin _).
  by  rewrite fk add1n /= leqnn ltnW.
by rewrite add0n leqnn leq_pred.
Qed.

Lemma findex_decrease (T : finType) (f : T -> T) (x y : T) :
  y \in orbit f x ->
  x != y -> findex f x y = (findex f (f x) y).+1.
Proof.
rewrite /findex /orbit => yo xny.
rewrite [RHS](_ : _ = index y (traject f x (fingraph.order f (f x)).+1));
  last first.
  by rewrite /= (negbTE xny).
have : fingraph.order f (f x) = fingraph.order f x \/
       (fingraph.order f (f x)) = (fingraph.order f x).-1.
  move: (order_stable f x).
  rewrite leq_eqVlt=> /andP[/orP[/eqP -> | ] ]; first by right.
  rewrite -(orderSpred f (f x)) -(orderSpred f x) !ltnS => /= xfx fxx.
  left; apply/eqP.
  by rewrite eqSS; apply/eqP; apply: anti_leq; rewrite xfx fxx.
case=> ->; last by rewrite orderSpred.
by rewrite trajectSr -cats1 /index find_cat has_pred1 yo.
Qed.

(*
Lemma map_orbitP (m : sort mf) x b n tl :
  b \in orbit (eval m) (eval m x) ->
  findex (eval m) (eval m x) b < n ->
  map_orbit eq_op m x b n tl =
  traject (eval m) x (findex (eval m) (eval m x) b).+1 ++ tl.
Proof.
elim: n x => [// | [ | n] IH] x bin.
  rewrite ltnS leqn0 => /eqP id0 {IH}.
  by rewrite id0 /=; case: ifP.
rewrite ltnS => idn1.
rewrite -[map_orbit _ _ _ _ _ _]/
   (if eval m x == b then x :: tl else
       x :: map_orbit eq_op m (eval m x) b n.+1 tl).
case: ifP => [/eqP atb | notat]; first by rewrite -atb findex0.
rewrite trajectS findex_decrease ?notat // IH //; last first.
  by have:= findex_decrease bin (negbT notat) => <-.
move: bin; rewrite -!fconnect_orbit=>/connectP [[ | a p] xp pb].
  by move: notat; rewrite pb eqxx.
move: pb xp; rewrite /= => pb /andP[ /eqP q xp]; rewrite q.
by apply/connectP; exists p.
Qed.
*)

Lemma inh_inh' f p x :
  fcycle f (orbit f p) -> reflect (inh f p x) (inh' (orbit f p) x).
Proof.
move=> cyco.
apply/introP.
  rewrite /inh'; move=> h' y yin.
  have := next_cycle cyco yin => /= /eqP fyq.
  by have := next_cycle h' yin; rewrite <- fyq.
move/negP=> h' h; apply/h'=> {h'}; rewrite /inh' /path.cycle.
move: h cyco; rewrite /inh /orbit; rewrite -orderSpred /= => h cyco.
apply/(pathP p)=> i szi.
move/pathP: cyco => /(_ p _ szi) /= /eqP <-; apply:h.
rewrite -rcons_cons nth_rcons; case: ifP => extra; first by apply: mem_nth.
by case: ifP=> _; rewrite inE eqxx.
Qed.

Definition hull_propf (inp : seq P) (m : sort mf) (p : P) :=
  forall q, q \in orbit (eval m) p ->
     forall x, x \in inp -> x != q -> x != eval m q ->
     ccw q (eval m q) x.

Lemma hull_prop_equiv (inp : seq P) (m : sort mf) (p : P) :
  fcycle (eval m) (orbit (eval m) p) ->
  hull_propf inp m p <-> hull_prop inp (orbit (eval m) p).
Proof.
move=> cyco; split.
  move=> hp; rewrite /hull_prop /orbit /path.cycle; rewrite -orderSpred /=.
  split; first by [].
  apply/(pathP p) => i szi; apply/allP=> x xin.
  apply/implyP=> xni; apply/implyP=> xni1.
  move:(cyco); rewrite /orbit/path.cycle; rewrite -orderSpred /= => /(pathP p).
  move=> /(_ i szi) /= /eqP eqi; rewrite -eqi; apply: hp; rewrite ?eqi //.
  rewrite /orbit -orderSpred /=; rewrite -rcons_cons nth_rcons.
  case: ifP=> // cnd; first by apply: mem_nth.
  by case: ifP; rewrite inE eqxx.
move=> [sn0 hp'] x xin y yin ynx ynfx.
move: hp' cyco xin; rewrite /path.cycle /orbit; rewrite -orderSpred /=.
set pp' := traject _ _ _.
move=> /pathP hp' /pathP cyco xin.
set i := index x (p :: pp').
have szi : (i < size (p :: pp')) by rewrite index_mem.
have szi' : (i < size (rcons pp' p)) by rewrite size_rcons.
move: (cyco p i szi'); rewrite /= => /eqP evq.
move: evq; rewrite -rcons_cons nth_rcons => evq.
move/(nth_index p) : (xin); rewrite -/i => vx.
move: (hp' p i szi') => /allP /(_ y yin); rewrite -rcons_cons.
by rewrite -evq nth_rcons szi vx ynx ynfx !implyTb.
Qed.

Definition surface_propsf (inp : seq P) (tr : seq (seq P))
  (m : sort mf) (p : P) :=
  (forall t1 t2 p, t1 \in tr -> t2 \in tr ->
    inside_triangle t1 p ->
    inside_triangle t2 p -> t1 = t2) /\
  (forall q, inh (eval m) p q ->
     (q \in inp \/ exists t, t \in tr /\ inside_triangle t q)).

Definition correct_triangulationf (inp : seq P) (tr : seq (seq P))
   (m : sort mf) (p : P) :=
  triangles_prop tr /\
  (flatten tr =i inp) /\
  (orbit (eval m) p \subset inp) /\
  hull_propf inp m p /\
  surface_propsf inp tr m p /\
  uniq tr /\
  (fcycle (eval m) (orbit (eval m) p)).

Lemma correct_triangulation_complete inp tr m p :
  correct_triangulationf inp tr m p ->
  correct_triangulation ccw inp tr (orbit (eval m) p).
Proof.
move=> [] trp [] allp [] oin [] hp [] [ut et] [] utr cyco.
split;[exact trp | split; [exact allp | split ]].
  by exact: (subsetP oin).
  split;[rewrite -hull_prop_equiv  //| split; [split;[exact ut|] | ]].
  by move=> q cnq; apply: et; apply/inh_inh'.
exact: utr.
Qed.

Definition seq_to_map (T : eqType) s (mf : map_funs T) :=
  foldr (fun (x : T) m => update m x (next s x)) (map0 mf) s.

Lemma eval_seq_to_map_cat (T : eqType) mf' (s1 s2 s : seq T) x :
  map_system mf' -> x \notin s1 ->
  eval (foldr (fun (x : T) m => update m x (next s x)) (map0 mf') (s1++s2)) x =
  eval (foldr (fun (x : T) m => update m x (next s x)) (map0 mf') s2) x.
Proof.
move=> ms'; move: x; elim: s1 => [// | a s1 IH].
move=> x xnas; rewrite /= eval_update_dif //; last first.
  by move: xnas; rewrite !inE negb_or eq_sym => /andP[].
by apply: IH; move: xnas; rewrite !inE negb_or => /andP[].
Qed.

Lemma eval_seq_to_map s x :
  uniq s -> x \in s -> eval (seq_to_map s mf) x = next s x.
Proof.
move=> uns xin.
rewrite -(nth_index x xin); set j := index _ _.
have szj : j < size s by rewrite /j index_mem.
move: (uns); rewrite /seq_to_map.
rewrite -[X in uniq X -> eval (foldr _ _ X) _ = _](cat_take_drop j).
rewrite (drop_nth x szj)=> uns'; rewrite eval_seq_to_map_cat //; last first.
  move: uns'; rewrite cat_uniq => /andP[] unt /andP[] disj und.
  by apply/negP=> A; case/negP: disj=> /=; rewrite A.
by rewrite /= eval_update1.
Qed.

Lemma order_seq_to_map a s :
  uniq (a :: s) -> fingraph.order (eval (seq_to_map (a :: s) mf)) a =
  size (a :: s).
Proof.
move=> uas.
rewrite /fingraph.order.
move: (uas) => /card_uniqP <-; apply: eq_card=> x; apply/idP/idP.
  rewrite inE fconnect_orbit=> /trajectP [i _]; move: i x.
  elim=> [ /= | i IH] x; first by move=> xi; rewrite xi !inE eqxx.
  rewrite iterS; set y := iter _ _ _ => xq; have IH' := IH y erefl.
  move/(nth_index a)/esym: (IH')=> yq.
  have iys : (index y (a :: s)) < size (a :: s) by rewrite index_mem.
  by rewrite xq eval_seq_to_map // mem_next.
move=> xin; rewrite -(nth_index a xin); move: (xin); rewrite -index_mem.
elim: (index x (a :: s)) => [ //= | i IH]; first by rewrite inE connect0.
move=> szi; have szim : i < size (a:: s) by rewrite (ltn_trans (ltnSn _)).
have /IH IH' := szim.
have := next_nth (a :: s) (nth a (a :: s) i).
rewrite mem_nth // nthK // -[nth a s i]/(nth a (a :: s) i.+1) => nextq.
rewrite -nextq -eval_seq_to_map // ?mem_nth //.
by apply (connect_trans IH'); rewrite fconnect1.
Qed.

Lemma orbit_seq_to_map (s : seq P) :
  0 < size s ->
  uniq s -> orbit (eval (seq_to_map s mf)) (head p0 s) = s.
Proof.
case: s => [// | a s] _.
move=> uas; rewrite /orbit [head _ _]/= order_seq_to_map //.
rewrite -[RHS](take_size (a :: s)).
apply: (@eq_from_nth _ a).
  by rewrite size_traject size_take; case: ifP.
rewrite size_traject=> i szi; rewrite nth_traject // nth_take //.
elim: i szi => [// | i IH] szi.
have szi' : i < size (a :: s) by apply: ltnW.
by rewrite iterS IH // eval_seq_to_map // ?next_nth // ?mem_nth// nthK.
Qed.

Lemma inh_orbit f p q : fcycle f (orbit f p) -> q \in orbit f p ->
  forall x, inh f p x <-> inh f q x.
Proof.
move=> cyc qin x; have [k oq] := orbit_rot_cycle cyc (orbit_uniq _ _) qin.
by rewrite /inh; split=> inh e; move: (inh e); rewrite oq mem_rot.
Qed.

Lemma correct_triangulation_perm i i' tr m p p' :
  perm_eq i i' -> p' \in (orbit (eval m) p) ->
  correct_triangulationf i tr m p ->
  correct_triangulationf i' tr m p'.
Proof.
move=> ii' pp' [] trP [] ctr [] incP [] hulP [] [no_i cov] [] unitr cyc.
split; first by apply: trP.
split.
  by move=> z; rewrite ctr; apply: perm_mem.
have [k oq] := orbit_rot_cycle cyc (orbit_uniq _ _) pp'.
have oqi : orbit (eval m) p' =i orbit (eval m) p.
  by move=> z; rewrite oq mem_rot.
split.
  apply/subsetP=> z; rewrite oqi; move/subsetP: incP=> A /A.
  by rewrite (perm_mem ii').
split.
  move=> q qin x xin'; have xin : x \in i by rewrite (perm_mem ii').
  by apply: (hulP q _ x xin); rewrite -oqi.
split;[split => // | ].
  move=> q; rewrite -(inh_orbit cyc pp') => qin.
  case : (cov _ qin) => [qinp | ex_t].
    by left; rewrite -(perm_mem ii').
  right; exact ex_t.
by rewrite oq rot_cycle.
Qed.

Lemma seq3_perm s : size s = 3 -> perm_eq s (seq3 s).
Proof.
case: s => [ | a [| b [| c []]]]// _.
rewrite /seq3 ![nth _ _ _]/=; case ccw => //.
by rewrite (perm_catCA [::a] [::b] [::c]).
Qed.

Lemma seq3_ccw s : size s = 3 -> uniq s -> ccw_seq (seq3 s).
Proof.
case s=> [| a [| b [| c []]]] // _ unabc.
rewrite /seq3 ![nth _ _ _]/=; case test: (ccw a b c) => //.
by move: (Knuth_3 unabc)=> /orP; rewrite test orFb.
Qed.

Lemma orbit0 f (x : P) : x \in orbit f x.
Proof.  by rewrite -fconnect_orbit connect0. Qed.

Notation eval_update_dif := (@eval_update_dif P mf ms).
Notation eval_update1 := (@eval_update1 P mf ms).
Notation map_iterP := (@map_iterP P mf ms).
Notation find_purple_points := (@find_purple_points P ccw mf).

Lemma map_cycle3_value a b c : uniq [:: a; b; c] ->
  eval (map_cycle3 [:: a; b; c]) a = b /\
  eval (map_cycle3 [:: a; b; c]) b = c /\
  eval (map_cycle3 [:: a; b; c]) c = a.
Proof.
move=> unabc; rewrite /map_cycle3 eval_update1; split; first by [].
have /andP [/andP [anb anc ] bnc] : (a != b) && (a != c) && (b != c).
  by move: unabc; rewrite /= !inE negb_or andbT.
rewrite eval_update_dif // eval_update1 eval_update_dif // eval_update_dif //.
by rewrite eval_update1.
Qed.

Lemma orbit_map_cycle3 a b c: uniq [:: a; b; c] ->
  orbit (eval (map_cycle3 [:: a; b; c])) a = [:: a; b; c].
Proof.
move=> unabc; move: (map_cycle3_value unabc).
set m := map_cycle3 _ => [][va [vb vc]].
have /andP [/andP [anb anc] bnc] : (a != b) && (a != c) && (b != c).
  by move: unabc; rewrite /= !inE negb_or andbA andbT.
have size : fingraph.order (eval m) a = 3.
  rewrite /fingraph.order -[3]/(size [:: a; b; c]) -(card_uniqP (unabc)).
  apply: eq_card => z; apply/connectP/idP.
    case=> x; have : a \in [:: a; b; c] by rewrite !inE eqxx.
    elim: x {1 3 4}a => [| e' tl IH] e ein; first by move=> _ ->; exact ein.
    set C := (_ \in _); rewrite /= => /andP []; move: ein; rewrite /= !inE.
    move=> /orP [ | /orP []] /eqP ->; rewrite ?va ?vb ?vc => vv;
    (have : e' \in [:: a; b; c] by rewrite -(eqP vv) !inE eqxx ?orbT);
    by rewrite /C; apply: IH.
  rewrite !inE => /orP [ | /orP [] ] /eqP ->; first by exists [::].
    by exists [:: b] => //=; rewrite va eqxx.
  by exists [:: b; c] => //=; rewrite va vb ?eqxx.
by rewrite /orbit size /= va vb.
Qed.

Lemma Knuth_1_1 a b c : ccw a b c -> ccw c a b.
Proof. by move=> *; apply/Knuth_1/Knuth_1. Qed.

Lemma base_case inp tr m p :
  size inp = 3 -> uniq inp -> naive inp = (tr, m, p) ->
  correct_triangulationf inp tr m p.
Proof.
case: inp => [ | a [| b [| c [|]]]] // s3 unabc.
rewrite /naive /= => [][] <- <- <-; set l := seq3 _.
have ps3 : perm_eq [:: a; b; c] l by apply: seq3_perm.
have s3' : size l = 3 by rewrite -(perm_size ps3).
have unl : uniq l by rewrite -(perm_uniq ps3).
have o0 := orbit0 (eval (map_cycle3 l)) (head p0 l).
move: (ps3); rewrite perm_sym => ps3'.
apply: (correct_triangulation_perm ps3' o0).
have := seq3_ccw s3 unabc; rewrite -/l.
move: (l) s3' unl=> {ps3' o0 ps3 l unabc s3 a b c}.
case=> [| a [| b [| c []]]] // s3 unabc abc.
split; first by move=> t; rewrite !inE => /eqP-> //.
split; first by [].
split; first by rewrite orbit_map_cycle3.
split.
  move=> q; rewrite orbit_map_cycle3 //.
  by have [va [vb vc]] := map_cycle3_value unabc; rewrite !inE;
  move => /orP [ | /orP []] /eqP ->; rewrite ?va ?vb ?vc => x;
  rewrite !inE => /orP [ | /orP []] /eqP ->;
  rewrite ?eqxx // => _ _; rewrite Knuth_1 // Knuth_1 //.
rewrite /surface_propsf and_assoc.
split; first by move=> t1 t2 p'; rewrite !inE => /eqP -> /eqP ->.
rewrite /inh orbit_map_cycle3 //= -?[update _ _ _]/(map_cycle3 [:: a; b; c]).
split.
  move=> q qin; right; exists [:: a; b; c]; rewrite !subE; split; first by [].
  move: (map_cycle3_value unabc) => [va [vb vc]].
  rewrite /inside_triangle; move: (qin a) (qin b) (qin c).
  by rewrite !subE va vb vc => /(_ isT) -> /(_ isT) -> /(_ isT) ->.
by move: (map_cycle3_value unabc) => [-> [-> ->]]; rewrite !eqxx.
Qed.

Lemma uniq_hull2 inp m p e:
  2 < size inp -> uniq inp ->
  e \in orbit (eval m) p ->
  hull_propf inp m p ->
  uniq [:: e; eval m e; eval m (eval m e)].
Proof.
move=> s3 uni ein hulP.
have [q [qin qdif]] : exists q, q \in inp /\ q \notin [:: e; eval m e].
  move: s3 uni; case h : inp => [| a [| b [| c tl]]] // _.
  have [ang | aok] := boolP(a \in [:: e; eval m e]); last first.
    by exists a; rewrite aok !subE.
  have [bng | bok] := boolP(b \in [:: e; eval m e]); last first.
    by exists b; rewrite bok !subE.
  move=> U; exists c; rewrite !subE negb_or; split=> //; move: ang bng U.
  by rewrite /= !inE => /orP[] /eqP -> /orP [] /eqP ->;
     rewrite ?eqxx ?orbT ?andbF ?negb_or !andbA -!(eq_sym c) // =>
     /andP [] /andP [] /andP [] /andP [] /andP [] /andP [] => *;
     apply/andP; split.
have /andP [qne qnme] : (q != e) && (q != eval m e).
  by move: qdif; rewrite !subE negb_or.
have := hulP _ ein _ qin qne qnme => efq; move/Knuth_2: (efq)=> nfeq.
have enf : e != eval m e.
  by apply/eqP=> abs; move: efq nfeq; rewrite -abs=> ->.
have [/eqP qff | qnff] := boolP (q == eval m (eval m e)).
  by rewrite /= !subE negb_or enf -qff -!(eq_sym q) qne qnme.
have fein := mem_orbit1 ein.
have := hulP _ fein _ qin qnme qnff => feffq; move/Knuth_2: (feffq)=> n'.
rewrite /= !subE negb_or enf /=; apply/andP; split; apply/eqP=> abs.
  by move: n'; rewrite -abs efq.
by move: feffq n'; rewrite -abs=> ->.
Qed.

Lemma no_triangle_red_edge (inp : seq P) (tr : seq (seq P)) m p q :
  (forall t, t \in tr -> ~~ inside_triangle t q) ->
  2 < size inp -> uniq inp ->
  q \notin inp ->
  correct_triangulationf inp tr m p ->
  exists2 e, e \in orbit (eval m) p & ccw (eval m e) e q.
Proof.
move=> no_t s3 uni qnotin cot.
move: (cot) => [] trP [] ctr [] incP [] hulP [] [no_i cov] cyc.
have [] := boolP ([exists e, (e \in orbit (eval m) p) && ccw (eval m e) e q]).
  by move=> /existsP [e /andP [ein ered]]; exists e; rewrite ?ein ?ered.
rewrite negb_exists=> /forallP allblue; have inhq : (inh (eval m) p q).
  rewrite /inh=> e ein; move: (allblue e); rewrite ein andTb=> /negbTE eblue.
  have qno : q \notin orbit (eval m) p.
    by apply/negP=> abs; move/negP: qnotin; apply; rewrite (subsetP incP).
  have qne : q != e by apply/eqP=> abs; move: qno; rewrite abs ein.
  have qnfe : q != eval m e.
    by apply/eqP=> abs; move: qno; rewrite abs mem_orbit1.
  have /Knuth_3 : uniq [:: e; eval m e; q].
    rewrite /= !subE negb_or -!(eq_sym q) qnfe qne.
    have:= (uniq_hull2 s3 uni ein hulP) => /=.
    by rewrite !inE negb_or => /andP[] /andP [] ->.
  by move/orP; rewrite eblue orbF.
have := cov _ inhq; case; first by rewrite (negbTE qnotin).
by move=> [] t [] ttr qint; move: (no_t t ttr); rewrite qint.
Qed.

Lemma perm_flatten_mem (T : finType) (s1 s2 : seq (seq T)) :
  perm_eq s1 s2 ->
  flatten s1 =i flatten s2.
Proof.
elim: {s1} (size s1) {-2} s1 s2 (erefl (size s1))=> [ | n IH] s1 s2.
  move=> /eqP; rewrite size_eq0 perm_sym=> /eqP -> /perm_size/eqP.
  by rewrite size_eq0=> /eqP ->.
case: s1 => [| e s1] //= /eqP; rewrite eqSS => /eqP sz1.
move=> peq; have ein : e \in s2 by rewrite -(perm_mem peq) !subE.
have sz2 : size s2 = n.+1 by rewrite -(perm_size peq) /= sz1.
have szr : size (rem e s2) = n by rewrite (size_rem ein) sz2.
have peq' : perm_eq s2 (e :: rem e s2) by apply: perm_to_rem.
have : perm_eq (e :: s1) (e :: rem e s2) by apply/(perm_trans peq).
rewrite perm_cons => peq''.
case q2 : s2 => [| e' s2']; first by move: sz2; rewrite q2.
have [ee' | ene'] := boolP (e == e').
  rewrite (eqP ee') /= => z; rewrite !mem_cat; case zin: (z \in e')=> //=.
  by apply: IH=> //; move: peq''; rewrite q2 /= eq_sym ee'.
move: (ein) => /perm_to_rem peq3.
have ein2 : e \in s2 by rewrite -(perm_mem peq) inE eqxx.
have ein2' : e \in s2' by move: ein2; rewrite q2 inE (negbTE ene').
move=> z; rewrite [LHS]/= mem_cat; case zin : (z \in e) => /=.
  apply/esym=> /=.
  rewrite mem_cat; case zin' : (z \in e') => //=.
  have peq4 : perm_eq s2' (e :: rem e s2') by apply perm_to_rem.
  have sz' : size s2' = n by apply/eqP; rewrite -eqSS -sz2 q2.
  by rewrite (IH _ (e :: rem e s2') sz') //=; rewrite mem_cat zin.
have ein1 : e' \in (e :: s1) by rewrite (perm_mem peq) q2 !inE eqxx.
have ein1': e' \in s1 by move: ein1; rewrite !inE eq_sym (negbTE ene').
move: (ein1') => /perm_to_rem peq4.
rewrite (IH _  _ sz1 peq4) /= !mem_cat; case : (z \in e') => //=.
have -> : (z \in flatten (rem e' s1)) = (z \in (flatten (e :: rem e' s1))).
  by rewrite /= mem_cat zin.
apply/esym/IH.
  by apply/eqP; rewrite -eqSS -sz2 q2.
rewrite -(perm_cons e') -q2 perm_sym (perm_catCA [:: e'] [:: e]) /=.
by apply: perm_trans peq; rewrite perm_cons perm_sym; apply: perm_to_rem.
Qed.

Section in_existing_triangle.

Variables (inp t : seq P) (tr trmt : seq (seq P)) (m : sort mf) (p q : P).
Hypotheses (s3 : 2 < size inp) (uni : uniq (q :: inp)).
Hypothesis cot : correct_triangulationf inp tr m p.
Hypotheses (qin : inside_triangle t q) (ptr : perm_eq tr (t :: trmt)).

Lemma tint : t \in tr.
Proof. by rewrite (perm_mem ptr) !subE. Qed.

Lemma t_dec :
  triangles_prop tr ->
  exists a b c, t = [:: a; b; c] /\ uniq [:: a; b; c] /\ ccw a b c.
Proof.
move=> trP.
by move/trP: tint=> []; case: (t) => [| a [| b [| c []]]] //; exists a, b, c.
Qed.

Lemma inside_triangles_seq1P :
  forall u, u \in inside_triangles t q -> size u = 3 /\ uniq u /\ ccw_seq u.
Proof.
move: (cot)=> [] trP [] ctr [] incP [] hulP [] no_i [] cov cyc u.
case : (t_dec trP) => a [b [c [tq [unabc abc]]]]; rewrite tq.
have : q \notin [:: a; b; c].
  apply/negP; rewrite -tq => abs; move: uni => /=; rewrite andbC=> /andP[] _.
  by move/negP; apply; rewrite -ctr (perm_flatten_mem ptr) /= mem_cat abs.
move: (unabc) => /=; rewrite !inE andbT !negb_or -!andbA.
move => /andP[] anb /andP[] anc bnc /andP[] qna /andP [] qnb qnc.
move: qin; rewrite /inside_triangle tq=> /andP[] /andP[]
   /Knuth_1 /Knuth_1 abq /Knuth_1 /Knuth_1 bcq /Knuth_1 /Knuth_1 caq.
move => /orP [ | /orP []] /eqP -> /=;
  rewrite !inE negb_or ?qna ?qnb ?qnc ?anb ?bnc ?abq ?bcq ?caq //.
by rewrite eq_sym anc.
Qed.

Lemma flatten_inside_triangles : flatten (inside_triangles t q) =i q::t.
Proof.
move: (cot)=> [] trP [] ctr [] incP [] hulP [] no_i [] cov cyc.
have [a [b [c [tq [ut abc]]]]] := t_dec trP; rewrite tq /= => z; rewrite !subE.
rewrite !(orbCA _ (z == q)) !orbA !orbb -!orbA ?orbb; congr orb.
rewrite -1?(orbC (z == a)) !(orbCA _ (z == a)) !orbA !orbb -!orbA ?orbb.
by congr orb; rewrite orbA orbb.
Qed.

Lemma oriented_no_dup a b : ~~ccw a a b.
Proof using ccs.
by apply/negP=> A; move/Knuth_2: (A) => /negP; apply.
Qed.

Lemma oriented_diff c a b : ccw a b c -> a != b.
Proof using ccs.
move=> abc; apply/negP=> /eqP A; move: abc; rewrite A.
apply/negP/oriented_no_dup.
Qed.

Lemma inside_triangle_edge1 a b c d e f :
  ccw a b c -> ccw a b d -> ccw a b e -> ccw c d f -> ccw c f e -> ccw f d e ->
  ccw a d c -> ccw a e c -> ccw a b f.
Proof.
move=> abc abd abe cdf cfe fde adc aec.
have [cna [ena enc]] : c != a /\ e != a /\ e != c.
  move: (abc) (abe) (cfe)=> /Knuth_1_1/oriented_diff ->.
  by move=> /Knuth_1_1/oriented_diff -> /Knuth_1_1/oriented_diff.
have [dna dne] : d != a /\ d != e.
  by move: abd fde=> /Knuth_1_1/oriented_diff-> /Knuth_1/oriented_diff.
have [anc [cne and]] : a != c /\ c != e /\ a != d.
  by repeat split; rewrite eq_sym.
have cde : ccw c d e.
  by apply: (@Knuth_4 _ _ _ f); do 3 (apply: Knuth_1 => //).
have [ecd cae] : ccw e c d /\ ccw c a e by split; do 3 (apply: Knuth_1 => //).
have caf : ccw c a f.
  by apply: (Knuth_5' _ ecd); do 3 (apply: Knuth_1 => //).
have/Knuth_3 [dae | ade] : uniq [:: d; a; e].
    by rewrite /= !inE negb_or dna dne eq_sym ena.
  apply: (Knuth_5' _ cae); do 3 (apply: Knuth_1 => //).
  by apply/Knuth_1_1/(Knuth_5 _ ecd); do 3 (apply: Knuth_1 => //).
have [cad dec] : ccw c a d /\ ccw d e c by split; do 3 (apply/Knuth_1 => //).
apply: (Knuth_5' _ cad); do 3 (apply/Knuth_1 => //).
apply/Knuth_1_1/(Knuth_5 _ dec); do 3 (apply/Knuth_1 => //).
Qed.

Lemma inside_triangle_left_of_edge a b c d e f :
  ccw a b c -> ccw a b d -> ccw a b e -> ccw c d f -> ccw c f e -> ccw f d e ->
  ccw a b f.
Proof.
move=> abc abd abe cdf cfe fde.
have /andP[ /andP[ad dc] ca] : (a != d) && (d !=c) && (c != a).
  move/oriented_diff: cdf abd abc; rewrite eq_sym !(eq_sym a) => ->.
  by move/Knuth_1_1/oriented_diff=> -> /Knuth_1_1/oriented_diff.
have /andP[ /andP[ac ce] ea] : (a != c) && (c != e) && (e != a).
  move: cfe abe=> /Knuth_1_1/oriented_diff; rewrite eq_sym=> ->.
  by rewrite eq_sym ca=> /Knuth_1_1/oriented_diff.
have /Knuth_3 [adc | dac] : uniq [:: a; d; c].
    by rewrite /= !inE negb_or ad ac dc.
  have /Knuth_3 [ace | cae] : uniq [:: a; c; e].
      by rewrite /= !subE negb_or ce ac eq_sym ea.
    apply: (inside_triangle_edge1 abe abc abd); do 3 (apply/Knuth_1 => //).
    by apply: (Knuth_5 abd abc abe).
  by apply: (inside_triangle_edge1 abc abd abe); do 3 (apply/Knuth_1 => //).
have ed :e != d.
  by move: fde=> /Knuth_1/oriented_diff; rewrite eq_sym.
have /Knuth_3 [aed | cae] : uniq [:: a; e; d].
    by rewrite /= !subE negb_or ed ad eq_sym ea.
  by apply: (inside_triangle_edge1 abd abe abc); do 3 (apply/Knuth_1=> //).
apply: (inside_triangle_edge1 abe abc abd); do 3 (apply/Knuth_1=> //).
by apply: (Knuth_5 abc abd); do 3 (apply/Knuth_1=> //).
Qed.

Lemma inside_triangle_in_hull z x :
  uniq inp ->
  triangles_prop tr ->
  flatten tr =i inp ->
  hull_propf inp m p ->
  z \in orbit (eval m) p ->
  inside_triangle t x ->
  x != z -> x != eval m z -> ccw z (eval m z) x.
Proof.
move=> uni' trP ctr hulP zin xin xnz xnfz.
have znfz : z != eval m z.
  have := uniq_hull2 s3 uni' zin hulP.
  by rewrite /= !inE negb_or=> /andP[] /andP[].
have [a [b [c [tq [ut abc]]]]] := t_dec trP.
have tsub : forall u, u \in t -> u \in inp.
  by move=> u uint; rewrite -ctr (perm_flatten_mem ptr) /= mem_cat uint.
have /andP[/andP[ain bin] cin] : (a \in inp) && (b \in inp) && (c \in inp).
   by rewrite !tsub // tq !subE.
have[/andP[znotin fznotin] | ]:= boolP ((z \notin t) && (eval m z \notin t)).
  have /andP[/andP[zfa zfb] zfc] :
    ccw z (eval m z) a && ccw z (eval m z) b && ccw z (eval m z) c.
    by rewrite !hulP //; apply/negP=> A; move: znotin fznotin;
       rewrite -(eqP A) tq !subE.
  by apply: (inside_triangle_left_of_edge zfa zfb zfc); move: xin;
  rewrite tq /= => /andP[] /andP[] // => *; do 2 (apply/Knuth_1 => //).
have [/andP [zint fzint] _ | onlyone] := boolP ((z \in t) && (eval m z \in t)).
have gen : forall u, u \in rem z (rem (eval m z) t) -> ccw z (eval m z) u.
    move=> u uin; have uin1 : u \in rem (eval m z) t by apply/(mem_rem uin).
    have uin2 : u \in inp by apply/tsub/(mem_rem uin1).
    have /(mem_rem_uniq (eval m z)) nn : uniq t by rewrite tq.
    have /(mem_rem_uniq z) nn' : uniq (rem (eval m z) t).
      by apply: rem_uniq; rewrite tq.
    move: uin uin1; rewrite nn nn' !inE => /andP[] unz _ /andP[] unfz _.
    apply: (hulP z zin u uin2 unz unfz).
  have : ((z == a) && (eval m z == b)) || ((z == b) && (eval m z == c)) ||
         ((z == c) && (eval m z == a)).
    by move: zint fzint znfz ut gen; rewrite tq /= !inE negb_or
      => /orP[|/orP[]]/eqP -> /orP[|/orP[]]/eqP ->;
      rewrite !eqxx ?andbT ?orbT => //= _ /andP[] /andP[] /negbTE c1 /negbTE c2
        /negbTE c3; do 2 (rewrite /= ?c1 ?c2 ?c3); rewrite /= ?eqxx ?inE;
        set u' := (X in [:: X]); move=> /(_ u'); rewrite !inE eqxx /u';
        move=> /(_ isT);
        do 3 ((move=>/Knuth_2; rewrite abc //) || (move=> /Knuth_1)).
  by move=> /orP[ /orP [] |] /andP[] /eqP -> /eqP ->; move: xin;
     rewrite /inside_triangle tq => /andP[] /andP[].
rewrite negb_and !negbK => /orP[zint | fzint].
  move: onlyone; rewrite zint /= => fznint.
  have [b' [c' /andP[] /andP[] /andP[] /andP[] zbx czx zfzb zfzc czb]] :
   exists b' c', ccw z b' x && ccw c' z x && ccw z (eval m z) b' &&
   ccw z (eval m z) c' && ccw c' z b'.
    by move: zint xin abc; rewrite tq /= !inE => /orP [| /orP[]] /eqP <-;
    set b1 := (X in ccw z X _); set c1 := (X in ccw X z _) => /andP[]/andP[];
    move=> A B C; exists b1, c1; rewrite ?A ?B ?C /= !hulP //;
    move/oriented_diff: A; move/oriented_diff: B; move/oriented_diff: C;
    rewrite !(eq_sym _ z) /c1 /b1=> // _ _ _; try(apply/eqP=> A; move: fznint;
    rewrite -A tq !subE //); do 3 (apply/Knuth_1 => //).
  move: zfzc=> /Knuth_1_1=> czfz.
  by apply: (Knuth_5' czfz czb czx zfzb zbx).
move: onlyone; rewrite fzint andbT => znint.
have [b' [c' /andP[] /andP[] /andP[] /andP[] fzbx cfzx zfzb zfzc cfzb]] :
 exists b' c', ccw (eval m z) b' x && ccw c' (eval m z) x &&
    ccw z (eval m z) b' &&
    ccw z (eval m z) c' && ccw c' (eval m z) b'.
  by move: fzint xin abc; rewrite tq /= !inE => /orP [| /orP[]] /eqP <-;
  set b1 := (X in ccw (eval m z) X _); set c1 := (X in ccw X (eval m z) _);
  move=> /andP[]/andP[] A B C; exists b1, c1; rewrite ?A ?B ?C /= !hulP //;
  move/oriented_diff: A; move/oriented_diff: B; move/oriented_diff: C;
  rewrite !(eq_sym _ (eval m z)) /c1 /b1=> // _ _ _;
  try(apply/eqP=> A; move: znint;
  rewrite -A tq !subE //); do 3 (apply/Knuth_1 => //).
apply/Knuth_1_1; move: cfzb zfzb=> /Knuth_1 fzbc /Knuth_1 fzbz.
move: cfzx zfzc=> /Knuth_1 fzxc /Knuth_1 fzcz.
by apply: (Knuth_5 fzbx fzbc fzbz fzxc fzcz).
Qed.

Lemma uniq_take (T : eqType) (n : nat) (s : seq T) :
    uniq s -> uniq (take n s).
Proof.
by rewrite -[X in uniq X](cat_take_drop n s); rewrite cat_uniq => /andP[].
Qed.

Lemma inside_sub_triangle a b c d e :
  inside_triangle [:: a; b; c] d ->
  inside_triangle [:: a; b; d] e ->
  inside_triangle [:: a; b; c] e.
Proof.
move=> /= /andP[] /andP[] abd bcd cad /andP[] /andP[] abe bde dae.
rewrite abe.
have abc : ccw a b c by apply/(Knuth_4 abd bcd cad).
have -> : ccw b c e by apply/(Knuth_5' abc abd abe bcd bde).
have -> // : ccw c a e.
by apply/Knuth_1_1/(Knuth_5 abe abd abc); apply/Knuth_1.
Qed.

Lemma inside_triangle_K1 a b c d :
  inside_triangle [:: a; b; c] d = inside_triangle [:: b; c; a] d.
Proof. by rewrite /= -andbA andbC. Qed.

Lemma sub_triangle_unique e (j : 'I_3) :
  triangles_prop tr ->
  inside_triangle (q :: (take 2 (rot j t))) e ->
  ~~inside_triangle (q :: (take 2 (rot (j + 1)%R t))) e.
Proof.
move=> trP; have [a [b [c [tq [unabc abc]]]]] := t_dec trP.
by rewrite tq; case: j => [[| [| [| ?]]] ?] //= =>
  /andP[] /andP[] _ _ /Knuth_2/negbTE ->.
Qed.

Lemma inside_triangles_index u :
  triangles_prop tr ->
  (u \in inside_triangles t q) =
  [exists j : 'I_3, u == q :: (take 2 (rot j t))].
Proof.
move=> trP; have [a [b [c [tq [unabc abc]]]]] := t_dec trP.
rewrite tq /inside_triangles; apply/idP/existsP.
  rewrite !inE=> /orP [| /orP[]] /eqP ->;
  (exists 0%R; rewrite /= eqxx //) || (exists 1%R; rewrite /= eqxx //) ||
  (exists ((-1)%R); rewrite /= eqxx //) || idtac.
by move=> [ [ [| [| [| ?]]] ?] // /eqP ->] /=; rewrite !subE.
Qed.

Lemma jdif_add1 (i j : 'I_3) : i != j -> (i == j + 1)%R || (j == i + 1)%R.
Proof.
by case: i => [ [| [| [| ?]]] ?] //; case: j => [ [| [| [| ?]]] ?] //.
Qed.

Lemma inside_triangle_uniq (a b c d : P) :
  inside_triangle [:: a; b; c] d -> uniq [:: a; b; c; d].
Proof.
move=> /andP[] /andP[] abd bcd cad; move: (abd) (bcd) (cad).
move=> /oriented_diff anb /oriented_diff bnc /oriented_diff cna.
move: (abd) (bcd) (cad)=> /Knuth_1/oriented_diff bnd.
move=>/Knuth_1/oriented_diff cnd /Knuth_1/oriented_diff and.
by rewrite /= !subE !negb_or anb and bnc bnd cnd eq_sym cna.
Qed.

Definition auto_uniq := (inE, negb_or, (fun x y z=> esym (andbA x y z))).

Lemma choose_sub_triangle a b c d e :
  d != e ->
  inside_triangle [:: a; b; c] d ->
  inside_triangle [:: a; b; c] e ->
  exists t, t \in inside_triangles [:: a; b; c] d /\
     inside_triangle t e.
Proof.
move=> dne abcd abce; move: (abcd) => /inside_triangle_uniq und.
move: (abce) => /inside_triangle_uniq une.
move: abcd abce=> /andP[]/andP[] abd bcd cad /andP[]/andP[] abe bce cae.
suff :
  [|| inside_triangle [:: a; b; d] e, inside_triangle [:: b; c; d] e |
      inside_triangle [:: c; a; d] e].
  by move=> /orP[| /orP[]]; rewrite -inside_triangle_K1; set u := (_ :: _);
  exists u=> /=; rewrite /u !subE; split.
rewrite /inside_triangle.
have /Knuth_3 [bde | dbe] : uniq [:: b; d; e].
    rewrite /= !negb_or dne !andbT; move: und une; rewrite /= !auto_uniq.
    by repeat ((move=> /andP[] A; rewrite ?A {A}) || move=> _).
  have /Knuth_3 [cde | dce] : uniq [:: c; d; e].
      rewrite /= !negb_or dne !andbT; move: und une; rewrite /= !auto_uniq.
      by repeat ((move=> /andP[] A; rewrite ?A {A}) || move=> _).
    have /Knuth_3 [ade | dae] : uniq [:: a; d; e].
        rewrite /= !negb_or dne !andbT; move: und une; rewrite /= !auto_uniq.
        by repeat ((move=> /andP[] A; rewrite ?A {A}) || move=> _).
      by move/Knuth_1/Knuth_2: cad; rewrite (@Knuth_5 d e a b c) //;
        do 3 (apply/Knuth_1 => //).
    by rewrite abe bde dae ?orbT.
  have /Knuth_3 [ade | dae] : uniq [:: a; d; e].
      rewrite /= !negb_or dne !andbT; move: und une; rewrite /= !auto_uniq.
      by repeat ((move=> /andP[] A; rewrite ?A {A}) || move=> _).
    by rewrite cae ade dce ?orbT.
  by rewrite abe bde dae ?orbT.
have /Knuth_3 [cde | dce] : uniq [:: c; d; e].
    rewrite /= !negb_or dne !andbT; move: und une; rewrite /= !auto_uniq.
    by repeat ((move=> /andP[] A; rewrite ?A {A}) || move=> _).
  by rewrite bce cde dbe ?orbT.
have /Knuth_3 [ade | dae] : uniq [:: a; d; e].
    rewrite /= !negb_or dne !andbT; move: und une; rewrite /= !auto_uniq.
    by repeat ((move=> /andP[] A; rewrite ?A {A}) || move=> _).
  by rewrite cae ade dce ?orbT.
by move/Knuth_1/Knuth_2: cae; rewrite (@Knuth_5 e d a b c) //;
  do 3 (apply/Knuth_1 => //).
Qed.

Lemma uniq_inside_triangles a b c d :
  uniq [:: a; b; c] ->
  uniq (inside_triangles [:: a; b; c] d).
Proof.
move=> abc; rewrite /=; rewrite !subE negb_or.
by apply/andP; split;[apply/andP; split | ]; apply/eqP=> [][] A B; move: abc;
  rewrite ?A ?B /= !subE.
Qed.

Lemma correct_inside_triangle :
  correct_triangulationf (q :: inp) (inside_triangles t q ++ trmt) m p.
Proof.
move: (cot)=> [] trP [] ctr [] incP [] hulP [] [no_i cov] [] unitr cyc.
have uni' : uniq inp by move: uni; rewrite /= => /andP[].
have [a [b [c [tq [ut abc]]]]] := t_dec trP.
split.
  move=> u; rewrite mem_cat => /orP[] utrmt; last first.
    by apply: trP; rewrite (perm_mem ptr) inE utrmt orbT.
  by apply: (inside_triangles_seq1P utrmt).
split.
  rewrite flatten_cat=> z; rewrite mem_cat flatten_inside_triangles !inE -orbA.
  congr orb; rewrite -[LHS]mem_cat -[_ ++ _]/(flatten (t :: trmt)).
  by rewrite -(perm_flatten_mem ptr); apply: ctr.
split.
  by apply/subsetP=> z /(subsetP incP); rewrite inE orbC => ->.
split.
  move=> z zin x xin xnz xnfz; move: xin; rewrite !inE => /orP []; last first.
    by move=> xin; apply: (hulP z zin x xin xnz xnfz).
  move=> /eqP xq; move: xnz xnfz; rewrite xq=> qnz qnfz.
  by apply: inside_triangle_in_hull.
split.
  split.
    move=> t1 t2 p1; rewrite !mem_cat.
    have gen: forall u, u \in inside_triangles t q -> inside_triangle u p1 ->
             inside_triangle t p1.
    move: qin; rewrite tq => qin'; have th := inside_triangle_K1.
    by move=> u /orP [|/orP[|/orP[]]] // /eqP ->; rewrite th => A;
      repeat (apply: inside_sub_triangle A => // || rewrite // th).
    have ttr : t \in tr by rewrite (perm_mem ptr) !subE.
    have trmtsub : {subset trmt <= tr}.
      by move=> z zin; rewrite (perm_mem ptr) inE zin orbT.
    move=> /orP[t1sub | t1o] /orP[t2sub |t2o] p1t1 p1t2.
          move: t1sub t2sub; rewrite !inside_triangles_index //.
          move=> /existsP [i /eqP t1v] /existsP [j /eqP t2v]; rewrite t1v t2v.
          have [/eqP -> // | /jdif_add1 ad1] := boolP (i == j).
          by move: ad1 t1v t2v p1t1 p1t2 => /orP [] /eqP ->;
          set k := (X in (X + 1)%R); rewrite -/k => -> -> A B;
          move: (@sub_triangle_unique p1 k trP); rewrite ?B ?A => /(_ isT).
        move: (no_i _ _ _ ttr (trmtsub _ t2o) (gen _ t1sub p1t1) p1t2)=> A.
        by move: unitr; rewrite (perm_uniq ptr) A /= t2o.
      move: (no_i _ _ _ ttr (trmtsub _ t1o) (gen _ t2sub p1t2) p1t1)=> A.
      by move: unitr; rewrite (perm_uniq ptr) A /= t1o.
    by apply: (no_i _ _ _ (trmtsub _ t1o) (trmtsub _ t2o) p1t1 p1t2).
  move=> p1 p1in; case: (cov p1 p1in) => [p1inp | [t' [t'in p1int']]].
    by left; rewrite inE p1inp orbT.
  have [/eqP tt' | tnott'] := boolP (t == t'); last first.
    right; exists t'; rewrite mem_cat p1int'; split => //; move: t'in.
    by rewrite (perm_mem ptr) inE eq_sym (negbTE tnott') /= orbC => ->.
  have [/eqP -> | p1nq] := boolP( p1 == q); first by left; rewrite !subE.
  right; move: p1nq p1int' qin; rewrite eq_sym -tt' tq=> qnp1 p1int qin'.
  have [t1 [t1in p1int1]]:= (choose_sub_triangle qnp1 qin' p1int).
  by exists t1; rewrite mem_cat t1in.
split=> //.
rewrite cat_uniq andbA; apply/andP; split; last first.
  by move: unitr; rewrite (perm_uniq ptr) cons_uniq => /andP[].
apply/andP; split; last first.
  have qnotin : q \notin inp by move: uni; rewrite cons_uniq=>/andP[].
  apply/negP=> /hasP [t' t'trmt /= t'ins]; case/negP: qnotin.
  rewrite -ctr (perm_flatten_mem ptr) /= mem_cat; apply/orP; right.
  have qt' : q \in t'.
    move: t'ins; rewrite tq /= !inE.
    by move => /orP [|/orP[]] /eqP ->; rewrite !subE.
  by apply/flattenP; exists t'.
by rewrite tq; apply: uniq_inside_triangles.
Qed.

End in_existing_triangle.

Section outside_hull.

Variables (inp : seq P) (tr : seq (seq P)) (m : sort mf) (p q : P).
Hypotheses (s3 : 2 < size inp) (uni : uniq (q :: inp)).
Hypothesis cot : correct_triangulationf inp tr m p.

Let f := eval m.

Variable red_point : P.
Hypothesis redin : red_point \in orbit f p.
Hypothesis redP : ccw (f red_point) red_point q.


Lemma convex_hull_path_inj : { in orbit f p &, injective f}.
Proof.
move: (cot)=> [] trP [] ctr [] incP [] hulP [] sfp [] unitr cyc.
by apply: cycle_orbit_injective.
Qed.

Lemma same_orbit : {in orbit f p, forall x, orbit f x =i orbit f p}.
Proof.
move: (cot)=> [] trP [] ctr [] incP [] hulP [] sfp [] unitr cyc.
move=> x xin; have [j ->]:= (orbit_rot_cycle cyc (orbit_uniq _ _) xin).
by move=> z; rewrite mem_rot.
Qed.

Lemma qnotiter a n : a \in orbit f p -> q != iter n f a.
Proof.
move: (cot)=> [] trP [] ctr [] incP [] hulP [] sfp [] unitr cyc.
move=> ain; apply/negP=> /eqP A; move: uni.
by rewrite cons_uniq A (subsetP incP) // -(same_orbit ain) mem_iter_orbit.
Qed.

Lemma general_position_orbit x :
  hull_propf inp m p -> x \in orbit f p -> ccw x (f x) q || ccw (f x) x q.
Proof.
move=> hulP xin.
have uni' : uniq inp by  move : uni; rewrite cons_uniq=> /andP[].
have : uniq [:: x; f x; q].
  have := uniq_hull2 s3 uni' xin hulP; rewrite -/f /= !inE !negb_or -andbA.
  move => /andP[] ->.
  by rewrite -!(eq_sym q) (@qnotiter x 0) // (@qnotiter x 1).
by move/Knuth_3/orP.
Qed.

Lemma sizeSpred (T : finType) (g : T -> T) x :
  (size (orbit g x)).-1.+1 = size (orbit g x).
Proof. by rewrite !size_orbit orderSpred. Qed.

Lemma size_orbit_stable :
  {in orbit f p, forall x, size (orbit f x) = size (orbit f p)}.
Proof.
move: (cot)=> [] trP [] ctr [] incP [] hulP [] sfp [] unitr cyc.
move=> x xin; have [j ->]:= (orbit_rot_cycle cyc (orbit_uniq _ _) xin).
by rewrite size_rot.
Qed.

(* Important lemma, deserves a comment in any paper about this work. *)
Lemma sub_convex_triangle x i j :
 x \in orbit f p ->
 ((0 < i < j) && (j < size (orbit f p)))%N -> ccw x (iter i f x) (iter j f x).
Proof using s3 cot ccs.
move: (cot)=> [] _ [] _ [] incP [] hulP _ xin cmps.
have sos := size_orbit_stable.
have/iter_lt_order_neq/= xnj : (0 < j < fingraph.order f x)%N.
  rewrite -size_orbit sos //; case/andP: (cmps) => _ ->; rewrite andbT.
  by case/andP: cmps => /andP [h1 h2] _; rewrite (ltn_trans h1 h2).
have/iter_lt_order_neq/= xni : (0 < i < fingraph.order f x)%N.
  rewrite -size_orbit sos //; case/andP: (cmps) => /andP [_ h1] h2.
  by rewrite (ltn_trans h1 h2) andbT; case/andP: cmps => /andP [].
have itin : forall k, iter k f x \in inp.
  by move=> k; apply/(subsetP incP)/(subset_orbit xin)/mem_iter_orbit.
move: cmps (xnj); have [/eqP -> cmps _ | in1] := boolP (i == 1)%N.
  move: (cmps); rewrite -(sos _ xin).
  rewrite ltnSn andTb size_orbit=> /iter_lt_order_neq/= fxnj.
  by apply: (hulP _ xin _ (itin j)); rewrite eq_sym.
case/andP => /andP [i0 ij]; rewrite -(subnK ij) => js; move: (js).
move: (i0); rewrite leq_eqVlt eq_sym (negbTE in1) /= => igt1.
rewrite (subnK ij) in js.
have /iter_lt_order_neq fxni : (1 < i < fingraph.order f x)%N.
  by rewrite igt1 (ltn_trans ij) // -size_orbit sos.
elim: (j - i.+1)%N => [ | k IH].
  rewrite add0n => i1s xni1; apply/Knuth_1_1.
  by apply: (hulP _ (subset_orbit xin (mem_iter_orbit f x _)) _ (itin 0)).
rewrite !addnS !addSn in IH * => k2s xnk2.
have k1s : ((k + i).+1 < size (orbit f p))%N by apply: ltn_trans k2s.
have /iter_lt_order_neq xnk1 : (0 < (k + i).+1 < fingraph.order f x)%N.
  by rewrite -size_orbit sos // k1s ltn0Sn.
have /iter_lt_order_neq fxnk1 : (1 < (k + i).+1 < fingraph.order f x)%N.
  by rewrite -size_orbit sos // k1s -addSn (leq_trans igt1) // leq_addl.
have /iter_lt_order_neq fxnk2 : (1 < (k + i).+2 < fingraph.order f x)%N.
  by rewrite -size_orbit sos // k2s -!addSn (leq_trans igt1) // leq_addl.
have := fun n => hulP _ xin _ (itin n); rewrite -/f=> chx.
have xfxk1 : ccw x (f x) (iter (k + i).+1 f x) by apply: chx; rewrite eq_sym.
have xk1k2 : ccw x (iter (k + i).+1 f x) (iter (k + i).+2 f x).
  rewrite [iter _.+2 _ _]iterS; apply/Knuth_1_1/hulP=> //.
    by apply/(subset_orbit xin)/mem_iter_orbit.
  by apply/(subsetP incP).
by apply: (Knuth_5 _ xfxk1) => //; apply: IH || (apply:chx; rewrite eq_sym).
Qed.

Lemma pre_contiguous_red a b c:
  a \in orbit f p -> c \in orbit f p -> a != b -> f a != b ->
  ccw a (f a) b -> ccw a (f a) c -> ccw (f a) b c -> ccw (f a) b (f c).
Proof.
move: (cot)=> [] trP [] ctr [] incP [] hulP [] sfp [] unitr cyc.
move=> ao co anb fanb afab afac fabc.
have [/eqP -> | fcna] := boolP (f c == a); first by apply /Knuth_1.
have fanc : f a != c by move: afac=>/Knuth_1/oriented_diff.
have anc : a != c by move: afac=>/Knuth_1_1/oriented_diff; rewrite eq_sym.
have fanfc : f a != f c by rewrite (inj_in_eq convex_hull_path_inj ao co) anc.
have fain : f a \in inp by apply/(subsetP incP)/mem_orbit1.
have fcin : f c \in inp by apply/(subsetP incP)/mem_orbit1.
have facfc : ccw (f a) c (f c).
  by apply/Knuth_1_1/(hulP c co _ _ fanc fanfc).
have afafc : ccw a (f a) (f c) by apply: (hulP _ ao _ fcin); rewrite // eq_sym.
by apply: (Knuth_5' afab afac afafc fabc facfc).
Qed.

Lemma iter_size' x : x \in orbit f p ->
  iter (size (orbit f p)) f x = x.
Proof.
move=> xo.
move: (cot) => [_ [_ [_ [_ [_ [_ cyc]]]]]].
by rewrite -(size_orbit_stable xo); apply: (iter_size cyc).
Qed.

Lemma findexf x : x \in orbit f p ->
  findex f (f x) x = (size (orbit f p)).-1.
Proof.
move=> xo; move: (iter_size' xo).
rewrite -(size_orbit_stable (mem_orbit1 xo)) -sizeSpred iterSr => xx.
have it : fconnect f (f x) x by rewrite -{2}xx fconnect_iter.
move/findex_max: (it); rewrite -size_orbit=> it'; move: (it').
rewrite -sizeSpred /= ltnS leq_eqVlt => /orP[/eqP // | abs].
move: (it); rewrite fconnect_orbit=> /(nth_index (f x)) => idxx.
have : findex f (f x) x < (fingraph.order f (f x)).-1 < fingraph.order f (f x).
  by rewrite -size_orbit abs sizeSpred leqnn.
move/iter_lt_order_neq; rewrite -size_orbit xx.
have := nth_traject f it' (f x).
by rewrite size_orbit -/(orbit f (f x)) idxx=> <-; rewrite eqxx.
Qed.

Lemma convex_hull_size_orbit_gt2 :
  hull_propf inp m p -> 2 < size (orbit f p).
Proof.
move=> hulP.
have uni' : uniq inp by  move : uni; rewrite cons_uniq=> /andP[].
have := uniq_hull2 s3 uni' (orbit0 _ _) hulP.
rewrite size_orbit  /= !inE negb_or andbT -/f=> /andP[] /andP[] pf pff fpff.
rewrite /fingraph.order (cardD1 (f (f p))) (cardD1 (f p)) (cardD1 p).
by rewrite !inE (fconnect_iter f 2) fconnect1 connect0 pf pff fpff.
Qed.

Lemma contiguous_red a i j :
  a \in orbit f p -> 0 < i -> ccw a (f a) q -> ccw (iter i f a) (f a) q ->
  ccw (iter i f a) (iter i.+1 f a) q ->
  i <= j <= size (orbit f p) -> ccw (iter j f a) (iter j.+1 f a) q.
Proof.
move: (cot)=> [] trP [] ctr [] incP [] hulP [] sfp [] unitr cyc.
move=> ain i0 afaq ifafaq ii1q /andP[] ij; have sc:= sub_convex_triangle.
rewrite -(subnK ij); elim (j - i)=> [ | k IH] => // {j ij}.
rewrite !addSn; set j := _ .+1.
move: i0; rewrite leq_eqVlt => /orP [/eqP A | i1].
  by move/oriented_diff: ifafaq; rewrite -A eqxx.
have ij : (i < j)%N by rewrite /j ltnS leq_addl.
have j2 : (2 < j)%N by rewrite (leq_trans _ ij).
rewrite leq_eqVlt => /orP [/eqP -> | js].
  by rewrite //= iter_size'.
have fain : f a \in orbit f p by apply/mem_orbit1.
have /(sc _ _ _ fain) : (0 < i.-1 < j.-1) && (j.-1 < size (orbit f p)).
  by to_lia; move: (leP js) (leP i1) (leP ij); ssr_lia.
rewrite -!iterSr (ltn_predK i1) (ltn_predK ij) => faij.
have/(sc _ _ _ ain) afai  : ((0 < 1 < i) && (i < size (orbit f p)))%N.
  by rewrite i1 !andTb (ltn_trans ij).
have/(sc _ _ _ ain) afaj : ((0 < 1 < j) && (j < size (orbit f p)))%N.
  by rewrite (ltn_trans i1) // size_orbit_stable.
have faqj : ccw (f a) q (iter j f a).
  by apply: (Knuth_5' _ afai) => //; apply/Knuth_1.
have/IH {IH} : k + i <= size (orbit f p).
  by rewrite (leq_trans _ js) // (leq_trans (leqnSn _)).
rewrite -[(k + i)%N]/j.-1 -[j.-1.+1]/j => jm1jp.
have jin : iter j f a \in orbit f p.
  by apply/(subset_orbit ain)/mem_iter_orbit.
have round : iter (size (orbit f p) - 1) f (iter j f a) = iter j.-1 f a.
  rewrite -iter_add [_ + j](_ : _ = j.-1 + size (orbit f p)).
    by rewrite iter_add iter_size'.
  by move: (leP j2) (leP js); ssr_lia.
have/(sc _ _ _ jin) : (0 < 1 < size (orbit f p) - 1) &&
                       (size (orbit f p) - 1 < size (orbit f p)).
  by to_lia; move: (leP js) (leP j2); ssr_lia.
rewrite round -iter_add add1n=> /Knuth_1_1=> jm1jj1.
have jm2p1 : j.-2.+1 = j.-1 by move: (leP j2); ssr_lia.
have/(sc _ _ _ fain) : (0 < j.-2 < j.-1) && (j.-1 < size (orbit f p)).
  by to_lia; move: (leP j2) (leP js); ssr_lia.
rewrite -!iterSr (ltn_predK j2) jm2p1 => /Knuth_1 jm1jfa.
have/(sc _ _ _ fain)/Knuth_1 : (0 < j.-1 < j) && (j < size (orbit f p)).
  by to_lia; move: (leP j2) (leP js); ssr_lia.
rewrite -!iterSr (ltn_predK j2)=> jj1fa.
apply: (Knuth_5' _ jm1jfa) => //; last by apply/Knuth_1_1.
Qed.

Lemma red_path n x : x \in orbit f p -> 0 < n < size (orbit f p) ->
  (forall i, i < n -> ccw (iter i.+1 f x) (iter i f x) q) ->
    ccw (iter n f x) x q.
Proof.
move=> xin; elim: n => [| [_ | n IH]] // /andP [] n0 nor red.
  by apply:red.
have xn1n2 : ccw x (iter n.+1 f x) (iter n.+2 f x).
  have : (0 < n.+1 < n.+2) && (n.+2 < size (orbit f p)) by rewrite ltnSn.
  by apply: sub_convex_triangle.
apply: (Knuth_4 (Knuth_1 (Knuth_1 xn1n2))); apply/Knuth_1.
  apply/IH; first by to_lia; move: (leP nor); ssr_lia.
  by move=> i c; apply red; rewrite ltnW.
by apply/Knuth_1/red.
Qed.

Lemma blue_edge :
  hull_propf inp m p -> exists2 x, (x \in orbit f p) & ccw x (f x) q.
Proof.
move=> hulP.
have uni' : uniq inp by move: uni; rewrite cons_uniq=> /andP[].
have [ | ] := boolP(~~[forall x, (x \in orbit f p) ==> ccw (f x) x q]).
  rewrite negb_forall=> /existsP[x]; rewrite negb_imply => /andP[] xin xblue.
  by exists x; have:= general_position_orbit hulP xin;
    rewrite ?(negbTE xblue) ?orbF.
rewrite negbK=>/forallP reds.
have sz : (0 < (size (orbit f p)).-1 < size (orbit f p))%N.
  by move: (convex_hull_size_orbit_gt2 hulP); case: (size _) => [ |[ | k]] //=.
have:= red_path (orbit0 f p) sz=> it; exists (iter (size (orbit f p)).-1 f p).
  by rewrite mem_iter_orbit.
rewrite -iterS sizeSpred size_orbit.
have := iter_order_in (fun y yin => mem_orbit1 yin) convex_hull_path_inj.
move=> ->; rewrite ?orbit0 // -size_orbit it // => e ein.
by move: (reds (iter e f p)); rewrite mem_iter_orbit implyTb /=.
Qed.

Lemma purple_point :
  exists a, [&& a \in orbit f p, ccw a (f a) q & ~~ ccw (f a) (f (f a)) q].
Proof using s3 cot uni redin redP ccs.
move: (cot)=> [] trP [] ctr [] incP [] hulP [] sfp [] unitr cyc.
have uni' : uniq inp by move: uni; rewrite cons_uniq=> /andP[].
move: (blue_edge hulP) => [y yin blue].
have [k oy] := orbit_rot_cycle cyc (orbit_uniq _ _) yin.
have : red_point \in orbit f y by rewrite oy mem_rot.
rewrite -fconnect_orbit => /iter_findex idred; move: redP; rewrite -idred.
elim: (findex _ _ _) => [ | n IH the_red].
  by rewrite /= => /Knuth_2; rewrite blue.
have nin : iter n f y \in orbit f p.
  by apply/(subset_orbit yin)/mem_iter_orbit.
have/orP[it|] := general_position_orbit hulP nin; last by apply: IH.
exists (iter n f y); rewrite -(same_orbit yin) mem_iter_orbit andTb.
  by move: it the_red; rewrite /= => -> /Knuth_2 ->.
Qed.

Lemma partition_red_blue:
  exists b, exists i,
  b \in orbit f p /\ 0 < i < size (orbit f p) /\
  (forall j, j < i -> ccw (iter j.+1 f b) (iter j f b) q) /\
  (forall j,  i <= j < size (orbit f p) -> ccw (iter j f b) (iter j.+1 f b) q).
Proof.
move: (cot)=> [] trP [] ctr [] incP [] hulP [] sfp [] unitr cyc.
have qnotin : q \notin inp by move:uni; rewrite cons_uniq=> /andP[].
have uni' : uniq inp by move:uni; rewrite cons_uniq=> /andP[].
have [b /andP[bin /andP [bblue fbnblue]]] := purple_point.
have chin i : iter i f b \in orbit f p.
  by apply/(subset_orbit bin)/mem_iter_orbit.
have fbo : f b \in orbit f p by apply/(mem_orbit1 bin).
move: fbnblue; have/orP[-> //| fbred _] := general_position_orbit hulP fbo.
have [j [reds [nextblue jb]]] : exists j,
     (forall k, 0 < k <= j -> ccw (iter k.+1 f b) (iter k f b) q) /\
     ccw (iter j.+1 f b) (iter j.+2 f b ) q /\ j < size (orbit f p).
  pose a v := ccw v (f v) q; set s := orbit f (f b).
  set j := find a s.
  have jb : j < size (orbit f (f b)).
    rewrite /j -has_find /a /s; apply/hasP; exists b =>//.
    rewrite -[X in X \in _](iter_size' bin) -sizeSpred.
    by rewrite iterSr mem_iter_orbit.
  exists j; split.
    move=> [ | k] //= kj; move: (kj)=> /(before_find (f b)); rewrite /a /s.
    rewrite /orbit -size_orbit nth_traject; last by apply: ltn_trans jb.
    rewrite -iterSr -!iterS => red.
  have := general_position_orbit hulP
            (subset_orbit bin (mem_iter_orbit _ b k.+1)).
    by rewrite red -iterS.
  move: (jb); rewrite /j /s -has_find => /(nth_find (f b)); rewrite /orbit.
  rewrite nth_traject -/j /a; last by rewrite -/j -size_orbit.
  rewrite -iterSr -iterS => ->; split=> //.
  by move: jb; rewrite size_orbit_stable.
exists (f b), j.
split; first by [].
have intj : 0 < j < size (orbit f p).
  rewrite jb andbT lt0n; apply/eqP=> j0; move: nextblue; rewrite j0 /=.
  by move => /Knuth_2; rewrite fbred.
split; first by [].
split; first by move=> k kj; rewrite -!iterSr; apply/reds; rewrite /=.
have frp : forall i, i < j -> ccw (iter i.+1 f (f b)) (iter i f (f b)) q.
  by move=> i ij; rewrite -!(iterSr _ f b); apply: reds.
have := red_path (mem_orbit1 bin) intj frp; rewrite -iterSr=> bigred.
have it := contiguous_red bin (isT : 0 < j.+1) bblue bigred nextblue.
by move=> k intk; rewrite -!iterSr; apply: it; rewrite ltnS.
Qed.

Section fixed_red_subpath.

Variables (b : P) (i : nat).

Hypothesis bin : b \in orbit f p.
Hypothesis ilto : 0 < i < size (orbit f p).
Let nf : P -> P := eval (new_map m b (iter i f b) q).
Hypothesis reds : forall k, k < i%N -> ccw (iter k.+1 f b) (iter k f b) q.
Hypothesis blues :
  forall k, (i <= k < size (orbit f p))%N ->
  ccw (iter k f b) (iter k.+1 f b) q.

Lemma iter_b_neq k l:
  k < l < size (orbit f p) -> iter k f b != iter l f b.
Proof.
by move=> ?; apply: iter_lt_order_neq; rewrite -size_orbit size_orbit_stable.
Qed.

Lemma igt0 : 0 < i.
Proof. by case/andP: ilto. Qed.

Lemma bred : ccw (f b) b q.
Proof. by rewrite -/(iter 0 f b) -iterS; apply/reds/igt0. Qed.

Lemma ilto' : i < size (orbit f p).
Proof. by case/andP: ilto. Qed.

Lemma qnb : q != b.
Proof. by apply: (qnotiter 0 bin). Qed.

Lemma nfb : nf b = q.
Proof. by rewrite /nf eval_update1. Qed.

Lemma nfq  : nf q = iter i f b.
Proof.
by rewrite /nf eval_update_dif ?eval_update1 // eq_sym (qnotiter 0 bin).
Qed.

Lemma nfk k : i <= k < size (orbit f p) -> nf (iter k f b) = iter k.+1 f b.
Proof.
move=> /andP[ik ko]; rewrite /nf eval_update_dif; last first.
  by rewrite -{1}/(iter 0 f b) iter_b_neq // ko (leq_trans _ ik) ?igt0.
by rewrite eval_update_dif ?qnotiter.
Qed.

Lemma new_path_offset k : 1 < k <= size (orbit f p) - i + 2 ->
  iter k nf b = iter (i + k - 2) f b.
Proof.
have ileo : i <= size (orbit f p) by rewrite leq_eqVlt orbC ilto'.
elim: k => [| [ | [ | k]] IH] //.
  by move=> _; rewrite addnK /= nfb nfq.
move=> /andP[] _; set k' := k.+2.
move=> klim; rewrite iterS IH; last first.
  by rewrite 2!ltnS leq0n; move: klim=>/ltnW.
move: klim; rewrite /k' !addnS !subSS !subn0 !ltnS addn0 => klim.
by rewrite nfk // leq_addr -ltn_subRL klim.
Qed.

Lemma new_path_cycle : iter (size (orbit f p) - i + 2) nf b = b.
Proof.
rewrite -[RHS](iter_size' bin).
have ileo : i <= size (orbit f p) by rewrite leq_eqVlt orbC ilto'.
rewrite new_path_offset.
  by rewrite -(addnC 2) addnA (addnC i) -addnA addKn (addnC i) subnK.
by rewrite !addnS addn0 !ltnS leq0n leqnn.
Qed.

Lemma findex_eqns e :
  e \in orbit f p -> (findex f e (f e) = 1) /\ (findex f e (f (f e)) = 2).
Proof.
move: (cot)=> [] trP [] ctr [] incP [] hulP [] sfp [] unitr cyc.
have uni' : uniq inp by move: uni=> /andP[].
move=> eo; have := uniq_hull2 s3 uni' eo hulP.
have := convex_hull_size_orbit_gt2 hulP.
have <- : size (orbit f e) = size (orbit f p) by rewrite size_orbit_stable //.
rewrite size_orbit /findex /orbit.
case (fingraph.order _) => [ | [ | [ |k]]] //= _.
rewrite !inE !negb_or -!andbA -/f !eqxx.
by repeat (move=>/andP[] ne; rewrite ?(negbTE ne) {ne}).
Qed.

Definition purple (side : bool) := if side then iter i f b else b.

Lemma mem_purple_orbit e side : e \in orbit f p -> purple side \in orbit f e.
Proof.
move: (cot)=> [] trP [] ctr [] incP [] hulP [] sfp [] unitr cyc.
move=> eo.
have [k oy] := orbit_rot_cycle cyc (orbit_uniq _ _) eo.
rewrite oy mem_rot; case: (side); last by apply: bin.
by apply/(subset_orbit bin)/mem_iter_orbit.
Qed.

Lemma purpleP side : ccw (purple side) (f (purple side)) q = side.
Proof.
case:side.
  have /blues: i <= i < size (orbit f p).
    by rewrite leqnn ilto'.
  by [].
by rewrite /purple; apply/negbTE/Knuth_2/bred.
Qed.

Lemma purple_unique e side : e \in orbit f p -> ccw e (f e) q = ~~ side ->
  ccw (f e) (f (f e)) q = side -> f e = purple side.
Proof.
move: (cot)=> [] trP [] ctr [] incP [] hulP [] sfp [] unitr cyc.
have [igt0 ilto'] := andP ilto.
move=> eo; have eob : e \in orbit f b.
  have [k oy] := orbit_rot_cycle cyc (orbit_uniq _ _) bin.
  by rewrite /f oy mem_rot.
move: eob; rewrite /orbit=> /trajectP=>[] []k.
rewrite -size_orbit size_orbit_stable // => klto ek.
case: side; rewrite /purple.
  have [ | ] := boolP(k < i.-1).
    by rewrite -ltnS (prednK igt0) ek -!iterS => /reds/Knuth_2/negbTE ->.
  rewrite -leqNgt leq_eqVlt (prednK igt0)=> /orP[/eqP ik | ik ].
    by rewrite ek -iterS -ik (prednK igt0).
  have /blues : i <= k < size (orbit f p) by rewrite ik klto.
  by rewrite ek -iterS => ->.
rewrite ek /= -!iterS.
have [/reds/Knuth_2/negbTE -> //|] := boolP (k < i).
rewrite -leqNgt=> ik; move: klto; rewrite leq_eqVlt=> /orP[/eqP -> | k1lto].
  by rewrite iter_size'.
have /blues -> // : i <= k.+1 < size (orbit f p).
by rewrite k1lto andbT; apply: (leq_trans ik).
Qed.

Lemma findex_decrease' x y : x \in orbit f p -> y \in orbit f p ->
  x != y -> findex f x y = (findex f (f x) y).+1.
Proof.
move: (cot)=> [] trP [] ctr [] incP [] hulP [] sfp [] unitr cyc.
move=> xo yo xny.
have yx : y \in orbit f x.
  have [k oy] := orbit_rot_cycle cyc (orbit_uniq _ _) xo.
  by rewrite /f oy mem_rot.
apply: findex_decrease=> //.
Qed.

Lemma find_next_purpleP side e : e \in orbit f p ->
  ccw e (f e) q = ~~side ->
  find_next_purple ccw q m side (f e) = purple side.
Proof.
move: (cot)=> [] trP [] ctr [] incP [] hulP [] sfp [] unitr cyc.
move=> ein notside; rewrite /find_next_purple.
set ff := (X in map_iter X _ _ _).
case : (map_iterP ff (f e) m (f e)) => [n [-> [ut lpf]]].
have ui : uniq inp by move: uni; rewrite /= => /andP[].
have nn0 : n != 0.
  apply/eqP=> n0; move: (uniq_hull2 s3 ui ein hulP).
  by move: lpf; rewrite n0 /looping /= !inE in_nil.
have tro : traject (eval m) (f e) n = orbit f (f e).
  by apply: traject_looping_orbit.
rewrite tro; move: (mem_purple_orbit side (mem_orbit1 ein)).
have: ccw e (head e (orbit f (f e))) q = ~~ side.
  by rewrite /orbit -orderSpred /=.
have peo : fpath f e (orbit f (f e)).
  by apply: fpath_traject.  
elim: (orbit f (f e)) {1 3 4 5}e peo ein
  => [// | a l IH] a' /= patha' a'in a'aq pin.
rewrite /ff; case: ifP => [afaq | nafaq].
  case/andP: patha' => /eqP fa'q _.
  rewrite -fa'q; apply: purple_unique=> //.
    by rewrite fa'q.
  by rewrite fa'q; apply/eqP.
case/andP: patha' => /eqP fa'q patha.
have pinl : purple side \in l.
  move: pin; rewrite inE => /orP[/eqP abs | //].
  move:(purpleP side) nafaq; rewrite -[eqb _ _]/(_ == _) abs => ->.
  by rewrite eqxx.
rewrite -/ff; apply: (IH a) => //.
  by rewrite -fa'q -(same_orbit a'in) mem_orbit1 ?orbit0.
have -> : head a l = f a. 
  by move: patha pinl; case (l) => [// | a2 tl] /= /andP[] /eqP ->.
move: nafaq; rewrite -/f; case: (ccw _ _ _); case: (side) => //.
Qed.

(*
Lemma map_sizeP' (x : P) : size (orbit (eval m) x) <= map_size m.
Proof.
have := orbit_uniq (eval m) x.
have /fpathP : exists n, behead (orbit (eval m) x) =
   traject (eval m) (eval m x) n.
  by rewrite /orbit -orderSpred trajectS /=; eexists; eauto.
rewrite /orbit -orderSpred trajectS [(behead _)]/=.
by apply: map_sizeP.
Qed.

Lemma map_orbitP' x : map_orbit m x = orbit (eval m) x.
Proof.
rewrite /orbit.
have := map_orbitP m x => [] [mot [lmo umo]].
rewrite mot; congr (traject _ _ _).
rewrite /fingraph.order -(card_uniqP umo); apply: eq_card.
  move=> y; apply/idP/idP.
  by rewrite mot=> /trajectP [] j js ->; rewrite inE fconnect_iter.
rewrite inE => yfc.
move/loopingP: lmo => /(_ (findex (eval m) x y)); rewrite -mot.
by rewrite iter_findex.
Qed.
*)
Lemma map_iterP' x : map_iter cons nil m x = orbit (eval m) x.
Proof.
have [n [-> [un lo]]] := map_iterP cons nil m x.
by rewrite traject_looping_orbit //; elim: (orbit _ _)=> [ | a l /= ->].
Qed.

Lemma find_purple_pointsP : find_purple_points q m p = (b, iter i f b).
Proof.
move: (cot)=> [] trP [] ctr [] incP [] hulP [] sfp [] unitr cyc.
rewrite /find_purple_points. 
by case: ifP=> [blue | red]; rewrite -/f;
 rewrite !find_next_purpleP ?mem_purple_orbit ?orbit0 // purpleP.
Qed.

(*
Lemma map_orbitP' x n trailer :
  x \in orbit f p -> findex f (f x) b < n ->
  map_orbit (mf := mf) eq_op m x b n trailer =
  traject f x (findex f (f x) b).+1 ++ trailer.
Proof.
move=> xo; apply: map_orbitP.
by rewrite same_orbit // mem_orbit1. Qed.
*)

Lemma traject_iota : traject f b (size (orbit f b)) =
      [seq iter k f b | k <- iota 0 (size (orbit f b))].
Proof.
suff : traject f (iter (size (orbit f b) - size (orbit f b)) f b)
        (size (orbit f b))
       =
       [seq iter k f b | k <- iota (size (orbit f b) - size (orbit f b))
                                   (size (orbit f b))].
  by rewrite subnn /=.
elim: {1 4 5 7 8}(size (orbit f b)) (leqnn (size (orbit f b)))
  => [// | l IHl /=].
by move=> llt; congr (_ :: _); rewrite -iterS subnSK //; apply/IHl/ltnW.
Qed.

Lemma im1red : ccw (iter i f b) (iter i.-1 f b) q.
Proof. by rewrite -{1}(prednK igt0); apply: reds; rewrite prednK ?igt0. Qed.

Lemma iblue : ccw (iter i.+1 f b) (iter i f b) q = false.
Proof. by apply/negbTE/Knuth_2/blues; rewrite leqnn ilto'.
Qed.

Lemma add_red_triangles_exact :
  add_red_triangles ccw q m b tr =
  [seq [:: iter k.+1 f b; iter k f b; q] | k <- iota 0 i] ++ tr.
Proof.
rewrite /add_red_triangles; set ff := (fun _ _ => _).
have [n [-> [unt lot]]] := map_iterP ff [::] m b; rewrite -/f.
have tro : traject f b n = orbit f b by apply: traject_looping_orbit.
have ilto' : i < size (orbit f p) by case/andP: ilto.
have iltn : i < n.
  rewrite [n](_ : _ = size (traject f b n)); last by rewrite size_traject.
  by rewrite tro (size_orbit_stable bin); move: ilto=> /andP[].
have : ccw (iter i f b) (iter i.+1 f b) q by apply: blues; rewrite leqnn.
elim: (n) i b iltn reds => [// | n' IH] j e jn' redsj jblue.
rewrite trajectS /= /ff.
case: ifP=> [blue | red].
  case jq: j => [// | j']; last by move/Knuth_2: blue; rewrite (redsj 0) ?jq.
case jq: j => [ | j']; first by move: jblue; rewrite jq red.
rewrite -(add1n j') iota_add (addnC 0 1) iota_addl -/ff [iota 0 1]/=.
rewrite map_cat -map_comp.
have : (fun i => ((fun k => [:: f (iter k f e); iter k f e; q]) \o addn 1) i)=1
       (fun i => [:: iter i.+1 f (f e); iter i f (f e); q]).
  by move=> k; rewrite -!iterSr.
move=> feq; rewrite (eq_map feq) (IH j') //.
    by move: jn'; rewrite jq ltnS.
  by move=> k kj'; rewrite -!iterSr; apply: redsj; rewrite jq ltnS.
by rewrite -!iterSr -jq.
Qed.

Lemma all_triangles_outtside_hull t :
  t \in add_red_triangles ccw q m b tr ->
  size t = 3 /\ uniq t /\ ccw_seq t.
Proof.
move: (cot)=> [] trP [] ctr [] incP [] hulP [] sfp [] unitr cyc.
rewrite add_red_triangles_exact mem_cat => /orP[ | ?]; last by apply: trP.
  move/mapP=> []j; rewrite mem_iota add0n leq0n andTb=> ji -> /=.
split; first by [].
split.
  rewrite !inE negb_or -!(eq_sym q) -!iterS !qnotiter // eq_sym !andbT.
  by apply: iter_b_neq; rewrite ltnSn (leq_trans _ ilto').
by apply: reds.
Qed.

Lemma ctr_outside_hull :
  flatten (add_red_triangles ccw q m b tr)
    =i q :: inp.
Proof.
move: (cot)=> [] trP [] ctr [] incP [] hulP [] sfp [] unitr cyc.
rewrite add_red_triangles_exact flatten_cat.
move=> z; apply/idP/idP; last first.
  rewrite inE=> /orP[/eqP -> | ].
    rewrite mem_cat; apply/orP; left; apply/flattenP.
    exists [:: iter 1 f b; iter 0 f b; q]; last by rewrite !subE.
    by apply/mapP; exists 0; rewrite // mem_iota leqnn add0n igt0.
  by move=> zin; rewrite mem_cat ctr zin orbT.
rewrite mem_cat=> /orP[]; last by rewrite ctr inE orbC => ->.
by move=> /flattenP [t] /mapP[] j _ ->; rewrite !inE => /orP[|/orP[]]/eqP ->;
  rewrite ?eqxx // orbC (subsetP incP) // -(same_orbit bin) mem_iter_orbit.
Qed.

Lemma iter_injective_in (T : eqType) (g : T -> T) (S : pred T) (l : nat) :
  {in S, forall x, g x \in S} ->
  {in S &, injective g} -> {in S &, injective (iter l g)}.
Proof.
elim: l => [ | l IH] gst ginj x y xs ys; rewrite ?iterSr /=; first by [].
by move/(IH gst ginj (g x) (g y) (gst _ xs) (gst _ ys)); apply: ginj.
Qed.

(* TODO replace by an earlier lemma in same file. *)
Lemma f_stable : {in orbit f p, forall x, f x \in orbit f p}.
Proof. by move=> z zin; apply mem_orbit1. Qed.

Lemma sub_orbit_uniq k l l' : k + l <= size (orbit f p) ->
  uniq [seq iter (j + l') f b | j <- iota k l].
Proof.
move=> klo; apply/(uniqP p)=> x y; rewrite size_map !inE=> xbnd ybnd.
have [xbnd' ybnd'] : x < l /\ y < l.
    by move: xbnd ybnd; rewrite size_iota; split.
have [kxbnd kybnd] : k + x < size (orbit f p) /\ k + y < size (orbit f p).
  by split; apply: leq_trans klo; rewrite ltn_add2l.
have [kxbnd' kybnd'] : k + x < size (orbit f b) /\ k + y < size (orbit f b).
  by rewrite size_orbit_stable // split.
rewrite !(nth_map 0) // !nth_iota // -!(addnC (l')).
rewrite [LHS]iter_add [RHS]iter_add => qq.
have/(uniqP p):= orbit_uniq f b=> /(_ (k + x) (k + y)).
rewrite size_orbit_stable // !inE kxbnd kybnd !nth_orbit //.
move/(iter_injective_in f_stable convex_hull_path_inj): (qq).
rewrite -!(same_orbit bin) !mem_iter_orbit=>/(_ isT isT)=> kxky.
move=>/(_ isT isT kxky) main.
by apply/eqP; rewrite -(eqn_add2l k); apply/eqP/main.
Qed.

Lemma cycle_orbit_nf_val :
  fcycle nf
    (q :: [seq iter (k + i) f b | k <- iota 0 (size (orbit f p) - i).+1]).
Proof.
apply/(pathP p)=>[] [| k]; first by move=>_ /=; rewrite nfq eqxx.
rewrite size_rcons size_map size_iota 1!ltnS leq_eqVlt=>/orP[/eqP-> |].
  rewrite nth_rcons size_map size_iota ltnn eqxx.
  have szi : 0 < size (orbit f p) - i by rewrite subn_gt0 ilto'.
  set s' := rcons _ _; rewrite /= nth_rcons size_map size_iota leqnn.
  rewrite (nth_map 0); last by rewrite size_iota leqnn.
  rewrite nth_iota // add0n subnK; last by rewrite (ltnW ilto').
  by rewrite iter_size' // nfb.
set s' := rcons _ _; rewrite ltnS /= => kbnd; rewrite nth_rcons.
rewrite size_map size_iota kbnd (nth_map 0); last by rewrite size_iota.
rewrite nth_iota // add1n addSn /s' nth_rcons size_map size_iota ltnS.
have kbnd' := ltnW kbnd.
rewrite (ltnW kbnd) (nth_map 0); last by rewrite size_iota.
rewrite nth_iota // add0n; apply/eqP/nfk.
by rewrite leq_addl addnC -ltn_subRL kbnd.
Qed.

Lemma orbit_nf : orbit nf q =
   q :: [seq iter (k + i) f b | k <- iota 0 (size (orbit f p) - i).+1].
Proof.
set s := _ :: map _ _.
have uns : uniq s.
  rewrite /s cons_uniq; apply/andP; split.
    by apply/negP=> /mapP [k _] /eqP; apply/negP/qnotiter/bin.
  apply sub_orbit_uniq; rewrite add0n -{2}(subn0 (size (orbit f p))).
  by rewrite ltn_sub2l ?igt0 // -sizeSpred.
have := cycle_orbit_nf_val; rewrite -/s=> cycs.
have qs : q \in s by rewrite !subE.
have := order_cycle cycs uns qs=> oq.
apply/esym; rewrite /orbit.
apply: (eq_from_nth (x0 := p)); first by rewrite size_traject.
move=> [| k]; first by rewrite /s /= oq /s.
move=> kbnd; rewrite oq [RHS](set_nth_default q) ?size_traject //.
rewrite nth_traject // -nfb -iterSr new_path_offset; last first.
  rewrite /= !addnS addn0 (leq_trans kbnd) // /s /= size_map size_iota.
  by rewrite leqnn.
rewrite /s; set s' := map _ _; rewrite !addnS !subSS subn0 /s /=.
rewrite (nth_map 0); last first.
  by move: kbnd; rewrite /s /= size_map size_iota ltnS.
rewrite nth_iota; last first.
  by move: kbnd; rewrite /s /= size_map size_iota ltnS.
by rewrite add0n addnC.
Qed.

Lemma orbit_nf_inc : orbit nf q \subset q :: inp.
Proof.
move: (cot)=> [] trP [] ctr [] incP [] hulP [] sfp [] unitr cyc.
rewrite orbit_nf; apply/subsetP=> z; rewrite inE => /orP[/eqP ->|].
  by rewrite !subE.
move/mapP=> [j] _ ->; rewrite inE; apply/orP; right; apply: (subsetP incP).
by rewrite -(same_orbit bin) mem_iter_orbit.
Qed.

Lemma new_hulP :
  forall r, r \in orbit nf q ->
  forall x, x \in q :: inp -> x != r -> x != nf r -> ccw r (nf r) x.
Proof.
move: (cot)=> [] trP [] ctr [] incP [] hulP [] sfp [] unitr cyc.
have uni' : uniq inp by move: uni=> /andP[].
have iterin k : iter k f b \in orbit f p.
  by rewrite -(same_orbit bin) mem_iter_orbit.
move=> r; rewrite orbit_nf inE => /orP [/eqP -> | ].
  move=> x; rewrite !inE=> /orP[/eqP -> |]; first by rewrite eqxx.
  move=> xinp xnq xnfq; have [/eqP -> | xnim1] := boolP(x == iter i.-1 f b).
    have/reds : i.-1 < i by rewrite (ltn_predK igt0) leqnn.
    by move/Knuth_1_1; rewrite (ltn_predK igt0) nfq.
  have [/eqP ->| xnnf2q ] := boolP (x == nf (nf q)).
    apply/Knuth_1_1; rewrite nfq nfk.
      by apply: blues; rewrite leqnn ilto'.
    by rewrite leqnn ilto'.
  have nf2v : nf (nf q) = iter i.+1 f b by rewrite nfq nfk ?leqnn ?ilto'.
  (* preparing the use of Knuth_5 *)
  have im1o : iter i.-1 f b \in orbit f p by rewrite iterin.
  have := uniq_hull2 s3 uni' im1o hulP=> /=; rewrite !inE negb_or -!iterS -/f.
  rewrite (prednK igt0)=> /andP[] /andP[] dif1 dif2 /andP[] dif3 _.
  have ff2x : ccw (nf q) (nf (nf q)) x.
    rewrite nf2v nfq //; apply/hulP => //; first by rewrite -nfq.
    by rewrite -iterS -nf2v.
  have ff2im1 : ccw (nf q) (nf (nf q)) (iter i.-1 f b).
    rewrite nf2v nfq //; apply/hulP => //.
    by apply/(subsetP incP).
  have ff2q : ccw (nf q) (nf (nf q)) q.
    by rewrite nf2v nfq; apply/blues; rewrite leqnn ilto'.
  have fxim1 : ccw (nf q) x (iter i.-1 f b).
    rewrite nfq; apply/Knuth_1; rewrite -{2}(prednK igt0); apply: hulP=> //.
    by rewrite -iterS (prednK igt0) -nfq.
  have fqim1q : ccw (nf q) (iter i.-1 f b) q.
    by rewrite nfq -{1}(prednK igt0); apply: reds; rewrite (prednK igt0).
  by apply/Knuth_1_1/(@Knuth_5 (nf q) (nf (nf q)) x (iter i.-1 f b) q).
case/mapP=> [j]; rewrite mem_iota add0n ltnS leq0n andTb leq_eqVlt.
move=> /orP[/eqP -> | jlt].
  rewrite (subnK (ltnW ilto')) iter_size' ?bin // => ->.
  move=> x; rewrite !inE=> /orP[/eqP -> |]; first by rewrite nfb eqxx.
  move=> xinp xnq xnfq; have [/eqP -> | xnim1] := boolP(x == f b).
    by have/reds := igt0; rewrite nfb /=; move/Knuth_1.
  rewrite nfb.
  have [/eqP ->| ] := boolP (x == iter (size (orbit f p)).-1 f b).
    set b' := iter _ _ _.
    have nfb' : f b' = b by rewrite /b' -iterS sizeSpred iter_size'.
    apply/Knuth_1; rewrite -{1}nfb' /b' -iterS; apply: blues.
    by rewrite -ltnS sizeSpred leqnn ilto'.
  set b' := iter _ _ _ => xnb'.
  have b'o : b' \in orbit f p by rewrite /b' iterin.
  (* preparing the use of Knuth_5' *)
  have := uniq_hull2 s3 uni' b'o hulP=> /=; rewrite !inE negb_or -!iterS -/f.
  rewrite sizeSpred /= (iter_size' bin).
  move => /andP[] /andP[] dif1 dif2 /andP[] dif3 _.
  have fb' : f b' = b by rewrite -(iter_size' bin) /b' -sizeSpred /=.
  have b'bq : ccw b' b q.
    by rewrite -fb' /b' -iterS; apply: blues; rewrite -ltnS sizeSpred ilto' /=.
  have b'bfb : ccw b' b (f b).
    rewrite -fb'; apply/hulP=> //.
        by apply/(subsetP incP); rewrite -/b' -!iterS iterin.
      by rewrite eq_sym /b' -!iterS sizeSpred /= (iter_size' bin).
    by rewrite -/f fb' eq_sym.
  have b'bx : ccw b' b x by rewrite -fb'; apply/hulP=> //; rewrite -/f fb'.
  have bqfb : ccw b q (f b).
    by apply/Knuth_1; rewrite -/(iter 0 f b) -iterS; apply/reds/igt0.
  have bfbx : ccw b (f b) x by apply/hulP.
  by apply/(@Knuth_5' b' b q (f b) x).
have jiint : i <= j + i < size (orbit f p).
  by rewrite leq_addl addnC -ltn_subRL jlt.
move=> -> x; rewrite inE nfk // => /orP [/eqP -> _ _ | ].
  by apply: blues.
by apply/hulP.
Qed.

Lemma no_i_inside_outside t1 t2 p1:
  t1 \in tr ->
  t2 \in [seq [:: iter k.+1 f b; iter k f b; q] | k <- iota 0 i] ->
  inside_triangle t1 p1 ->
  ~inside_triangle t2 p1.
Proof.
have uni' : uniq inp by move: uni; rewrite /= => /andP[].
move: (cot)=> [] trP [] ctr [] incP [] hulP [] [no_i cov] [] unitr cyc.
have iterin k : iter k f b \in orbit f p.
  by rewrite -(same_orbit bin) mem_iter_orbit.
move=> t1tr /mapP[] k; rewrite mem_iota add0n leq0n andTb.
move=> ki t2q p1t1 p1t2.
have kin : iter k f b \in orbit f p by rewrite iterin.
move: (p1t2); rewrite t2q=> /andP[] /andP[]/Knuth_1/oriented_diff.
rewrite eq_sym=> p1nk _ /Knuth_1/oriented_diff; rewrite eq_sym => p1nk1.
have /Knuth_2/negbTE kk1p1 := inside_triangle_in_hull
          s3 (perm_to_rem t1tr) uni' trP ctr hulP kin p1t1 p1nk p1nk1.
by move:p1t2; rewrite t2q /= kk1p1.
Qed.

Lemma pre_no_i_outside k l p1 :
  k + l < i ->
  inside_triangle [:: iter k.+1 f b; iter k f b; q] p1 ->
  ccw q (iter (k + l).+1 f b) p1.
Proof.
move: (cot)=> [] trP [] ctr [] incP [] hulP [] [no_i cov] [] unitr cyc.
have iterin u : iter u f b \in orbit f p.
  by rewrite -(same_orbit bin) mem_iter_orbit.
have iinp u : iter u f b \in q :: inp.
  by rewrite inE; apply/orP; right; apply/(subsetP incP)/iterin.
have binn : b \in orbit nf q.
  rewrite orbit_nf inE; apply/orP; right; apply/mapP.
  exists (size (orbit f p) - i).
    by rewrite mem_iota leq0n add0n leqnn.
  by rewrite (subnK (ltnW ilto')) (iter_size' bin).
move=> kli p1k; move: (p1k) => /andP[] /andP[] k1kp1 kqp1 qkp1.
have [/eqP -> | p1nb] := boolP(p1 == b).
  apply/Knuth_1; rewrite -nfb; apply/new_hulP=> //.
    rewrite eq_sym -{1}/(iter 0 f b); apply: iter_b_neq.
    by rewrite ltnS leq0n (leq_trans _ ilto').
  by rewrite nfb eq_sym qnotiter.
elim: l kli => [|l IH]; first by rewrite addn0.
rewrite addnS=> kli; have /IH IH' := ltnW kli.
have kl1nb : iter (k + l).+1 f b != b.
  rewrite eq_sym -{1}/(iter 0 f b); apply iter_b_neq.
  by rewrite ltnS leq0n (ltn_trans _ ilto').
have kl1nq : iter (k + l).+1 f b != nf b.
  by rewrite eq_sym nfb qnotiter.
have kl2nb : iter (k + l).+2 f b != b.
  rewrite eq_sym -{1}/(iter 0 f b); apply iter_b_neq.
  by rewrite ltnS leq0n (leq_trans _ ilto').
have kl2nq : iter (k + l).+2 f b != nf b.
  by rewrite eq_sym nfb qnotiter.
have := (new_hulP binn (iinp (k + l).+1) kl1nb kl1nq); rewrite nfb=> bqkl1.
have := (new_hulP binn (iinp (k + l).+2) kl2nb kl2nq); rewrite nfb=> bqkl2.
have bqp1 : ccw b q p1.
  have s3' : 2 < size (q :: inp) by rewrite /= ltnW.
  have p1nq : p1 != nf b by move/Knuth_1_1/oriented_diff: IH'; rewrite nfb.
  have/perm_to_rem prt1 : [:: iter k.+1 f b; iter k f b; q] \in
       add_red_triangles ccw q m b tr.
    rewrite add_red_triangles_exact mem_cat;apply/orP; left; apply/mapP.
    exists k => //; rewrite mem_iota leq0n add0n (leq_trans _ kli) //.
    by rewrite ltnS -!addnS leq_addr.
  by have := inside_triangle_in_hull  s3' prt1 uni all_triangles_outtside_hull
   ctr_outside_hull new_hulP binn p1k p1nb p1nq; rewrite -/nf nfb.
apply: (@Knuth_5' b q (iter (k + l).+2 f b) (iter (k + l).+1 f b) p1)=> //.
by apply/Knuth_1_1/reds.
Qed.

Lemma no_i_outside_hull t1 t2 p1 :
  t1 \in add_red_triangles ccw q m b tr ->
  t2 \in add_red_triangles ccw q m b tr ->
  inside_triangle t1 p1 ->
  inside_triangle t2 p1 -> t1 = t2.
Proof.
move: (cot)=> [] trP [] ctr [] incP [] hulP [] [no_i cov] [] unitr cyc.
rewrite add_red_triangles_exact; set ts := map _ _.
rewrite 2!mem_cat=> /orP[t1ts | t1tr]; last first.
  move=>/orP [t2ts | t2tr]; last by apply: no_i.
  by move=> p1t1 p1t2; have := no_i_inside_outside t1tr t2ts p1t1 p1t2.
move=>/orP [t2ts | t2tr]; last first.
  by move=> p1t1 p1t2; have := no_i_inside_outside t2tr t1ts p1t2 p1t1.
move: t1ts t2ts; rewrite /ts=>/mapP[k kin ->] /mapP[l lin ->].
wlog : k l kin lin / k <= l.
move=> main; have[klel | ] := boolP(k <= l); first by apply: main.
  by rewrite -ltnNge=>/ltnW cmp ? ?; apply/esym; apply: (main _ _ _ _ cmp).
rewrite leq_eqVlt=> /orP[/eqP -> // | kltl].
set l' := (l - k.+1); have lq : l = k.+1 + l' by rewrite -(subnK kltl) addnC.
move=> p1t1.
have/pre_no_i_outside : k + l' < i.
  move: lin; rewrite mem_iota leq0n add0n andTb=> lin.
  by rewrite (leq_trans _ lin) // ltnS lq leq_add2r.
move=> /(_ _ p1t1); rewrite -addSn -lq=> abs /andP[] /andP[] l1lp1 /Knuth_2.
by rewrite abs.
Qed.

Lemma convex_hull_one_triangle x k :
  hull_propf inp m p ->
  orbit f p \subset inp ->
  k.+1 < size (orbit f p) -> ccw (iter k.+1 f b) b x &&
   ccw b (iter k f b) x && ccw (iter k f b) (iter k.+1 f b) x ->
  (forall k' : nat,
   k' < k.+1 -> ccw (iter k' f b) (iter k'.+1 f b) x).
Proof.
move=> hulP incP kp1lto /andP [] /andP [] kp1bx bkx kkp1x k'.
have klto : (k < size (orbit f p)) by apply: (ltn_trans (ltnSn _)).
rewrite ltnS leq_eqVlt => /orP [/eqP -> // | k'lt].
have [/eqP k0 | kn0] := boolP(k == 0)%N; first by move: k'lt; rewrite k0 ltn0.
have kgt0 : (0 < k)%N by rewrite lt0n.
have bnk : b != iter k f b.
  by have/iter_b_neq : 0 < k < size (orbit f p) by rewrite lt0n kn0.
have iterin u : iter u f b \in orbit f p.
  by rewrite -(same_orbit bin) mem_iter_orbit.
have kkp1b : ccw (iter k f b) (iter k.+1 f b) b.
  have:= (hulP _ (iterin k) _ (subsetP incP _ bin) bnk); rewrite -iterS -/f.
  have/iter_b_neq -> : 0 < k.+1 < size (orbit f p) by rewrite ltn0Sn.
  by apply.
have bnkp1 : b != iter k.+1 f b.
  by have/iter_b_neq-> // : 0 < k.+1 < size (orbit f p) by rewrite ltn0Sn.
have := hulP _ (iterin k'); rewrite -iterS=> chk'.
have k'lto : k' < size (orbit f p) by apply/(ltn_trans k'lt).
move: kkp1b=> /Knuth_1=> kp1bk.
have/Knuth_1_1 kp1bfb : ccw b (f b) (iter k.+1 f b).
  move: (hulP _ bin (iter k.+1 f b)); rewrite (subsetP incP) //.
  rewrite -(eq_sym b) bnkp1 -(eq_sym (f b)).
  have/iter_b_neq -> : 1 < k.+1 < size (orbit f p) by rewrite ltnS lt0n kn0.
  by apply.
have [/eqP k1 | kn1] := boolP (k == 1%N).
  by move: k'lt bkx; rewrite k1 ltnS leqn0=> /eqP ->.
have bfbk : ccw b (f b) (iter k f b).
  move: (hulP _ bin (iter k f b)); rewrite (subsetP incP) //.
  rewrite !(eq_sym (iter k f b)).
  have/iter_b_neq -> : 0 < k < size (orbit f p) by rewrite kgt0.
  have/iter_b_neq -> : 1 < k < size (orbit f p).
    by rewrite ltn_neqAle eq_sym kn1 kgt0.
  by apply.
have bfbx : ccw b (f b) x by apply: (Knuth_5' kp1bfb kp1bk kp1bx bfbk bkx).
have binp : b \in inp by apply: (subsetP incP).
have [/eqP -> // | ] := boolP(k' == 0%N);rewrite -lt0n => k'gt0.
have [k'p1k | gen ] := boolP (k'.+1 == k).
  move/Knuth_1_1: kp1bk => kkp1b.
  have kbk' : ccw (iter k f b) b (iter k' f b).
    apply/Knuth_1; rewrite -(eqP k'p1k); move: (hulP _ (iterin k') _ binp).
    have/iter_b_neq -> : 0 < k' < size (orbit f p).
      by rewrite  k'gt0 (ltn_trans k'lt).
    have/iter_b_neq -> : 0 < k'.+1 < size (orbit f p).
      by rewrite ltn0Sn (eqP k'p1k).
    by apply.
  have kkp1k': ccw (iter k f b) (iter k.+1 f b) (iter k' f b).
    move: (hulP _ (iterin k) (iter k' f b)); rewrite (subsetP incP) //.
    have/iter_b_neq -> // : (k' < k.+1 < size (orbit f p))%N.
      by rewrite (eqP k'p1k) leqnSn.
    have/iter_b_neq -> : (k' < k < size (orbit f p))%N.
      by rewrite (eqP k'p1k) leqnn.
    by apply.
  have/Knuth_1_1 := Knuth_5 kkp1x kkp1b kkp1k' (Knuth_1 bkx) kbk'.
  by rewrite -(eqP k'p1k).
move: kp1bx kkp1x=> /Knuth_1 bxkp1 /Knuth_1_1 xkkp1.
have k'kb : ccw (iter k' f b) (iter k f b) b.
  have trk : (0 < k' < k) && (k < size (orbit f p)) by rewrite k'gt0 k'lt.
  by have/Knuth_1 := sub_convex_triangle bin trk.
have k'p1lt : k'.+1 < k by move: k'lt; rewrite leq_eqVlt (negbTE gen).
have k'k'p1b : ccw (iter k' f b) (iter k'.+1 f b) b.
  move: (chk' b); rewrite binp.
  have/iter_b_neq -> : 0 < k' < size (orbit f p).
    by rewrite k'gt0 (ltn_trans k'lt).
  have/iter_b_neq -> : 0 < k'.+1 < size (orbit f p).
    by rewrite ltn0Sn (ltn_trans k'p1lt) // (ltn_trans ki).
  by apply.
have k'k'p1k : ccw (iter k' f b) (iter k'.+1 f b) (iter k f b).
  move: (chk' (iter k f b)); rewrite (subsetP incP) // !(eq_sym (iter k f b)).
  have/iter_b_neq -> : k' < k < size (orbit f p) by rewrite k'lt.
  have/iter_b_neq -> : k'.+1 < k < size (orbit f p) by rewrite k'p1lt.
  by apply.
have k'k'p1kp1 : ccw (iter k' f b) (iter k'.+1 f b) (iter k.+1 f b).
  move: (chk' (iter k.+1 f b)); rewrite (subsetP incP) //
         !(eq_sym (iter k.+1 f b)).
  have/iter_b_neq -> : k' < k.+1 < size (orbit f p).
    by rewrite (ltn_trans _ (ltnSn k)).
  have/iter_b_neq -> : k'.+1 < k.+1 < size (orbit f p).
    by rewrite (ltn_trans k'p1lt (ltnSn _)).
  by apply.
by apply:(inside_triangle_left_of_edge k'k'p1b k'k'p1k k'k'p1kp1 bkx).
Qed.

Lemma convex_hull_split x k :
  k < size (orbit f p) ->
  ccw b (iter k f b) x ->
  (forall u, x != iter u f b) ->
  (forall l, k <= l < size (orbit f p) ->
  ccw (iter l f b) (iter l.+1 f b) x) ->
  forall l, l < k -> ccw (iter l f b) (iter l.+1 f b) x.
Proof.
move: (cot)=> [] trP [] ctr [] incP [] hulP [] sfp [] unitr cyc.
move=> klto bkx xniter blues_k.
suff main : forall j, j + k < size (orbit f p) ->
  ccw (iter (j + k) f b) b x ->
  forall l : nat, l < k -> ccw (iter l f b) (iter l.+1 f b) x.
  have arith : ((size (orbit f p)).-1 - k + k = (size (orbit f p)).-1)%N.
    by rewrite subnK // -ltnS sizeSpred.
  apply: (main ((size (orbit f p)).-1 - k)%N) => //.
    by rewrite arith sizeSpred.
  rewrite -2![in X in ccw _ X _](iter_size' bin, sizeSpred) subnK.
    by apply:blues_k; rewrite -ltnS sizeSpred klto leqnn.
  by rewrite -ltnS sizeSpred.
elim => [ | j IH] kp1lto lbx l llek.
  by move/Knuth_2: lbx; rewrite add0n bkx.
have jklto : j + k < size (orbit f p).
  by apply: ltn_trans kp1lto; apply: ltnSn.
move: kp1lto; rewrite addSn => kp1lto.
have/Knuth_3[bjx |jbx] : uniq [:: iter 0 f b; iter (j + k) f b; x].
  have kn0 : k != 0%N by apply/negP=> /eqP A; move: llek; rewrite A ltn0.
  have/iter_b_neq : (0 < j + k < size (orbit f p))%N.
    by rewrite jklto; move: kn0; case: (k)=> // n _; rewrite addnS ltn0Sn.
  by rewrite !cons_uniq !inE -!(eq_sym x) negb_or !xniter => ->.
  have := convex_hull_one_triangle hulP incP kp1lto=> /(_ x).
  rewrite bjx lbx blues_k; last by rewrite leq_addl jklto.
  move=> /(_ isT); apply.
  by apply: (leq_trans llek); rewrite -addSn leq_addl.
by apply: IH.
Qed.

Lemma cover_hull_outside_hull r :
  inh (eval (new_map m b (iter i f b) q)) q r ->
  r \in q :: inp \/
  (exists t : seq_eqType P,
     t \in add_red_triangles ccw q m b tr /\
     inside_triangle t r).
Proof.
move: (cot)=> [] trP [] ctr [] incP [] hulP [] [no_i cov] [] unitr cyc.
rewrite /inh -/nf=> xh.
set ts' := add_red_triangles _ _ _ _ _.
have b_new_orbit : b \in orbit nf q.
  rewrite orbit_nf inE; apply/orP/or_intror/mapP.
  exists (size (orbit f p) - i).
    by rewrite mem_iota leq0n /=.
  by rewrite (subnK (ltnW ilto')) iter_size'.
have [| rnotin] := boolP(r \in q :: inp);[left => //| right].
have rniter : forall k, r != iter k f b.
  move=> k; apply/eqP=> abs; case/negP: rnotin.
  rewrite inE;apply/orP/or_intror/(subsetP incP); rewrite abs.
  by rewrite -(same_orbit bin) mem_iter_orbit.
have nfi : nf (iter i f b) = (iter i.+1 f b).
  by apply: nfk; rewrite leqnn ilto'.
have blues_r k (kint : i <= k < size (orbit f p)):
     ccw (iter k f b) (iter k.+1 f b) r.
  suff/xh /= : iter k f b \in orbit nf q.
    by rewrite nfk.
  rewrite orbit_nf inE; apply/orP/or_intror/mapP/(ex_intro2 _ _ (k - i)).
    rewrite mem_iota leq0n andTb add0n ltnS leq_sub2r //.
    by move: kint=> /andP[] _ /ltnW.
  by rewrite subnK; move: kint=> /andP[].
have kqfk k : k < i -> ccw (iter k f b) q (iter k.+1 f b).
  by move=> klti; apply/Knuth_1/reds.
have main: forall k, k <= i -> inside_triangle [:: b; q; iter k f b] r ->
   (exists t, t \in ts' /\ inside_triangle t r) \/
   (forall k', k' < k -> ccw (iter k' f b) (iter k'.+1 f b) r).
  elim=>[ | k IH]; first by move=> _ _ ; right.
  have [/eqP -> ki insx| kn0 ki xins] := boolP(k == 0).
    left; exists [:: f b; b; q].
    split; last by rewrite inside_triangle_K1.
    rewrite /ts' add_red_triangles_exact mem_cat; apply/orP/or_introl/mapP.
    by exists 0 => //; rewrite mem_iota leq0n andTb.
(* preparatory work for choose_sub_triangle. *)
  have kgt0 : 0 < k by rewrite lt0n.
  have bnk : b != iter k f b.
    have/iter_b_neq// : 0 < k < size (orbit f p).
      by rewrite lt0n kn0 (ltn_trans ki) // ilto'.
  have bnkp1 : b != iter k.+1 f b.
    have/iter_b_neq -> // : 0 < k.+1 < size (orbit f p).
    by rewrite ltn0Sn (leq_ltn_trans ki) // ilto'.
  have knkp1 : iter k f b != iter k.+1 f b.
    have/iter_b_neq// : k < k.+1 < size (orbit f p).
    by rewrite ltnSn (leq_ltn_trans ki) // ilto'.
  have bpk : ccw b q (iter k f b).
    have := new_hulP b_new_orbit; rewrite nfb=> /(_ (iter k f b)).
    rewrite !(eq_sym (iter k f b)) bnk qnotiter //.
    rewrite inE (subsetP incP) ?orbT; first by apply.
    by rewrite -(same_orbit bin) mem_iter_orbit.
  have bpkp1 : ccw b q (iter k.+1 f b).
    have := new_hulP b_new_orbit; rewrite nfb=> /(_ (iter k.+1 f b)).
    rewrite !(eq_sym (iter k.+1 f b)) bnkp1 qnotiter //.
    rewrite inE (subsetP incP) ?orbT; first by apply.
    by rewrite -(same_orbit bin) mem_iter_orbit.
  have kkp1b : ccw (iter k f b) (iter k.+1 f b) b.
    apply: hulP=> //; first by rewrite -(same_orbit bin) mem_iter_orbit.
    by apply/(subsetP incP).
  have kins : inside_triangle [:: b; q; iter k.+1 f b] (iter k f b).
    by rewrite /inside_triangle bpk (Knuth_1 kkp1b) (Knuth_1_1 (reds ki)).
    move: (rniter k); rewrite eq_sym=> knr.
    have := choose_sub_triangle knr kins xins; rewrite /inside_triangles.
  move=>[] t; rewrite !inE=>[][]/orP[| /orP []]/eqP -> {t}.
      rewrite inside_triangle_K1=> kbqr.
      case: (IH (ltnW ki) kbqr) => [ | inpath]; first by left.
      suff kkp1r : ccw (iter k f b) (iter k.+1 f b) r.
        right=> k'; rewrite leq_eqVlt=>/orP[k'kp1 | k'kp1].
          by move: k'kp1; rewrite eqSS=> /eqP ->.
        by move: k'kp1; rewrite ltnS; apply: inpath.
      have chm1 s :
        [&& (s \in inp), (s != iter k.-1 f b) & (s  != iter k f b)] ->
        ccw (iter k.-1 f b) (iter k f b) s.
        move=> /andP[] sinp /andP[] snkm1 snk.
        move: (hulP (iter k.-1 f b)); rewrite -(same_orbit bin) mem_iter_orbit.
        move=> /(_ isT _ sinp snkm1); rewrite -iterS (prednK kgt0) snk.
        by apply.
      have km1kkp1 : ccw (iter k.-1 f b) (iter k f b) (iter k.+1 f b).
        apply: chm1.
        rewrite (subsetP incP); last first.
          by rewrite -(same_orbit bin) mem_iter_orbit.
        rewrite andTb !(eq_sym (iter k.+1 f b)).
        have /iter_b_neq -> : k.-1 < k.+1 < size (orbit f p).
          rewrite (leq_ltn_trans ki ilto') andbT (ltn_trans _ (ltnSn _)) //.
          by rewrite prednK ?leqnn.
        have /iter_b_neq -> // : k < k.+1 < size (orbit f p).
        by rewrite (leq_ltn_trans ki ilto') // ltnSn.
      have km1kr : ccw (iter k.-1 f b) (iter k f b) r.
        rewrite -[in X in ccw _ X _](prednK kgt0); apply: inpath.
        by rewrite prednK ?leqnn.
      have km1kb : ccw (iter k.-1 f b) (iter k f b) b.
        apply: chm1; rewrite (subsetP incP) // bnk andTb andbT.
        apply/negP=> /eqP A.
        by move: kbqr=>/=; rewrite {4}A (negbTE (Knuth_2 km1kr)) andbF.
      by apply: (Knuth_5' km1kkp1 km1kb) => //; move: kbqr => /andP[].
    move=> it; left; exists [:: iter k.+1 f b; iter k f b; q].
    rewrite inside_triangle_K1 it /ts' add_red_triangles_exact; split=> //.
    rewrite mem_cat; apply/orP/or_introl/mapP/(ex_intro2 _ _ k) => //.
    by rewrite mem_iota leq0n add0n ki.
  rewrite inside_triangle_K1 /inside_triangle=> kp1bk ; right.
  have := convex_hull_one_triangle hulP incP=> /(_ r k).
  by rewrite (leq_ltn_trans ki ilto') kp1bk; apply.
have bqi : ccw b q (iter i f b) by apply/Knuth_1/red_path; rewrite ?bin.
suff main'' :
 (forall k' : nat, (k' < i)%N -> ccw (iter k' f b) (iter k'.+1 f b) r) ->
  exists t, t \in ts' /\ inside_triangle t r.
  have bnr : b != r by rewrite -/(iter 0 f b) eq_sym rniter.
  have /Knuth_3[ibr | bir] : uniq [:: iter i f b; b; r].
    rewrite /= !inE negb_or bnr eq_sym -{1}/(iter 0 f b) iter_b_neq //.
    by rewrite eq_sym rniter.
    have lower : inside_triangle [:: b; q; iter i f b] r.
      rewrite /=.
      have bqr : ccw b q r by rewrite -nfb; apply (xh b).
      have qir : ccw q (iter i f b) r.
        by rewrite -nfq; apply: xh; rewrite orbit0.
      by rewrite bqr qir ibr.
    by case: (main i (leqnn _) lower).
  by apply: main''; have := convex_hull_split ilto' bir rniter blues_r.
move=> main'.
have rnotins : r \notin inp.
  by apply/(contraNN _ rnotin); rewrite !inE orbC=> ->.
have : inh f p r.
  move=> y; rewrite -(same_orbit bin)=> /trajectP.
  rewrite -size_orbit size_orbit_stable // => [][k] klto ->.
  rewrite -iterS; have [ilek | ] := boolP (i <= k).
    by apply: blues_r; rewrite ilek.
  by rewrite -ltnNge; apply: main'.
move=> /cov [rinp |]; first by move: rnotin; rewrite inE rinp orbT.
case=> t [tin rint]; exists t; split=> //.
by rewrite /ts' add_red_triangles_exact mem_cat tin orbT.
Qed.

Lemma uniq_tr_outside_hull :
  uniq (add_red_triangles ccw q m b tr).
Proof.
move: (cot)=> [] trP [] ctr [] incP [] hulP [] sfp [] unitr cyc.
rewrite add_red_triangles_exact cat_uniq unitr andbT andbC; apply/andP; split.
  apply/hasPn=> t ttr; apply/negP=> /mapP[] j _ t_dec.
  move: uni; rewrite cons_uniq=>/andP[]/negP[]; rewrite -ctr.
  by rewrite (perm_flatten_mem (perm_to_rem ttr)) /= mem_cat t_dec !subE.
rewrite map_inj_in_uniq; first by rewrite iota_uniq.
move=> j1 j2; rewrite !mem_iota add0n !leq0n !andTb=> j1i j2i [] _.
have/sub_orbit_uniq: 0 + i <= size (orbit f p) by rewrite add0n ltnW // ilto'.
move=> /(_ 0)/(uniqP p); rewrite size_map size_iota=> /(_ _ _ j1i j2i).
by rewrite !(nth_map 0) ?size_iota // !nth_iota // !add0n !addn0.
Qed.

Lemma cycle_outside_hull : fcycle nf (orbit nf q).
Proof. by rewrite -/nf orbit_nf cycle_orbit_nf_val. Qed.

Lemma correct_outside_hull :
  correct_triangulationf (q :: inp)
  (add_red_triangles ccw q m b tr)
  (new_map m b (iter i f b) q) q.
Proof.
split; first by apply: all_triangles_outtside_hull.
split; first by apply: ctr_outside_hull.
split; first by apply: orbit_nf_inc.
split; first by apply: new_hulP.
split; [split; first by apply: no_i_outside_hull|].
  by apply: cover_hull_outside_hull.
split; first by apply: uniq_tr_outside_hull.
by apply: cycle_outside_hull.
Qed.

End fixed_red_subpath.

End outside_hull.

Lemma size_le_3_correct (T : Type) (s : seq T) :
  size_le_3 s = (size s <= 3)%N.
Proof.
by move: s => [ | a [ | b [ | c [ | ?]]]]. Qed.

Lemma main_correct inp : uniq inp -> 2 < size inp ->
   correct_triangulationf inp (naive inp).1.1 (naive inp).1.2 (naive inp).2.
Proof.
elim: inp => [// | q inp IH] uni; rewrite leq_eqVlt=> /orP[/eqP sq3|].
  have:= base_case (esym sq3) uni; case: (naive _) => [[tr hf] bp].
  by move=>/(_ _ _ _ erefl).
cbn [naive]; rewrite size_le_3_correct.
rewrite /= ltnS => s3; have -> : (size inp < 3) = false.
  by move: s3; rewrite leqNgt=> /negbTE.
have uni': uniq inp by move: uni; rewrite cons_uniq=> /andP[].
have qnotin : q \notin inp by move: uni; rewrite cons_uniq=> /andP[].
move: (IH uni' s3); case: (naive inp)=> [[tr m] p] /= cot.
case h : (pick_triangle tr q) => /= [[t tr'] |].
  have /andP[ins]:= pick_triangle_someP h; rewrite perm_sym=> pr.
  by apply: (correct_inside_triangle s3 uni cot ins pr).
have no_triangle := pick_triangle_noneP h.
have [red_point redo redP]:=
   no_triangle_red_edge no_triangle s3 uni' qnotin cot.
have [b [i [bin [iint [reds blues]]]]] :=
    partition_red_blue s3 uni cot redo redP.
have -> := find_purple_pointsP s3 uni cot bin iint reds blues.
by apply: (correct_outside_hull s3 uni cot bin iint reds blues).
Qed.

End proofs_in_finType.

Parametricity seq.
Parametricity prod.
Parametricity bool.
Parametricity nat.
Parametricity map_funs.
Parametricity eq.
Parametricity False.
Parametricity reflect.
Parametricity Equality.mixin_of.
Parametricity eqType.
Parametricity map_iter.
Parametricity new_map.
Parametricity map_cycle3.
Parametricity head.
Parametricity option.
Parametricity pick_triangle.
Parametricity inside_triangles.
Parametricity True.
Parametricity find_next_purple.
Parametricity find_purple_points.
Parametricity add_red_triangles.
Parametricity size_le_3.
Parametricity Recursive nth.
Proof.
by move=> /= T t0 [ | n].
Parametricity Done.
Parametricity Recursive naive.
by move=> /= P p0 ccf mf [ | a tl].
Parametricity Done.
Parametricity Recursive flatten.

Section bridge_finType_eqType.

Variables (P : choiceType) (p0 : P) (ccw : P -> P -> P -> bool)
  (mf : map_funs P) (context : seq P) (inp : seq P).

Hypothesis uc : uniq context.

Hypothesis inp_sub_context : forall x, x \in p0 :: inp -> x \in context.

Lemma size_context_gt0 : 0 < size context.
Proof.
apply: (@leq_ltn_trans (index p0 context)); rewrite // index_mem.
by rewrite inp_sub_context // inE eqxx.
Qed.

Hypothesis (ms : map_system mf).

Definition P' := seq_sub context.

Variable mf' : map_funs P'.

Definition PP' (x : P) (y : P') : Type :=
  x = val y.

Hypothesis mfR : map_funs_R PP' mf mf'.

Definition ccw' (a b c : P') := ccw (val a) (val b) (val c).

Lemma p0'_proof : p0 \in context.
Proof. by rewrite inp_sub_context // inE eqxx. Qed.

Definition p0' : P' := SeqSub p0'_proof.

Definition seq_from_map (T : Type) (eq_f : T -> T -> bool)
   (mf : map_funs T) (r : seq (seq T) * sort mf * T) :=
  map_iter cons nil r.1.2 r.2.

Lemma p0_p0' : PP' p0 p0'.
Proof. by []. Qed.

Lemma bool_R_refl x : bool_R x x.
Proof. by case: x; constructor. Qed.

Lemma ccw_ccw' a a' (ha : PP' a a') b b' (hb : PP' b b') c c' (hc : PP' c c') :
  bool_R (ccw a b c) (ccw' a' b' c').
Proof. by rewrite ha hb hc; apply: bool_R_refl. Qed.

Lemma naive_R' : prod_R (prod_R (list_R (list_R PP'))
                            (sort_R mfR)) PP'
                   (naive p0 ccw mf inp)
                   (naive p0' ccw' mf' [seq (insubd p0' x) | x <- inp]).
Proof.
apply: naive_R.
- reflexivity.
- apply: ccw_ccw'.
have : all (fun x => x \in inp) inp by apply/allP=> x it; exact it.
elim: (X in all _ X -> list_R _ X [seq _ | _ <- X]) => [| a l IH] pin /=.
  by constructor.
constructor.
  move:pin=> /=/andP[ain _]; rewrite /PP' insubdK //=.
  by rewrite inp_sub_context // inE ain orbT.
by apply: IH; move: pin; rewrite /= => /andP[].
Qed.

Hypothesis ccf_s : cc_system ccw.

Lemma ccf's : cc_system ccw'.
Proof.
constructor.
- move=> a b c abc.
  apply: (Knuth_1 ccf_s); exact: abc.
- move=> a b c abc.
  apply: (Knuth_2 ccf_s); exact abc.
- move=> a b c uabc.
  apply: (Knuth_3 ccf_s).
  by move: uabc; rewrite /= !inE !(inj_eq val_inj).
- move=> a b c d abd bcd cad.
  apply: (Knuth_4 ccf_s abd bcd cad).
- move=> a b c d e abc abd abe acd ade.
  apply: (Knuth_5 ccf_s abc abd abe acd ade).
- move=> a b c d e abc abd abe bcd bde.
  apply: (Knuth_5' ccf_s abc abd abe bcd bde).
Qed.

Hypothesis mf's : map_system mf'.

Hypothesis ui : uniq inp.

Lemma list_R_size (T1 T2 : Type) (R : T1 -> T2 -> Type)
  (l : seq T1) (l' : seq T2):  list_R R l l' -> size l = size l'.
Proof.
by elim => [// | a a' aa' ll ll' lll'] /= ->.
Qed.

Lemma list_R_nth (T1 T2 : Type) (R : T1 -> T2 -> Type)
  (l : seq T1) (l' : seq T2) e1 e2 (ee : R e1 e2):
  list_R R l l' -> forall k,  R (nth e1 l k) (nth e2 l' k).
Proof.
by elim=> [ [|k] //= | a a' aa' ll ll' lll' IH [|k] /=].
Qed.

Lemma map_nth_iota (T : Type) (s : seq T) (e : T) :
  s = [seq nth e s i | i <- iota 0 (size s)].
Proof.
elim: s => [// | a s IH] /=.
  congr (_ :: _).
apply: (@eq_from_nth _ e); rewrite ?size_map ?size_iota // => i ilts.
by rewrite (nth_map (size s)) ?size_iota // nth_iota.
Qed.

Definition inp' : seq P' := [seq insubd p0' x | x <- inp].

Lemma val_inp' : inp = [seq val x | x <- inp'].
Proof.
apply: (@eq_from_nth _ p0); first by rewrite !size_map.
move=> i ilts; rewrite (nth_map p0') /inp' ?size_map // (nth_map p0) //.
by rewrite insubdK // inp_sub_context // inE orbC mem_nth.
Qed.

Lemma nth0' (T : Type) (e a : T) (s : seq T) :
  nth e (a :: s) 0 = a.
Proof. by []. Qed.

Lemma nat_R_refl n : nat_R n n.
Proof. by elim: n => [ | n IH]; constructor. Qed.

Lemma nat_R_eq n m : nat_R n m -> n = m.
Proof. by elim=> // k l _ ->. Qed.

Lemma naive_correct' : 2 < size inp ->
   correct_triangulation2 ccw context inp (naive p0 ccw mf inp).1.1
     (seq_from_map eq_op (naive p0 ccw mf inp)).
Proof.
move=> sz.
move: naive_R'.
set res' := naive p0' ccw' mf' inp'.
set res := naive _ _ _ _.
move=> n5r.
inversion n5r as [dum1 dum2 dum3 b b' bb' eq1 eq2].
move: bb' eq1; rewrite /PP' => -> {b} eq1.
inversion dum3 as [tr tr' trtr' m m' mm' eq3 eq4]; move=> {dum3}.
move: eq1 eq2; rewrite -eq3 -eq4 {eq3 eq4} /seq_from_map /= => eq1 eq2.
move=> {dum1 dum2}.
have mprop e: eval m (val e) = val (eval m' e).
  destruct mfR; move: mm'; rewrite /=.
  by move/eval_R /(_ (val e) e erefl); rewrite /PP'.
have ct:
  correct_triangulationf ccw' inp' res'.1.1 res'.1.2 res'.2.
  apply: main_correct; rewrite ?size_map => //; first by exact: ccf's.
  have : all (fun x => x \in inp) inp by apply/allP=> x it; exact it.
  elim: (X in uniq X -> all _ X -> uniq [seq _ | _ <- X]) ui
      => [ | a l IH] //=.
  move=> /andP[anin ul] /andP[ain lin]; rewrite (IH ul lin) andbT.
  elim: l anin ul lin {IH} => [ | b l IH] //=.
  rewrite !inE !negb_or => /andP[anb anin] /andP[bnin ul] /andP[bin lin].
  rewrite (IH anin ul lin) andbT -(inj_eq val_inj).
  by rewrite !insubdK ?inp_sub_context ?inE ?bin ?ain ?orbT.
move /correct_triangulation_complete: (ct) => ct'.
case: (ct) => [_ [_ [_ [_ [_ [_]]]]]]; rewrite -eq2 /= => cyco.
have cr : forall (p1 : P) (p2 : P'), p1 = val p2 ->
          forall (l1 : seq P) (l2 : seq P'), list_R PP' l1 l2 ->
          list_R PP' (p1::l1) (p2::l2).
  by apply: list_R_cons_R.            
have : orbit (eval m') b' =
       [seq insubd p0' x | x <- map_iter cons nil m (val b')].
  have:= map_iter_R cr (list_R_nil_R PP') mm' (erefl (val b')).
  rewrite -map_iterP' //; elim; first by constructor.
  by move=> x x' xx' l l' ll' -> /=; rewrite xx' valKd.
rewrite /=; set ww := map_iter _ _ _ _ => oq.
have tp : triangles_prop ccw tr.
  move: ct' => [A B]; move: A; rewrite -eq2 /= => tp' t tin.
  move/(nth_index [::]): (tin) => tin'.
  have tt' := list_R_nth (list_R_nil_R PP') trtr' (index t tr).
  have [ts trs] := conj (list_R_size tt') (list_R_size trtr').
  move: (tin); rewrite -{-1}tin' ts -index_mem trs.
  move=> /(mem_nth [::])/tp' [t's [ut' cct']]; split=> //.
  move: ts; set t' := (_ _ tr' _); rewrite t's => ts.
  rewrite tin' (map_nth_iota t p0) -[in size _]tin' ts; cbn[iota map].
  move: ut' cct'; rewrite -/t' (map_nth_iota t' p0') t's; cbn [iota map].
  have := list_R_nth p0_p0' tt'; rewrite tin' -/t' /PP' => vt.
  rewrite !vt; cbn[uniq]; rewrite !inE !(inj_eq val_inj).
  by move=> ut' cct'; split.
split; first by [].
split.
  case: ct' => [_ [A _]]; move: A; rewrite -eq2 /= => fh x; rewrite val_inp'.
  have := flatten_R trtr' => ftrtr'.
  apply/idP/idP.
    move=> xin; move/(nth_index p0): (xin)=> xin'.
    move: (list_R_nth p0_p0' ftrtr' (index x (flatten tr))).
    rewrite /PP' xin' => ->.
    by apply: map_f; rewrite -fh mem_nth // -(list_R_size ftrtr') index_mem.
  move/mapP=> [x' x'in xx'].
  move: (x'in); rewrite -fh=> /(nth_index p0') x'in2.
  move: (list_R_nth p0_p0' ftrtr' (index x' (flatten tr'))).
  rewrite /PP' x'in2.
  by rewrite xx' => <-; rewrite mem_nth // (list_R_size ftrtr') index_mem fh.
have oin : forall x, x \in ww -> x \in inp.
  have eq_R : forall x (y : P'), x = val y -> forall z t, z = val t ->
    bool_R (eq_op x z) (eq_op y t).
    move=> x y xy z t zt; have [/eqP xz | xnz] := boolP(x == z).
      by rewrite -(inj_eq val_inj) -xy xz zt eqxx; constructor.
    by rewrite -(inj_eq val_inj) -xy -zt (negbTE xnz); constructor.
  have:= map_iter_R cr (list_R_nil_R PP') mm' (erefl (val b')).
    rewrite map_iterP' // oq.
  rewrite -[X in list_R _ X _]/ww => oo'.
  case: ct' => [_ [_ [A _]]].
  move: A; rewrite -eq2 [X in X -> _]/= oq => hinp'.
  move=> x xin; move/(nth_index p0): (xin) => xi.
  have := list_R_nth p0_p0' oo' (index x ww); rewrite /PP' xi => ->.
  rewrite val_inp'; apply: map_f.
  apply: hinp'; rewrite -oq.
  by apply: mem_nth; rewrite oq size_map index_mem.
split; first by [].
split.
  case: ct' => [_ [_ [_ [A _]]]]; move: A; rewrite -eq2 /=.
  rewrite oq=> [][szb benc].
  have szb' : 0 < size ww by move: szb; rewrite size_map.
  split; first by [].
  case wwq : ww szb' => [// | a ww'] /= _.
  apply/(pathP p0); rewrite size_rcons => i ilts.
  move: benc; rewrite wwq /= => /(pathP p0').
  rewrite !size_rcons size_map=> benc.
  move/allP: (benc _ ilts)=> ben'; apply/allP=> x xin; apply/implyP=>xni.
  apply/implyP=>xnsi.
  have xin' : insubd p0' x \in inp' by apply: map_f.
  move/ben': (xin')=> {ben'} benx.
  have ilts' : i < (size ww').+2 by rewrite ltnW //.
  have nth1in : nth p0 (a :: rcons ww' a) i \in inp.
    rewrite oin ?orbT //; case iq : i => [ | i'] /=.
      by rewrite wwq inE eqxx.
    by rewrite nth_rcons -ltnS -iq ilts wwq inE mem_nth ?orbT // -ltnS -iq.
  have nth2in : nth p0 (rcons ww' a) i \in inp.
    rewrite oin ?orbT //.
    rewrite nth_rcons; case: ifP => [ci | notgt].
      by rewrite wwq inE mem_nth ?orbT.
    move: (ilts); rewrite ltnS leq_eqVlt notgt orbF => ->.
    by rewrite wwq inE eqxx.
  have c1 :insubd p0' x !=
         nth p0' (insubd p0' a :: rcons [seq insubd p0' x | x <- ww']
                                        (insubd p0' a)) i.
    rewrite -(inj_eq val_inj) insubdK ?inp_sub_context // ?inE ?xin ?orbT //.
    rewrite -map_rcons -map_cons (nth_map p0); last by rewrite /= size_rcons.
    by rewrite insubdK // inp_sub_context // inE nth1in orbT.
  move: benx; rewrite c1 /= => benx.
  have c2 : insubd p0' x
          != nth p0' (rcons [seq insubd p0' x | x <- ww'] (insubd p0' a)) i.
    rewrite -(inj_eq val_inj).
    rewrite insubdK ?inp_sub_context ?inE ?xin ?orbT //.
    rewrite -map_rcons (nth_map p0); last by rewrite /= size_rcons.
    by rewrite insubdK // inp_sub_context // inE nth2in orbT.
  move: benx; rewrite c2 /ccw' insubdK ?inp_sub_context ?inE ?xin ?orbT //.
  rewrite -map_rcons -map_cons (nth_map p0); last first.
    by rewrite /= size_rcons.
  rewrite insubdK; last by rewrite inp_sub_context // inE nth1in orbT.
  rewrite (nth_map p0); last first.
    by rewrite size_rcons.
  by rewrite insubdK // inp_sub_context // inE nth2in orbT.
case: (ct')=> [A _]; move: A; rewrite -eq2 /= => tp'.
rewrite /surface_props and_assoc.
split.
  case: (ct') => [_ [_ [_ [_ [[A _] _]]]]]; move: A; rewrite -eq2 /= => noi.
  move=> t1 t2 p pc t1in t2in pin1 pin2.
  move/(nth_index [::]): (t1in) => t1ini.
  move/(nth_index [::]): (t2in) => t2ini.
  have pp' : val (insubd p0' p) = p by rewrite insubdK.
  have t1in' : nth [::] tr' (index t1 tr) \in tr'.
    by rewrite mem_nth // -(list_R_size trtr') index_mem.
  have t2in' : nth [::] tr' (index t2 tr) \in tr'.
    by rewrite mem_nth // -(list_R_size trtr') index_mem.
  have := list_R_nth (list_R_nil_R PP') trtr' (index t1 tr).
  rewrite t1ini => t1t1'.
  have : inside_triangle ccw' (nth [::] tr' (index t1 tr)) (insubd p0' p).
    rewrite (map_nth_iota (nth [::] tr' (index t1 tr)) p0').
    rewrite (proj1 (tp' _ t1in')); cbn [iota map].
    move: pin1; rewrite [X in inside_triangle _ X](map_nth_iota t1 p0).
    rewrite (proj1 (tp _ t1in)); cbn [iota map].
    rewrite !(list_R_nth p0_p0' t1t1') /inside_triangle /ccw'.
    by rewrite pp'.
  move=> p'int1'.
  have := list_R_nth (list_R_nil_R PP') trtr' (index t2 tr).
  rewrite t2ini => t2t2'.
  have : inside_triangle ccw' (nth [::] tr' (index t2 tr)) (insubd p0' p).
    rewrite (map_nth_iota (nth [::] tr' (index t2 tr)) p0').
    rewrite (proj1 (tp' _ t2in')); cbn [iota map].
    move: pin2; rewrite [X in inside_triangle _ X](map_nth_iota t2 p0).
    rewrite (proj1 (tp _ t2in)); cbn [iota map].
    rewrite !(list_R_nth p0_p0' t2t2') /inside_triangle /ccw'.
    by rewrite pp'.
  move=> p'int2'.
  apply: (@eq_from_nth _ p0).
    by rewrite !(fun x (h : x \in tr) => proj1 (tp x h)).
  move=> i isz.
  have := noi _ _ _ t1in' t2in' p'int1' p'int2' => t1t2.
  by rewrite (list_R_nth p0_p0' t1t1') t1t2 -(list_R_nth p0_p0' t2t2').
split.
  move: (ct') => [_ [_ [_ [_ [[_ A] _]]]]].
  move: A; rewrite -eq2 /= => ext.
  move=> q qc qinh.
  have : path.cycle (fun x y => ccw (val x) (val y) (val (insubd p0' q)))
               (orbit (eval m') b').
    move: qinh; have := map_iter_R cr (list_R_nil_R PP') mm' (erefl (val b')).
    rewrite /ww /= map_iterP' //.
    elim; first by [].
    move=> a a' -> l l' ll' _ /= {a}.
    have : list_R PP' (rcons l (ssval a')) (rcons l' a').
      by rewrite -!cats1; apply: cat_R=> //; constructor=> //; constructor.
    move=> rcll'.
    elim: rcll' {1 3} a' => //= c c' -> {c} l1 l2 l1l2 IH d /andP[ccc pat].
    apply/andP; split; last by apply: IH.
    by rewrite insubdK // ccc /=.
  move/ext=> [ininp | [t [tint qint]]].
    left; rewrite val_inp'; apply/mapP; exists (insubd p0' q) => //.
    by rewrite insubdK.
  move/(nth_index [::]): (tint)=> tint'.
  right; exists (nth [::] tr (index t tr')).
  split; first by rewrite mem_nth // (list_R_size trtr') index_mem.
  rewrite (map_nth_iota (nth [::] tr (index t tr')) p0).
  have := list_R_nth (list_R_nil_R PP') trtr' (index t tr') => tt.
  have := list_R_size tt => stt; rewrite stt tint'.
  move: qint; rewrite /inside_triangle.
  rewrite (proj1 (tp' _ tint)); cbn [iota map].
  rewrite {1}(map_nth_iota t p0') (proj1 (tp' _ tint)); cbn [iota map].
  move:tt; rewrite tint'=> tt; rewrite !(list_R_nth p0_p0' tt).
  by rewrite /ccw' (insubdK p0' qc).
split.
  move: (ct') => [_ [_ [_ [_ [_]]]]].
  rewrite -eq2 /=.
  elim: trtr' => // t1 t2 t1t2 l l' ll' IH /= /andP[t2n ul'].
(*  have tpl : triangles_prop ccf l.
    by move=> z zin; apply: tpt1l; rewrite inE zin orbT. *)
  rewrite IH // andbT; apply/negP=> t1in; case/negP: t2n.
  move/(nth_index [::]): (t1in) => t1q.
  have := list_R_nth (list_R_nil_R PP') ll' (index t1 l).
  rewrite t1q; set t2' := nth _ _ _ => t1t2'.
  suff -> : t2 = t2' by rewrite mem_nth // -(list_R_size ll') index_mem.
  apply: (@eq_from_nth _ p0').
    by rewrite -(list_R_size t1t2) (list_R_size t1t2').
  move=> i isz.
   apply: val_inj; rewrite -(list_R_nth p0_p0' t1t2).
   by rewrite -(list_R_nth p0_p0' t1t2').
have/map_inj_in_uniq <- : {in ww &, injective (insubd p0')}.
  move=> x y.
  move=>/oin xin /oin yin xy.
  have xin' : x \in context by rewrite inp_sub_context // inE xin orbT.
  by rewrite -(insubdK p0' xin') xy insubdK // inp_sub_context // inE yin orbT.
by rewrite -oq orbit_uniq.
Qed.

End bridge_finType_eqType.

Section final_statement.

Fixpoint lookup (A B : Type) (p : A -> bool)(d : B)(s : seq (A * B)) : B :=
  match s with
  | nil => d
  | (a, v):: tl =>
    if p a then v else lookup p d tl
  end.

Definition pre_eval (A : Type) (eq_op : A -> A -> bool) (s : seq (A * A))
  (x : A) := lookup (eq_op x) x s.

Definition pre_update (A : Type) (s : seq (A * A)) (x y : A) :=
  (x, y)::s.

Definition pre_map_size (A : Type) (s : seq (A * A)) := (size s).+1.

Lemma pre_eval_map0 (A : eqType) (x : A) : pre_eval eq_op nil x = x.
Proof. by []. Qed.

Lemma pre_eval_update1 (A : eqType)
  (s : seq (A * A)) (x y : A) :
  pre_eval eq_op (pre_update s x y) x = y.
Proof.
rewrite /pre_update /pre_eval /=.
by rewrite (_ : eq_op x x = true) //; apply/eqP.
Qed.

Lemma pre_eval_update_dif (A : eqType) (s : seq (A * A)) (x x' y : A) :
  x != x' ->
  pre_eval eq_op (pre_update s x y) x' = pre_eval eq_op s x'.
Proof.
by move=> xnx'; rewrite /pre_update /pre_eval /= eq_sym (negbTE xnx').
Qed.

Lemma pre_eval_in (A : eqType) (s : seq (A * A)) (x y : A) :
  x != y -> pre_eval eq_op s x = y -> (x, y) \in s.
Proof.
move=> xny; elim: s => [|[a b] s IH]; rewrite /pre_eval /=.
  by move=> /eqP; rewrite (negbTE xny).
case: ifP=> [/eqP -> | xna]; last by  move=> evxs;  rewrite inE IH ?orbT.
by move=> <-; rewrite inE eqxx.
Qed.

Lemma pre_map_sizeP (A : eqType) (s : seq (A * A)) (x : A)(p : seq A):
    fpath (pre_eval eq_op s) x p -> uniq (x :: p) ->
            size (x :: p) <= pre_map_size s.
Proof.
have := lastI x p; set x' := last x p; set p' := belast x p => sdec.
case p'q : p' => [ | x1 p''].
  by rewrite sdec p'q size_rcons /pre_map_size ltn0Sn.
move=> pathp uniqxp; move: (pathp) (uniqxp).
move: (sdec); rewrite p'q /= => [] [xx1 pq].
rewrite pq rcons_uniq => pathp' /andP [] xnin /andP[] x'nin unp''.
have xin : (x, head x' p'') \in s.
  move/(pathP x): pathp' => /(_ 0).
  rewrite size_rcons ltn0Sn headI !nth0 /==> /(_ isT)/eqP.
  by apply: pre_eval_in; move: xnin; rewrite headI inE negb_or => /andP[].
set subs := [seq (nth x (x :: p) j, nth x p j) | j <- iota 0 (size p)].
have subsq : [seq a.1 | a <- subs] = (x :: p'').
  apply: (@eq_from_nth _ x).
    by rewrite !size_map size_iota pq size_rcons.
  move=> i; rewrite !size_map size_iota => isz.
  rewrite (nth_map (x, x)); last first.
    by rewrite !size_map size_iota.
  rewrite (nth_map 0); last by rewrite size_iota.
  rewrite nth_iota // add0n pq.
  case: i isz => [| i] //; rewrite pq size_rcons ltnS => isz.
  by rewrite !nthS nth_rcons isz.
have : uniq (x :: p'').
  rewrite /= unp'' andbT; move: xnin.
  by rewrite -cats1 mem_cat negb_or=> /andP[].
rewrite -subsq=> /map_uniq => subs_uniq.
have nostudder : forall i, i < size p -> nth x (x :: p) i != nth x p i.
  move=> i isz.
  have isz' : i < size (x :: p) by rewrite /= ltnW.
  have i1sz : i.+1 < size (x :: p) by rewrite /= ltnS.
  rewrite -[nth x p i]/(nth x (x :: p) i.+1).
    by rewrite nth_uniq // neq_ltn ltnSn.
have subsP : {subset subs <= s}.
  move=> e /(nthP (x, x)) [] i; rewrite size_map size_iota => isz <-.
    rewrite (nth_map i) ?size_iota // nth_iota // add0n.
  move/(pathP x): pathp => /(_ _ isz) /= /eqP eqi.
  by apply: pre_eval_in => //; apply: nostudder.
rewrite /pre_map_size size_rcons ltnS.
rewrite [(size p'').+1](_ : _ = size subs); last first.
  by rewrite !size_map size_iota pq size_rcons.
apply: uniq_leq_size=> //.
Qed.

Fixpoint pre_undup (A : Type) (eq_op : A -> A -> bool) (s : seq A) :=
  match s with
  | [::] => [::]
  | a :: tl =>
    if (has (eq_op a) tl) then pre_undup eq_op tl else a :: pre_undup eq_op tl
  end.

Lemma pre_undupP (A : eqType) :
   pre_undup (eq_op : A -> A -> bool) =1 undup.
Proof.
elim => [// | a s IH] /=.
have cnd : (eq_op a) =1 (pred1 a) by move=> x; rewrite eq_sym.
by rewrite -has_pred1 IH (eq_has cnd).
Qed.

Definition pre_map_orbit (A : Type) eq_op (s : seq (A * A)) (x : A) :=
  traject (pre_eval eq_op s) x
    (size (pre_undup eq_op (traject (pre_eval eq_op s) x (pre_map_size s)))).

Lemma pre_map_orbitP (A : eqType) (s : seq (A * A)) (x : A) :
  pre_map_orbit eq_op s x =
      traject (pre_eval eq_op s) x (size (pre_map_orbit eq_op s x)) /\
  looping (pre_eval eq_op s ) x (size (pre_map_orbit eq_op s x)) /\
  uniq (pre_map_orbit eq_op s x).
Proof.
split.
  by rewrite /pre_map_orbit size_traject.
set f := pre_eval eq_op s.
have anyloop : forall i k, iter i f x = iter (i + k.+1) f x ->
          forall j, iter j f x \in traject f x (i + k.+1).
  move=> i k cnd j; elim: j  {-2}j (leqnn j).
    by move=> j; rewrite leqn0 addnS trajectS inE => /eqP ->; rewrite eqxx.
  move=> n IH j; rewrite leq_eqVlt ltnS orbC=> /orP[/IH //| /eqP ->].
  have [lek | ] := boolP (n.+1 < i + k.+1).
    by apply/trajectP; exists (n.+1).
  rewrite -leqNgt addnS ltnS => ikn.
  have -> : n.+1 = (i + k.+1) + (n.+1 - (i + k.+1)).
    by rewrite subnKC // addnS ltnS.
  rewrite addnC iter_add -cnd addnS subSS -addnS.
  rewrite -iter_add IH //.
  by to_lia; move: (leP ikn); ssr_lia.
have xin : x \in pre_map_orbit eq_op s x.
  apply/trajectP; exists 0=> //.
  rewrite -has_predT; apply/hasP; exists x => //; rewrite pre_undupP mem_undup.
  by rewrite /pre_map_size trajectS inE eqxx.
have cn2 m : {subset traject f x m <= undup (traject f x (pre_map_size s))}.
  elim: m => [ | m IH]; first by [].
  move=> e /trajectP[] k; rewrite ltnS leq_eqVlt orbC=>/orP[].
    by move=> km ->; apply: IH; apply/trajectP; exists k.
  move=> /eqP -> -> {k}.
  have [ |/(uniqPn x) [y [z]] ] := boolP(uniq (traject f x m.+1)).
    rewrite trajectS=> /(@pre_map_sizeP A s).
     rewrite fpath_traject => /(_ isT).
    rewrite [size _]/= size_traject mem_undup=> ms.
    by apply/trajectP; exists m.
  rewrite size_traject; move=> [yltz zlts].
  rewrite !nth_traject ?(ltn_trans yltz) // => yqz.
  apply: IH.
  set k := z - y.+1.
  have kp : z = y + k.+1 by rewrite /k addnS -addSn subnKC.
  move: yqz; rewrite kp=> /anyloop /(_ m) /trajectP=> [][]m' m'lt ->.
  by apply/trajectP; exists m'=> //; rewrite (leq_trans m'lt) -?kp -1?ltnS.
have cnd : {subset undup (traject f x (pre_map_size s)) <=
                pre_map_orbit eq_op s x}.
  move=> e; rewrite mem_undup=>/trajectP [] i ilts -> {e}.
  suff : forall e, e \in traject f x i.+1 -> e \in pre_map_orbit eq_op s x.
    by apply; apply/trajectP; exists i.
  elim: i ilts => [ | i IH] ilts e.
    by move=>/trajectP=> [][]j; rewrite ltnS leqn0=> /eqP -> ->; rewrite xin.
  rewrite trajectSr mem_rcons inE=> /orP[eip1 | ein]; last first.
    by apply: IH; rewrite // (ltn_trans _ ilts).
  have [utj | /(uniqPn x)[y [z]]]:= boolP(uniq (traject f x i.+2)).
    have tojin : {subset traject f x i.+2 <=
                     undup (traject f x (pre_map_size s))}.
      move=> e' /trajectP=> [] [k kj ->]{e'}; rewrite mem_undup.
      by apply/trajectP; exists k =>//; rewrite (leq_ltn_trans _ ilts).
    move: (uniq_leq_size utj tojin).
    rewrite size_traject /pre_map_orbit=> jles.
    apply/trajectP; exists i.+1; first by rewrite pre_undupP.
    by apply/eqP.
  rewrite size_traject=> [][yz zlts].
  set k := z - y.+1.
  have kp : z = y + k.+1 by rewrite /k addnS -addSn subnKC.
  rewrite !nth_traject ?(ltn_trans yz) // kp=> /anyloop al.
  apply: IH; first by rewrite (ltn_trans _ ilts).
  move/trajectP: (al i.+1) => [] j' j'lt; rewrite (eqP eip1) => ->.
  apply/trajectP; exists j'=> //.
  by move: zlts; rewrite ltnS; apply: leq_trans; rewrite kp.
split; last first .
  have : uniq (undup (traject f x (pre_map_size s))) by rewrite undup_uniq.
  move/uniq_size_uniq => /(_ (pre_map_orbit eq_op s x)) => ->.
    by rewrite size_traject pre_undupP eqxx.
  move=> e; apply/idP/idP; first by apply: cnd.
  by apply: cn2.
apply/loopingP => m; rewrite size_traject -/(pre_map_orbit eq_op s x).
apply: cnd.
apply: (cn2 m.+1).
by apply/trajectP; exists m.
Qed.

Definition pre_map_iter (A : Type) (eqf : A -> A -> bool)
  (B : Type) (f : A -> B -> B) (v : B) (s : seq (A * A)) (x : A) : B :=
  foldr f v (pre_map_orbit eqf s x).

Lemma pre_map_iterP (A : eqType) (B : Type) (f : A -> B -> B) (v : B)
  (s : seq (A * A)) (x : A) :
 exists n,
   pre_map_iter eq_op f v s x = foldr f v (traject (pre_eval eq_op s) x n) /\
   uniq (traject (pre_eval eq_op s) x n) /\
   looping (pre_eval eq_op s) x n.
Proof.
have [oq [lo un]] := (pre_map_orbitP s x).
exists (size (pre_map_orbit eq_op s x)).
split; first by rewrite /pre_map_iter oq size_traject.
split; first by rewrite -oq.
by [].
Qed.

Parametricity pre_eval.
Parametricity pre_update.
Parametricity pre_map_size.

(*
Lemma pre_update_R (A1 A2 : Type)(A_R : A1 -> A2 -> Type)
      (s1 : seq (A1 * A1)) (s2 : seq (A2 * A2))
      (hs : list_R (prod_R A_R A_R) s1 s2)
      (x1 : A1) (x2 : A2) (hx : A_R x1 x2)
      (y1 : A1) (y2 : A2) (hy : A_R y1 y2) :
  list_R (prod_R A_R A_R) (pre_update s1 x1 y1) (pre_update s2 x2 y2).
Proof.
rewrite /pre_update //.
apply: list_R_cons_R.
  apply: prod_R_pair_R; assumption.
assumption.
Qed.

Realizer pre_update as pre_update_RR := pre_update_R.

*)

Definition a_list_map_funs (A : Type) (eqf : A -> A -> bool) :
  map_funs A :=
  Build_map_funs (nil : seq (A * A)) (pre_eval eqf) (@pre_update _)
  (pre_map_iter eqf).

Parametricity a_list_map_funs.

Lemma a_list_map_funs_system (T : eqType) :
  map_system (T := T)(a_list_map_funs eq_op).
Proof.
constructor.
- apply: pre_eval_update1.
- apply: pre_eval_update_dif.
- apply: pre_map_iterP.
- apply: pre_eval_map0.
Qed.

Lemma update_ext (P : eqType)
  (mf mf' : map_funs P) (mfs : map_system mf) (mfs' : map_system mf')
  (m1 : sort mf) (m2 : sort mf') (m1m2: eval m1 =1 eval m2) (x y : P):
  eval (update m1 x y) =1 eval (update m2 x y).
Proof.
move=> z; have [/eqP xz | xnz] := boolP(x == z).
  by rewrite -xz !eval_update1.
by rewrite !eval_update_dif.
Qed.

Lemma map_cycle_ext (P : eqType) (mf mf': map_funs P) (mfs : map_system mf)
  (mfs' : map_system mf') (s : seq P) :
  eval (map_cycle3 mf s) =1 eval (map_cycle3 mf' s).
Proof.
move=> z; rewrite /map_cycle3.
case: s => [ | a [ | b [ | c [ | d s']]]];
  try (rewrite !eval_map0 //).
by do 3 (apply: update_ext => //); move=> z'; rewrite !eval_map0 //.
Qed.

Lemma foldr_ext (A B : Type) (f f' : A -> B -> B) (v : B) :
  f =2 f' -> foldr f v =1 foldr f' v.
Proof. by move=> extf; elim=> [ | a s /= ->] //. Qed.

Lemma map_iter_ext (P : eqType)
  (mf mf' : map_funs P) (mfs : map_system mf) (mfs' : map_system mf')
  (m : sort mf) (m' : sort mf') (B : Type) (f f' : P -> B -> B) (v : B):
  f =2 f' -> eval m =1 eval m' -> map_iter f v m =1 map_iter f' v m'.
Proof.
move=> extf ext x.
have sametraj k : traject (eval m) x k = traject (eval m') x k.
  by elim: k (x) => [// | k IH] y /=; rewrite ext IH.
have [n [ov [un lo]]] := map_iterP mfs f v m x.
have [n' [ov' [un' lo']]] := map_iterP mfs' f' v m' x.
wlog : n n' f f' mf mf' mfs mfs' m m' extf ext sametraj ov un lo ov' un' lo'/
  n <= n'.
  move=> oneside.
  have [mlem' | ] := boolP (n <= n').
    by apply: (oneside n n') => //.
  rewrite -ltnNge => m'lem; apply esym.
  have : n' <= n.
    by rewrite leq_eqVlt m'lem orbT.
  by apply: (oneside n' n).
rewrite leq_eqVlt=> /orP[/eqP samesize | mltm'].
  by rewrite ov samesize ov' sametraj (foldr_ext _ extf).
have : uniq (traject (eval m) x n.+1).
  rewrite trajectSr -cats1 cat_uniq un /= andbT orbF.
  apply/negP=>/trajectP[] i isz.
  rewrite !(eq_iter ext) => sqi.
  move: un'; apply/negP/(uniqPn x); exists i; exists n.
  rewrite size_traject mltm' isz; split=> //.
  by rewrite !nth_traject ?sqi //; apply: (ltn_trans isz).
by rewrite looping_uniq lo.
Qed.

Lemma find_next_purple_ext (P : eqType) ccw
  (mf mf': map_funs P) (mfs : map_system mf) (mfs' : map_system mf')
  (m1 : sort mf) (m2 : sort mf') (c p : P) side:
  eval m1 =1 eval m2 ->
  find_next_purple ccw p m1 side c =
     find_next_purple ccw p m2 side c.
Proof.
move=> ext; rewrite /find_next_purple. 
set f1 := fun _ => _.
set f2 := fun _ => _.
have extf : f1 =2 f2 by move=> x y; rewrite /f1 /f2 ext.
by apply: map_iter_ext.
Qed.

Lemma find_purple_points_ext (P : eqType) ccw
  (mf mf': map_funs P) (mfs : map_system mf) (mfs' : map_system mf')
  (m1 : sort mf) (m2 : sort mf') (c p : P) :
  eval m1 =1 eval m2 ->
  find_purple_points ccw p m1 c = find_purple_points ccw p m2 c.
Proof.
move=> m1m2; rewrite /find_purple_points.
by rewrite !(find_next_purple_ext ccw mfs mfs' _ _ _ m1m2) !m1m2.
Qed.

Lemma naive_map (P : eqType) (p0 : P) ccw
 (mf mf': map_funs P) (mfs : map_system mf) (mfs' : map_system mf')
 (inp : seq P) tr1 tr2 m1 m2 p1 p2:
 naive p0 ccw mf inp = (tr1, m1, p1) ->
 naive p0 ccw mf' inp = (tr2, m2, p2) ->
 tr1 = tr2 /\  eval m1 =1 eval m2 /\  p1 = p2.
Proof.
elim: inp tr1 tr2 m1 m2 p1 p2 => [ | a s IH] /=.
  move=> tr1 tr2 m1 m2 p1 p2 [] <- <- <- [] <- <- <-; split; first by [].
  split; last by [].
  have/(update_ext mfs mfs') : eval (map0 mf) =1 eval (map0 mf').
    by move=> z; rewrite !eval_map0.
  by move=>/(_ p0 p0).
case sq: s => [ | b [ | c [ | p s']]].
      move=> tr1 tr2 m1 m2 p1 p2 [] <- <- <- [] <- <- <-; split; first by [].
      split; last by [].
      have/(update_ext mfs mfs') : eval (map0 mf) =1 eval (map0 mf').
        by move=> z; rewrite !eval_map0.
      by move=> abs; apply: map_cycle_ext.
    move=> tr1 tr2 m1 m2 p1 p2 [] <- <- <- [] <- <- <-; split; first by [].
    split; last by [].
    have/(update_ext mfs mfs') : eval (map0 mf) =1 eval (map0 mf').
      by move=> z; rewrite !eval_map0.
    by move=> abs; apply: map_cycle_ext.
  move=> tr1 tr2 m1 m2 p1 p2 [] <- <- <- [] <- <- <-; split; first by [].
  split; last by [].
  have/(update_ext mfs mfs') : eval (map0 mf) =1 eval (map0 mf').
    by move=> z; rewrite !eval_map0.
  by move=> abs; apply: map_cycle_ext.
move=> tr1 tr2 m1 m2 p1 p2.
rewrite -sq; move: IH.
case: (naive p0 ccw mf s) => [[tr3 m3] p3].
case: (naive p0 ccw mf' s) => [[tr4 m4] p4].
move=> /(_ tr3 tr4 m3 m4 p3 p4 erefl erefl)=> [] [-> [m3m4 ->]].
case pick_triangleP: (pick_triangle ccw tr4 a) => [[t trmt] | ].
  by move=> [] <- <- <- [] <- <- <-; split;[ | split].
rewrite (find_purple_points_ext ccw mfs mfs' _ _ m3m4).
case: (find_purple_points _ _ _ _) => p5 p6.
rewrite /add_red_triangles.
set f1 := fun _ => _; set f2 := fun _ => _.
have extf : f1 =2 f2 by move=> x y; rewrite /f1 /f2 !m3m4.
rewrite (map_iter_ext mfs mfs' _ extf m3m4).
move=> [] <- <- <- [] <- <- <-; split; first by [].
split; last by [].
rewrite /new_map; do 2 (apply: update_ext=> //).
Qed.


Lemma eq_op_R (T : choiceType)(context : seq T)
   (x1 : T) (x2 : P' context) (hx : PP' x1 x2)
   (y1 : T) (y2 : P' context) (hy : PP' y1 y2) :
  bool_R (eq_op x1 y1) (eq_op x2 y2).
Proof.
move: hx hy; rewrite /PP' => hx hy.
rewrite hx hy (inj_eq val_inj); apply: bool_R_refl.
Qed.

Lemma naive_correct2 (P : choiceType) (p0 : P) ccw
  (context inp : seq P) :
  {subset (p0 :: inp) <= context} ->
  cc_system ccw -> uniq inp -> 2 < size inp ->
  correct_triangulation2 ccw context inp
    (naive p0 ccw (a_list_map_funs eq_op) inp).1.1
  (seq_from_map eq_op (naive p0 ccw (a_list_map_funs eq_op) inp)).
Proof.
move=> subic ccsf ui szi.
have tmp2 := a_list_map_funs_R (@eq_op_R P context).
exact (naive_correct' subic (a_list_map_funs_system P) tmp2 ccsf
  (a_list_map_funs_system [finType of (P' context)]) ui szi).
Qed.

Lemma naive_correct_a_list (P :choiceType) (p0 : P) ccw
  (inp : seq P) : cc_system ccw ->
  uniq inp -> 2 < size inp ->
  correct_triangulation ccw inp
    (naive p0 ccw (a_list_map_funs eq_op) inp).1.1
    (seq_from_map eq_op (naive p0 ccw (a_list_map_funs eq_op) inp)).
Proof.
move=> ccfs ui szi.
pose pre_context := p0 :: inp.
have pcsup : {subset p0 :: inp <= pre_context} by [].
have mainpcsup := naive_correct2 pcsup ccfs ui szi.
pose extend p := p :: p0 :: inp.
have extendsup p : {subset p0 :: inp <= extend p}.
  by move=> q qin; rewrite inE pcsup ?orbT.
have mainextend p := naive_correct2 (extendsup p) ccfs ui szi.
split.
  by move: mainpcsup=> [A _].
split.
  by move: mainpcsup=> [_ [A _]].
split.
  by move: mainpcsup =>[_ [_ [A _]]].
split.
  by move: mainpcsup =>[_ [_ [_ [A _]]]].
split.
  split.
    move=> t1 t2 p.
    move: (mainextend p) => [_ [_ [_ [_ [[A _] _]]]]].
    by apply: A; rewrite inE eqxx.
  move=> p.
  move: (mainextend p) => [_ [_ [_ [_ [[_ A] _]]]]].
  by apply: A; rewrite inE eqxx.
by move: mainpcsup =>[_ [_ [_ [_ [_ [A _]]]]]].
Qed.

Lemma foldr_cons_nil (T : Type) (l : seq T) : foldr cons nil l = l.
Proof. by elim: l => [ | a l /= ->]. Qed.

Lemma naive_correct (P : choiceType) (p0 : P) ccw mf (inp : seq P) :
  cc_system ccw -> map_system mf -> uniq inp -> 2 < size inp ->
  correct_triangulation ccw inp
         (naive p0 ccw mf inp).1.1
         (seq_from_map eq_op (naive p0 ccw mf inp)).
Proof.
move=> ccs mfs uip isz.
set res := naive _ _ _ _.
pose res' := naive p0 ccw (a_list_map_funs eq_op) inp.
case resq : res=> [[tr m] p].
case res'q : res'=> [[tr' m'] p'].
case: (naive_map mfs (@a_list_map_funs_system P) resq res'q) =>  -> [] mq pq.
rewrite /seq_from_map /=.
suff -> : map_iter cons [::] m p = map_iter cons [::] m' p'.
  rewrite -[map_iter _ _ _ _]/(seq_from_map eq_op (tr', m', p')).
  by rewrite -[tr']/(tr', m', p').1.1 -res'q; apply: naive_correct_a_list.
have c_ext : @cons P =2 @cons P by move=> u v; congr (_ :: _).
rewrite pq; apply:(map_iter_ext mfs (a_list_map_funs_system _) nil c_ext mq).
Qed.

End final_statement.
