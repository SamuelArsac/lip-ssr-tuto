From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_fingroup.
From mathcomp Require Import all_algebra all_solvable all_field.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma test : True. Proof. by []. Qed.

Add Search Blacklist "__canonical__" "__to__" "HB_unamed_mixin". (* HB bug #418 to fix *)

Search addn muln.
Search (_ * _.+1) inside ssrnat.
Search "add" "M".
Search "Gauss".



Module GoalModel.
Section GoalModel.
Variables (Ti Tj Tl : Type) (ej : Tj).
Variables (Pk : Ti -> Type) (Pn : Tl -> Type).
Variables (Conclusion : Ti -> Tj -> Tl -> Type).

Lemma goal_model_example (ci : Ti) (dj : Tj := ej) (Fk : Pk ci) :
  forall (xl : Tl), Pn xl -> Conclusion ci dj xl.
Proof.
move=> xl pnxl.
Fail move: xl.
move: ci Fk.
Abort.
End GoalModel.
End GoalModel.

Module ArgumentsToTactics.

Lemma negb_and : forall b c, ~~ (b && c) = ~~ b || ~~ c.
Proof.
move=> b. move=> c. move: b. move: c.
Restart.
move=> c b. move: b c.
Restart.
move=> b; case: b; move=> c; case: c.
Restart.
by case; case.
Qed.

Lemma test_modus_ponens P Q : P -> (P -> Q) -> Q.
Proof.
move=> p.
apply. (* equivalent to `move=> pq; apply: pq` *)
by []. (* or simply `exact` instead of `by apply`. *)
Qed.

End ArgumentsToTactics.

Module BooleanReflection.

Fixpoint leq (n m : nat) : bool :=
  if n is p.+1 then
    if m is q.+1 then leq p q
    else false
  else true.

Arguments leq !n !m.
Infix "<=" := leq.

Lemma leq0n n : (0 <= n) = true.
Proof. (* compute. *) by []. Qed.

Lemma leqSS n m : (n.+1 <= m.+1) = (n <= m).
Proof. (* simpl *) by []. Qed.

Lemma leqnn n : (n <= n) = true.
Proof.
elim: n => [|m IHm].
  by apply: leq0n. (* or `exact: leq0n.` *)
by rewrite leqSS IHm.
Restart.
by elim: n.
Qed.

Definition andb (b1 b2 : bool) : bool :=
  if b1 then b2 else false.
Infix "&&" := andb.

Definition orb (b1 b2 : bool) : bool :=
  if b1 then true else b2.
Infix "||" := orb.

Definition negb b : bool :=
  if b then false else true.
Notation "~~ b" := (negb b).

Lemma andbC b1 b2 : (b1 && b2) = (b2 && b1).
Proof.
case: b1 => /=.
  case: b2.
    rewrite /=.
    by [].
  by [].
by case: b2.
(* by case: b1; case: b2. *)
Qed.
End BooleanReflection.

Search (_ <= _) inside ssrnat.
Locate "_ < _".
Check (forall x, x.+1 <= x).
Search orb "C" inside ssr.ssrbool.
Print commutative.
Check (3 == 4) || (3 <= 4).
Eval compute in (3 == 4) || (3 <= 4).
Check (true == false).
Check (3 != 4).

Lemma test_is_true_coercion : true.
Proof. rewrite /is_true. by []. Qed.

Lemma test_eqP n m : n == m -> n.+1 + m.+1 = m.+1.*2.
Proof.
(*#
Check eqP.
move=> /eqP. move=> /eqP. move=> /eqP Enm. rewrite Enm.
apply/eqP.
apply/eqP.
Search (_ + _) _.*2 inside ssrnat.
exact: addnn.
#*)
by move=> /eqP ->; rewrite -addnn.
Qed.

Lemma test2_eqP b1 b2 : b1 == ~~ b2 -> b1 || b2.
Proof.
(*
Search orb inside ssrbool.
*)
by move=> /eqP->; exact: orNb.
Qed.

Lemma test_leqW i j k : (i <= k) && (k.+1 <= j) -> i <= j.+1.
Proof.
(* move=> /andP. case. move=> /leqW. move=> leq_ik1. *)
move=> /andP[/leqW leq_ik1 /leqW leq_k1j1].
exact: leq_trans leq_ik1 leq_k1j1.
Qed.

Module reflect_for_eqP.

Print reflect.

Fixpoint eqn m n :=
  match m, n with
  | 0, 0 => true
  | j.+1,k.+1 => eqn j k
  | _, _ => false
  end.
Arguments eqn !m !n.

Lemma myeqP m n : reflect (m = n) (eqn m n).
Proof.
apply: (iffP idP) => [|->]; last by elim: n.
by elim: m n => [|m IHm] // [|n] // /IHm->.
Qed.

Lemma test_myeqP n m : (eqn n m) -> m = n.
Proof. by move=> /myeqP ->. Qed.

End reflect_for_eqP.

