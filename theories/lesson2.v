(**
---
customTheme : "solarized"
slideNumber: true
title: "Lip Ssr Tutorial"
minScale: 0.2
width: 2000
height: 1250
---

# Recaps

---

## Recap 1/2

- Proof language:
  - the stack model
  - `=> name // /view /= {name} [|..|]`, to post-process the goal,
  - `rewrite lem -lem ?lem // /= /def`,
  - `apply: lem` to use a lemma in backward reasoning,
  - `apply/view` to use a view on the stack,
  - `apply` to apply the top of the stack to the rest of the stack,
  - `elim` to do elimination,
  - `elim: n m` to do elimination on `n` while generalizing on `m`.

---

## Recap 2/2

- Library:
  - naming convention: `addnC`, `eqP`, `orbN`, `orNb`, ...
  - notations: `.+1`, `if-is-then-else`,
  - `Search (_ + _) inside ssrnat`,
  - `Search addn "C" inside ssrnat`,
  - Use the HTML doc!
- Methodology:
  - boolean predicates, (e.g. `<=`, `\in`, `==`)
  - indentation of subgoals,
  - `reflect P b` to link `bool` with `Prop`.
  - convenience lemma `iffP` for proving `reflect`

---

Setting up a file using the mathcomp library:
*)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_fingroup.
From mathcomp Require Import all_algebra all_solvable all_field.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
(**

⋄

This setup is interactive using Vscode and Coq-lsp
*)
Lemma test : True. Proof. by []. Qed.
(**

---

#  Advanced ssreflect tactics

---

## More bookkeeping

---

### Bookkeeping 101 Reminders

---

#### Heap & Stack model of a Goal **vs** Curry-Howard (reminder)

```
(* begining of heap *)
ci : Ti
…
dj := ej : Tj
…
Fk : Pk ci
…
(* end of heap *)
=================
forall (xl : Tl) (* top of the stack *)
…,
Pn xl ->         (* nth element of the stack *)
… ->
Conclusion       (* bottom of the stack = no more elements *)
```

---

#### Bookkeeping 101 Operations:

- Stack operations:
  - pop `move=> FRESH_NAME`
  - push `move: EXISTING_NAME`
  - application at the top: `move=> /LEMMA`
  - case analysis / induction at the top: `case` or `elim` (no argument)

- Arbitrary position operations:
  - simplification / trivial stuff / clearing: `move=> /= // //= {name_to_clear}`
  - rewriting `rewrite lem -lem /def /= // {name_to_clear}`

- Whole goal operations:
  - application: `apply` or `apply: lem` or `apply/lem`

---

#### Examples 101

---

#### Intro patterns = (Intro items)*

*)

Lemma test2 n (A B C D : bool) (view : 0 <= n -> true && true -> A <-> B) :
  (n <= n * 2 -> C) -> A -> B = true && (C || true).
Proof.
move=> fresh_name /view /= {view} -> //.
by [rewrite orbT|rewrite andbT]. (* brackets can be omitted if only one tactic *)
(*
Restart.
Fail move=> -> /view.
move=> ->.
  by move=> /view->.
by rewrite leq_pmulr.
Restart.
move: A B view.
case=> [|//].
case=> [|//].
  rewrite orbT.
  by [].
*)
Abort.
(**

---

### Advanced Bookkeeping

---

#### Bookkeeping 102 Operations:

- More stack intro-items:
  - skip `move=> +`, dup `move=> /[dup]` and `move=> /[swap]`
  - case analysis at the top: `move=> []`
  - applications at the top `move=> /(_ x)` and  `move=> /[apply]`

- Control flow operations:
  - `first`, `last`, `last first`, `last n first`, etc
  - `have`, `suff`, `pose`

- On the fly generalization and abbreviation:
  - `move: (pattern)`
  - `set x := (pattern)`

---

#### Skip, Dup and Swap (More intro items 1/3)

- The syntax of Dup and Swap is the combination of `/` and `[dup]` or `[swap]`

*)
Lemma test_dup_and_swap m n (P := fun b => m <= (if b then n else 0) <= m) :
  n <= m <= n -> P (m <= n).
Proof.
move=> /andP[].
move=> /[swap].
Fail by move=> ->.
rewrite /P.
Fail by move=> ->.
by move=> /[dup] + -> -> => ->.
Qed.
(**

---

#### Intro-item case (More intro items 2/3)

- Case analysis can be performed as part of an intro pattern
- One can continue the intro pattern in two ways:
  1. inside the brackets (with the right number of cases)
  2. outside the brackets


*)
Lemma test_intro_case (P : pred nat) : P 0 -> (forall m, P 0 -> P m.+1) -> forall n, P n.
Proof.
move=> P0 PS [//|n].
by rewrite PS.
(*
Restart.
move=> P0 /[swap].
Fail rewrite P0 => [|].
by rewrite P0 => - []// n ->.
*)
Qed.
(**


---

#### Intro-item application (More intro items 3/3)

- Specialization of top of the stack lemma is `/(_ t)`.
- Indeed: `(_ t)` is `fun f => f t`, which has type `(forall x : A, B x) -> B t`

*)
Lemma test_intro_apply (P : pred nat) k : P 0 ->
  forall n, P k -> (forall m, P k -> P m.+1) -> P n.
Proof.
move=> P0 [//|n] Pk.
by move=> /(_ n Pk).
(*
Restart.
move=> P0 [//|n] /[swap].
move=> /[apply]. (* same as `=> H /H` *)
by [].
*)
Qed.
(**

---

#### Reordering goals (Control flow operations 1/3)

Simple forms:
- `tac1; first tac2.` or - `tac1; last tac2.`
- `tac1; last first.` or `tac1; first last`
- `tac1; last 2 first.` or `tac1; first 2 last`

Demo:
*)
Lemma test_first_last (G P1 P2 P3 : Prop) (p1 : forall u : unit, P1) :
   (P1 -> P2 -> P3 -> G) -> G.
Proof.
apply; first exact: p1.
(*
Restart.
apply; last first.
Restart.
apply; first 2 last.
*)
Abort.
(**

---

#### Have (Control flow operations 2/3)

- `have` is the equivalent of Coq's `assert`
- it has 2 $\times$ two variants
- `have: stuff; first by tac` is abbreviated `have: stuff by tac`

| | `have := proof` | `have : statement` |
|---|---|---|
| identified  | `have f x := S x` | `have f x : list x` |
| introductive | `have [n] := ubnP`  | `have [p] : exists p, prime p` |


Try me:
*)
Goal False.
have f x := S x.            have l x : list x by exact: [::].
have [n n_gt0] := ubnP 0.   have [p p_prime] : exists p, prime p by exists 2.
Abort.
(**

---

#### Suff and pose (Control flow operations 3/3)

- `suff` is almost like `have: stuff; last first.`
- `pose idents :=` is almost like `have idents := ` but transparent.

Try me:
*)

Goal False.
pose f n := n + 1.
suff : forall n, f n != f (n + 1).
Abort.

(**

---

## Rewrite: one command to rule them all.

---

### Chaining rewrites

- 1/3 of the lines of Math Comp proofs are rewrite
- side conditions handling via // and ?
- rewrite a boolean predicate (is_true hides an equation)

*)
Lemma test_leq_cond p : prime p -> p.-1.+1 + p = p.*2.
Proof.
(*
move=> pr_p.
Search predn inside ssrnat.
rewrite prednK. (* main step *)
  by rewrite addnn. (* side condition *)
Search prime leq 0.
by apply: prime_gt0. (* conclusion *)
#*)
(* idiomatic use of conditional rewrite rules *)
by move=> pr_p; rewrite prednK ?addnn // prime_gt0.
Qed.
(**

---

### rewrite and subterm selection

- keyed matching drives the search
- specialization via argument passing
- specialization via pattern `rewrite [pat]stuff`
- localization via contextual pattern (approximate or precise)
- LHS and RHS notations
- subterm selection also works with `move: (pat)` and `set := (pat)`

*)
Lemma subterm_selection n m :
  n + (m * 2).+1 = n * (m + m.+1).
Proof.
rewrite addnC.
rewrite (addnC m).
rewrite [_ + m]addnC.
rewrite [in n * _]addnC.
rewrite [X in _ = _ * X]addnC.
rewrite [in RHS]addnC.
rewrite -[n in RHS]addn0.
set k := (X in _ = _ * X).
move: (0 in RHS).
Abort.
(**

---

## Reflect and spec lemmas

---

### The reflect predicate

 P b is the preferred way to state that the predicate P (in Prop) is logically equivalent to b = true

*)
Module reflect_for_eqP.

Print reflect.

(* we use this boolean predicate in the examples below *)
Fixpoint eqn m n :=
  match m, n with
  | 0, 0 => true
  | j.+1,k.+1 => eqn j k
  | _, _ => false
  end.
Arguments eqn !m !n.
(**

---

### Proving the reflection lemma for eqn

- the convenience lemma iffP
- the congr tactic

*)
Lemma myeqP m n : reflect (m = n) (eqn m n).
Proof.
apply: (iffP idP) => [|->]; last by elim: n.
elim: m n; first by case.
move=> n IHn m eq_n1m.
case: m eq_n1m => // m eq_n1m1. (* case with generalization *)
congr (_.+1). (* cleanup of the goal *)
by apply: IHn.
(*
Restart.
apply: (iffP idP) => [|->]; last by elim: n.
by elim: m n => [|m IHm] // [|n] // /IHm->.
*)
Qed.

Lemma test_myeqP n m : (eqn n m) -> m = n.
Proof. by move=> /myeqP ->. Qed.

End reflect_for_eqP.
(**

---

### Spec lemmas

- Inductive predicates to drive the proof:
  - you chose how many branches
  - you chose which equations are automatically applied
  - you chose which extra assumption a branch has
- of syntax for inductives

*)
Inductive leq_xor_gtn m n : bool -> bool -> Prop :=
  | LeqNotGtn of m <= n : leq_xor_gtn m n true false
  | GtnNotLeq of n < m  : leq_xor_gtn m n false true.

Axiom leqP : forall m n : nat, leq_xor_gtn m n (m <= n) (n < m).
(**

---

### Let's try out leqP on an ugly goal

matching of indexes uses the same discipline of rewrite

*)
Lemma test_leqP m n1 n2 :
  (m <= (if n1 < n2 then n1 else n2)) =
  (m <= n1) && (m <= n2) && ((n1 < n2) || (n2 <= n1)).
Proof.
(* the indexes of <tt>leqP</tt> give rise to patterns, which are matched
   right to left. So the first one is <tt>_ < _</tt> which finds <tt>n1 < n2</tt>
   and replaces it with <tt>false</tt> in the first branch and <tt>true</tt> in the
   second. Then it is the turn of <tt>n2 <= n1</tt>.

   use: Set Debug "ssreflect". for a slow motion *)
case: leqP => [leqn21 | /ltnW ltn12 ]; rewrite /= andbT.
  by rewrite andb_idl // => /leq_trans /(_ leqn21).
by rewrite andb_idr // => /leq_trans->.
Qed.
(**

---

### Another commodity: ifP

- a spec lemma for if-then-else
- handy with case, since matching spares you to write the expressions involved
- remark how the goal is used as a work space

*)
Lemma test_ifP n m : if n <= m then 0 <= m - n else m - n == 0.
Proof.
case: ifP => //.
(* MC idiom: don't introduce hyps if not necessary *)
by move=> /negbT; rewrite subn_eq0 leqNgt negbK=> /ltnW.
Qed.
(**

---

### Strong inductions on the fly: ubnP

- a spec lemma for strong induction

*)
Lemma test_ubnP P : P 0 -> (forall n, (forall m, m < n -> P m) -> P n) ->
  forall n, P n.
Proof.
move=> P0 Plt k.
have [n] := ubnP k.
elim: n k => // n IHn [|k] kn.
  exact: P0.
apply: Plt => m mk; apply/IHn.
by rewrite (leq_trans mk).

(**


---

## Resources

- Greatly inspired by Enrico Tassi's lectures at [Math Comp School & Workshop - 2022.](https://mathcomp-schools.gitlabpages.inria.fr/2022-12-school/school)
- The [Cheat Sheet](https://www-sop.inria.fr/teams/marelle/MC-2022/cheatsheet.pdf) (various versions [here](https://math-comp.github.io/documentation.html#org3b59844)) and the [interactive cheat sheet](https://perso.crans.org/cohen/IRIF-mathcomp-2021/irif.cheat_sheet.html)
- The [Mathcomp Book](https://math-comp.github.io/mcb/) (needs to be updated to mathcomp v2) <center><br/><img src="images/cover-front-web.png"></image><br/></center> and the [documentation](https://math-comp.github.io/)

- The [SSReflect User Manual](https://coq.inria.fr/doc/v8.20/refman/proof-engine/ssreflect-proof-language.html)

---

## Next time(s)

- Generic lemmas and hierarchies
- Finite types and iterated operators
- black belt tactics (such as `wlog` and `gen have`)
*)
