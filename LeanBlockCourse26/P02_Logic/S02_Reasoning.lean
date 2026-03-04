/-
This part is mostly inspired by `Robo` and `A Lean Intro to Logic`:
https://adam.math.hhu.de/#/g/hhu-adam/robo
https://adam.math.hhu.de/#/g/trequetrum/lean4game-logic
-/

import Mathlib.Tactic.Basic

/-
# Reasoning Tactics
=====================

After learning the basic building blocks, we now look at two complementary styles of reasoning:

Forward reasoning:
- `have`: introduce new facts from existing ones

Backward reasoning:
- `apply`: transform goals using implications
- `suffices`: introduce a fact and use it to rewrite the goal
- `refine`: a version of `exact` that permits placeholders
-/

/-
## A small side note on Lemmas and Facts

A *Lemma* is (usually) a statement that is re-usable and cleanly
abstracted with defined assumptions, that is stated **outside** of
the proof of a bigger *Theorem* but used inside it.

Lean also has `lemma` but since the distinction between
Lemmas and Theorems (and Propositions...) is blurry, mathlib just
embraces calling everything a `theorem`.

A *Fact* is (usually) a cleanly separate su-statement in the 
proof of a bigger *Theorem* that is not worth abstracting into
its own *Lemma* since there is no expectation it will be used
in any other proofs besides this one specific one.

This is remarkably similar to the `DRY`(Do Not Repeat Yourself)
principle in coding: if a block of code is only used in this one
particular method, this is where it should live. If it will or
can reasonably be used in other methods, you should abstract it
into its own method.

Lean also allows you to structure your proof by stating separate
facts in it through the `have` tactic.
-/

/-
## Forward Reasoning with `have`

The `have` tactic introduces new facts derived from existing ones.
It's useful for breaking down complex proofs into steps and is
used around 30,000 times in mathlib.
-/

-- Using have to build up facts step by step
theorem example_forward (P Q R : Prop) (h₁ : P → Q) (h₂ : Q → R) (p : P) : R := by
  have q : Q := by exact h₁ p -- Since P implies Q and we have a proof of P, we have a proof of Q
  have r : R := by exact h₂ q -- Since Q implies R and we have a proof of Q, we have a proof of R
  exact r                     -- We need and have a proof of R

#print example_forward -- The `have` actually show up in term mode

-- We can of course simplify this proof in term mode
example (P Q R : Prop) (h₁ : P → Q) (h₂ : Q → R) (p : P) : R := by
  have q : Q := h₁ p
  have r : R := h₂ q
  exact r

example (P Q R : Prop) (h₁ : P → Q) (h₂ : Q → R) (p : P) : R := by
  exact h₂ (h₁ p)

example (P Q R : Prop) (h₁ : P → Q) (h₂ : Q → R) (p : P) : R :=
  h₂ (h₁ p) -- or `h₂ <| h₁ p` or `(h₂ ∘ h₁) p`

/-
There is some overlap between `let` and `have`. The simple mental
model you should use is:

* A definition ("Let S be the set of primes.") should be `let`.
* A fact ("Since we know X and Y, we know Z.") should be `have`.
-/

/-
## Backward Reasoning with `apply`

The `apply` tactic works backward from the goal, reducing it to simpler subgoals.
If we want to prove `Q` and we have `h : P → Q`, then `apply h` changes the goal
from `Q` to `P`. This tactic is used around 17,000 times in mathlib.
-/

-- The same proof using apply to work backward
theorem example_backward (P Q R : Prop) (h₁ : P → Q) (h₂ : Q → R) (p : P) : R := by
  apply h₂ -- To prove R, it suffices to prove Q
  apply h₁ -- To prove Q, it suffices to prove P
  exact p  -- We need and have a proof of P

#print example_backward -- This just produces the forward term proof `h₂ (h₁ p)`


/-
Note that `apply`ing an implication to your goal is inherently destructive:
it is very possible that you end up with a goal that is actually hard
or even impossible to prove: everything follows from `⊥`, so you can
always rewrite your goal to `⊥`. But that will not be helpful.

Lean also inherently argues forward through type theory, so the backward
reasoning is a tactic mode convenience layer for mathematicians.

Also note that `rw [...] at ...` and `rw [...]` from P02S01 also can be
viewed in this forward and backward arguing model, but they are non-destructive.
-/

/-
## Exercise Block B01: Graph of Implications

This exercise demonstrates how forward and backward reasoning can lead to very
different-looking proofs of the same fact. Consider the following graph of
implications:

A - f -> B <- g - C
|        |        |
h        i        j
|        |        |
v        v        v
D <- k - E - l -> F
^        ^        |
|        |        p
m        n        |
|        |        v
G <- q - H - r -> I

Find a path from `A` to `I` using different reasoning styles. Have at least
one purely forward arguing path and one purely backward arguing path.
-/

example (A B C D E F G H I : Prop)
    (f : A → B) (g : C → B) (h : A → D) (i : B → E) (j : C → F)
    (k : E → D) (l : E → F) (m : G → D) (n : H → E) (p : F → I)
    (q : H → G) (r : H → I) (a : A) : I := by
  sorry
