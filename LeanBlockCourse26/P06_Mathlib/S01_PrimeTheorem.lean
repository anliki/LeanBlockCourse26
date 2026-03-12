import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Nth
import Mathlib.Data.Nat.PrimeFin
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.Tactic.TFAE

/-
## Euclid's theorem: there are infinitely many primes

How exactly is this result stated?

### [Wikipedia](https://en.wikipedia.org/wiki/Euclid%27s_theorem)

"Euclid's theorem (...) asserts that there are infinitely many prime numbers."

### Aigner and Ziegler: Proofs from THE BOOK

* "It shows that the sequence of primes does not end."
* "a finite set {p1,...,pr} cannot be the collection of all prime numbers"
* "We will show that any two Fermat numbers are relatively prime; hence there must be infinitely
   many primes.
* "The set of primes cannot be finite"
* "The function counting the number of primes that are less than or equal to a real number x is
   unbounded, and so there are infinitely many primes"
* "Our final proof goes a considerable step further and demonstrates not only that there are
   infinitely many primes, but also that the series ∑p 1/p diverges.""
-/


/-
You will now have to work with mathlib, i.e., understand its definitions and find its results.

To do this, you should:

(I)   Look up the correct section of the area / type / structure that you are interested in
      and read the comments and basic definitions of at least the main files (`Defs.lean` and
      `Basic.lean`). Either understand the definitions or, if they are too opaque and disappear
      in formal abstraction, find the relevant equivalent definition statements to `rw` with.

(II)  Hover or cmd-click anything that is unclear or unexpected and click through in VS Code.

(III) Use `exact?` or `simp?` whenever you think you have a nuclear expression that *should*
      be in mathlib to try and find it. Often it is advisable to extract the statement into
      separate `example` for this. You can also manually search the files, guess the 
      expected theorem name based on the [mathlib naming convention](https://leanprover-community.github.io/contribute/naming.html),
      use [leansearch.net](https://leansearch.net) or [Loogle](https://loogle.lean-lang.org),
      talk to people on [Is there code for X? on zulip](https://leanprover.zulipchat.com/#narrow/channel/217875-Is-there-code-for-X.3F/topic/Complexity.20theory/with/578655619)
      or ask ChatGPT, Claude, ... with online research tools and maybe even a lean environment.

**When is a `Nat` `Prime`?**

`Mathlib.Data.Nat.Prime.Defs` tells us that `def Prime (p : ℕ) := Irreducible`,
which takes us to `Mathlib.Algebra.Group.Irreducible.Defs`... but really you
probably just want to use one of the many more intuitive definitions and
properties stated in `Mathlib.Data.Nat.Prime.Defs`, for example:

```
variable {p : ℕ}

theorem prime_def : Prime p ↔ 2 ≤ p ∧ ∀ m, m ∣ p → m = 1 ∨ m = p := ...

theorem prime_def_lt : Prime p ↔ 2 ≤ p ∧ ∀ m < p, m ∣ p → m = 1 := ...

theorem prime_def_lt' : Prime p ↔ 2 ≤ p ∧ ∀ m, 2 ≤ m → m < p → ¬m ∣ p := ...

theorem prime_iff_not_exists_mul_eq :
   p.Prime ↔ 2 ≤ p ∧ ¬ ∃ m n, m < p ∧ n < p ∧ m * n = p := ...
```

### When is a `Set` `Finite` ...

We have already seen in P03 that `Set` is just defined as `Type → Type`.
The relevant part of mathlib to start with is `import Mathlib.Data.Set.Basic`.
For the notion of when a `Set` is `Finite` or `Infinite`, one starting
point in mathlib is `Mathlib.Data.Finite.Defs`. There we see that ...

```
Infinite (s : Set α) : Prop := ¬s.Finite
```

... also captured by ...

```
theorem not_infinite {s : Set α} : ¬s.Infinite ↔ s.Finite := ...
```

... and `Finite` itself is an inductively defined type class ...

```
class inductive Finite (α : Sort*) : Prop
   | intro {n : ℕ} : α ≃ Fin n → Finite _
```

... based on the type `Fin n`, capturing `Nat` that are strictly less
than `n`, defined in `Lean.Init.Prelude` as a structure ...

```
structure Fin (n : Nat) where
   mk ::
   val  : Nat
   isLt : LT.lt val n
```

### ... and how does it differ from `Finset`?

In `Mathlib.Data.Finset.Def` we can find the

```
structure Finset (α : Type*) where
  val : Multiset α
  nodup : Nodup val
```

`Mathlib.Data.Set.Finite.Basic` tells you that for any pair of
infinite and finite set we can find an element only in the former ...

```
theorem Set.Infinite.exists_notMem_finset (hs : s.Infinite) (t : Finset α) :
   ∃ a ∈ s, a ∉ t := ...
```

... as well as coerce any `Finite` `Set` to a `Finset`...

```
def Set.Finite.toFinset {s : Set α} (h : s.Finite) : Finset α :=
   @Set.toFinset _ _ h.fintype
```

... while using the fact that an element needs to exist in both versions ...

```
theorem Set.mem_toFinset : a ∈ hs.toFinset ↔ a ∈ s := ...
```  
-/

theorem infinitude_of_primes_tfae {ℵ₀} : [
   /-
   **(1) The set of primes is infinite**
   -/
   { p : ℕ | p.Prime }.Infinite,

   /-
   **(2) The subtype of primes is infinite**
   -/
   Infinite { p : ℕ // p.Prime },

   /-
   **(3) For any finite set we can find a prime number outside of it**
   -/
   ∀ (S : Finset ℕ), (∃ p ∉ S, p.Prime),

   /-
   **(4) For any finite set *of primes* we can find a prime outside of it**
   -/
   (∀ (S : Finset ℕ) (_ : ∀ s ∈ S, Nat.Prime s), (∃ p ∉ S, p.Prime)),

   /-
   **(5) For any natural number there exists a prime strictly greater than it**
   -/
   (∀ n : ℕ, (∃ p > n, p.Prime)),

   /-
   **(6) There exists an injection from the Natural numbers into the primes**
   -/
   ∃ (P : ℕ → ℕ) (h : P.Injective), (∀ k, (P k).Prime),

   /-
   **(7) The sequence of primes is strictly monotone increasing**
   -/
   StrictMono (Nat.nth Nat.Prime),

   /-
   **(8) The prime counting function is unbounded**
   -/
   ∀ n : ℕ, ∃ m, n ≤ Nat.primeCounting m,

   /-
   **(9) The cardinality of the primes equals ℵ₀**
   -/
   Cardinal.mk { p : ℕ // p.Prime } = ℵ₀,
  ].TFAE := by

  tfae_have 5 → 6 := by sorry -- Theo

  tfae_have 2 → 3 := by sorry -- Arthur

  tfae_have 1 → 2 := by sorry -- Onat

  tfae_have 1 → 6 := by sorry -- Bohdan

  tfae_have 3 → 2 := by sorry -- Leonie

  tfae_have 3 → 4 := by sorry -- Alexandra

  tfae_have 5 → 4 := by sorry -- Sammy

  tfae_have 6 → 3 := by
   intro h
   rcases h with ⟨P, hP_inj, hP_prime⟩
   intro S
   -- die Menge des Bilds von der inj. Fkt P ist unendlich
   have hR : (Set.range P).Infinite := Set.infinite_range_of_injective hP_inj
   -- ∃ p ∈ ℕ , p ∈ hR ∧ p ∉ S , weil S endl. hR unendlich
   obtain ⟨p, hpR, hpS⟩ := Set.Infinite.exists_notMem_finset hR S
   -- p ∈ hR -> ∃ k ∈ ℕ , p = P k
   rcases hpR with ⟨k, rfl⟩
   -- p = P k ist eine Primzahl
   have g : Nat.Prime (P k) := hP_prime k
   use (P k)


  tfae_have 6 → 1 := by sorry -- Alexander

  tfae_have 4 → 1 := by sorry -- Cara

  tfae_have 1 → 5 := by sorry -- Tonio

  tfae_have 1 → 3 := by sorry -- Nina

  tfae_have 3 → 5 := by sorry -- Daniel

  tfae_have 7 → 1 := by sorry -- Bohdan / Kimia

  tfae_have 1 → 7 := by sorry -- Bohdan / Kimia

  tfae_have 7 → 3 := by sorry -- Kimia

  tfae_have 1 → 8 := by sorry 

  tfae_have 8 → 5 := by sorry

  tfae_have 2 → 9 := by sorry

  tfae_have 9 → 2 := by sorry

  tfae_finish

