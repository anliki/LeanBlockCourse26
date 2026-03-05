---
title: "When · focusing is optional"
parent: Addendum
nav_order: 9994
---

# When `·` focusing is optional
{: .no_toc }

*March 5, 2026*

---

In Exercise 2.2 of **S03 Connectives**, we saw a proof where some `·` (focus dot) separators are missing and the linter stays silent. This is not a linter bug — it is intended behavior. Here is why.

## The two styles

Consider proving `a ∧ b ∧ c` (which parses as `a ∧ (b ∧ c)`). The **fully nested** style places every subgoal under a `·`:

```lean
example (ha : a) (hb : b) (hc : c) : a ∧ b ∧ c := by
  constructor
  · exact ha
  · constructor
    · exact hb
    · exact hc
```

The **flat** style omits the `·` for the second branch of the outer `constructor`:

```lean
example (ha : a) (hb : b) (hc : c) : a ∧ b ∧ c := by
  constructor
  · exact ha
  constructor
  · exact hb
  · exact hc
```

Both are valid Lean and both pass all Mathlib linters.

## Why the linter allows the flat style

The relevant linter is **`multiGoal`** ([mathlib4#12339](https://github.com/leanprover-community/mathlib4/pull/12339), October 2024). It warns when a non-excluded tactic runs with multiple goals in scope. The check is *dynamic* (based on the goal count at each tactic invocation), not *structural* (based on the nesting of the proof tree).

In the flat style, here is what happens step by step:

| Tactic | Goals before | Goals after | Linter |
|--------|-------------|-------------|--------|
| `constructor` | 1 | 2 | Excluded (goal-creating) |
| `· exact ha` | 1 (focused) | 0 + 1 remaining | OK |
| `constructor` | **1** | 2 | Excluded — and only 1 goal was in scope |
| `· exact hb` | 1 (focused) | 0 + 1 remaining | OK |
| `· exact hc` | 1 (focused) | 0 | OK |

After `· exact ha` closes the focused goal, only **one** goal remains. The second `constructor` therefore runs in a single-goal context. At no point does a non-excluded tactic see multiple unfocused goals.

## Which style to prefer

Both styles are correct. However, the **fully nested** style makes the proof tree structure explicit: you can see at a glance that `constructor` produces exactly two branches. The flat style can be confusing when combined with case splits (like `rintro`), because unfocused branches from one `constructor` appear at the same indentation level as the next case.

In this course, we recommend the fully nested style for clarity.

## Further reading

- [`linter.style.multiGoal`](https://github.com/leanprover-community/mathlib4/pull/12339) — the linter enforcing goal focusing
- [`linter.style.cdot`](https://github.com/leanprover-community/mathlib4/pull/15010) — a separate linter checking only the `·` character itself (not structure)
- [Mathlib style guide on tactic proofs](https://leanprover-community.github.io/contribute/style.html) — "new goals arising as side conditions or steps are indented and preceded by a focusing dot `·`"
