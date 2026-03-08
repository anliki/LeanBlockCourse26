import Mathlib.Topology.Basic
import Mathlib.Tactic.Basic

/-
# An example from topology
=====================
-/

variable {X Y Z : Type*}
variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

-- A very detailed proof in tactic mode
theorem cont_comp_cont {f : X → Y} {g : Y → Z}
        (f_cont : Continuous f) (g_cont : Continuous g) :
        Continuous (g ∘ f) := by

  constructor
  intros U U_open

  let V := g⁻¹' U
  let W := f⁻¹' V

  have V_open : IsOpen V := g_cont.isOpen_preimage U U_open
  have W_open : IsOpen W := f_cont.isOpen_preimage V V_open

  have : W = (g ∘ f)⁻¹' U := rfl
  rw [← this]

  exact W_open

-- The same proof, inlining the intermediate names
example {f : X → Y} {g : Y → Z}
        (f_cont : Continuous f) (g_cont : Continuous g) :
        Continuous (g ∘ f) := by

  constructor
  intros U U_open

  have V_open : IsOpen (g⁻¹' U) := g_cont.isOpen_preimage U U_open
  have W_open : IsOpen (f⁻¹' (g⁻¹' U)) := f_cont.isOpen_preimage (g⁻¹' U) V_open

  exact W_open

-- A more concise proof in tactic mode
example {f : X → Y} {g : Y → Z}
        (f_cont : Continuous f) (g_cont : Continuous g) :
        Continuous (g ∘ f) := by
  constructor
  intros U U_open
  exact f_cont.isOpen_preimage (g⁻¹' U) (g_cont.isOpen_preimage U U_open)

-- A proof in term mode
example {f : X → Y} {g : Y → Z}
        (f_cont : Continuous f) (g_cont : Continuous g) :
        Continuous (g ∘ f) :=
  { isOpen_preimage := fun U U_open =>
      f_cont.isOpen_preimage (g⁻¹' U) (g_cont.isOpen_preimage U U_open) }
