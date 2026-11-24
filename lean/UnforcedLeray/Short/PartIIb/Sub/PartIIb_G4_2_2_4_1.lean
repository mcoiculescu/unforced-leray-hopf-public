import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_2_2_4

/-!
# Part II-b, task `PartII-b:G4/2/2/4/1` (`RadOneDDecay`): leaves

Source of record: `the November 2 reference manuscript`, lines 2349-2352.

`RadOneDDecay` (see `Sub/PartIIb_G4_2_2_4.lean`) is assembled as follows: extend `s ↦ g(√s)` and
`s ↦ s⁻¹` from `(0,∞)` to global smooth functions `G₁, I₁` (leaf `SmoothExtOn`), put `β = G₁ · I₁`,
and bound `β^{(m)}` on `t ≥ 1` by Leibniz (`norm_iteratedFDeriv_mul_le`) from the Gaussian bounds of
`(g ∘ √)^{(i)}` (leaf `GaussSqrtComp`, which uses `SqrtIterBound` and a Faà di Bruno bound) and the
bounds of `(s⁻¹)^{(i)}` (leaf `InvIterBound`); derivatives of the extensions agree with those of
the originals on `t > 1/2` (`Filter.EventuallyEq.iteratedDeriv_eq`/`iteratedFDeriv`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-- **Leaf `PartII-b:G4/2/2/4/1/1`**: all derivatives of `√` of order `≥ 1` are bounded on `[1,∞)`
(`d^{i+1}√t = c_i t^{1/2-i-1}`). -/
def SqrtIterBound : Prop :=
  ∀ i : ℕ, ∃ D : ℝ, ∀ t : ℝ, 1 ≤ t → ‖iteratedDeriv (i + 1) Real.sqrt t‖ ≤ D

/-- **Leaf `PartII-b:G4/2/2/4/1/2`**: all derivatives of `s ↦ s⁻¹` (as `ℂ`-valued) are bounded on
`[1,∞)` (`d^i s⁻¹ = (-1)^i i! s^{-i-1}`). -/
def InvIterBound : Prop :=
  ∀ i : ℕ, ∃ D : ℝ, ∀ t : ℝ, 1 ≤ t → ‖iteratedDeriv i (fun s : ℝ => ((s⁻¹ : ℝ) : ℂ)) t‖ ≤ D

/-- **Leaf `PartII-b:G4/2/2/4/1/3`**: a function smooth on `(0,∞)` has a globally smooth extension
agreeing with it on `t > 1/2` (cutoff `Real.smoothTransition`, or `exists_contDiff_...` bump). -/
def SmoothExtOn : Prop :=
  ∀ h : ℝ → ℂ, ContDiffOn ℝ ∞ h (Ioi 0) →
    ∃ h' : ℝ → ℂ, ContDiff ℝ ∞ h' ∧ ∀ t : ℝ, 1 / 2 < t → h' t = h t

/-- **Leaf `PartII-b:G4/2/2/4/1/4`**: Gaussian bounds for the derivatives of `s ↦ g(√s)` on `[1,∞)`
(Faà di Bruno `norm_iteratedFDerivWithin_comp_le` on `Ioi (1/2)`, using `SqrtIterBound`; the bound of
`g^{(i)}(√t)` is `C e^{-κ t}` because `(√t)² = t`). -/
def GaussSqrtComp : Prop :=
  ∀ g : ℝ → ℂ, ContDiffOn ℝ ∞ g (Ioi 0) →
    (∀ j : ℕ, ∃ (C κ : ℝ), 0 < κ ∧ ∀ r : ℝ, 1 ≤ r →
      ‖iteratedDeriv j g r‖ ≤ C * Real.exp (-(κ * r ^ 2))) →
    ∀ k : ℕ, ∃ (C κ : ℝ), 0 < κ ∧ ∀ m : ℕ, m ≤ k → ∀ t : ℝ, 1 ≤ t →
      ‖iteratedDeriv m (fun s : ℝ => g (Real.sqrt s)) t‖ ≤ C * Real.exp (-(κ * t))

end UnforcedLeray.Short.IIb
