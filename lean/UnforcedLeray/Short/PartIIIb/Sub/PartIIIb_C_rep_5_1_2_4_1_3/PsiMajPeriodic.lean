import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_1_2_4_1_3.Kernel
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_1.L1

/-!
# `PartIII-b:C/rep/5/1/2/4/1/3/3/5`: `psiMaj` is `2c/R`-periodic in the phase

Source `the November 2 reference manuscript` 2672-2674: the chart point
`chartOf R c z τ` is invariant under `τ ↦ τ + k·(2c/R)`, so the source weight
`srcW R c G σ z` is `2c/R`-periodic in `σ`, and so is the majorant `psiMaj` in `τ`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete.WYCore

/-- The source weight is `2c/R`-periodic in its phase argument. -/
theorem srcW_add_period (R c : ℝ) (hR : 0 < R) (hc : 0 < c) (G : Chart → ℝ≥0∞)
    (σ : ℝ) (z : Space) :
    srcW R c G (σ + 2 * c / R) z = srcW R c G σ z := by
  have h := chartOf_add_int_period R c hR hc z σ 1
  have e : σ + 2 * c / R = σ + ((1 : ℤ) : ℝ) * (2 * c / R) := by
    push_cast
    ring
  unfold srcW
  rw [e, h]

theorem psiMajPeriodic : PsiMajPeriodic := by
  intro R c θ G hR hc y τ
  show psiMaj R c θ G (τ + 2 * c / R) y = psiMaj R c θ G τ y
  unfold psiMaj
  refine lintegral_congr fun l => lintegral_congr fun z => ?_
  rw [show τ + 2 * c / R + 2 * Real.log l = (τ + 2 * Real.log l) + 2 * c / R by ring,
    srcW_add_period R c hR hc G]

end UnforcedLeray.Short.PartIIIb.Concrete.WYCore
