import UnforcedLeray.Short.PartI.Sub.T02_3_10
import UnforcedLeray.Lib.Cylinder.IBP

/-!
# Part I, toolkit leaf `EbDerivBounds`: `ebDerivBounds`

Source of record: `the November 2 reference manuscript`, lines 276-282.
The Props `EbSliceSmooth` and `EbDerivBounds` are defined in `Short/PartI/Sub/T02_3_10.lean`
(lines 107-127); `HasBoundedDerivsOn` is in `Short/PartI/Sub/T02.lean` (line 103).

## Argument (fixed `s ∈ [0,T]`, write `w = v s`)

* `w` is `C^∞`, hence differentiable, by `EbSliceSmooth`.
* `‖w z‖ = ‖iteratedFDeriv ℝ 0 w z‖ ≤ M0` (order `0` of `HasBoundedDerivsOn`).
* `‖fderiv ℝ w z‖ = ‖iteratedFDeriv ℝ 1 w z‖ ≤ M1` (order `1` of `HasBoundedDerivsOn`).
* `Cyl.partialEta w z = fderiv ℝ w z (0, 1)`, and `‖fderiv ℝ w z (0, 1)‖ ≤ ‖fderiv ℝ w z‖ * ‖(0, 1)‖`
  with `‖(0, 1)‖ = 1`.

So `Mv := max M0 0` and `Kv := max M1 0` are nonnegative and bound both quantities.
-/

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Cyl (Plane)

/-- **Toolkit leaf `EbDerivBounds`**: `HasBoundedDerivsOn` at orders `0` and `1` gives uniform
bounds `‖v s z‖ ≤ Mv` and `‖∂_η v s z‖ ≤ Kv` on `[0,T] × ℝ²`. -/
theorem ebDerivBounds : EbSliceSmooth → EbDerivBounds := by
  intro hS ν c T v p hcl hb
  obtain ⟨M0, hM0⟩ := hb 0
  obtain ⟨M1, hM1⟩ := hb 1
  refine ⟨max M0 0, max M1 0, le_max_right _ _, le_max_right _ _, ?_⟩
  intro s hs z
  have hdiff : Differentiable ℝ (v s) :=
    (hS ν c T v p hcl s hs).1.differentiable (by simp)
  -- order zero: `‖v s z‖ ≤ M0`
  have h0 : ‖v s z‖ ≤ M0 := by
    have := hM0 s hs z
    rwa [norm_iteratedFDeriv_zero] at this
  -- order one: `‖fderiv ℝ (v s) z‖ ≤ M1`
  have h1 : ‖fderiv ℝ (v s) z‖ ≤ M1 := by
    have e : ‖iteratedFDeriv ℝ 0 (fderiv ℝ (v s)) z‖ = ‖iteratedFDeriv ℝ (0 + 1) (v s) z‖ :=
      norm_iteratedFDeriv_fderiv
    rw [norm_iteratedFDeriv_zero] at e
    rw [e]
    exact hM1 s hs z
  -- the norm of the unit vector `(0, 1)` in the sup-norm on `ℝ × ℝ`
  have hone : ‖((0 : ℝ), (1 : ℝ))‖ = 1 := by
    simp [Prod.norm_def]
  -- the `η`-derivative bound
  have hpe : ‖Cyl.partialEta (v s) z‖ ≤ M1 := by
    rw [UnforcedLeray.Cyl.partialEta_eq_fderiv hdiff z]
    calc ‖fderiv ℝ (v s) z ((0 : ℝ), (1 : ℝ))‖
        ≤ ‖fderiv ℝ (v s) z‖ * ‖((0 : ℝ), (1 : ℝ))‖ := (fderiv ℝ (v s) z).le_opNorm _
      _ = ‖fderiv ℝ (v s) z‖ := by rw [hone, mul_one]
      _ ≤ M1 := h1
  exact ⟨le_trans h0 (le_max_left _ _), le_trans hpe (le_max_left _ _)⟩

end UnforcedLeray.Short.PartI
