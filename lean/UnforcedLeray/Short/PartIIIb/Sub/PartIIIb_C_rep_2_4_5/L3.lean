import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_4_5.Defs
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# `PartIII-b:C/rep/2/4/5` : `VertDil` (task `PartIII-b:C/rep/2/4/5/3`)

Source `the November 2 reference manuscript` 3631-3645 (the dilation `s ↦ l s`),
one-dimensional form.  The change of variables for lintegrals along `s ↦ l s` holds for arbitrary
functions, because it is a measurable equivalence (`lintegral_map_equiv`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- `∫ H(l s) ds = |l|⁻¹ ∫ H(w) dw` for every `H : ℝ → ℝ≥0∞` and `l ≠ 0`. -/
theorem vd_scale {l : ℝ} (hl : l ≠ 0) (H : ℝ → ℝ≥0∞) :
    ∫⁻ s : ℝ, H (l * s) = ENNReal.ofReal |l⁻¹| * ∫⁻ w : ℝ, H w := by
  have hmap : Measure.map (MeasurableEquiv.mulLeft₀ l hl) (volume : Measure ℝ) =
      ENNReal.ofReal |l⁻¹| • (volume : Measure ℝ) := Real.map_volume_mul_left hl
  calc ∫⁻ s : ℝ, H (l * s)
      = ∫⁻ w : ℝ, H w ∂(Measure.map (MeasurableEquiv.mulLeft₀ l hl) (volume : Measure ℝ)) :=
        (lintegral_map_equiv H (MeasurableEquiv.mulLeft₀ l hl)).symm
    _ = ∫⁻ w : ℝ, H w ∂(ENNReal.ofReal |l⁻¹| • (volume : Measure ℝ)) := by rw [hmap]
    _ = ENNReal.ofReal |l⁻¹| * ∫⁻ w : ℝ, H w := lintegral_smul_measure _ _

/-- Part (i) of `VertDil`: the substitution `w = l s`. -/
theorem vd_part1 {l : ℝ} (hl : 0 < l) (S g : ℝ → ℝ≥0∞) (z : ℝ) :
    ∫⁻ s : ℝ, S (z - l * s) * g s = ENNReal.ofReal l⁻¹ * ∫⁻ w : ℝ, S (z - w) * g (l⁻¹ * w) := by
  calc ∫⁻ s : ℝ, S (z - l * s) * g s
      = ∫⁻ s : ℝ, (fun w : ℝ => S (z - w) * g (l⁻¹ * w)) (l * s) :=
        lintegral_congr (fun s => by simp only [inv_mul_cancel_left₀ hl.ne'])
    _ = ENNReal.ofReal |l⁻¹| * ∫⁻ w : ℝ, S (z - w) * g (l⁻¹ * w) :=
        vd_scale hl.ne' (fun w : ℝ => S (z - w) * g (l⁻¹ * w))
    _ = ENNReal.ofReal l⁻¹ * ∫⁻ w : ℝ, S (z - w) * g (l⁻¹ * w) := by
        rw [abs_of_pos (inv_pos.mpr hl)]

/-- Part (ii) of `VertDil`: `‖g(·/l)‖_{L^p} = l^{1/p} ‖g‖_{L^p}`. -/
theorem vd_part2 {l : ℝ} (hl : 0 < l) {p : ℝ} (hp : 0 < p) (g : ℝ → ℝ≥0∞) :
    lqNorm1 p (fun w => g (l⁻¹ * w)) = ENNReal.ofReal (l ^ (1 / p)) * lqNorm1 p g := by
  have h1 : ∫⁻ w : ℝ, g (l⁻¹ * w) ^ p = ENNReal.ofReal l * ∫⁻ w : ℝ, g w ^ p := by
    have h := vd_scale (l := l⁻¹) (inv_ne_zero hl.ne') (fun s => g s ^ p)
    rw [inv_inv, abs_of_pos hl] at h
    exact h
  unfold lqNorm1
  rw [h1, ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ENNReal.ofReal_rpow_of_pos hl]

/-- **Dilation `s ↦ λ s` on `ℝ`** (3631-3645). -/
theorem vertDil : VertDil := by
  intro l hl
  exact ⟨fun S g z => vd_part1 hl S g z, fun p hp g => vd_part2 hl hp g⟩

end UnforcedLeray.Short.PartIIIb.Concrete
