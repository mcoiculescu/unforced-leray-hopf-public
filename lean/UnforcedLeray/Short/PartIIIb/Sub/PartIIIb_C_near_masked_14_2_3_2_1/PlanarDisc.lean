import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Planar disc integral of `ρ⁻¹` (`PartIII-b:C/near/masked/14/2/3/2/1/4`; source 3996-4011)

Polar coordinates on `ℝ × ℝ`: the integrand `ρ · ρ⁻¹ 1{ρ < r}` is the indicator of `{ρ < r}`
on the polar target `(0,∞) × (-π,π)`, whose area is `r · 2π`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Real
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb

theorem lintegral_planar_disc (r : ℝ) (hr : 0 < r) : ∫⁻ p : ℝ × ℝ, (if Real.sqrt (p.1 ^ 2 + p.2 ^ 2) < r then ENNReal.ofReal (Real.sqrt (p.1 ^ 2 + p.2 ^ 2))⁻¹ else 0) = ENNReal.ofReal (2 * Real.pi * r) := by
  set f : ℝ × ℝ → ENNReal := fun p => if Real.sqrt (p.1 ^ 2 + p.2 ^ 2) < r then ENNReal.ofReal (Real.sqrt (p.1 ^ 2 + p.2 ^ 2))⁻¹ else 0 with hf
  have hT : MeasurableSet polarCoord.target := polarCoord.open_target.measurableSet
  have hTset : polarCoord.target = Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi := rfl
  have hpt : ∀ q ∈ polarCoord.target,
      ENNReal.ofReal q.1 • f (polarCoord.symm q)
        = ({q : ℝ × ℝ | q.1 < r}).indicator (fun _ => (1 : ENNReal)) q := by
    rintro ⟨ρ, θ⟩ hq
    have hρ : 0 < ρ := hq.1
    have hn : Real.sqrt ((ρ * Real.cos θ) ^ 2 + (ρ * Real.sin θ) ^ 2) = ρ := by
      rw [show (ρ * Real.cos θ) ^ 2 + (ρ * Real.sin θ) ^ 2 = ρ ^ 2 * (Real.sin θ ^ 2 + Real.cos θ ^ 2) by ring,
        Real.sin_sq_add_cos_sq, mul_one, Real.sqrt_sq hρ.le]
    have hsymm : polarCoord.symm (ρ, θ) = (ρ * Real.cos θ, ρ * Real.sin θ) := rfl
    rw [hf]
    simp only [hsymm, hn]
    by_cases h : ρ < r
    · rw [if_pos h, Set.indicator_of_mem (show ((ρ, θ) : ℝ × ℝ) ∈ {q : ℝ × ℝ | q.1 < r} from h),
        smul_eq_mul, ← ENNReal.ofReal_mul hρ.le, mul_inv_cancel₀ hρ.ne', ENNReal.ofReal_one]
    · rw [if_neg h, Set.indicator_of_notMem (show ((ρ, θ) : ℝ × ℝ) ∉ {q : ℝ × ℝ | q.1 < r} from h),
        smul_zero]
  rw [← lintegral_comp_polarCoord_symm f]
  rw [setLIntegral_congr_fun hT hpt]
  rw [setLIntegral_indicator (measurableSet_lt measurable_fst measurable_const)]
  have hset : ({q : ℝ × ℝ | q.1 < r} ∩ polarCoord.target) = Ioo (0 : ℝ) r ×ˢ Ioo (-Real.pi) Real.pi := by
    rw [hTset]
    ext ⟨a, b⟩
    simp only [mem_inter_iff, mem_setOf_eq, mem_prod, mem_Ioi, mem_Ioo]
    tauto
  rw [hset, setLIntegral_const, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ioo, Real.volume_Ioo,
    one_mul, ← ENNReal.ofReal_mul (show (0:ℝ) ≤ r - 0 by linarith)]
  congr 1
  ring
