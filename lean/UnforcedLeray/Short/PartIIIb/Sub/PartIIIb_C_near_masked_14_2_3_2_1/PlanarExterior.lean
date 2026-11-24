import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Planar exterior integral of `ρ⁻³` (`PartIII-b:C/near/masked/14/2/3/2/1/5`; source 3996-4011)

Polar coordinates on `ℝ × ℝ`: the integrand `ρ · ρ^{-3} 1{r < ρ}` is `ρ^{-2}` on `{r < ρ}`;
the radial integral `∫_r^∞ ρ^{-2} dρ = 1/r` and the angular range has length `2π`.
Companion of `lintegral_planar_disc`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Real
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb

theorem lintegral_planar_exterior (r : ℝ) (hr : 0 < r) : ∫⁻ p : ℝ × ℝ, (if r < Real.sqrt (p.1 ^ 2 + p.2 ^ 2) then ENNReal.ofReal (Real.sqrt (p.1 ^ 2 + p.2 ^ 2) ^ (-3 : ℝ)) else 0) = ENNReal.ofReal (2 * Real.pi / r) := by
  set f : ℝ × ℝ → ENNReal := fun p => if r < Real.sqrt (p.1 ^ 2 + p.2 ^ 2) then ENNReal.ofReal (Real.sqrt (p.1 ^ 2 + p.2 ^ 2) ^ (-3 : ℝ)) else 0 with hf
  have hT : MeasurableSet polarCoord.target := polarCoord.open_target.measurableSet
  have hTset : polarCoord.target = Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi := rfl
  have hpt : ∀ q ∈ polarCoord.target,
      ENNReal.ofReal q.1 • f (polarCoord.symm q)
        = ({q : ℝ × ℝ | r < q.1}).indicator (fun q => ENNReal.ofReal (q.1 ^ (-2 : ℝ))) q := by
    rintro ⟨ρ, θ⟩ hq
    have hρ : 0 < ρ := hq.1
    have hn : Real.sqrt ((ρ * Real.cos θ) ^ 2 + (ρ * Real.sin θ) ^ 2) = ρ := by
      rw [show (ρ * Real.cos θ) ^ 2 + (ρ * Real.sin θ) ^ 2 = ρ ^ 2 * (Real.sin θ ^ 2 + Real.cos θ ^ 2) by ring,
        Real.sin_sq_add_cos_sq, mul_one, Real.sqrt_sq hρ.le]
    have hsymm : polarCoord.symm (ρ, θ) = (ρ * Real.cos θ, ρ * Real.sin θ) := rfl
    have hpow : ρ * ρ ^ (-3 : ℝ) = ρ ^ (-2 : ℝ) := by
      rw [show (-2 : ℝ) = -3 + 1 by norm_num, Real.rpow_add hρ, Real.rpow_one, mul_comm]
    rw [hf]
    simp only [hsymm, hn]
    by_cases h : r < ρ
    · rw [if_pos h, Set.indicator_of_mem (show ((ρ, θ) : ℝ × ℝ) ∈ {q : ℝ × ℝ | r < q.1} from h),
        smul_eq_mul, ← ENNReal.ofReal_mul hρ.le, hpow]
    · rw [if_neg h, Set.indicator_of_notMem (show ((ρ, θ) : ℝ × ℝ) ∉ {q : ℝ × ℝ | r < q.1} from h),
        smul_zero]
  rw [← lintegral_comp_polarCoord_symm f]
  rw [setLIntegral_congr_fun hT hpt]
  rw [setLIntegral_indicator (measurableSet_lt measurable_const measurable_fst)]
  have hset : ({q : ℝ × ℝ | r < q.1} ∩ polarCoord.target) = Ioi r ×ˢ Ioo (-Real.pi) Real.pi := by
    rw [hTset]
    ext ⟨a, b⟩
    simp only [mem_inter_iff, mem_setOf_eq, mem_prod, mem_Ioi, mem_Ioo]
    constructor
    · rintro ⟨h1, _, h3, h4⟩
      exact ⟨h1, h3, h4⟩
    · rintro ⟨h1, h3, h4⟩
      exact ⟨h1, by linarith, h3, h4⟩
  have hI : ∫ x in Ioi r, x ^ (-2 : ℝ) = r⁻¹ := by
    rw [integral_Ioi_rpow_of_lt (by norm_num) hr, show (-2 : ℝ) + 1 = -1 by norm_num, Real.rpow_neg_one]
    ring
  have hint : IntegrableOn (fun x : ℝ => x ^ (-2 : ℝ)) (Ioi r) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) hr
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi r)] (fun x : ℝ => x ^ (-2 : ℝ)) :=
    (ae_restrict_mem measurableSet_Ioi).mono (fun x hx => Real.rpow_nonneg (lt_trans hr hx).le _)
  have hlin : ∫⁻ x in Ioi r, ENNReal.ofReal (x ^ (-2 : ℝ)) = ENNReal.ofReal r⁻¹ := by
    rw [← ofReal_integral_eq_lintegral_ofReal hint hnn, hI]
  rw [hset, Measure.volume_eq_prod, ← Measure.prod_restrict]
  have hsplit : (fun q : ℝ × ℝ => ENNReal.ofReal (q.1 ^ (-2 : ℝ)))
      = fun q : ℝ × ℝ => (fun x : ℝ => ENNReal.ofReal (x ^ (-2 : ℝ))) q.1 * (fun _ : ℝ => (1 : ENNReal)) q.2 := by
    funext q
    simp
  have hm1 : Measurable (fun x : ℝ => ENNReal.ofReal (x ^ (-2 : ℝ))) := by fun_prop
  have hm2 : Measurable (fun _ : ℝ => (1 : ENNReal)) := measurable_const
  rw [hsplit]
  refine (lintegral_prod_mul hm1.aemeasurable hm2.aemeasurable).trans ?_
  simp only [hlin, setLIntegral_const, Real.volume_Ioo, one_mul]
  rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hr.le)]
  congr 1
  ring
