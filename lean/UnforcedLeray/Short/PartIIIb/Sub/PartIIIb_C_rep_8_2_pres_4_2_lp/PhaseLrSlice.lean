import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Estimates
import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.ENNReal.Real

/-!
# The phase average of slice norms (task `PartIII-b:C/rep/8/2/pres/4/2/lp/4/3`)

Source `the November 2 reference manuscript` 5134-5139. The phase-normalized
`L^r` norm of `F` is at most the sup of its slice `L^r_y` norms.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The phase average of the slice norms is at most their sup (source 5134-5139). -/
theorem phaseLr_le_of_slice {P r : ℝ} (hP : 0 < P) (hr : 0 < r) (M : ℝ≥0∞) {F : ℝ → Space → ℝ} (h : ∀ τ, eLpNorm (fun y => F τ y) (ENNReal.ofReal r) volume ≤ M) : phaseLr P r (fun x => F x.1 x.2) ≤ M := by
  have hp0 : ENNReal.ofReal r ≠ 0 := (ENNReal.ofReal_pos.mpr hr).ne'
  have hpt : ENNReal.ofReal r ≠ ⊤ := ENNReal.ofReal_ne_top
  have htoReal : (ENNReal.ofReal r).toReal = r := ENNReal.toReal_ofReal hr.le
  have key : ∀ τ : ℝ, ∫⁻ y : Space, ENNReal.ofReal |F τ y| ^ r ≤ M ^ r := by
    intro τ
    have h1 := h τ
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt, htoReal] at h1
    have h2 : ∫⁻ y : Space, ‖F τ y‖ₑ ^ r = ∫⁻ y : Space, ENNReal.ofReal |F τ y| ^ r :=
      lintegral_congr (fun y => by rw [Real.enorm_eq_ofReal_abs])
    rw [h2] at h1
    calc ∫⁻ y : Space, ENNReal.ofReal |F τ y| ^ r
        = ((∫⁻ y : Space, ENNReal.ofReal |F τ y| ^ r) ^ (1 / r)) ^ r := by
          rw [← ENNReal.rpow_mul, one_div_mul_cancel hr.ne', ENNReal.rpow_one]
      _ ≤ M ^ r := ENNReal.rpow_le_rpow h1 hr.le
  have hPinv : ENNReal.ofReal P⁻¹ * ENNReal.ofReal P = 1 := by
    rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hP.le), inv_mul_cancel₀ hP.ne', ENNReal.ofReal_one]
  have hint : ∫⁻ t in Ioc (0 : ℝ) P, ∫⁻ y : Space, ENNReal.ofReal |F t y| ^ r ≤
      ∫⁻ _t in Ioc (0 : ℝ) P, M ^ r :=
    lintegral_mono key
  rw [setLIntegral_const, Real.volume_Ioc, sub_zero] at hint
  unfold phaseLr
  calc (ENNReal.ofReal P⁻¹ * ∫⁻ t in Ioc (0 : ℝ) P, ∫⁻ y : Space, ENNReal.ofReal |F t y| ^ r) ^ (1 / r)
      ≤ (ENNReal.ofReal P⁻¹ * (M ^ r * ENNReal.ofReal P)) ^ (1 / r) :=
        ENNReal.rpow_le_rpow (mul_le_mul_of_nonneg_left hint (by positivity)) (one_div_nonneg.mpr hr.le)
    _ = (M ^ r) ^ (1 / r) := by rw [mul_left_comm, hPinv, mul_one]
    _ = M := by rw [← ENNReal.rpow_mul, mul_one_div_cancel hr.ne', ENNReal.rpow_one]

end UnforcedLeray.Short.PartIIIb.Concrete
