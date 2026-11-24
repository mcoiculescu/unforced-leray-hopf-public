import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_4_5.Defs
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# `PartIII-b:C/rep/2/4/5` : `VertKernLb` (task `PartIII-b:C/rep/2/4/5/1`)

Source `the November 2 reference manuscript` 3624-3631 (the vertical kernel in
`L^{11/3}(ℝ)`), one-dimensional form of `VertKernLb`.  The kernel is
`vertKern rIn D t = ofReal (rIn / (2 D (D²+t²)))`; its `11/3`-power is
`(rIn/(2D))^{11/3} (D²+t²)^{-11/3}`, the substitution `t = D u` gives
`∫ (D²+t²)^{-11/3} dt = D^{-19/3} ∫ (1+u²)^{-11/3} du`, and the integral is finite.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Change of variables `t = D u` in a lintegral on `ℝ` (`D > 0`). -/
theorem vkl_lintegral_scale {D : ℝ} (hD : 0 < D) (H : ℝ → ℝ≥0∞) (hH : Measurable H) :
    ∫⁻ t : ℝ, H t = ENNReal.ofReal D * ∫⁻ u : ℝ, H (D * u) := by
  calc ∫⁻ t : ℝ, H t
      = ∫⁻ t : ℝ, H t ∂(ENNReal.ofReal |D| • Measure.map (D * ·) (volume : Measure ℝ)) := by
        rw [Real.smul_map_volume_mul_left hD.ne']
    _ = ENNReal.ofReal |D| * ∫⁻ t : ℝ, H t ∂(Measure.map (D * ·) (volume : Measure ℝ)) :=
        lintegral_smul_measure _ _
    _ = ENNReal.ofReal |D| * ∫⁻ u : ℝ, H (D * u) := by
        rw [lintegral_map hH (measurable_const_mul D)]
    _ = ENNReal.ofReal D * ∫⁻ u : ℝ, H (D * u) := by
        rw [abs_of_pos hD]

/-- The `11/3`-power of the vertical kernel. -/
theorem vkl_pow_eq (rIn D t : ℝ) (hr : 0 < rIn) (hD : 0 < D) :
    vertKern rIn D t ^ (11 / 3 : ℝ) =
      ENNReal.ofReal ((rIn / (2 * D)) ^ (11 / 3 : ℝ)) *
        ENNReal.ofReal ((D ^ 2 + t ^ 2) ^ (-(11 / 3 : ℝ))) := by
  have hq : 0 < D ^ 2 + t ^ 2 := by positivity
  have hA : 0 < rIn / (2 * D) := by positivity
  have hnn : 0 ≤ rIn / (2 * D * (D ^ 2 + t ^ 2)) := by positivity
  have hx : rIn / (2 * D * (D ^ 2 + t ^ 2)) = (rIn / (2 * D)) * (D ^ 2 + t ^ 2) ^ (-1 : ℝ) := by
    rw [Real.rpow_neg_one]
    field_simp
  have key : (rIn / (2 * D * (D ^ 2 + t ^ 2))) ^ (11 / 3 : ℝ) =
      (rIn / (2 * D)) ^ (11 / 3 : ℝ) * (D ^ 2 + t ^ 2) ^ (-(11 / 3 : ℝ)) := by
    rw [hx, Real.mul_rpow hA.le (by positivity), ← Real.rpow_mul hq.le]
    norm_num
  unfold vertKern
  rw [ENNReal.ofReal_rpow_of_nonneg hnn (by norm_num), key,
    ENNReal.ofReal_mul (Real.rpow_nonneg hA.le _)]

/-- The lintegral of `(D²+t²)^{-11/3}` in terms of the reference integral. -/
theorem vkl_integral_eq {D : ℝ} (hD : 0 < D) :
    ∫⁻ t : ℝ, ENNReal.ofReal ((D ^ 2 + t ^ 2) ^ (-(11 / 3 : ℝ))) =
      ENNReal.ofReal (D ^ (-(19 / 3 : ℝ))) *
        ∫⁻ u : ℝ, ENNReal.ofReal ((1 + u ^ 2) ^ (-(11 / 3 : ℝ))) := by
  have hmeas : Measurable fun t : ℝ => ENNReal.ofReal ((D ^ 2 + t ^ 2) ^ (-(11 / 3 : ℝ))) :=
    ENNReal.measurable_ofReal.comp (by fun_prop)
  rw [vkl_lintegral_scale hD _ hmeas]
  have hpt : ∀ u : ℝ, ENNReal.ofReal ((D ^ 2 + (D * u) ^ 2) ^ (-(11 / 3 : ℝ))) =
      ENNReal.ofReal (D ^ (-(22 / 3 : ℝ))) * ENNReal.ofReal ((1 + u ^ 2) ^ (-(11 / 3 : ℝ))) := by
    intro u
    have h1 : D ^ 2 + (D * u) ^ 2 = D ^ 2 * (1 + u ^ 2) := by ring
    rw [h1, Real.mul_rpow (by positivity) (by positivity),
      ENNReal.ofReal_mul (p := (D ^ 2) ^ (-(11 / 3 : ℝ))) (by positivity)]
    congr 2
    rw [← Real.rpow_natCast D 2, ← Real.rpow_mul hD.le]
    norm_num
  simp only [hpt]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← mul_assoc,
    ← ENNReal.ofReal_mul hD.le,
    show D * D ^ (-(22 / 3 : ℝ)) = D ^ (-(19 / 3 : ℝ)) by
      rw [show (-(19 / 3 : ℝ)) = 1 + -(22 / 3 : ℝ) by norm_num, Real.rpow_add hD, Real.rpow_one]]

/-- **(K) The vertical kernel in `L^{11/3}(ℝ)`** (3624-3631 in one dimension). -/
theorem vertKernLb : VertKernLb := by
  have hint : MeasureTheory.Integrable (fun u : ℝ => (1 + u ^ 2) ^ (-(11 / 3 : ℝ))) := by
    have h2 : (fun u : ℝ => (1 + u ^ 2) ^ (-(11 / 3 : ℝ))) =
        fun u : ℝ => ((1 : ℝ) + ‖u‖ ^ 2) ^ (-(22 / 3 : ℝ) / 2) := by
      funext u
      rw [Real.norm_eq_abs, sq_abs]
      norm_num
    rw [h2]
    exact integrable_rpow_neg_one_add_norm_sq (r := 22 / 3) (by
      simp only [Module.finrank_self, Nat.cast_one]
      norm_num)
  have hJ : ∫⁻ u : ℝ, ENNReal.ofReal ((1 + u ^ 2) ^ (-(11 / 3 : ℝ))) ≠ ⊤ :=
    (hint.lintegral_lt_top).ne
  refine ⟨(1 / 2) * (∫⁻ u : ℝ, ENNReal.ofReal ((1 + u ^ 2) ^ (-(11 / 3 : ℝ)))).toReal ^ (3 / 11 : ℝ),
    mul_nonneg (by norm_num) (Real.rpow_nonneg ENNReal.toReal_nonneg _), ?_⟩
  intro rIn D hr hD
  have hA : 0 < rIn / (2 * D) := by positivity
  have hIt : ∫⁻ t : ℝ, vertKern rIn D t ^ (11 / 3 : ℝ) =
      ENNReal.ofReal ((rIn / (2 * D)) ^ (11 / 3 : ℝ)) *
        (ENNReal.ofReal (D ^ (-(19 / 3 : ℝ))) *
          ∫⁻ u : ℝ, ENNReal.ofReal ((1 + u ^ 2) ^ (-(11 / 3 : ℝ)))) := by
    simp_rw [vkl_pow_eq rIn D _ hr hD]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, vkl_integral_eq hD]
  have hIr : ∫⁻ u : ℝ, ENNReal.ofReal ((1 + u ^ 2) ^ (-(11 / 3 : ℝ))) =
      ENNReal.ofReal (∫⁻ u : ℝ, ENNReal.ofReal ((1 + u ^ 2) ^ (-(11 / 3 : ℝ)))).toReal :=
    (ENNReal.ofReal_toReal hJ).symm
  have hQ : ∫⁻ t : ℝ, vertKern rIn D t ^ (11 / 3 : ℝ) =
      ENNReal.ofReal ((rIn / (2 * D)) ^ (11 / 3 : ℝ) * D ^ (-(19 / 3 : ℝ)) *
        (∫⁻ u : ℝ, ENNReal.ofReal ((1 + u ^ 2) ^ (-(11 / 3 : ℝ)))).toReal) := by
    rw [hIt]
    conv_lhs => rw [hIr]
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
    ring
  have heq : ((rIn / (2 * D)) ^ (11 / 3 : ℝ) * D ^ (-(19 / 3 : ℝ)) *
        (∫⁻ u : ℝ, ENNReal.ofReal ((1 + u ^ 2) ^ (-(11 / 3 : ℝ)))).toReal) ^ (1 / (11 / 3 : ℝ)) =
      (1 / 2) * (∫⁻ u : ℝ, ENNReal.ofReal ((1 + u ^ 2) ^ (-(11 / 3 : ℝ)))).toReal ^ (3 / 11 : ℝ) *
        (rIn / D) * D ^ (-(19 / 11 : ℝ)) := by
    rw [show (1 / (11 / 3 : ℝ)) = 3 / 11 by norm_num,
      Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by positivity) (by positivity),
      ← Real.rpow_mul hA.le, ← Real.rpow_mul hD.le,
      show (11 / 3 : ℝ) * (3 / 11) = 1 by norm_num,
      show (-(19 / 3 : ℝ)) * (3 / 11) = -(19 / 11) by norm_num, Real.rpow_one]
    ring
  unfold lqNorm1
  rw [hQ, ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), heq]
  apply ENNReal.ofReal_le_ofReal
  rw [show (-2 + 3 / 11 : ℝ) = -(19 / 11) by norm_num]

end UnforcedLeray.Short.PartIIIb.Concrete
