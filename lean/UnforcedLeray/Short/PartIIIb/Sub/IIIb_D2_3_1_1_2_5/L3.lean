import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_2_5
import Mathlib.Data.Real.ConjExponents
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

/-!
# Hölder bound for the `z`-weight (`PartIII-b:IIIb-D2/3/1/1/2/5/3`)

For `l ∈ (0,1)`, Cauchy-Schwarz in `z` (exponents `2`, `2`) against the weight
`(1+l|z|)^{-(4+n)}`, whose square has `∫_z ≤ C' l^{-3}` by the scaling `z = w/l`
(`2(4+n) > 3 = dim`). This gives `‖(1+l|·|)^{-(4+n)}‖_{L²} ≲ l^{-3/2}` (3631-3646, `sep:young`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Lebesgue scaling of a lower integral on the 3-dimensional space `Space`
(same argument as `l2_lintegral_scale`, restated locally). -/
theorem l5Holder_lintegral_scale (G : Space → ℝ≥0∞) (hG : Measurable G) (R : ℝ) (hR : R ≠ 0) :
    ∫⁻ z, G (R • z) = ENNReal.ofReal (|(R ^ 3)⁻¹|) * ∫⁻ w, G w := by
  have hmap := Measure.map_addHaar_smul (μ := (volume : Measure Space)) hR
  rw [finrank_euclideanSpace_fin] at hmap
  have h1 : ∫⁻ z, G (R • z) = ∫⁻ y, G y ∂(Measure.map (fun x : Space => R • x) volume) :=
    (lintegral_map hG (measurable_const_smul R)).symm
  rw [h1, hmap, lintegral_smul_measure, smul_eq_mul]

theorem l5Holder : L5Holder := by
  intro n
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hd : (Module.finrank ℝ Space : ℝ) = 3 := by
    rw [finrank_euclideanSpace_fin]; norm_num
  have hq' : (Module.finrank ℝ Space : ℝ) < (4 + (n : ℝ)) * 2 := by
    rw [hd]; linarith
  have hint := integrable_one_add_norm (μ := (volume : Measure Space)) hq'
  have hI0 : 0 ≤ ∫ w : Space, (1 + ‖w‖) ^ (-((4 + (n : ℝ)) * 2)) :=
    integral_nonneg fun w => Real.rpow_nonneg (by positivity) _
  refine ⟨(∫ w : Space, (1 + ‖w‖) ^ (-((4 + (n : ℝ)) * 2))) ^ (1 / 2 : ℝ),
    Real.rpow_nonneg hI0 _, fun l hl F hF => ?_⟩
  have hl0 : 0 < l := hl.1
  have hpt : ∀ z : Space, 0 ≤ 1 + l * ‖z‖ := fun z =>
    add_nonneg zero_le_one (mul_nonneg hl0.le (norm_nonneg z))
  have hgm : Measurable (fun z : Space => ENNReal.ofReal ((1 + l * ‖z‖) ^ (-(4 + (n : ℝ))))) :=
    ((measurable_const.add (measurable_const.mul measurable_norm)).pow_const _).ennreal_ofReal
  -- squared weight integral: scaling and the integrability of (1+|w|)^{-2(4+n)}
  have hsq : ∫⁻ z : Space, ENNReal.ofReal ((1 + l * ‖z‖) ^ (-(4 + (n : ℝ)))) ^ (2 : ℝ) =
      ENNReal.ofReal ((∫ w : Space, (1 + ‖w‖) ^ (-((4 + (n : ℝ)) * 2))) * l ^ (-3 : ℝ)) := by
    have hG : Measurable fun w : Space =>
        ENNReal.ofReal ((1 + ‖w‖) ^ (-((4 + (n : ℝ)) * 2))) :=
      ((measurable_const.add measurable_norm).pow_const _).ennreal_ofReal
    have hlin : ∫⁻ w : Space, ENNReal.ofReal ((1 + ‖w‖) ^ (-((4 + (n : ℝ)) * 2))) =
        ENNReal.ofReal (∫ w : Space, (1 + ‖w‖) ^ (-((4 + (n : ℝ)) * 2))) :=
      (ofReal_integral_eq_lintegral_ofReal hint
        (Filter.Eventually.of_forall fun w => Real.rpow_nonneg (by positivity) _)).symm
    calc ∫⁻ z : Space, ENNReal.ofReal ((1 + l * ‖z‖) ^ (-(4 + (n : ℝ)))) ^ (2 : ℝ)
        = ∫⁻ z : Space, ENNReal.ofReal ((1 + ‖l • z‖) ^ (-((4 + (n : ℝ)) * 2))) := by
          refine lintegral_congr fun z => ?_
          rw [ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg (hpt z) _) (by norm_num),
            ← Real.rpow_mul (hpt z), norm_smul, Real.norm_of_nonneg hl0.le, neg_mul]
      _ = ∫⁻ z : Space, (fun w : Space =>
            ENNReal.ofReal ((1 + ‖w‖) ^ (-((4 + (n : ℝ)) * 2)))) (l • z) := rfl
      _ = ENNReal.ofReal (|(l ^ 3)⁻¹|) * ∫⁻ w : Space,
            ENNReal.ofReal ((1 + ‖w‖) ^ (-((4 + (n : ℝ)) * 2))) :=
          l5Holder_lintegral_scale _ hG l hl0.ne'
      _ = ENNReal.ofReal ((∫ w : Space, (1 + ‖w‖) ^ (-((4 + (n : ℝ)) * 2))) * l ^ (-3 : ℝ)) := by
          rw [hlin, ← ENNReal.ofReal_mul (abs_nonneg _)]
          congr 1
          rw [abs_of_pos (inv_pos.2 (pow_pos hl0 3)), show (-3 : ℝ) = -((3 : ℕ) : ℝ) by norm_num,
            Real.rpow_neg hl0.le, Real.rpow_natCast]
          ring
  -- the square root of the weight norm
  have hpow : ((∫ w : Space, (1 + ‖w‖) ^ (-((4 + (n : ℝ)) * 2))) * l ^ (-3 : ℝ)) ^ (1 / 2 : ℝ) =
      (∫ w : Space, (1 + ‖w‖) ^ (-((4 + (n : ℝ)) * 2))) ^ (1 / 2 : ℝ) * l ^ (-(3 / 2 : ℝ)) := by
    rw [Real.mul_rpow hI0 (Real.rpow_nonneg hl0.le _), ← Real.rpow_mul hl0.le,
      show (-3 : ℝ) * (1 / 2) = -(3 / 2) by norm_num]
  have hA : (∫⁻ z : Space, ENNReal.ofReal ((1 + l * ‖z‖) ^ (-(4 + (n : ℝ)))) ^ (2 : ℝ)) ^ (1 / 2 : ℝ)
      ≤ ENNReal.ofReal ((∫ w : Space, (1 + ‖w‖) ^ (-((4 + (n : ℝ)) * 2))) ^ (1 / 2 : ℝ) *
          l ^ (-(3 / 2 : ℝ))) := by
    refine le_of_eq ?_
    rw [hsq, ENNReal.ofReal_rpow_of_nonneg
      (mul_nonneg hI0 (Real.rpow_nonneg hl0.le _)) (by norm_num), hpow]
  -- Cauchy-Schwarz in z with exponents 2, 2
  have hCS := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume : Measure Space)
    Real.HolderConjugate.two_two hgm.aemeasurable hF.aemeasurable
  calc ∫⁻ z : Space, ENNReal.ofReal ((1 + l * ‖z‖) ^ (-(4 + (n : ℝ)))) * F z
      ≤ (∫⁻ z : Space, ENNReal.ofReal ((1 + l * ‖z‖) ^ (-(4 + (n : ℝ)))) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) *
          (∫⁻ z : Space, F z ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := hCS
    _ ≤ ENNReal.ofReal ((∫ w : Space, (1 + ‖w‖) ^ (-((4 + (n : ℝ)) * 2))) ^ (1 / 2 : ℝ) *
          l ^ (-(3 / 2 : ℝ))) * (∫⁻ z : Space, F z ^ (2 : ℝ)) ^ (1 / 2 : ℝ) :=
        mul_le_mul' hA le_rfl

end UnforcedLeray.Short.PartIIIb.Concrete
