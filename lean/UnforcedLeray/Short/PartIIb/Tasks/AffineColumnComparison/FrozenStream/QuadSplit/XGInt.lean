import UnforcedLeray.Short.PartIIb.Sub.G4_2_2_1

/-!
# Part II-b, task `PartII-b:G4/2/2/3/3`: `XGInt`

Source of record: `the November 2 reference manuscript`, lines 2349-2352.

Route: for `q ∈ X_G`, `s³ ‖q‖` and `s⁻¹ ‖q‖` are dominated by AM-GM with the weighted
integrand `‖q‖² e^{s²/4} s` (a multiple of `‖q‖² G⁻¹ s`) plus `s⁵ e^{-s²/4}` on `(0,∞)`,
resp. `r⁻³ e^{-s²/4}` on `(r,∞)`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Blueprint

/-- AM-GM with weights: `2 s³ x ≤ x² u s + s⁵ v` when `u v = 1`, `u > 0`, `s ≥ 0`. -/
private lemma xgint_core_a (x s u v : ℝ) (hs : 0 ≤ s) (hu : 0 < u) (huv : u * v = 1) :
    2 * (s ^ 3 * x) ≤ x ^ 2 * u * s + s ^ 5 * v := by
  have key : u * (x ^ 2 * u * s + s ^ 5 * v - 2 * (s ^ 3 * x)) = s * (x * u - s ^ 2) ^ 2 := by
    linear_combination (s ^ 5) * huv
  have h2 : 0 ≤ u * (x ^ 2 * u * s + s ^ 5 * v - 2 * (s ^ 3 * x)) := by
    rw [key]; exact mul_nonneg hs (sq_nonneg _)
  have h3 := (mul_nonneg_iff_of_pos_left hu).mp h2
  linarith

/-- AM-GM with weights: `2 w x ≤ x² u s + w³ v` when `s w = 1`, `w > 0`, `u v = 1`, `u > 0`. -/
private lemma xgint_core_b (x s w u v : ℝ) (hw : 0 < w) (hsw : s * w = 1) (hu : 0 < u)
    (huv : u * v = 1) : 2 * (w * x) ≤ x ^ 2 * u * s + w ^ 3 * v := by
  have key : w * u * (x ^ 2 * u * s + w ^ 3 * v - 2 * (w * x)) = (x * u - w ^ 2) ^ 2 := by
    linear_combination (x ^ 2 * u ^ 2) * hsw + w ^ 4 * huv
  have h2 : 0 ≤ w * u * (x ^ 2 * u * s + w ^ 3 * v - 2 * (w * x)) := by
    rw [key]; exact sq_nonneg _
  have h3 := (mul_nonneg_iff_of_pos_left (mul_pos hw hu)).mp h2
  linarith

private lemma xgint_exp_pair (s : ℝ) :
    Real.exp (s ^ 2 / 4) * Real.exp (-(1 / 4) * s ^ 2) = 1 := by
  rw [← Real.exp_add, show s ^ 2 / 4 + -(1 / 4) * s ^ 2 = (0 : ℝ) by ring, Real.exp_zero]

private lemma xgint_gauss_pow5 :
    IntegrableOn (fun s : ℝ => s ^ 5 * Real.exp (-(1 / 4) * s ^ 2)) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_sq (b := 1 / 4) (by norm_num) (s := 5) (by norm_num)
  refine IntegrableOn.congr_fun h (fun s _ => ?_) measurableSet_Ioi
  show s ^ (5 : ℝ) * Real.exp (-(1 / 4) * s ^ 2) = s ^ 5 * Real.exp (-(1 / 4) * s ^ 2)
  rw [show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

theorem xGInt : UnforcedLeray.Short.IIb.XGInt := by
  intro q hq
  -- weighted integrability: `‖q‖² e^{s²/4} s = (4π)⁻¹ ‖q‖² G⁻¹(s) s`
  have hW : IntegrableOn (fun s : ℝ => ‖q s‖ ^ 2 * Real.exp (s ^ 2 / 4) * s) (Ioi 0) := by
    have h : IntegrableOn (fun s : ℝ => 1 / (4 * Real.pi) * (‖q s‖ ^ 2 * Planar.gaussianWeightInv s * s))
        (Ioi 0) := hq.integrable.const_mul (1 / (4 * Real.pi))
    refine IntegrableOn.congr_fun h (fun s _ => ?_) measurableSet_Ioi
    have hπ : (1 / (4 * Real.pi)) * (4 * Real.pi) = 1 := by
      rw [one_div, inv_mul_cancel₀ (by positivity)]
    show 1 / (4 * Real.pi) * (‖q s‖ ^ 2 * Planar.gaussianWeightInv s * s)
        = ‖q s‖ ^ 2 * Real.exp (s ^ 2 / 4) * s
    unfold Planar.gaussianWeightInv
    linear_combination (‖q s‖ ^ 2 * Real.exp (s ^ 2 / 4) * s) * hπ
  have hA := xgint_gauss_pow5
  refine ⟨?_, fun r hr => ?_⟩
  · -- `s³ q` on `(0,∞)`
    have hint : IntegrableOn (fun s : ℝ => (1 / 2 : ℝ) * (‖q s‖ ^ 2 * Real.exp (s ^ 2 / 4) * s)
        + (1 / 2 : ℝ) * (s ^ 5 * Real.exp (-(1 / 4) * s ^ 2))) (Ioi 0) :=
      (hW.const_mul (1 / 2)).add (hA.const_mul (1 / 2))
    refine Integrable.mono' hint ?_ ?_
    · exact ((Complex.continuous_ofReal.pow 3).aestronglyMeasurable).mul hq.measurable
    · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun s hs => ?_)
      have hs0 : (0 : ℝ) < s := hs
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hs0.le]
      have hc := xgint_core_a ‖q s‖ s (Real.exp (s ^ 2 / 4)) (Real.exp (-(1 / 4) * s ^ 2))
        hs0.le (Real.exp_pos _) (xgint_exp_pair s)
      show s ^ 3 * ‖q s‖ ≤ (1 / 2 : ℝ) * (‖q s‖ ^ 2 * Real.exp (s ^ 2 / 4) * s)
        + (1 / 2 : ℝ) * (s ^ 5 * Real.exp (-(1 / 4) * s ^ 2))
      linarith
  · -- `s⁻¹ q` on `(r,∞)`
    have hr0 : (0 : ℝ) < r := hr
    have hWr : IntegrableOn (fun s : ℝ => ‖q s‖ ^ 2 * Real.exp (s ^ 2 / 4) * s) (Ioi r) :=
      hW.mono_set (Ioi_subset_Ioi hr0.le)
    have hGr : IntegrableOn (fun s : ℝ => Real.exp (-(1 / 4) * s ^ 2)) (Ioi r) :=
      (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 4)).integrableOn
    have hint : IntegrableOn (fun s : ℝ => (1 / 2 : ℝ) * (‖q s‖ ^ 2 * Real.exp (s ^ 2 / 4) * s)
        + (1 / 2 : ℝ) * ((r⁻¹) ^ 3 * Real.exp (-(1 / 4) * s ^ 2))) (Ioi r) :=
      (hWr.const_mul (1 / 2)).add ((hGr.const_mul ((r⁻¹) ^ 3)).const_mul (1 / 2))
    refine Integrable.mono' hint ?_ ?_
    · have hmeas : AEStronglyMeasurable q (volume.restrict (Ioi r)) :=
        hq.measurable.mono_measure (Measure.restrict_mono (Ioi_subset_Ioi hr0.le) le_rfl)
      have hinv : ContinuousOn (fun s : ℝ => (s : ℂ)⁻¹) (Ioi r) :=
        Complex.continuous_ofReal.continuousOn.inv₀ (fun s hs =>
          Complex.ofReal_ne_zero.mpr (lt_trans hr0 (Set.mem_Ioi.mp hs)).ne')
      exact (hinv.aestronglyMeasurable measurableSet_Ioi).mul hmeas
    · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun s hs => ?_)
      have hrs : r < s := hs
      have hs0 : (0 : ℝ) < s := lt_trans hr0 hrs
      have hsw : s * s⁻¹ = 1 := mul_inv_cancel₀ hs0.ne'
      have hwpos : 0 < s⁻¹ := inv_pos.mpr hs0
      have hwr : s⁻¹ ≤ r⁻¹ := inv_anti₀ hr0 hrs.le
      have hc := xgint_core_b ‖q s‖ s s⁻¹ (Real.exp (s ^ 2 / 4)) (Real.exp (-(1 / 4) * s ^ 2))
        hwpos hsw (Real.exp_pos _) (xgint_exp_pair s)
      have hp : s⁻¹ ^ 3 ≤ r⁻¹ ^ 3 := pow_le_pow_left₀ hwpos.le hwr 3
      have hm : s⁻¹ ^ 3 * Real.exp (-(1 / 4) * s ^ 2)
          ≤ r⁻¹ ^ 3 * Real.exp (-(1 / 4) * s ^ 2) :=
        mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le
      show ‖(s : ℂ)⁻¹ * q s‖ ≤ (1 / 2 : ℝ) * (‖q s‖ ^ 2 * Real.exp (s ^ 2 / 4) * s)
        + (1 / 2 : ℝ) * ((r⁻¹) ^ 3 * Real.exp (-(1 / 4) * s ^ 2))
      rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hs0.le]
      linarith

end UnforcedLeray.Short.IIb

end
