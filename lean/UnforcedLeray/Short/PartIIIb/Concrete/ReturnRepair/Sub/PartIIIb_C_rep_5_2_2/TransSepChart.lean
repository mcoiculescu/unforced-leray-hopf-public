import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_2TransOrg
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_2.TransSepDom
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_2.TransMajChart

/-!
# `PartIII-b:C/rep/5/2/2/13` : `transSepChart`

Source `the November 2 reference manuscript` 2683-2689 (chart normalization,
`coefOf`), 5590-5592 (the chart bound of both stream transitions).

Composition only. With `R = ε⁻¹ ≥ 1`, `P = 2εc`:
1. `transSepDom` (pointwise): `‖sepTrans‖ₑ ≤ C₁ν⁻¹^{k₁} · transMaj` wherever `ϱ > 0`.
2. The chart coefficient: `‖coefOf R G p‖ₑ ≤ (√p.1)⁻¹ ‖G‖ₑ`, and `((√p.1)⁻¹)² = p.1⁻¹`
   for `p.1 > 0`; for `p.1 ≤ 0` the coefficient vanishes (`√p.1 = 0`).
3. `eLpNorm` on `srcMeasure c` is the `L²` integral (`eLpNorm_eq_lintegral_rpow_enorm_toReal`);
   the constant `C₁ν⁻¹^{k₁}` is pulled out and `transMajChart` bounds the integral.
   The constants combine into `C = C₁C₂`, `k = k₁ + k₂`.
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi
open scoped ENNReal
open UnforcedLeray.Blueprint.Planar (PlanarData)

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The meridional pair has norm at most the Euclidean norm of the vector. -/
theorem tsc_merid_norm_le (v : Space) : ‖(!₂[v 0, v 2] : Merid)‖ ≤ ‖v‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  simp [Fin.sum_univ_three, Fin.sum_univ_two]
  nlinarith [sq_nonneg (v 1)]

/-- The chart coefficient is at most `(√p.1)⁻¹` times the field, in `ℝ≥0∞`. -/
theorem tsc_coef_enorm (R : ℝ) (G : ℝ → Space → Space) (p : Chart) :
    ‖coefOf R G p‖ₑ ≤
      ENNReal.ofReal (Real.sqrt p.1)⁻¹ * ‖G (NearInst.chartTau R p) (NearInst.chartY R p)‖ₑ := by
  have h1 : ‖coefOf R G p‖ ≤
      (Real.sqrt p.1)⁻¹ * ‖G (NearInst.chartTau R p) (NearInst.chartY R p)‖ := by
    unfold coefOf
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _))]
    exact mul_le_mul_of_nonneg_left (tsc_merid_norm_le _) (inv_nonneg.2 (Real.sqrt_nonneg _))
  calc ‖coefOf R G p‖ₑ = ENNReal.ofReal ‖coefOf R G p‖ := (ofReal_norm_eq_enorm _).symm
    _ ≤ ENNReal.ofReal ((Real.sqrt p.1)⁻¹ * ‖G (NearInst.chartTau R p) (NearInst.chartY R p)‖) :=
        ENNReal.ofReal_le_ofReal h1
    _ = ENNReal.ofReal (Real.sqrt p.1)⁻¹ * ‖G (NearInst.chartTau R p) (NearInst.chartY R p)‖ₑ := by
        rw [ENNReal.ofReal_mul (inv_nonneg.2 (Real.sqrt_nonneg _)), ofReal_norm_eq_enorm]

/-- The pointwise `L²` bound of the chart coefficient by a majorant, valid at every chart point
(the case `p.1 ≤ 0` is trivial since the coefficient vanishes there). -/
theorem tsc_pt (R : ℝ) (G : ℝ → Space → Space) (K : ℝ≥0∞) (M : Chart → ℝ≥0∞) (p : Chart)
    (h : 0 < p.1 → ‖G (NearInst.chartTau R p) (NearInst.chartY R p)‖ₑ ≤ K * M p) :
    ‖coefOf R G p‖ₑ ^ (2 : ℝ) ≤ K ^ (2 : ℝ) * (ENNReal.ofReal p.1⁻¹ * M p ^ (2 : ℝ)) := by
  rcases le_or_gt p.1 0 with hp | hp
  · have hs : Real.sqrt p.1 = 0 := Real.sqrt_eq_zero'.2 hp
    have h0 : ‖coefOf R G p‖ₑ = 0 := by
      have := tsc_coef_enorm R G p
      rw [hs, inv_zero, ENNReal.ofReal_zero, zero_mul, nonpos_iff_eq_zero] at this
      exact this
    rw [h0, ENNReal.zero_rpow_of_pos (by norm_num)]
    exact zero_le
  · have hA : ENNReal.ofReal (Real.sqrt p.1)⁻¹ ^ (2 : ℝ) = ENNReal.ofReal p.1⁻¹ := by
      rw [ENNReal.ofReal_rpow_of_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _)) (by norm_num),
        Real.rpow_two, inv_pow, Real.sq_sqrt hp.le]
    have h1 : ‖coefOf R G p‖ₑ ≤ ENNReal.ofReal (Real.sqrt p.1)⁻¹ * (K * M p) :=
      (tsc_coef_enorm R G p).trans (mul_le_mul' le_rfl (h hp))
    calc ‖coefOf R G p‖ₑ ^ (2 : ℝ)
        ≤ (ENNReal.ofReal (Real.sqrt p.1)⁻¹ * (K * M p)) ^ (2 : ℝ) :=
          ENNReal.rpow_le_rpow h1 (by norm_num)
      _ = ENNReal.ofReal (Real.sqrt p.1)⁻¹ ^ (2 : ℝ) * (K ^ (2 : ℝ) * M p ^ (2 : ℝ)) := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
            ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
      _ = K ^ (2 : ℝ) * (ENNReal.ofReal p.1⁻¹ * M p ^ (2 : ℝ)) := by rw [hA]; ring

/-- The radial coordinate of the chart reading: `ϱ(chartY R p) = R / √p.1`. -/
theorem tsc_varrho (R : ℝ) (hR : 0 < R) {p : Chart} (hs : 0 < p.1) :
    ϱ (NearInst.chartY R p) = R / Real.sqrt p.1 := by
  have : 0 < Real.sqrt p.1 := Real.sqrt_pos.2 hs
  unfold ϱ NearInst.chartY
  simp only [PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  rw [show (R / Real.sqrt p.1) ^ 2 + 0 ^ 2 = (R / Real.sqrt p.1) ^ 2 by ring]
  exact Real.sqrt_sq (div_pos hR this).le

/-- **`TransSepChart`** (source 2683-2689, 5590-5592): both stream transitions in the ungained
normalized norm, composed from `transSepDom` and `transMajChart`. -/
theorem transSepChart : TransSepChart := by
  classical
  have hD : TransSepDom := transSepDom
  have hM : TransMajChart := transMajChart
  unfold TransSepChart
  intro σ₁ σ₂ hσ χy hχ
  obtain ⟨C1, k1, hC10, hDom⟩ := hD σ₁ σ₂ hσ χy hχ
  obtain ⟨C2, k2, hC20, hMaj⟩ := hM
  refine ⟨C1 * C2, k1 + k2, mul_nonneg hC10 hC20, ?_⟩
  intro ν μ ε c hν hν1 hε hε1 hc hμ T hT hSM hA
  have hR : (0 : ℝ) < ε⁻¹ := inv_pos.2 hε
  have hR1 : (1 : ℝ) ≤ ε⁻¹ := (one_le_inv₀ hε).2 hε1
  have hP : 0 < 2 * ε * c := mul_pos (mul_pos two_pos hε) hc
  have key : ∀ p : Chart, ‖coefOf ε⁻¹ (sepTrans ν μ ε⁻¹ χy T) p‖ₑ ^ (2 : ℝ) ≤
      ENNReal.ofReal (C1 * ν⁻¹ ^ k1) ^ (2 : ℝ) * (ENNReal.ofReal p.1⁻¹ *
        transMaj ν ε⁻¹ (IIIa.srcNorm T) (NearInst.chartTau ε⁻¹ p) (NearInst.chartY ε⁻¹ p) ^
          (2 : ℝ)) := by
    intro p
    refine tsc_pt ε⁻¹ (sepTrans ν μ ε⁻¹ χy T) (ENNReal.ofReal (C1 * ν⁻¹ ^ k1))
      (fun p => transMaj ν ε⁻¹ (IIIa.srcNorm T) (NearInst.chartTau ε⁻¹ p)
        (NearInst.chartY ε⁻¹ p)) p ?_
    intro hp
    have hy : 0 < ϱ (NearInst.chartY ε⁻¹ p) := by
      rw [tsc_varrho ε⁻¹ hR hp]
      exact div_pos hR (Real.sqrt_pos.2 hp)
    exact hDom ν μ ε⁻¹ (2 * ε * c) hν hν1 hR1 hP hμ T hT hSM hA _ _ hy
  have hL : eLpNorm (coefOf ε⁻¹ (sepTrans ν μ ε⁻¹ χy T)) 2 (srcMeasure c) ≤
      ENNReal.ofReal (C1 * ν⁻¹ ^ k1) * (∫⁻ p, ENNReal.ofReal p.1⁻¹ *
        transMaj ν ε⁻¹ (IIIa.srcNorm T) (NearInst.chartTau ε⁻¹ p) (NearInst.chartY ε⁻¹ p) ^
          (2 : ℝ) ∂srcMeasure c) ^ (1 / 2 : ℝ) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (p := 2) (by norm_num) (by norm_num)]
    have e2 : (2 : ℝ≥0∞).toReal = 2 := by norm_num
    rw [e2]
    calc (∫⁻ p, ‖coefOf ε⁻¹ (sepTrans ν μ ε⁻¹ χy T) p‖ₑ ^ (2 : ℝ) ∂srcMeasure c) ^ (1 / (2 : ℝ))
        ≤ (∫⁻ p, ENNReal.ofReal (C1 * ν⁻¹ ^ k1) ^ (2 : ℝ) * (ENNReal.ofReal p.1⁻¹ *
            transMaj ν ε⁻¹ (IIIa.srcNorm T) (NearInst.chartTau ε⁻¹ p) (NearInst.chartY ε⁻¹ p) ^
              (2 : ℝ)) ∂srcMeasure c) ^ (1 / (2 : ℝ)) :=
          ENNReal.rpow_le_rpow (lintegral_mono (fun p => key p)) (by norm_num)
      _ = ENNReal.ofReal (C1 * ν⁻¹ ^ k1) * (∫⁻ p, ENNReal.ofReal p.1⁻¹ *
            transMaj ν ε⁻¹ (IIIa.srcNorm T) (NearInst.chartTau ε⁻¹ p) (NearInst.chartY ε⁻¹ p) ^
              (2 : ℝ) ∂srcMeasure c) ^ (1 / (2 : ℝ)) := by
          rw [lintegral_const_mul' _ _
              (ENNReal.rpow_ne_top_of_nonneg (by norm_num : (0 : ℝ) ≤ 2) ENNReal.ofReal_ne_top),
            ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul]
          norm_num
  refine hL.trans ?_
  have hM2 := hMaj ν ε c hν hν1 hε hε1 hc T hT hA
  have ha0 : 0 ≤ C1 * ν⁻¹ ^ k1 := mul_nonneg hC10 (pow_nonneg (inv_nonneg.2 hν.le) _)
  calc ENNReal.ofReal (C1 * ν⁻¹ ^ k1) * (∫⁻ p, ENNReal.ofReal p.1⁻¹ *
        transMaj ν ε⁻¹ (IIIa.srcNorm T) (NearInst.chartTau ε⁻¹ p) (NearInst.chartY ε⁻¹ p) ^
          (2 : ℝ) ∂srcMeasure c) ^ (1 / 2 : ℝ)
      ≤ ENNReal.ofReal (C1 * ν⁻¹ ^ k1) * (ENNReal.ofReal (C2 * ν⁻¹ ^ k2 * ε ^ (34 / 11 : ℝ)) *
          IIIa.ltauLq (2 * ε * c) (22 / 19) (IIIa.srcNorm T)) :=
        mul_le_mul' le_rfl hM2
    _ = ENNReal.ofReal (C1 * C2 * ν⁻¹ ^ (k1 + k2) * ε ^ (34 / 11 : ℝ)) *
          IIIa.ltauLq (2 * ε * c) (22 / 19) (IIIa.srcNorm T) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul ha0,
          show C1 * ν⁻¹ ^ k1 * (C2 * ν⁻¹ ^ k2 * ε ^ (34 / 11 : ℝ)) =
            C1 * C2 * ν⁻¹ ^ (k1 + k2) * ε ^ (34 / 11 : ℝ) by rw [pow_add]; ring]

end UnforcedLeray.Short.PartIIIb.Concrete
