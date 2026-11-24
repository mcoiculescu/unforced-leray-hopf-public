import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2.PresCoef
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.ChiOMultYoung

/-!
# `RingHolderConv`: Hölder in the ring chart (`PartIII-b:C/rep/8/2/pres/2`)

Source: `the November 2 reference manuscript`, 2681-2688 (Jacobian
`πR²s^{-5/2}ds dη`, normalized phase `dq/c`), 5261 and 5285-5287 (Hölder `4/11 + 3/22 = 1/2`,
`R⁻¹ = ε`).  Step (1): `|coefOf R F| ≤ s^{-1/2}|F|`.  Step (2): `srcMeasure c = π ageμ c (-3/2)`
against `ringPhysμ R c = πR² ageμ c (-5/2)`, with `s^{-1}s^{-3/2} = s^{-5/2}`.  Step (3): Hölder.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The chart coefficient is bounded by `s^{-1/2}` times the physical field (for `s > 0`). -/
lemma holderConv_coef_norm_le (R : ℝ) (F : ℝ → Space → Space) (p : Chart) (hp : 0 < p.1) :
    ‖coefOf R F p‖ ≤ (Real.sqrt p.1)⁻¹ *
      ‖F (NearInst.chartTau R p) (NearInst.chartY R p)‖ := by
  unfold coefOf
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _))]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.2 (Real.sqrt_nonneg _))
  set v := F (NearInst.chartTau R p) (NearInst.chartY R p) with hv
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  rw [Fin.sum_univ_two, Fin.sum_univ_three]
  simp only [Real.norm_eq_abs, sq_abs]
  simp
  nlinarith [sq_nonneg (v 1), sq_nonneg (v 0), sq_nonneg (v 2)]

/-- Pointwise bound of the chart coefficient by the product `a·b` (real form). -/
lemma holderConv_pt (R : ℝ) (F : ℝ → Space → Space) (G : Chart → ℝ)
    (hG : ∀ p : Chart, 0 < p.1 → ‖F (NearInst.chartTau R p) (NearInst.chartY R p)‖ ≤ G p)
    (p : Chart) :
    ‖coefOf R F p‖ ≤ (Real.sqrt p.1)⁻¹ * ‖G p‖ := by
  by_cases hp : 0 < p.1
  · have h1 := holderConv_coef_norm_le R F p hp
    have h2 := hG p hp
    calc ‖coefOf R F p‖ ≤ (Real.sqrt p.1)⁻¹ * ‖F (NearInst.chartTau R p) (NearInst.chartY R p)‖ :=
          h1
      _ ≤ (Real.sqrt p.1)⁻¹ * ‖G p‖ :=
          mul_le_mul_of_nonneg_left (h2.trans (le_abs_self _) |>.trans (by rw [Real.norm_eq_abs]))
            (inv_nonneg.2 (Real.sqrt_nonneg _))
  · have hs : Real.sqrt p.1 = 0 := Real.sqrt_eq_zero'.2 (not_lt.1 hp)
    have h0 : coefOf R F p = 0 := by simp [coefOf, hs]
    rw [h0, norm_zero, hs, inv_zero, zero_mul]

/-- The `ageμ` almost-everywhere transfer from `ringPhysμ` to `srcMeasure`. -/
lemma holderConv_ae_src {R c : ℝ} (hR : 0 < R) (hc : 0 < c) {P : Chart → Prop}
    (h : ∀ᵐ p ∂(ringPhysμ R c), P p) : ∀ᵐ p ∂(srcMeasure c), P p := by
  have hπR : ENNReal.ofReal (Real.pi * R ^ 2) ≠ 0 :=
    (ENNReal.ofReal_pos.2 (by positivity)).ne'
  have hπ : ENNReal.ofReal Real.pi ≠ 0 := (ENNReal.ofReal_pos.2 Real.pi_pos).ne'
  unfold ringPhysμ at h
  rw [Measure.ae_ennreal_smul_measure_eq hπR] at h
  have hac : ageμ c (-3 / 2) ≪ ageμ c (-5 / 2) := cmo_ac_ageμ c (-3 / 2) (-5 / 2)
  have h2 := hac.ae_le h
  unfold srcMeasure
  rw [Measure.ae_ennreal_smul_measure_eq hπ]
  exact h2

/-- The exponent arithmetic `4/11 + 3/22 = 1/2` in `ℝ≥0∞`. -/
lemma holderConv_arith : (11 / 4 : ENNReal)⁻¹ + (22 / 3 : ENNReal)⁻¹ = (2 : ENNReal)⁻¹ := by
  have h1 : (11 / 4 : ENNReal) = ((11 / 4 : NNReal) : ENNReal) := by norm_num
  have h2 : (22 / 3 : ENNReal) = ((22 / 3 : NNReal) : ENNReal) := by norm_num
  have h3 : (2 : ENNReal) = ((2 : NNReal) : ENNReal) := by norm_num
  have n1 : (11 / 4 : NNReal) ≠ 0 := by norm_num
  have n2 : (22 / 3 : NNReal) ≠ 0 := by norm_num
  have n3 : (2 : NNReal) ≠ 0 := by norm_num
  rw [h1, h2, h3, ← ENNReal.coe_inv n1, ← ENNReal.coe_inv n2, ← ENNReal.coe_inv n3,
    ← ENNReal.coe_add]
  congr 1
  norm_num

/-- The density identity: `s^{-3/2}·s^{-1} = s^{-5/2}` for `s > 0`, with `(√s)^{-2} = s^{-1}`. -/
lemma holderConv_dens {c s : ℝ} (hc : 0 < c) (hs : 0 < s) (X : ENNReal) :
    ENNReal.ofReal (c⁻¹ * s ^ (-3 / 2 : ℝ)) * (ENNReal.ofReal ((Real.sqrt s)⁻¹) ^ 2 * X) =
      ENNReal.ofReal (c⁻¹ * s ^ (-5 / 2 : ℝ)) * X := by
  have hre : c⁻¹ * s ^ (-3 / 2 : ℝ) * ((Real.sqrt s)⁻¹) ^ 2 = c⁻¹ * s ^ (-5 / 2 : ℝ) := by
    have h1 : s ^ (-5 / 2 : ℝ) = s ^ (-3 / 2 : ℝ) * s⁻¹ := by
      rw [← Real.rpow_neg_one, ← Real.rpow_add hs]
      norm_num
    rw [h1, inv_pow, Real.sq_sqrt hs.le]
    ring
  have hnn : 0 ≤ c⁻¹ * s ^ (-3 / 2 : ℝ) :=
    mul_nonneg (inv_nonneg.2 hc.le) (Real.rpow_nonneg hs.le _)
  rw [← mul_assoc, ← ENNReal.ofReal_pow (inv_nonneg.2 (Real.sqrt_nonneg _)),
    ← ENNReal.ofReal_mul hnn, hre]

/-- The chart Hölder inequality (`RingHolderConv`). -/
theorem ringHolderConv : RingHolderConv := by
  unfold RingHolderConv
  intro R c hR hc F a b hA hB hpt
  set A' : Chart → ℝ := hA.mk (ringRead R a) with hA'def
  set B' : Chart → ℝ := hB.mk (ringRead R b) with hB'def
  have hA'm : Measurable A' := hA.stronglyMeasurable_mk.measurable
  have hB'm : Measurable B' := hB.stronglyMeasurable_mk.measurable
  have hAe : ∀ᵐ p ∂(ringPhysμ R c), ringRead R a p = A' p := hA.ae_eq_mk
  have hBe : ∀ᵐ p ∂(ringPhysμ R c), ringRead R b p = B' p := hB.ae_eq_mk
  have hAs : ∀ᵐ p ∂(srcMeasure c), ringRead R a p = A' p := holderConv_ae_src hR hc hAe
  have hBs : ∀ᵐ p ∂(srcMeasure c), ringRead R b p = B' p := holderConv_ae_src hR hc hBe
  have hGs : ∀ᵐ p ∂(srcMeasure c), ringRead R a p * ringRead R b p = A' p * B' p := by
    filter_upwards [hAs, hBs] with p h1 h2
    rw [h1, h2]
  have hpt1 : ∀ p : Chart, ‖coefOf R F p‖ₑ ≤
      ENNReal.ofReal ((Real.sqrt p.1)⁻¹) * ‖ringRead R a p * ringRead R b p‖ₑ := by
    intro p
    have h := holderConv_pt R F (fun p => ringRead R a p * ringRead R b p) hpt p
    rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm,
      ← ENNReal.ofReal_mul (inv_nonneg.2 (Real.sqrt_nonneg _))]
    exact ENNReal.ofReal_le_ofReal h
  have hpt2 : ∀ p : Chart, ‖coefOf R F p‖ₑ ^ 2 ≤
      ENNReal.ofReal ((Real.sqrt p.1)⁻¹) ^ 2 * ‖ringRead R a p * ringRead R b p‖ₑ ^ 2 := by
    intro p
    rw [← mul_pow]
    exact ENNReal.pow_le_pow_left (hpt1 p)
  have hG'm : Measurable (fun p : Chart => A' p * B' p) := hA'm.mul hB'm
  have hΨm : Measurable (fun p : Chart => ENNReal.ofReal ((Real.sqrt p.1)⁻¹) ^ 2 *
      ‖A' p * B' p‖ₑ ^ 2) := by
    have m1 : Measurable fun p : Chart => ENNReal.ofReal ((Real.sqrt p.1)⁻¹) ^ 2 :=
      (ENNReal.measurable_ofReal.comp ((Real.continuous_sqrt.measurable.comp measurable_fst).inv)).pow_const 2
    have m2 : Measurable fun p : Chart => ‖A' p * B' p‖ₑ ^ 2 := (hG'm.enorm).pow_const 2
    exact Measurable.mul m1 m2
  have hpt3 : ∀ᵐ p ∂(srcMeasure c), ‖coefOf R F p‖ₑ ^ 2 ≤
      ENNReal.ofReal ((Real.sqrt p.1)⁻¹) ^ 2 * ‖A' p * B' p‖ₑ ^ 2 := by
    filter_upwards [hGs] with p hp
    have e : ‖ringRead R a p * ringRead R b p‖ₑ = ‖A' p * B' p‖ₑ := by rw [hp]
    exact (hpt2 p).trans (le_of_eq (by rw [e]))
  have hRHS : ∫⁻ p, ENNReal.ofReal ((Real.sqrt p.1)⁻¹) ^ 2 * ‖A' p * B' p‖ₑ ^ 2
      ∂(srcMeasure c) =
      ENNReal.ofReal Real.pi * ∫⁻ p, ‖A' p * B' p‖ₑ ^ 2 ∂(ageμ c (-5 / 2)) := by
    unfold srcMeasure
    rw [lintegral_smul_measure, lintegral_ageμ hc (-3 / 2) hΨm,
      lintegral_ageμ hc (-5 / 2) (hG'm.enorm.pow_const 2), smul_eq_mul]
    congr 1
    refine setLIntegral_congr_fun ?_ ?_
    · unfold qCell
      exact measurableSet_Ioi.prod ((measurableSet_Ico).prod MeasurableSet.univ)
    · intro p hp
      have hs : 0 < p.1 := hp.1
      exact holderConv_dens hc hs _
  have hstep1 : ∫⁻ p, ‖coefOf R F p‖ₑ ^ 2 ∂(srcMeasure c) ≤
      ENNReal.ofReal Real.pi * ∫⁻ p, ‖A' p * B' p‖ₑ ^ 2 ∂(ageμ c (-5 / 2)) :=
    (lintegral_mono_ae hpt3).trans (le_of_eq hRHS)
  have hμpI : ∫⁻ p, ‖A' p * B' p‖ₑ ^ 2 ∂(ringPhysμ R c) =
      ENNReal.ofReal (Real.pi * R ^ 2) * ∫⁻ p, ‖A' p * B' p‖ₑ ^ 2 ∂(ageμ c (-5 / 2)) := by
    unfold ringPhysμ
    rw [lintegral_smul_measure, smul_eq_mul]
  have hconst : ENNReal.ofReal Real.pi = ENNReal.ofReal (R⁻¹) ^ 2 * ENNReal.ofReal (Real.pi * R ^ 2) := by
    rw [← ENNReal.ofReal_pow (inv_nonneg.2 hR.le), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    field_simp
  have hGae : ∫⁻ p, ‖ringRead R a p * ringRead R b p‖ₑ ^ 2 ∂(ringPhysμ R c) =
      ∫⁻ p, ‖A' p * B' p‖ₑ ^ 2 ∂(ringPhysμ R c) := by
    apply lintegral_congr_ae
    filter_upwards [hAe, hBe] with p h1 h2
    rw [h1, h2]
  have hsq : eLpNorm (coefOf R F) 2 (srcMeasure c) ^ 2 ≤
      (ENNReal.ofReal R⁻¹ * eLpNorm (fun p => ringRead R a p * ringRead R b p) 2
        (ringPhysμ R c)) ^ 2 := by
    have hX : eLpNorm (coefOf R F) 2 (srcMeasure c) ^ 2 =
        ∫⁻ p, ‖coefOf R F p‖ₑ ^ 2 ∂(srcMeasure c) := by
      have h := eLpNorm_nnreal_pow_eq_lintegral (f := coefOf R F) (μ := srcMeasure c)
        (p := 2) two_ne_zero
      simpa [ENNReal.rpow_two] using h
    have hY : eLpNorm (fun p => ringRead R a p * ringRead R b p) 2 (ringPhysμ R c) ^ 2 =
        ∫⁻ p, ‖ringRead R a p * ringRead R b p‖ₑ ^ 2 ∂(ringPhysμ R c) := by
      have h := eLpNorm_nnreal_pow_eq_lintegral (f := fun p => ringRead R a p * ringRead R b p)
        (μ := ringPhysμ R c) (p := 2) two_ne_zero
      simpa [ENNReal.rpow_two] using h
    rw [mul_pow, hY, hX]
    calc ∫⁻ p, ‖coefOf R F p‖ₑ ^ 2 ∂(srcMeasure c)
        ≤ ENNReal.ofReal Real.pi * ∫⁻ p, ‖A' p * B' p‖ₑ ^ 2 ∂(ageμ c (-5 / 2)) := hstep1
      _ = ENNReal.ofReal (R⁻¹) ^ 2 * (ENNReal.ofReal (Real.pi * R ^ 2) *
            ∫⁻ p, ‖A' p * B' p‖ₑ ^ 2 ∂(ageμ c (-5 / 2))) := by
          rw [hconst, mul_assoc]
      _ = ENNReal.ofReal (R⁻¹) ^ 2 * ∫⁻ p, ‖A' p * B' p‖ₑ ^ 2 ∂(ringPhysμ R c) := by
          rw [hμpI]
      _ = ENNReal.ofReal (R⁻¹) ^ 2 * ∫⁻ p, ‖ringRead R a p * ringRead R b p‖ₑ ^ 2
            ∂(ringPhysμ R c) := by
          rw [hGae]
  have hXY : eLpNorm (coefOf R F) 2 (srcMeasure c) ≤
      ENNReal.ofReal R⁻¹ * eLpNorm (fun p => ringRead R a p * ringRead R b p) 2
        (ringPhysμ R c) :=
    (ENNReal.pow_le_pow_left_iff two_ne_zero).1 hsq
  have hHo : eLpNorm (fun p => ringRead R a p * ringRead R b p) 2 (ringPhysμ R c) ≤
      1 * eLpNorm (ringRead R a) (11 / 4) (ringPhysμ R c) *
        eLpNorm (ringRead R b) (22 / 3) (ringPhysμ R c) := by
    haveI : ENNReal.HolderTriple (11 / 4 : ENNReal) (22 / 3 : ENNReal) 2 := ⟨holderConv_arith⟩
    exact eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm hA hB (fun x y : ℝ => x * y) 1
      (ae_of_all _ fun p => by simp [nnnorm_mul])
  calc eLpNorm (coefOf R F) 2 (srcMeasure c)
      ≤ ENNReal.ofReal R⁻¹ * eLpNorm (fun p => ringRead R a p * ringRead R b p) 2
          (ringPhysμ R c) := hXY
    _ ≤ ENNReal.ofReal R⁻¹ * (1 * eLpNorm (ringRead R a) (11 / 4) (ringPhysμ R c) *
          eLpNorm (ringRead R b) (22 / 3) (ringPhysμ R c)) := by
        gcongr
    _ = ENNReal.ofReal R⁻¹ * eLpNorm (ringRead R a) (11 / 4) (ringPhysμ R c) *
          eLpNorm (ringRead R b) (22 / 3) (ringPhysμ R c) := by
        rw [one_mul, mul_assoc]

end UnforcedLeray.Short.PartIIIb.Concrete
