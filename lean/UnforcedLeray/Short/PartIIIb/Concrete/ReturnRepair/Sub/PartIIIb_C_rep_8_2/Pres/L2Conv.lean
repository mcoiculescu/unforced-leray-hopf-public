import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2.Pres.HolderConv

/-!
# `RingL2Conv`: the `L²` chart step (`PartIII-b:C/rep/8/2/pres/4/org2/4`)

Source: `the November 2 reference manuscript`, 2681-2688 (Jacobian
`πR²s^{-5/2}ds dη`, normalized phase `dq/c`), 5470-5476.  Reuses the density identity
`holderConv_dens` and the pointwise bound `holderConv_pt` of `Pres/HolderConv.lean`.

Pointwise `|coefOf R F|² ≤ s^{-1}|g|²` on `s > 0`, and `coefOf R F = 0` for `s ≤ 0`.
The integral over `srcMeasure c` is bounded by the lower integral of the measurable minorants
`s ↦ s^{-1}·(s·…)`, which avoids any measurability hypothesis on `ringRead R g`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The weight `(√s)⁻²` of the chart coefficient, times `s`, is `1` for `s > 0`. -/
lemma l2conv_w_mul (p : Chart) (hp : 0 < p.1) :
    ENNReal.ofReal p.1 * ENNReal.ofReal ((Real.sqrt p.1)⁻¹) ^ 2 = 1 := by
  rw [← ENNReal.ofReal_pow (inv_nonneg.2 (Real.sqrt_nonneg _)), ← ENNReal.ofReal_mul hp.le]
  have h : p.1 * ((Real.sqrt p.1)⁻¹ ^ 2) = 1 := by
    rw [inv_pow, Real.sq_sqrt hp.le, mul_inv_cancel₀ hp.ne']
  rw [h, ENNReal.ofReal_one]

/-- The density identity for a measurable integrand: `∫ (√s)⁻²·G dsrcMeasure = π ∫ G dageμ(-5/2)`. -/
lemma l2conv_key {c : ℝ} (hc : 0 < c) (G : Chart → ℝ≥0∞) (hG : Measurable G) :
    ∫⁻ p, ENNReal.ofReal ((Real.sqrt p.1)⁻¹) ^ 2 * G p ∂(srcMeasure c) =
      ENNReal.ofReal Real.pi * ∫⁻ p, G p ∂(ageμ c (-5 / 2)) := by
  have hw : Measurable fun p : Chart => ENNReal.ofReal ((Real.sqrt p.1)⁻¹) ^ 2 :=
    (ENNReal.measurable_ofReal.comp ((Real.continuous_sqrt.measurable.comp measurable_fst).inv)).pow_const 2
  have hΨm : Measurable (fun p : Chart => ENNReal.ofReal ((Real.sqrt p.1)⁻¹) ^ 2 * G p) :=
    hw.mul hG
  unfold srcMeasure
  rw [lintegral_smul_measure, lintegral_ageμ hc (-3 / 2) hΨm, lintegral_ageμ hc (-5 / 2) hG,
    smul_eq_mul]
  congr 1
  refine setLIntegral_congr_fun ?_ ?_
  · unfold qCell
    exact measurableSet_Ioi.prod ((measurableSet_Ico).prod MeasurableSet.univ)
  · intro p hp
    exact holderConv_dens hc hp.1 _

/-- **The `L²` chart step** (`RingL2Conv`). -/
theorem ringL2Conv : RingL2Conv := by
  unfold RingL2Conv
  intro R c hR hc F g hpt
  -- pointwise bound on every chart point (both signs of `s`)
  have hpt1 : ∀ p : Chart, ‖coefOf R F p‖ₑ ^ 2 ≤
      ENNReal.ofReal ((Real.sqrt p.1)⁻¹) ^ 2 * ‖ringRead R g p‖ₑ ^ 2 := by
    intro p
    by_cases hp : 0 < p.1
    · have h := holderConv_pt R F (ringRead R g) hpt p
      rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm]
      calc ENNReal.ofReal ‖coefOf R F p‖ ^ 2
          ≤ ENNReal.ofReal ((Real.sqrt p.1)⁻¹ * ‖ringRead R g p‖) ^ 2 :=
            ENNReal.pow_le_pow_left (ENNReal.ofReal_le_ofReal h)
        _ = ENNReal.ofReal ((Real.sqrt p.1)⁻¹) ^ 2 * ENNReal.ofReal ‖ringRead R g p‖ ^ 2 := by
            rw [ENNReal.ofReal_mul (inv_nonneg.2 (Real.sqrt_nonneg _)), mul_pow]
    · have hs : Real.sqrt p.1 = 0 := Real.sqrt_eq_zero'.2 (not_lt.1 hp)
      have h0 : coefOf R F p = 0 := by simp [coefOf, hs]
      rw [h0]
      simp
  -- the lower integral is the supremum over measurable minorants
  have hint : ∫⁻ p, ‖coefOf R F p‖ₑ ^ 2 ∂(srcMeasure c) ≤
      ENNReal.ofReal Real.pi * ∫⁻ p, ‖ringRead R g p‖ₑ ^ 2 ∂(ageμ c (-5 / 2)) := by
    refine (le_of_eq (iSup_lintegral_measurable_le_eq_lintegral (μ := srcMeasure c)
      (fun p : Chart => ‖coefOf R F p‖ₑ ^ 2)).symm).trans ?_
    refine iSup_le fun s => iSup_le fun hs => iSup_le fun hsh => ?_
    have hgm : Measurable fun p : Chart => ENNReal.ofReal p.1 * s p :=
      (ENNReal.measurable_ofReal.comp measurable_fst).mul hs
    have hgf : ∀ p : Chart, ENNReal.ofReal p.1 * s p ≤ ‖ringRead R g p‖ₑ ^ 2 := by
      intro p
      by_cases hp : 0 < p.1
      · calc ENNReal.ofReal p.1 * s p
            ≤ ENNReal.ofReal p.1 *
                (ENNReal.ofReal ((Real.sqrt p.1)⁻¹) ^ 2 * ‖ringRead R g p‖ₑ ^ 2) :=
              by gcongr; exact (hsh p).trans (hpt1 p)
          _ = (ENNReal.ofReal p.1 * ENNReal.ofReal ((Real.sqrt p.1)⁻¹) ^ 2) *
                ‖ringRead R g p‖ₑ ^ 2 := (mul_assoc _ _ _).symm
          _ = ‖ringRead R g p‖ₑ ^ 2 := by rw [l2conv_w_mul p hp, one_mul]
      · rw [ENNReal.ofReal_of_nonpos (not_lt.1 hp), zero_mul]
        exact zero_le
    have hsle : ∀ p : Chart, s p ≤
        ENNReal.ofReal ((Real.sqrt p.1)⁻¹) ^ 2 * (ENNReal.ofReal p.1 * s p) := by
      intro p
      by_cases hp : 0 < p.1
      · have e : ENNReal.ofReal ((Real.sqrt p.1)⁻¹) ^ 2 * (ENNReal.ofReal p.1 * s p) = s p := by
          calc ENNReal.ofReal ((Real.sqrt p.1)⁻¹) ^ 2 * (ENNReal.ofReal p.1 * s p)
              = (ENNReal.ofReal p.1 * ENNReal.ofReal ((Real.sqrt p.1)⁻¹) ^ 2) * s p := by ring
            _ = s p := by rw [l2conv_w_mul p hp, one_mul]
        exact le_of_eq e.symm
      · have hw0 : ENNReal.ofReal ((Real.sqrt p.1)⁻¹) ^ 2 = 0 := by
          rw [Real.sqrt_eq_zero'.2 (not_lt.1 hp), inv_zero, ENNReal.ofReal_zero,
            zero_pow two_ne_zero]
        have hs0 : s p ≤ 0 := by
          have h := (hsh p).trans (hpt1 p)
          rwa [hw0, zero_mul] at h
        rw [hw0, zero_mul]
        exact hs0
    calc ∫⁻ p, s p ∂(srcMeasure c)
        ≤ ∫⁻ p, ENNReal.ofReal ((Real.sqrt p.1)⁻¹) ^ 2 * (ENNReal.ofReal p.1 * s p)
            ∂(srcMeasure c) := lintegral_mono hsle
      _ = ENNReal.ofReal Real.pi * ∫⁻ p, ENNReal.ofReal p.1 * s p ∂(ageμ c (-5 / 2)) :=
          l2conv_key hc _ hgm
      _ ≤ ENNReal.ofReal Real.pi * ∫⁻ p, ‖ringRead R g p‖ₑ ^ 2 ∂(ageμ c (-5 / 2)) :=
          mul_le_mul_of_nonneg_left (lintegral_mono hgf) zero_le
  -- the ring measure
  have hμ : ∫⁻ p, ‖ringRead R g p‖ₑ ^ 2 ∂(ringPhysμ R c) =
      ENNReal.ofReal (Real.pi * R ^ 2) * ∫⁻ p, ‖ringRead R g p‖ₑ ^ 2 ∂(ageμ c (-5 / 2)) := by
    unfold ringPhysμ
    rw [lintegral_smul_measure, smul_eq_mul]
  have hconst : ENNReal.ofReal Real.pi =
      ENNReal.ofReal (R⁻¹) ^ 2 * ENNReal.ofReal (Real.pi * R ^ 2) := by
    rw [← ENNReal.ofReal_pow (inv_nonneg.2 hR.le), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    field_simp
  have hX : eLpNorm (coefOf R F) 2 (srcMeasure c) ^ 2 =
      ∫⁻ p, ‖coefOf R F p‖ₑ ^ 2 ∂(srcMeasure c) := by
    have h := eLpNorm_nnreal_pow_eq_lintegral (f := coefOf R F) (μ := srcMeasure c)
      (p := 2) two_ne_zero
    simpa [ENNReal.rpow_two] using h
  have hY : eLpNorm (ringRead R g) 2 (ringPhysμ R c) ^ 2 =
      ∫⁻ p, ‖ringRead R g p‖ₑ ^ 2 ∂(ringPhysμ R c) := by
    have h := eLpNorm_nnreal_pow_eq_lintegral (f := ringRead R g)
      (μ := ringPhysμ R c) (p := 2) two_ne_zero
    simpa [ENNReal.rpow_two] using h
  have hsq : eLpNorm (coefOf R F) 2 (srcMeasure c) ^ 2 ≤
      (ENNReal.ofReal R⁻¹ * eLpNorm (ringRead R g) 2 (ringPhysμ R c)) ^ 2 := by
    rw [mul_pow, hY, hX]
    calc ∫⁻ p, ‖coefOf R F p‖ₑ ^ 2 ∂(srcMeasure c)
        ≤ ENNReal.ofReal Real.pi * ∫⁻ p, ‖ringRead R g p‖ₑ ^ 2 ∂(ageμ c (-5 / 2)) := hint
      _ = ENNReal.ofReal (R⁻¹) ^ 2 * (ENNReal.ofReal (Real.pi * R ^ 2) *
            ∫⁻ p, ‖ringRead R g p‖ₑ ^ 2 ∂(ageμ c (-5 / 2))) := by
          rw [hconst, mul_assoc]
      _ = ENNReal.ofReal (R⁻¹) ^ 2 * ∫⁻ p, ‖ringRead R g p‖ₑ ^ 2 ∂(ringPhysμ R c) := by
          rw [hμ]
  exact (ENNReal.pow_le_pow_left_iff two_ne_zero).1 hsq

end UnforcedLeray.Short.PartIIIb.Concrete
