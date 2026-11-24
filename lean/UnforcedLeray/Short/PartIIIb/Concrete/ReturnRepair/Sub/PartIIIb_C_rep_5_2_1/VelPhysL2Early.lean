import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_1Org

/-!
# `PartIII-b:C/rep/5/2/1/10`: early source velocity in `Y_2` (source 2683-2689, 5318-5319)

Same proof as the leaf `velPhysL2` (`C₁ = 1`), with the gain bound on the support of
`1 - χ_o(νs)`: there `νs < 3/2`, so `g(s) ≤ e^{3γ/(5ν)}` (`ftGain_early`), i.e.
`π g⁻²` is at least `e^{-6γ/(5ν)} π`, and `|1 - χ_o| ≤ 1`.
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Real comparison: `π h² ≤ E² (π G⁻² x²)` when `0 < G ≤ E` and `0 ≤ h ≤ x`. -/
theorem earlyVel_real (π' E G h x : ℝ) (hπ : 0 ≤ π') (hG : 0 < G) (hGE : G ≤ E)
    (hh : 0 ≤ h) (hhx : h ≤ x) :
    π' * h ^ 2 ≤ E ^ 2 * (π' * (G⁻¹) ^ 2 * x ^ 2) := by
  have h1 : 1 ≤ E / G := (one_le_div hG).2 hGE
  have h2 : 1 ≤ (E / G) ^ 2 := one_le_pow₀ h1
  have h3 : E ^ 2 * (G⁻¹) ^ 2 = (E / G) ^ 2 := by rw [div_eq_mul_inv, mul_pow]
  have h4 : h ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ hh hhx 2
  calc π' * h ^ 2 ≤ π' * x ^ 2 := mul_le_mul_of_nonneg_left h4 hπ
    _ ≤ π' * x ^ 2 * (E / G) ^ 2 := le_mul_of_one_le_right (mul_nonneg hπ (sq_nonneg _)) h2
    _ = E ^ 2 * (π' * (G⁻¹) ^ 2 * x ^ 2) := by rw [← h3]; ring

theorem velPhysL2Early : VelPhysL2Early := by
  refine ⟨1, zero_le_one, ?_⟩
  intro Pl hγ K L w
  have hc := cOf_pos L.ν_pos
  have hε := L.ε_pos
  have hν := L.ν_pos
  have hv : Measurable (w : Chart → Merid) := (Lp.stronglyMeasurable w).measurable
  have hcut : Measurable fun p : Chart => (1 : ℝ) - K.χo (L.ν * p.1) :=
    measurable_const.sub
      (K.hχo.smooth.continuous.measurable.comp (measurable_const.mul measurable_fst))
  have hmeas : Measurable (earlyVel K L (w : Chart → Merid)) := by
    unfold earlyVel
    exact hcut.smul hv
  have h1 := SrcPairing.sp_lintegral_velPhys hc hε hmeas
  have e1 : ∀ (t : ℝ) (y : Space),
      ENNReal.ofReal ‖velPhys L.ε⁻¹ (cOf L.ν) (earlyVel K L (w : Chart → Merid)) (t, y)‖ ^ 2 =
        ‖velPhys L.ε⁻¹ (cOf L.ν) (earlyVel K L (w : Chart → Merid)) (t, y)‖ₑ ^ (2 : ℝ) :=
    fun t y => by
      rw [ENNReal.rpow_two, ofReal_norm]
  simp only [e1]
  rw [h1]
  have hE : ∀ (f : Chart → Merid) (μ : Measure Chart),
      eLpNorm f 2 μ ^ 2 = ∫⁻ p, ‖f p‖ₑ ^ (2 : ℝ) ∂μ := by
    intro f μ
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  have hnorm : ENNReal.ofReal ‖w‖ =
      eLpNorm (w : Chart → Merid) 2 (bodyMeasure (cOf L.ν) (gRate Pl) L.ν) := by
    rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.memLp w).eLpNorm_lt_top.ne]
  have hwE : ∫⁻ p, ‖(w : Chart → Merid) p‖ₑ ^ (2 : ℝ) ∂bodyMeasure (cOf L.ν) (gRate Pl) L.ν =
      ENNReal.ofReal (‖w‖ ^ 2) := by
    rw [ENNReal.ofReal_pow (norm_nonneg _), hnorm, hE]
  have hgm : Measurable fun p : Chart => ENNReal.ofReal (Real.pi * ginv (gRate Pl) L.ν p ^ 2) :=
    (((NearInst.ginv_measurable' (gRate Pl) L.ν).pow_const 2).const_mul Real.pi).ennreal_ofReal
  have hwm : Measurable fun p : Chart => ‖(w : Chart → Merid) p‖ₑ ^ (2 : ℝ) :=
    hv.enorm.pow_const _
  have hLb : ∫⁻ p, ‖(w : Chart → Merid) p‖ₑ ^ (2 : ℝ) ∂bodyMeasure (cOf L.ν) (gRate Pl) L.ν =
      ∫⁻ p, ENNReal.ofReal (Real.pi * ginv (gRate Pl) L.ν p ^ 2) *
        ‖(w : Chart → Merid) p‖ₑ ^ (2 : ℝ) ∂ageμ (cOf L.ν) (-3 / 2) :=
    lintegral_withDensity_eq_lintegral_mul _ hgm hwm
  have hmain : ENNReal.ofReal Real.pi *
        ∫⁻ p, ‖earlyVel K L (w : Chart → Merid) p‖ₑ ^ (2 : ℝ) ∂ageμ (cOf L.ν) (-3 / 2) ≤
      ENNReal.ofReal (Real.exp (3 * gRate Pl / 5 / L.ν) ^ 2) *
        ∫⁻ p, ‖(w : Chart → Merid) p‖ₑ ^ (2 : ℝ) ∂bodyMeasure (cOf L.ν) (gRate Pl) L.ν := by
    rw [hLb, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun p => ?_
    by_cases ht : 1 - K.χo (L.ν * p.1) = 0
    · have hz : earlyVel K L (w : Chart → Merid) p = 0 := by
        change (1 - K.χo (L.ν * p.1)) • (w : Chart → Merid) p = 0
        rw [ht, zero_smul]
      rw [hz, enorm_zero, ENNReal.zero_rpow_of_pos (by norm_num), mul_zero]
      positivity
    · have hcut1 : K.χo (L.ν * p.1) ≠ 1 := fun h => ht (by rw [h, sub_self])
      have hlt : L.ν * p.1 < 3 / 2 := by
        by_contra hh
        push_neg at hh
        exact hcut1 (K.hχo.one _ hh)
      have hs0 : 0 ≤ max p.1 0 := le_max_right _ _
      have hsle : max p.1 0 ≤ 3 / 2 / L.ν :=
        max_le (by rw [le_div_iff₀ hν]; linarith [mul_comm L.ν p.1])
          (div_nonneg (by norm_num) hν.le)
      have hG : 0 < UnforcedLeray.Short.IIIa.gainG (gRate Pl) L.ν (max p.1 0) := by
        unfold UnforcedLeray.Short.IIIa.gainG
        exact Real.exp_pos _
      have hGE : UnforcedLeray.Short.IIIa.gainG (gRate Pl) L.ν (max p.1 0) ≤
          Real.exp (3 * gRate Pl / 5 / L.ν) :=
        ftGain_early hγ hν hs0 hsle
      have ht1 : ‖1 - K.χo (L.ν * p.1)‖ ≤ 1 := by
        have hr : 0 ≤ K.χo (L.ν * p.1) ∧ K.χo (L.ν * p.1) ≤ 1 := K.hχo.range _
        rw [Real.norm_eq_abs, abs_le]
        constructor <;> linarith [hr.1, hr.2]
      have hh : ‖earlyVel K L (w : Chart → Merid) p‖ ≤ ‖(w : Chart → Merid) p‖ := by
        change ‖(1 - K.χo (L.ν * p.1)) • (w : Chart → Merid) p‖ ≤ ‖(w : Chart → Merid) p‖
        rw [norm_smul]
        exact mul_le_of_le_one_left (norm_nonneg _) ht1
      have e1' : ‖earlyVel K L (w : Chart → Merid) p‖ₑ ^ (2 : ℝ) =
          ENNReal.ofReal (‖earlyVel K L (w : Chart → Merid) p‖ ^ 2) := by
        rw [ENNReal.rpow_two, ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
      have e2' : ‖(w : Chart → Merid) p‖ₑ ^ (2 : ℝ) =
          ENNReal.ofReal (‖(w : Chart → Merid) p‖ ^ 2) := by
        rw [ENNReal.rpow_two, ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
      rw [e1', e2', ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      exact earlyVel_real Real.pi _ _ _ _ Real.pi_pos.le hG hGE (norm_nonneg _) hh
  have hfin : ENNReal.ofReal (Real.pi * L.ε⁻¹ ^ 2) *
        ∫⁻ p, ‖earlyVel K L (w : Chart → Merid) p‖ₑ ^ (2 : ℝ) ∂ageμ (cOf L.ν) (-3 / 2) =
      ENNReal.ofReal (L.ε⁻¹ ^ 2) * (ENNReal.ofReal Real.pi *
        ∫⁻ p, ‖earlyVel K L (w : Chart → Merid) p‖ₑ ^ (2 : ℝ) ∂ageμ (cOf L.ν) (-3 / 2)) := by
    rw [ENNReal.ofReal_mul Real.pi_pos.le]
    ring
  rw [hfin]
  calc ENNReal.ofReal (L.ε⁻¹ ^ 2) * (ENNReal.ofReal Real.pi *
          ∫⁻ p, ‖earlyVel K L (w : Chart → Merid) p‖ₑ ^ (2 : ℝ) ∂ageμ (cOf L.ν) (-3 / 2))
      ≤ ENNReal.ofReal (L.ε⁻¹ ^ 2) * (ENNReal.ofReal (Real.exp (3 * gRate Pl / 5 / L.ν) ^ 2) *
          ∫⁻ p, ‖(w : Chart → Merid) p‖ₑ ^ (2 : ℝ) ∂bodyMeasure (cOf L.ν) (gRate Pl) L.ν) :=
        mul_le_mul_of_nonneg_left hmain (by positivity)
    _ = ENNReal.ofReal ((1 * L.ε⁻¹ * Real.exp (3 * gRate Pl / 5 / L.ν) * ‖w‖) ^ 2) := by
        rw [hwE, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring

end UnforcedLeray.Short.PartIIIb.Concrete
