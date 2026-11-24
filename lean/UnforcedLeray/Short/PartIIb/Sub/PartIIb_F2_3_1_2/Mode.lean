import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F2_3_1_2.Polar
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F2_3_1

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIb.PlanarModesHelp

open UnforcedLeray.Short.IIb

/-- The unit-scale real direct mode. -/
def dirModeG (q : Blueprint.Planar.Profile) (i : Fin 2) (y : B0579.Plane) : ℝ :=
  ![2 * (planarMode2D q y).re, -2 * (planarMode2D q y).im] i

lemma mode_eq_dl (q : Blueprint.Planar.Profile) (a : ℝ) (i : Fin 2) :
    planarFrozenDirectMode q a i = dl a (dirModeG q i) := by
  funext x
  unfold planarFrozenDirectMode dilPlanarMode dl dirModeG sc
  have : ((Real.sqrt a)⁻¹ • x) = (x.1 / Real.sqrt a, x.2 / Real.sqrt a) := by
    ext <;> simp [div_eq_inv_mul]
  rw [this]
  have hre : ∀ (r : ℝ) (z : ℂ), ((r : ℂ) * z).re = r * z.re := fun r z => Complex.re_ofReal_mul r z
  have him : ∀ (r : ℝ) (z : ℂ), ((r : ℂ) * z).im = r * z.im := fun r z => Complex.im_ofReal_mul r z
  fin_cases i <;> simp only [Fin.zero_eta, Matrix.cons_val_zero, Fin.mk_one, Matrix.cons_val_one,
    Matrix.head_cons, hre, him] <;> ring

lemma norm_ang_le (x : B0579.Plane) : ‖angTwoPlanar x‖ ≤ 1 := by
  unfold angTwoPlanar
  rw [norm_div, norm_pow]
  have h1 : ‖((x.1 : ℂ) + (x.2 : ℂ) * Complex.I)‖ ^ 2 = x.1 ^ 2 + x.2 ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_add_mul_I]
  have h2 : ‖(((x.1 ^ 2 + x.2 ^ 2 : ℝ)) : ℂ)‖ = x.1 ^ 2 + x.2 ^ 2 := by
    rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  rw [h1, h2]
  by_cases h : x.1 ^ 2 + x.2 ^ 2 = 0
  · rw [h]; simp
  · rw [div_self h]

lemma norm_Gq_le (q : Blueprint.Planar.Profile) (i : Fin 2) (y : B0579.Plane) :
    ‖dirModeG q i y‖ ≤ 2 * ‖q (rho y)‖ := by
  have hz : ‖planarMode2D q y‖ ≤ ‖q (rho y)‖ := by
    unfold planarMode2D
    rw [norm_mul]
    calc ‖q (Real.sqrt (y.1 ^ 2 + y.2 ^ 2))‖ * ‖angTwoPlanar y‖ ≤ ‖q (Real.sqrt (y.1 ^ 2 + y.2 ^ 2))‖ * 1 :=
          mul_le_mul_of_nonneg_left (norm_ang_le y) (norm_nonneg _)
      _ = _ := mul_one _
  have h1 := Complex.abs_re_le_norm (planarMode2D q y)
  have h2 := Complex.abs_im_le_norm (planarMode2D q y)
  unfold dirModeG
  fin_cases i <;> simp [abs_mul] <;> nlinarith

lemma aestronglyMeasurable_comp_rho {q : ℝ → ℂ}
    (hq : AEStronglyMeasurable q (volume.restrict (Ioi (0 : ℝ)))) :
    AEStronglyMeasurable (fun x => q (rho x)) (volume : Measure B0579.Plane) := by
  refine ⟨fun x => hq.mk q (rho x), hq.stronglyMeasurable_mk.comp_measurable measurable_rho, ?_⟩
  have h := hq.ae_eq_mk
  rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioi] at h
  have hN : volume ({r : ℝ | q r ≠ hq.mk q r} ∩ Ioi 0) = 0 := by
    rw [ae_iff] at h
    refine measure_mono_null ?_ h
    intro r hr
    exact fun hh => hr.1 (hh hr.2)
  have := rho_preimage_null _ hN
  rw [Filter.EventuallyEq, ae_iff]
  exact this


lemma poly_le (m : ℝ) (hm : 0 < m) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, (1 + r ^ 2) ^ m ≤ C * Real.exp (r ^ 2 / 4) := by
  refine ⟨Real.exp (1 / 4 - m + m * Real.log (4 * m)), Real.exp_pos _, fun r => ?_⟩
  have ht : 0 < 1 + r ^ 2 := by positivity
  have h4 : 0 < 4 * m := by positivity
  have hlog : Real.log ((1 + r ^ 2) / (4 * m)) ≤ (1 + r ^ 2) / (4 * m) - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  rw [Real.log_div ht.ne' h4.ne'] at hlog
  rw [Real.rpow_def_of_pos ht, ← Real.exp_add]
  apply Real.exp_le_exp.2
  have : m * Real.log (1 + r ^ 2) ≤ m * ((1 + r ^ 2) / (4 * m) - 1 + Real.log (4 * m)) :=
    mul_le_mul_of_nonneg_left (by linarith) hm.le
  have e : m * ((1 + r ^ 2) / (4 * m) - 1 + Real.log (4 * m)) =
      1 / 4 - m + m * Real.log (4 * m) + r ^ 2 / 4 := by
    field_simp; ring
  linarith


lemma enorm_sq_eq {E : Type*} [NormedAddCommGroup E] (z : E) : ‖z‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (‖z‖ ^ 2) := by
  rw [ENNReal.rpow_two, ← ofReal_norm, ENNReal.ofReal_pow (norm_nonneg _)]

theorem memLp_Gq (m : ℝ) (hm : 0 < m) {q : Blueprint.Planar.Profile}
    (hq : Blueprint.Planar.MemXG q) (i : Fin 2) :
    MemLp (dirModeG q i) 2 (planeMeasure m) := by
  have hm0 : 0 ≤ m := hm.le
  obtain ⟨C, hCpos, hC⟩ := poly_le m hm
  have hmeasq : AEStronglyMeasurable (fun x => q (rho x)) (volume : Measure B0579.Plane) :=
    aestronglyMeasurable_comp_rho hq.measurable
  have hang : AEStronglyMeasurable angTwoPlanar (volume : Measure B0579.Plane) := by
    have : Measurable angTwoPlanar := by unfold angTwoPlanar; fun_prop
    exact this.aestronglyMeasurable
  have hz : AEStronglyMeasurable (planarMode2D q) (volume : Measure B0579.Plane) := by
    unfold planarMode2D
    exact hmeasq.mul hang
  have hG : AEStronglyMeasurable (dirModeG q i) (volume : Measure B0579.Plane) := by
    fin_cases i
    · exact (Complex.continuous_re.comp_aestronglyMeasurable hz).const_mul 2
    · exact (Complex.continuous_im.comp_aestronglyMeasurable hz).const_mul (-2)
  have hF : AEMeasurable (fun r : ℝ => ENNReal.ofReal ((1 + r ^ 2) ^ m) * (4 * ‖q r‖ₑ ^ (2 : ℝ)))
      (volume.restrict (Ioi (0 : ℝ))) := by
    have h1 : Measurable (fun r : ℝ => ENNReal.ofReal ((1 + r ^ 2) ^ m)) := by
      refine ENNReal.measurable_ofReal.comp ?_
      exact (Continuous.rpow_const (by fun_prop) (fun r => Or.inr hm0)).measurable
    exact h1.aemeasurable.mul (aemeasurable_const.mul (hq.measurable.enorm.pow_const _))
  have hpt : ∀ y : B0579.Plane, (B0579.density m y : ℝ≥0∞) * ‖dirModeG q i y‖ₑ ^ (2 : ℝ) ≤
      ENNReal.ofReal ((1 + rho y ^ 2) ^ m) * (4 * ‖q (rho y)‖ₑ ^ (2 : ℝ)) := by
    intro y
    have hj : B0579.jb y = 1 + rho y ^ 2 := by
      unfold B0579.jb rho
      rw [Real.sq_sqrt (by positivity)]; ring
    rw [density_coe, hj]
    refine mul_le_mul' le_rfl ?_
    rw [enorm_sq_eq, enorm_sq_eq]
    have h4 : ENNReal.ofReal (‖dirModeG q i y‖ ^ 2) ≤ ENNReal.ofReal (4 * ‖q (rho y)‖ ^ 2) := by
      apply ENNReal.ofReal_le_ofReal
      have := norm_Gq_le q i y
      nlinarith [norm_nonneg (dirModeG q i y), norm_nonneg (q (rho y))]
    rwa [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat] at h4
  have hlint : ∫⁻ y, ‖dirModeG q i y‖ₑ ^ (2 : ℝ) ∂planeMeasure m < ⊤ := by
    rw [lint_planeMeasure m hm0]
    calc _ ≤ ∫⁻ y : B0579.Plane, (fun r : ℝ => ENNReal.ofReal ((1 + r ^ 2) ^ m) *
              (4 * ‖q r‖ₑ ^ (2 : ℝ))) (rho y) := lintegral_mono hpt
      _ = _ := lint_radial _ hF
      _ < ⊤ := ?_
    refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
    have hfin := hq.integrable.hasFiniteIntegral
    unfold HasFiniteIntegral at hfin
    refine lt_of_le_of_lt ?_ (ENNReal.mul_lt_top (ENNReal.ofReal_lt_top (r := C / Real.pi)) hfin)
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine setLIntegral_mono' measurableSet_Ioi (fun r hr => ?_)
    have hr0 : 0 < r := hr
    have hnn : 0 ≤ ‖q r‖ ^ 2 * Blueprint.Planar.gaussianWeightInv r * r := by
      unfold Blueprint.Planar.gaussianWeightInv; positivity
    rw [Real.enorm_of_nonneg hnn, enorm_sq_eq]
    have hLHS : ENNReal.ofReal r * (ENNReal.ofReal ((1 + r ^ 2) ^ m) * (4 * ENNReal.ofReal (‖q r‖ ^ 2))) =
        ENNReal.ofReal (r * ((1 + r ^ 2) ^ m * (4 * ‖q r‖ ^ 2))) := by
      rw [ENNReal.ofReal_mul hr0.le, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by norm_num),
        ENNReal.ofReal_ofNat]
    rw [hLHS, ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have hCr := hC r
    unfold Blueprint.Planar.gaussianWeightInv
    have hpi : 0 < Real.pi := Real.pi_pos
    have e : C / Real.pi * (‖q r‖ ^ 2 * (4 * Real.pi * Real.exp (r ^ 2 / 4)) * r) =
        r * (C * Real.exp (r ^ 2 / 4) * (4 * ‖q r‖ ^ 2)) := by
      field_simp
    rw [e]
    have : 0 ≤ 4 * ‖q r‖ ^ 2 := by positivity
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hCr this) hr0.le
  refine ⟨hG.mono_ac (withDensity_absolutelyContinuous _ _), ?_⟩
  rw [eLpNorm_two_eq]
  exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hlint.ne

end UnforcedLeray.Short.IIb.PlanarModesHelp
