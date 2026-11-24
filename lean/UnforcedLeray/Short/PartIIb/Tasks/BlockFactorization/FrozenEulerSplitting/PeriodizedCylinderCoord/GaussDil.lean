import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F2_3
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F2_3_1_2.Polar
import UnforcedLeray.Lib.Gaussian.PeriodizationCell
import UnforcedLeray.Lib.Gaussian.Absorb
import UnforcedLeray.Lib.CylinderB.Periodize

/-!
# Helper 1 for `PartII-b:F2/3/2` (`PeriodizedCylinderCoord`): Gaussian bounds for dilated modes

Source of record: `the November 2 reference manuscript`, lines 931–953, 2167–2171,
2347–2358.

Establishes measurability, 90-degree antisymmetry (zero plane integral), uniform Gaussian `L²`
bounds, and `L¹(ℝ²)` integrability for `dilPlanarMode q a` over `a ∈ [1, A]`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace UnforcedLeray.Short.IIb.PeriodizedCylCoordAux

open UnforcedLeray.Short.IIb

lemma periodizePlanar_eq_cylPeriodize (c : ℝ) (g : B0579.Plane → ℂ) (x : B0579.Plane) :
    periodizePlanar c g x = UnforcedLeray.Cyl.periodize c g x := by
  unfold periodizePlanar UnforcedLeray.Cyl.periodize
  rw [← (Equiv.neg ℤ).tsum_eq]
  congr 1
  funext n
  simp [sub_eq_add_neg]

lemma cell_eq_cylCell (c : ℝ) : B0579.cell c = UnforcedLeray.Cyl.cell c := by
  unfold B0579.cell UnforcedLeray.Cyl.cell
  rw [neg_div]

lemma planarMode2D_eq_piecewise (q : Blueprint.Planar.Profile) (y : B0579.Plane) :
    planarMode2D q y = (Ioi (0 : ℝ)).piecewise q 0 (PlanarModesHelp.rho y) * angTwoPlanar y := by
  unfold planarMode2D PlanarModesHelp.rho angTwoPlanar
  by_cases hy : y.1 ^ 2 + y.2 ^ 2 = 0
  · simp [hy]
  · have hpos : 0 < y.1 ^ 2 + y.2 ^ 2 :=
      lt_of_le_of_ne (by positivity) (Ne.symm hy)
    have hr : Real.sqrt (y.1 ^ 2 + y.2 ^ 2) ∈ Ioi (0 : ℝ) := Real.sqrt_pos.mpr hpos
    rw [piecewise_eq_of_mem _ _ _ hr]

lemma measurable_angTwoPlanar : Measurable angTwoPlanar := by
  unfold angTwoPlanar
  fun_prop

lemma measurable_planarMode2D {q : Blueprint.Planar.Profile} (hqc : ContinuousOn q (Ioi 0)) :
    Measurable (planarMode2D q) := by
  have hpw : Measurable ((Ioi (0 : ℝ)).piecewise q 0) :=
    hqc.measurable_piecewise continuousOn_const measurableSet_Ioi
  have heq : planarMode2D q =
      fun y => (Ioi (0 : ℝ)).piecewise q 0 (PlanarModesHelp.rho y) * angTwoPlanar y :=
    funext (planarMode2D_eq_piecewise q)
  rw [heq]
  exact (hpw.comp PlanarModesHelp.measurable_rho).mul measurable_angTwoPlanar

lemma measurable_dilPlanarMode {q : Blueprint.Planar.Profile} (hqc : ContinuousOn q (Ioi 0))
    (a : ℝ) : Measurable (dilPlanarMode q a) := by
  unfold dilPlanarMode
  have hsh : Measurable (fun x : B0579.Plane => (x.1 / Real.sqrt a, x.2 / Real.sqrt a)) :=
    (measurable_fst.div_const _).prodMk (measurable_snd.div_const _)
  exact measurable_const.mul ((measurable_planarMode2D hqc).comp hsh)

lemma angTwoPlanar_rot90 (y : B0579.Plane) :
    angTwoPlanar (-y.2, y.1) = -angTwoPlanar y := by
  unfold angTwoPlanar
  have hsq : (-y.2) ^ 2 + y.1 ^ 2 = y.1 ^ 2 + y.2 ^ 2 := by ring
  have hnum : (((-y.2 : ℝ) : ℂ) + (y.1 : ℂ) * Complex.I) ^ 2 =
      -(((y.1 : ℂ) + (y.2 : ℂ) * Complex.I) ^ 2) := by
    calc (((-y.2 : ℝ) : ℂ) + (y.1 : ℂ) * Complex.I) ^ 2
        = (Complex.I * ((y.1 : ℂ) + (y.2 : ℂ) * Complex.I)) ^ 2 := by
            congr 1; push_cast; linear_combination -(y.2 : ℂ) * Complex.I_sq
      _ = Complex.I ^ 2 * ((y.1 : ℂ) + (y.2 : ℂ) * Complex.I) ^ 2 := mul_pow _ _ 2
      _ = -(((y.1 : ℂ) + (y.2 : ℂ) * Complex.I) ^ 2) := by rw [Complex.I_sq, neg_one_mul]
  dsimp only
  rw [hsq, hnum, neg_div]

lemma dilPlanarMode_rot90 (q : Blueprint.Planar.Profile) (a : ℝ) (x : B0579.Plane) :
    dilPlanarMode q a (-x.2, x.1) = -dilPlanarMode q a x := by
  unfold dilPlanarMode planarMode2D
  have h1 : (-x.2) / Real.sqrt a = -(x.2 / Real.sqrt a) := neg_div _ _
  have hsq : (-(x.2 / Real.sqrt a)) ^ 2 + (x.1 / Real.sqrt a) ^ 2 =
      (x.1 / Real.sqrt a) ^ 2 + (x.2 / Real.sqrt a) ^ 2 := by ring
  dsimp only
  rw [h1, hsq]
  have hang := angTwoPlanar_rot90 (x.1 / Real.sqrt a, x.2 / Real.sqrt a)
  dsimp only at hang
  rw [hang, mul_neg, mul_neg]

lemma integral_dilPlanarMode_eq_zero (q : Blueprint.Planar.Profile) (a : ℝ) :
    (∫ x : B0579.Plane, dilPlanarMode q a x) = 0 := by
  let R : ℝ × ℝ ≃ᵐ ℝ × ℝ :=
    (MeasurableEquiv.prodComm).trans
      (MeasurableEquiv.prodCongr (MeasurableEquiv.neg ℝ) (MeasurableEquiv.refl ℝ))
  have h1 : MeasurePreserving (Prod.swap : ℝ × ℝ → ℝ × ℝ) (volume : Measure (ℝ × ℝ)) volume := by
    rw [Measure.volume_eq_prod]
    exact Measure.measurePreserving_swap
  have h2 : MeasurePreserving (Prod.map (fun x : ℝ => -x) id)
      (volume : Measure (ℝ × ℝ)) volume := by
    rw [Measure.volume_eq_prod]
    exact (Measure.measurePreserving_neg (volume : Measure ℝ)).prod (MeasurePreserving.id _)
  have hRm : MeasurePreserving R volume volume := by
    have hfun : ⇑R = Prod.map (fun x : ℝ => -x) id ∘ Prod.swap := rfl
    rw [hfun]
    exact h2.comp h1
  have hc : (∫ y, dilPlanarMode q a (R y)) = ∫ y, dilPlanarMode q a y :=
    hRm.integral_comp' (dilPlanarMode q a)
  have hodd : ∀ y : ℝ × ℝ, dilPlanarMode q a (R y) = -dilPlanarMode q a y :=
    fun y => dilPlanarMode_rot90 q a y
  simp only [hodd, integral_neg] at hc
  linear_combination -hc / 2

lemma norm_angTwoPlanar_le (x : B0579.Plane) : ‖angTwoPlanar x‖ ≤ 1 := by
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

lemma norm_planarMode2D_le (q : Blueprint.Planar.Profile) (y : B0579.Plane) :
    ‖planarMode2D q y‖ ≤ ‖q (PlanarModesHelp.rho y)‖ := by
  unfold planarMode2D PlanarModesHelp.rho
  rw [norm_mul]
  calc ‖q (Real.sqrt (y.1 ^ 2 + y.2 ^ 2))‖ * ‖angTwoPlanar y‖
      ≤ ‖q (Real.sqrt (y.1 ^ 2 + y.2 ^ 2))‖ * 1 :=
        mul_le_mul_of_nonneg_left (norm_angTwoPlanar_le y) (norm_nonneg _)
    _ = ‖q (Real.sqrt (y.1 ^ 2 + y.2 ^ 2))‖ := mul_one _

lemma lintegral_planarMode2D_gauss_le {q : Blueprint.Planar.Profile}
    (hq : Blueprint.Planar.MemXG q) :
    ∫⁻ y : B0579.Plane, ‖planarMode2D q y‖ₑ ^ 2 *
        ENNReal.ofReal (Real.exp ((y.1 ^ 2 + y.2 ^ 2) / 4)) ≤
      ENNReal.ofReal (Blueprint.Planar.gaussianNorm q ^ 2) := by
  let F : ℝ → ℝ≥0∞ := fun r => ‖q r‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (r ^ 2 / 4))
  have hFm : AEMeasurable F (volume.restrict (Ioi (0 : ℝ))) :=
    (hq.measurable.enorm.pow_const 2).mul (by fun_prop)
  have hpt : ∀ y : B0579.Plane,
      ‖planarMode2D q y‖ₑ ^ 2 * ENNReal.ofReal (Real.exp ((y.1 ^ 2 + y.2 ^ 2) / 4)) ≤
        F (PlanarModesHelp.rho y) := by
    intro y
    dsimp [F]
    have hsq : (PlanarModesHelp.rho y) ^ 2 = y.1 ^ 2 + y.2 ^ 2 := by
      unfold PlanarModesHelp.rho
      exact Real.sq_sqrt (by positivity)
    rw [hsq]
    gcongr
    exact enorm_le_iff_norm_le.mpr (norm_planarMode2D_le q y)
  calc ∫⁻ y : B0579.Plane, ‖planarMode2D q y‖ₑ ^ 2 *
          ENNReal.ofReal (Real.exp ((y.1 ^ 2 + y.2 ^ 2) / 4))
      ≤ ∫⁻ y : B0579.Plane, F (PlanarModesHelp.rho y) := lintegral_mono hpt
    _ = ENNReal.ofReal (2 * Real.pi) * ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal r * F r :=
        PlanarModesHelp.lint_radial F hFm
    _ = ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (2 * Real.pi) * (ENNReal.ofReal r * F r) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ∫⁻ r in Ioi (0 : ℝ),
          ENNReal.ofReal (‖q r‖ ^ 2 * Blueprint.Planar.gaussianWeightInv r * r) := by
        refine setLIntegral_mono' measurableSet_Ioi fun r (hr : 0 < r) => ?_
        dsimp [F]
        rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _),
          ← ENNReal.ofReal_mul (sq_nonneg _), ← ENNReal.ofReal_mul hr.le,
          ← ENNReal.ofReal_mul (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        unfold Blueprint.Planar.gaussianWeightInv
        have hpi : 0 ≤ Real.pi := Real.pi_pos.le
        have hexp : 0 ≤ Real.exp (r ^ 2 / 4) := (Real.exp_pos _).le
        nlinarith [sq_nonneg ‖q r‖, mul_nonneg (mul_nonneg hpi hexp) (mul_nonneg (sq_nonneg ‖q r‖) hr.le)]
    _ = ENNReal.ofReal (Blueprint.Planar.gaussianNorm q ^ 2) := by
        have hnonneg : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))]
            fun r : ℝ => ‖q r‖ ^ 2 * Blueprint.Planar.gaussianWeightInv r * r := by
          refine (ae_restrict_mem measurableSet_Ioi).mono fun r (hr : 0 < r) => ?_
          have : 0 ≤ Blueprint.Planar.gaussianWeightInv r := by
            unfold Blueprint.Planar.gaussianWeightInv; positivity
          positivity
        rw [← ofReal_integral_eq_lintegral_ofReal hq.integrable hnonneg]
        congr 1
        unfold Blueprint.Planar.gaussianNorm
        exact (Real.sq_sqrt (integral_nonneg_of_ae hnonneg)).symm

lemma lintegral_dilPlanarMode_gauss_le {q : Blueprint.Planar.Profile} {A a : ℝ}
    (ha1 : 1 ≤ a) (haA : a ≤ A) (hq : Blueprint.Planar.MemXG q) :
    ∫⁻ x : B0579.Plane, ‖dilPlanarMode q a x‖ₑ ^ 2 *
        ENNReal.ofReal (Real.exp ((x.1 ^ 2 + x.2 ^ 2) / (4 * A))) ≤
      ENNReal.ofReal (A * Blueprint.Planar.gaussianNorm q ^ 2) := by
  have ha0 : 0 < a := lt_of_lt_of_le one_pos ha1
  have hA0 : 0 < A := lt_of_lt_of_le ha0 haA
  have hsa : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha0
  have hsq : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha0.le
  rw [PlanarModesHelp.lint_smul (Real.sqrt a) hsa.ne']
  rw [hsq]
  have hpt : ∀ y : B0579.Plane,
      ‖dilPlanarMode q a (Real.sqrt a • y)‖ₑ ^ 2 *
        ENNReal.ofReal (Real.exp (((Real.sqrt a • y).1 ^ 2 + (Real.sqrt a • y).2 ^ 2) / (4 * A))) ≤
      ‖planarMode2D q y‖ₑ ^ 2 * ENNReal.ofReal (Real.exp ((y.1 ^ 2 + y.2 ^ 2) / 4)) := by
    intro y
    have harg : ((Real.sqrt a • y).1 / Real.sqrt a, (Real.sqrt a • y).2 / Real.sqrt a) = y := by
      ext <;> simp [mul_div_cancel_left₀ _ hsa.ne']
    have hnorm : ‖dilPlanarMode q a (Real.sqrt a • y)‖ ≤ ‖planarMode2D q y‖ := by
      unfold dilPlanarMode
      rw [harg, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      have ha_pow : a ^ (-2 : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos ha1 (by norm_num)
      calc a ^ (-2 : ℝ) * ‖planarMode2D q y‖
          ≤ 1 * ‖planarMode2D q y‖ := mul_le_mul_of_nonneg_right ha_pow (norm_nonneg _)
        _ = ‖planarMode2D q y‖ := one_mul _
    have hexp : ((Real.sqrt a • y).1 ^ 2 + (Real.sqrt a • y).2 ^ 2) / (4 * A) ≤
        (y.1 ^ 2 + y.2 ^ 2) / 4 := by
      simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      have h1 : (Real.sqrt a * y.1) ^ 2 + (Real.sqrt a * y.2) ^ 2 = a * (y.1 ^ 2 + y.2 ^ 2) := by
        calc (Real.sqrt a * y.1) ^ 2 + (Real.sqrt a * y.2) ^ 2
            = Real.sqrt a ^ 2 * (y.1 ^ 2 + y.2 ^ 2) := by ring
          _ = a * (y.1 ^ 2 + y.2 ^ 2) := by rw [hsq]
      rw [h1, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [sq_nonneg y.1, sq_nonneg y.2]
    gcongr
    exact enorm_le_iff_norm_le.mpr hnorm
  calc ENNReal.ofReal a * ∫⁻ y : B0579.Plane,
          ‖dilPlanarMode q a (Real.sqrt a • y)‖ₑ ^ 2 *
            ENNReal.ofReal (Real.exp (((Real.sqrt a • y).1 ^ 2 + (Real.sqrt a • y).2 ^ 2) / (4 * A)))
      ≤ ENNReal.ofReal A * ∫⁻ y : B0579.Plane,
          ‖planarMode2D q y‖ₑ ^ 2 * ENNReal.ofReal (Real.exp ((y.1 ^ 2 + y.2 ^ 2) / 4)) := by
        exact mul_le_mul' (ENNReal.ofReal_le_ofReal haA) (lintegral_mono hpt)
    _ ≤ ENNReal.ofReal A * ENNReal.ofReal (Blueprint.Planar.gaussianNorm q ^ 2) :=
        mul_le_mul' le_rfl (lintegral_planarMode2D_gauss_le hq)
    _ = ENNReal.ofReal (A * Blueprint.Planar.gaussianNorm q ^ 2) := by
        rw [← ENNReal.ofReal_mul hA0.le]

lemma integrable_dilPlanarMode {q : Blueprint.Planar.Profile} {A a : ℝ}
    (ha1 : 1 ≤ a) (haA : a ≤ A) (hq : Blueprint.Planar.MemXG q) (hqc : ContinuousOn q (Ioi 0)) :
    Integrable (dilPlanarMode q a) volume := by
  have hA0 : 0 < A := lt_of_lt_of_le one_pos (ha1.trans haA)
  refine ⟨(measurable_dilPlanarMode hqc a).aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  have hpt : ∀ x : B0579.Plane, ‖dilPlanarMode q a x‖ₑ ≤
      ENNReal.ofReal (1 / 2) *
        (‖dilPlanarMode q a x‖ₑ ^ 2 * ENNReal.ofReal (Real.exp ((x.1 ^ 2 + x.2 ^ 2) / (4 * A))) +
          ENNReal.ofReal (Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (4 * A)))) := by
    intro x
    set u := ‖dilPlanarMode q a x‖
    set w := Real.exp ((x.1 ^ 2 + x.2 ^ 2) / (4 * A))
    set winv := Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (4 * A))
    have hw_pos : 0 < w := Real.exp_pos _
    have hwinv_nn : 0 ≤ winv := (Real.exp_pos _).le
    have hww : w * winv = 1 := by
      dsimp [w, winv]
      rw [← Real.exp_add]
      have : (x.1 ^ 2 + x.2 ^ 2) / (4 * A) + -(x.1 ^ 2 + x.2 ^ 2) / (4 * A) = 0 := by ring
      rw [this, Real.exp_zero]
    have hamgm : u ≤ (1 / 2) * (u ^ 2 * w + winv) := by
      have hsq : 0 ≤ (u * w - 1) ^ 2 := sq_nonneg _
      have hkey : w * ((1 / 2) * (u ^ 2 * w + winv) - u) = (1 / 2) * (u * w - 1) ^ 2 := by
        calc w * ((1 / 2) * (u ^ 2 * w + winv) - u)
            = (1 / 2) * (u ^ 2 * w ^ 2 - 2 * u * w + w * winv) := by ring
          _ = (1 / 2) * (u * w - 1) ^ 2 := by rw [hww]; ring
      have hnonneg : 0 ≤ w * ((1 / 2) * (u ^ 2 * w + winv) - u) := by linarith
      have hsub : 0 ≤ (1 / 2) * (u ^ 2 * w + winv) - u :=
        nonneg_of_mul_nonneg_right hnonneg hw_pos
      linarith
    rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), ← ENNReal.ofReal_mul (sq_nonneg _),
      ← ENNReal.ofReal_add (by positivity) hwinv_nn, ← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal hamgm
  have h1 : (∫⁻ x : B0579.Plane, ‖dilPlanarMode q a x‖ₑ ^ 2 *
      ENNReal.ofReal (Real.exp ((x.1 ^ 2 + x.2 ^ 2) / (4 * A)))) < ⊤ :=
    lt_of_le_of_lt (lintegral_dilPlanarMode_gauss_le ha1 haA hq) ENNReal.ofReal_lt_top
  have h2_int := UnforcedLeray.Gaussian.integrable_gauss_plane hA0
  have h2 : (∫⁻ x : B0579.Plane,
      ENNReal.ofReal (Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (4 * A)))) < ⊤ := by
    refine lt_of_le_of_lt (lintegral_mono fun x => ?_) h2_int.2
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (le_abs_self _)
  have hm1 : Measurable (fun x : B0579.Plane => ‖dilPlanarMode q a x‖ₑ ^ 2 *
      ENNReal.ofReal (Real.exp ((x.1 ^ 2 + x.2 ^ 2) / (4 * A)))) :=
    ((measurable_dilPlanarMode hqc a).enorm.pow_const 2).mul (by fun_prop)
  calc ∫⁻ x : B0579.Plane, ‖dilPlanarMode q a x‖ₑ
      ≤ ∫⁻ x : B0579.Plane, ENNReal.ofReal (1 / 2) *
          (‖dilPlanarMode q a x‖ₑ ^ 2 * ENNReal.ofReal (Real.exp ((x.1 ^ 2 + x.2 ^ 2) / (4 * A))) +
            ENNReal.ofReal (Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (4 * A)))) :=
        lintegral_mono hpt
    _ = ENNReal.ofReal (1 / 2) *
          ((∫⁻ x : B0579.Plane, ‖dilPlanarMode q a x‖ₑ ^ 2 *
            ENNReal.ofReal (Real.exp ((x.1 ^ 2 + x.2 ^ 2) / (4 * A)))) +
          (∫⁻ x : B0579.Plane,
            ENNReal.ofReal (Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (4 * A))))) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_left hm1]
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.add_lt_top.mpr ⟨h1, h2⟩)

end UnforcedLeray.Short.IIb.PeriodizedCylCoordAux
