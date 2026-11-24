import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2_G3_1_4_3
import UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Pair.Of
import UnforcedLeray.Lib.Gaussian.PeriodizationCell
import UnforcedLeray.Lib.Gaussian.Absorb
import UnforcedLeray.Lib.CylinderB.Periodize
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_data_1.PlaneZero
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_data_1.GaussMeasurable
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_data_1.PeriodizeIntegral
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_data_1.PeriodizeMeas

/-!
# `PartIII-b:IIIb-D3/2/G3/1/4/3/2`: `PeriodizePlanarModeXmc`

Source of record: `the November 2 reference manuscript`, lines 3127–3130,
4445–4447.

Proves `periodizePlanarModeXmc_of : PeriodizePlanarModeXmc`: for `m > 8` and `c ≥ 1`, the
periodization `f ↦ IIIa.periodizeC c (IIIa.planarMode f)` maps continuous `MemXG` profiles into
`Xmc c m` with Lipschitz norm bound `‖qf - qg‖ ≤ C_m * gaussianNorm (fun r => f r - g r)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff ComplexConjugate NNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif.G3

open FlatSettingInst

/-! ## Step 1: Measurability, symmetry, and linearity of `IIIa.planarMode` -/

private lemma planarMode_eq_piecewise (f : Profile) (y : ℝ × ℝ) :
    IIIa.planarMode f y = (Ioi (0 : ℝ)).piecewise f 0 (planeR y) * IIIa.angTwo y := by
  unfold IIIa.planarMode planeR IIIa.angTwo
  by_cases hy : y.1 ^ 2 + y.2 ^ 2 = 0
  · simp [hy]
  · have hpos : 0 < y.1 ^ 2 + y.2 ^ 2 :=
      lt_of_le_of_ne (by positivity) (Ne.symm hy)
    have hr : Real.sqrt (y.1 ^ 2 + y.2 ^ 2) ∈ Ioi (0 : ℝ) := Real.sqrt_pos.mpr hpos
    rw [piecewise_eq_of_mem _ _ _ hr]

private lemma measurable_planarMode {f : Profile} (hfc : ContinuousOn f (Ioi 0)) :
    Measurable (IIIa.planarMode f) := by
  have hpw : Measurable ((Ioi (0 : ℝ)).piecewise f 0) :=
    hfc.measurable_piecewise continuousOn_const measurableSet_Ioi
  have heq : IIIa.planarMode f =
      fun y => (Ioi (0 : ℝ)).piecewise f 0 (planeR y) * IIIa.angTwo y :=
    funext (planarMode_eq_piecewise f)
  rw [heq]
  exact (hpw.comp gm_planeR_measurable).mul gm_angTwo_measurable

private lemma planarMode_even (f : Profile) (x : ℝ × ℝ) :
    IIIa.planarMode f (-x) = IIIa.planarMode f x := by
  unfold IIIa.planarMode
  rw [angTwo_neg]
  simp only [Prod.fst_neg, Prod.snd_neg, neg_sq]

private lemma planarMode_rot90 (f : Profile) (y : ℝ × ℝ) :
    IIIa.planarMode f (-y.2, y.1) = -IIIa.planarMode f y := by
  unfold IIIa.planarMode IIIa.angTwo
  have hsq : (-y.2) ^ 2 + y.1 ^ 2 = y.1 ^ 2 + y.2 ^ 2 := by ring
  have hnum : (((-y.2 : ℝ) : ℂ) + (y.1 : ℂ) * Complex.I) ^ 2 =
      -(((y.1 : ℂ) + (y.2 : ℂ) * Complex.I) ^ 2) := by
    calc (((-y.2 : ℝ) : ℂ) + (y.1 : ℂ) * Complex.I) ^ 2
        = (Complex.I * ((y.1 : ℂ) + (y.2 : ℂ) * Complex.I)) ^ 2 := by
            congr 1; push_cast; linear_combination -(y.2 : ℂ) * Complex.I_sq
      _ = Complex.I ^ 2 * ((y.1 : ℂ) + (y.2 : ℂ) * Complex.I) ^ 2 := mul_pow _ _ 2
      _ = -(((y.1 : ℂ) + (y.2 : ℂ) * Complex.I) ^ 2) := by rw [Complex.I_sq, neg_one_mul]
  dsimp only
  rw [hsq, hnum, neg_div, mul_neg]

private lemma integral_planarMode_eq_zero (f : Profile) :
    (∫ y : ℝ × ℝ, IIIa.planarMode f y) = 0 := by
  let R : ℝ × ℝ ≃ᵐ ℝ × ℝ :=
    (MeasurableEquiv.prodComm).trans
      (MeasurableEquiv.prodCongr (MeasurableEquiv.neg ℝ) (MeasurableEquiv.refl ℝ))
  have hRapp : ∀ y : ℝ × ℝ, R y = (-y.2, y.1) := fun _ => rfl
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
  have hc : (∫ y, IIIa.planarMode f (R y)) = ∫ y, IIIa.planarMode f y :=
    hRm.integral_comp' (IIIa.planarMode f)
  have hodd : ∀ y : ℝ × ℝ, IIIa.planarMode f (R y) = -IIIa.planarMode f y := fun y =>
    planarMode_rot90 f y
  simp only [hodd, integral_neg] at hc
  linear_combination -hc / 2

private lemma planarMode_sub (f g : Profile) (y : ℝ × ℝ) :
    IIIa.planarMode (fun r => f r - g r) y = IIIa.planarMode f y - IIIa.planarMode g y := by
  unfold IIIa.planarMode
  exact sub_mul _ _ _

private lemma memXG_sub {f g : Profile} (hf : MemXG f) (hg : MemXG g) :
    MemXG (fun r => f r - g r) where
  measurable := hf.measurable.sub hg.measurable
  integrable := by
    have hdom : IntegrableOn (fun r : ℝ =>
        2 * (‖f r‖ ^ 2 * gaussianWeightInv r * r + ‖g r‖ ^ 2 * gaussianWeightInv r * r))
        (Ioi 0) := (hf.integrable.add hg.integrable).const_mul 2
    refine hdom.mono' ?_ ?_
    · have h1 : AEStronglyMeasurable (fun r : ℝ => ‖f r - g r‖ ^ 2) (volume.restrict (Ioi 0)) :=
        ((hf.measurable.sub hg.measurable).norm.pow 2)
      have h2 : Continuous (fun r : ℝ => gaussianWeightInv r) := by
        unfold gaussianWeightInv
        fun_prop
      exact (h1.mul h2.aestronglyMeasurable).mul continuous_id.aestronglyMeasurable
    · refine (ae_restrict_mem measurableSet_Ioi).mono fun r (hr : 0 < r) => ?_
      have hw : 0 ≤ gaussianWeightInv r * r := by
        unfold gaussianWeightInv
        positivity
      have hnorm : ‖f r - g r‖ ^ 2 ≤ 2 * (‖f r‖ ^ 2 + ‖g r‖ ^ 2) := by
        have htri : ‖f r - g r‖ ≤ ‖f r‖ + ‖g r‖ := norm_sub_le (f r) (g r)
        have hsq : (‖f r - g r‖) ^ 2 ≤ (‖f r‖ + ‖g r‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) htri 2
        nlinarith [sq_nonneg (‖f r‖ - ‖g r‖)]
      have hnonneg : 0 ≤ ‖f r - g r‖ ^ 2 * gaussianWeightInv r * r := by
        rw [mul_assoc]
        exact mul_nonneg (sq_nonneg _) hw
      rw [Real.norm_of_nonneg hnonneg]
      calc ‖f r - g r‖ ^ 2 * gaussianWeightInv r * r
          = ‖f r - g r‖ ^ 2 * (gaussianWeightInv r * r) := by ring
        _ ≤ (2 * (‖f r‖ ^ 2 + ‖g r‖ ^ 2)) * (gaussianWeightInv r * r) :=
            mul_le_mul_of_nonneg_right hnorm hw
        _ = 2 * (‖f r‖ ^ 2 * gaussianWeightInv r * r + ‖g r‖ ^ 2 * gaussianWeightInv r * r) := by
            ring

/-! ## Step 2 & 3: Weighted plane `L²` identity and `L¹` integrability of `IIIa.planarMode f` -/

private lemma lintegral_planarMode_gauss {f : Profile} (hf : MemXG f) :
    ∫⁻ y : ℝ × ℝ, ‖IIIa.planarMode f y‖ₑ ^ 2 *
        ENNReal.ofReal (4 * Real.pi * Real.exp ((y.1 ^ 2 + y.2 ^ 2) / 4)) =
      ENNReal.ofReal (2 * Real.pi * gaussianNorm f ^ 2) := by
  have hpol := lintegral_comp_polarCoord_symm (fun y : ℝ × ℝ =>
    ‖IIIa.planarMode f y‖ₑ ^ 2 *
      ENNReal.ofReal (4 * Real.pi * Real.exp ((y.1 ^ 2 + y.2 ^ 2) / 4)))
  rw [← hpol, pz_target]
  have hmeas_set : MeasurableSet (Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi) :=
    measurableSet_Ioi.prod measurableSet_Ioo
  have hcongr : ∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
      ENNReal.ofReal p.1 • (‖IIIa.planarMode f (polarCoord.symm p)‖ₑ ^ 2 *
        ENNReal.ofReal (4 * Real.pi * Real.exp (((polarCoord.symm p).1 ^ 2 +
          (polarCoord.symm p).2 ^ 2) / 4))) =
    ∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
      ENNReal.ofReal (‖f p.1‖ ^ 2 * gaussianWeightInv p.1 * p.1) * (1 : ℝ≥0∞) := by
    refine setLIntegral_congr_fun hmeas_set (fun p hp => ?_)
    have hr : 0 < p.1 := hp.1
    rw [pz_symm]
    have hsq : (p.1 * Real.cos p.2) ^ 2 + (p.1 * Real.sin p.2) ^ 2 = p.1 ^ 2 := by
      linear_combination p.1 ^ 2 * Real.cos_sq_add_sin_sq p.2
    have hF : IIIa.planarMode f (p.1 * Real.cos p.2, p.1 * Real.sin p.2) =
        f p.1 * Complex.exp (2 * Complex.I * (p.2 : ℂ)) := by
      unfold IIIa.planarMode
      have hpr := pz_planeR_polar p.1 p.2 hr
      unfold planeR at hpr
      rw [hpr, pz_angTwo_polar p.1 p.2 hr]
    have hnormF : ‖IIIa.planarMode f (p.1 * Real.cos p.2, p.1 * Real.sin p.2)‖ = ‖f p.1‖ := by
      rw [hF, norm_mul, show 2 * Complex.I * (p.2 : ℂ) = ((2 * p.2 : ℝ) : ℂ) * Complex.I by
        push_cast; ring, Complex.norm_exp_ofReal_mul_I, mul_one]
    have hen : ‖IIIa.planarMode f (p.1 * Real.cos p.2, p.1 * Real.sin p.2)‖ₑ ^ 2 =
        ENNReal.ofReal (‖f p.1‖ ^ 2) := by
      rw [← ofReal_norm, hnormF, ENNReal.ofReal_pow (norm_nonneg _)]
    rw [smul_eq_mul, hen, hsq]
    change ENNReal.ofReal p.1 * (ENNReal.ofReal (‖f p.1‖ ^ 2) *
      ENNReal.ofReal (gaussianWeightInv p.1)) =
      ENNReal.ofReal (‖f p.1‖ ^ 2 * gaussianWeightInv p.1 * p.1) * 1
    have hw0 : 0 ≤ gaussianWeightInv p.1 := by unfold gaussianWeightInv; positivity
    rw [mul_one, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hr.le]
    congr 1
    ring
  rw [hcongr, Measure.volume_eq_prod, ← Measure.prod_restrict]
  have hae_r : AEMeasurable (fun r : ℝ => ENNReal.ofReal (‖f r‖ ^ 2 * gaussianWeightInv r * r))
      (volume.restrict (Ioi 0)) :=
    hf.integrable.1.aemeasurable.ennreal_ofReal
  rw [lintegral_prod_mul hae_r aemeasurable_const]
  have hθ : (∫⁻ _ : ℝ in Ioo (-Real.pi) Real.pi, (1 : ℝ≥0∞)) = ENNReal.ofReal (2 * Real.pi) := by
    rw [setLIntegral_one, Real.volume_Ioo]
    congr 1
    ring
  have hr_int : (∫⁻ r : ℝ in Ioi (0 : ℝ), ENNReal.ofReal (‖f r‖ ^ 2 * gaussianWeightInv r * r)) =
      ENNReal.ofReal (gaussianNorm f ^ 2) := by
    have hnonneg : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))]
        fun r : ℝ => ‖f r‖ ^ 2 * gaussianWeightInv r * r := by
      refine (ae_restrict_mem measurableSet_Ioi).mono fun r (hr : 0 < r) => ?_
      have : 0 ≤ gaussianWeightInv r := by unfold gaussianWeightInv; positivity
      positivity
    rw [← ofReal_integral_eq_lintegral_ofReal hf.integrable hnonneg]
    congr 1
    unfold gaussianNorm
    exact (Real.sq_sqrt (integral_nonneg_of_ae hnonneg)).symm
  rw [hr_int, hθ, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

private lemma integrable_planarMode {f : Profile} (hf : MemXG f) (hfc : ContinuousOn f (Ioi 0)) :
    Integrable (IIIa.planarMode f) volume := by
  refine ⟨(measurable_planarMode hfc).aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  have hpt : ∀ y : ℝ × ℝ, ‖IIIa.planarMode f y‖ₑ ≤
      ENNReal.ofReal (1 / 2) * (‖IIIa.planarMode f y‖ₑ ^ 2 *
        ENNReal.ofReal (4 * Real.pi * Real.exp ((y.1 ^ 2 + y.2 ^ 2) / 4)) +
        ENNReal.ofReal ((4 * Real.pi)⁻¹ * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 4))) := by
    intro y
    set u := ‖IIIa.planarMode f y‖
    set w := 4 * Real.pi * Real.exp ((y.1 ^ 2 + y.2 ^ 2) / 4)
    set winv := (4 * Real.pi)⁻¹ * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 4)
    have hw_pos : 0 < w := by unfold w; positivity
    have hwinv_pos : 0 ≤ winv := by unfold winv; positivity
    have hww : w * winv = 1 := by
      unfold w winv
      have hexp : Real.exp ((y.1 ^ 2 + y.2 ^ 2) / 4) * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 4) = 1 := by
        rw [← Real.exp_add]
        have : (y.1 ^ 2 + y.2 ^ 2) / 4 + -(y.1 ^ 2 + y.2 ^ 2) / 4 = 0 := by ring
        rw [this, Real.exp_zero]
      calc 4 * Real.pi * Real.exp ((y.1 ^ 2 + y.2 ^ 2) / 4) *
            ((4 * Real.pi)⁻¹ * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 4))
          = (4 * Real.pi * (4 * Real.pi)⁻¹) *
            (Real.exp ((y.1 ^ 2 + y.2 ^ 2) / 4) * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 4)) := by ring
        _ = 1 := by rw [mul_inv_cancel₀ (by positivity), hexp, one_mul]
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
    rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_add (by positivity) hwinv_pos, ← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal hamgm
  have h1 : (∫⁻ y : ℝ × ℝ, ‖IIIa.planarMode f y‖ₑ ^ 2 *
      ENNReal.ofReal (4 * Real.pi * Real.exp ((y.1 ^ 2 + y.2 ^ 2) / 4))) < ⊤ := by
    rw [lintegral_planarMode_gauss hf]
    exact ENNReal.ofReal_lt_top
  have h2_int : Integrable (fun y : ℝ × ℝ =>
      (4 * Real.pi)⁻¹ * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 4)) volume := by
    have hg := (UnforcedLeray.Gaussian.integrable_gauss_plane one_pos).const_mul (4 * Real.pi)⁻¹
    refine hg.congr (Eventually.of_forall fun y => ?_)
    simp [mul_one]
  have h2 : (∫⁻ y : ℝ × ℝ,
      ENNReal.ofReal ((4 * Real.pi)⁻¹ * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 4))) < ⊤ := by
    refine lt_of_le_of_lt (lintegral_mono fun y => ?_) h2_int.2
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (le_abs_self _)
  have hm1 : Measurable (fun y : ℝ × ℝ => ‖IIIa.planarMode f y‖ₑ ^ 2 *
      ENNReal.ofReal (4 * Real.pi * Real.exp ((y.1 ^ 2 + y.2 ^ 2) / 4))) :=
    ((measurable_planarMode hfc).enorm.pow_const 2).mul (by fun_prop)
  calc ∫⁻ y : ℝ × ℝ, ‖IIIa.planarMode f y‖ₑ
      ≤ ∫⁻ y : ℝ × ℝ, ENNReal.ofReal (1 / 2) * (‖IIIa.planarMode f y‖ₑ ^ 2 *
          ENNReal.ofReal (4 * Real.pi * Real.exp ((y.1 ^ 2 + y.2 ^ 2) / 4)) +
          ENNReal.ofReal ((4 * Real.pi)⁻¹ * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 4))) :=
        lintegral_mono hpt
    _ = ENNReal.ofReal (1 / 2) *
          ((∫⁻ y : ℝ × ℝ, ‖IIIa.planarMode f y‖ₑ ^ 2 *
            ENNReal.ofReal (4 * Real.pi * Real.exp ((y.1 ^ 2 + y.2 ^ 2) / 4))) +
          (∫⁻ y : ℝ × ℝ,
            ENNReal.ofReal ((4 * Real.pi)⁻¹ * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 4)))) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_left hm1]
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.add_lt_top.mpr ⟨h1, h2⟩)

/-! ## A.e. summability and measurability of `IIIa.periodizeC` -/

private lemma cell_eq_cylCell (c : ℝ) : B0579.cell c = UnforcedLeray.Cyl.cell c := by
  unfold B0579.cell UnforcedLeray.Cyl.cell
  rw [neg_div]

private lemma ae_summable_periodizeC {c : ℝ} (hc : 0 < c) {F : ℝ × ℝ → ℂ}
    (hFm : Measurable F) (hFi : Integrable F volume) :
    ∀ᵐ x ∂(volume.restrict (B0579.cell c)),
      Summable (fun n : ℤ => F (x.1 - n * c, x.2)) := by
  have hlin : ∫⁻ x in B0579.cell c, (∑' n : ℤ, ‖F (x.1 - n * c, x.2)‖ₑ) = ∫⁻ y, ‖F y‖ₑ := by
    rw [cell_eq_cylCell]
    exact UnforcedLeray.Cyl.lintegral_cell_periodize hc hFm.enorm
  have hmeas_sum : Measurable (fun x : ℝ × ℝ => ∑' n : ℤ, ‖F (x.1 - n * c, x.2)‖ₑ) :=
    Measurable.tsum fun n => hFm.enorm.comp (UnforcedLeray.Cyl.measurable_shift c n)
  have hlt : ∀ᵐ x ∂(volume.restrict (B0579.cell c)),
      (∑' n : ℤ, ‖F (x.1 - n * c, x.2)‖ₑ) < ⊤ :=
    ae_lt_top hmeas_sum (by rw [hlin]; exact hFi.2.ne)
  filter_upwards [hlt] with x hx
  have hnn : Summable (fun n : ℤ => ‖F (x.1 - n * c, x.2)‖₊) :=
    ENNReal.tsum_coe_ne_top_iff_summable.mp hx.ne
  exact Summable.of_nnnorm hnn

private lemma aestronglyMeasurable_periodizeC {c m : ℝ} (hc : 0 < c) {F : ℝ × ℝ → ℂ}
    (hFm : Measurable F) (hFi : Integrable F volume) :
    AEStronglyMeasurable (IIIa.periodizeC c F) (B0579.cellMeasure c m) := by
  have hae : ∀ᵐ x ∂(B0579.cellMeasure c m),
      Summable (fun n : ℤ => F (x.1 - n * c, x.2)) :=
    (B0579.cellMeasure_ac c m).ae_le (ae_summable_periodizeC hc hFm hFi)
  refine aestronglyMeasurable_of_tendsto_ae (u := (atTop : Filter (Finset ℤ)))
    (f := fun (s : Finset ℤ) (x : ℝ × ℝ) => ∑ n ∈ s, F (x.1 - n * c, x.2))
    (fun s => ?_) ?_
  · exact (Finset.measurable_sum s fun n _ =>
      hFm.comp (UnforcedLeray.Cyl.measurable_shift c n)).aestronglyMeasurable
  · filter_upwards [hae] with x hx
    exact hx.hasSum

/-! ## Step 4: Cell shift inequality, Cauchy-Schwarz on `ℤ`, and weighted `L²` bound -/

private lemma cell_shift_sq_ge {c : ℝ} (hc1 : 1 ≤ c) {x : ℝ × ℝ} (hx : x ∈ B0579.cell c)
    (n : ℤ) :
    (x.1 ^ 2 + x.2 ^ 2) / 2 + (n : ℝ) ^ 2 / 8 ≤ (x.1 - n * c) ^ 2 + x.2 ^ 2 := by
  have hx1_lo : -(c / 2) ≤ x.1 := hx.1.1
  have hx1_hi : x.1 ≤ c / 2 := hx.1.2.le
  have hx1_sq : x.1 ^ 2 ≤ c ^ 2 / 4 := by nlinarith
  have hc_sq : 1 ≤ c ^ 2 := by nlinarith
  have h1 : x.1 ^ 2 / 2 + (n : ℝ) ^ 2 / 8 ≤ (x.1 - n * c) ^ 2 := by
    by_cases hn0 : n = 0
    · subst hn0
      simp only [Int.cast_zero, zero_mul, sub_zero, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, zero_pow, zero_div, add_zero]
      linarith [sq_nonneg x.1]
    · have hnc : (n : ℝ) ^ 2 * c ^ 2 / 4 ≤ (x.1 - n * c) ^ 2 := by
        rcases lt_or_gt_of_ne hn0 with hlt | hgt
        · have hn_le : n ≤ -1 := Int.le_sub_one_of_lt hlt
          have hnr : (n : ℝ) ≤ -1 := by exact_mod_cast hn_le
          have h1' : (n : ℝ) * c / 2 ≤ -(c / 2) := by nlinarith
          have h2' : -(n : ℝ) * c / 2 ≤ x.1 - (n : ℝ) * c := by linarith
          have h3' : 0 ≤ -(n : ℝ) * c / 2 := by nlinarith
          nlinarith
        · have hn_ge : 1 ≤ n := hgt
          have hnr : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_ge
          have h1' : c / 2 ≤ (n : ℝ) * c / 2 := by nlinarith
          have h2' : (n : ℝ) * c / 2 ≤ (n : ℝ) * c - x.1 := by linarith
          have h3' : 0 ≤ (n : ℝ) * c / 2 := by nlinarith
          nlinarith
      have hn_sq : 1 ≤ (n : ℝ) ^ 2 := by
        have h1 : 1 ≤ |n| := Int.one_le_abs hn0
        have h2 : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast h1
        nlinarith [sq_abs (n : ℝ)]
      have hpart1 : x.1 ^ 2 / 2 ≤ (n : ℝ) ^ 2 * c ^ 2 / 8 := by
        calc x.1 ^ 2 / 2 ≤ c ^ 2 / 8 := by linarith
          _ = 1 * c ^ 2 / 8 := by ring
          _ ≤ (n : ℝ) ^ 2 * c ^ 2 / 8 := by nlinarith
      have hpart2 : (n : ℝ) ^ 2 / 8 ≤ (n : ℝ) ^ 2 * c ^ 2 / 8 := by
        nlinarith
      linarith
  linarith [sq_nonneg x.2]

private lemma periodizeC_enorm_sq_le (c : ℝ) (F : ℝ × ℝ → ℂ) (x : ℝ × ℝ) :
    let w : ℤ → ℝ := fun n => Real.exp (-(1 / 32 * (n : ℝ) ^ 2))
    let S : ℝ := ∑' n : ℤ, w n
    ‖IIIa.periodizeC c F x‖ₑ ^ 2 ≤
      ENNReal.ofReal S *
        ∑' n : ℤ, ENNReal.ofReal (Real.exp (1 / 32 * (n : ℝ) ^ 2)) *
          ‖F (x.1 - n * c, x.2)‖ₑ ^ 2 := by
  intro w S
  have hw_sum : Summable w := pm_summable (1 / 32) (by norm_num)
  have hw_pos : ∀ n : ℤ, 0 < w n := fun _ => Real.exp_pos _
  have hS_pos : 0 < S := by
    have h0 : w 0 ≤ S := hw_sum.le_tsum 0 (fun n _ => (hw_pos n).le)
    have hw0 : w 0 = 1 := by simp [w]
    linarith
  set u : ℤ → ℝ := fun n => ‖F (x.1 - n * c, x.2)‖
  set v : ℤ → ℝ := fun n => Real.exp (1 / 32 * (n : ℝ) ^ 2) * u n ^ 2
  have hv_nonneg : ∀ n : ℤ, 0 ≤ v n := fun n => by positivity
  have hwv : ∀ n : ℤ, w n * Real.exp (1 / 32 * (n : ℝ) ^ 2) = 1 := fun n => by
    unfold w
    rw [← Real.exp_add]
    simp
  have hterm_eq : ∀ n : ℤ,
      ENNReal.ofReal (Real.exp (1 / 32 * (n : ℝ) ^ 2)) * ‖F (x.1 - n * c, x.2)‖ₑ ^ 2 =
        ENNReal.ofReal (v n) := fun n => by
    rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _),
      ← ENNReal.ofReal_mul (Real.exp_pos _).le]
  simp_rw [hterm_eq]
  by_cases hv : Summable v
  · have hu : Summable u := by
      refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
        ((hw_sum.add hv).mul_left (1 / 2))
      have hsq : 0 ≤ w n * (1 - Real.exp (1 / 32 * (n : ℝ) ^ 2) * u n) ^ 2 := by positivity
      have hexp : w n * (1 - Real.exp (1 / 32 * (n : ℝ) ^ 2) * u n) ^ 2 =
          w n - 2 * u n + v n := by
        unfold v
        calc w n * (1 - Real.exp (1 / 32 * (n : ℝ) ^ 2) * u n) ^ 2
            = w n - 2 * (w n * Real.exp (1 / 32 * (n : ℝ) ^ 2)) * u n +
              (w n * Real.exp (1 / 32 * (n : ℝ) ^ 2)) *
                (Real.exp (1 / 32 * (n : ℝ) ^ 2) * u n ^ 2) := by ring
          _ = w n - 2 * u n + Real.exp (1 / 32 * (n : ℝ) ^ 2) * u n ^ 2 := by
            rw [hwv n]; ring
      linarith
    set U := (∑' n : ℤ, u n) / S
    have hpt_amgm : ∀ n : ℤ, 2 * U * u n ≤ U ^ 2 * w n + v n := fun n => by
      have hsq : 0 ≤ w n * (U - Real.exp (1 / 32 * (n : ℝ) ^ 2) * u n) ^ 2 := by positivity
      have hexp : w n * (U - Real.exp (1 / 32 * (n : ℝ) ^ 2) * u n) ^ 2 =
          U ^ 2 * w n - 2 * U * u n + v n := by
        unfold v
        calc w n * (U - Real.exp (1 / 32 * (n : ℝ) ^ 2) * u n) ^ 2
            = U ^ 2 * w n - 2 * U * (w n * Real.exp (1 / 32 * (n : ℝ) ^ 2)) * u n +
              (w n * Real.exp (1 / 32 * (n : ℝ) ^ 2)) *
                (Real.exp (1 / 32 * (n : ℝ) ^ 2) * u n ^ 2) := by ring
          _ = U ^ 2 * w n - 2 * U * u n + Real.exp (1 / 32 * (n : ℝ) ^ 2) * u n ^ 2 := by
            rw [hwv n]; ring
      linarith
    have hsum_le := (hu.mul_left (2 * U)).tsum_le_tsum hpt_amgm ((hw_sum.mul_left (U ^ 2)).add hv)
    rw [tsum_mul_left, Summable.tsum_add (hw_sum.mul_left (U ^ 2)) hv, tsum_mul_left] at hsum_le
    have hcs : (∑' n : ℤ, u n) ^ 2 ≤ S * ∑' n : ℤ, v n := by
      have hmul := mul_le_mul_of_nonneg_left hsum_le hS_pos.le
      have hS_ne : S ≠ 0 := hS_pos.ne'
      have h1 : S * (2 * U * ∑' n : ℤ, u n) = 2 * (∑' n : ℤ, u n) ^ 2 := by
        unfold U; field_simp
      have h2 : S * (U ^ 2 * S + ∑' n : ℤ, v n) =
          (∑' n : ℤ, u n) ^ 2 + S * ∑' n : ℤ, v n := by
        unfold U; field_simp
      linarith
    have hnorm_per : ‖IIIa.periodizeC c F x‖ ≤ ∑' n : ℤ, u n :=
      norm_tsum_le_tsum_norm hu
    have hnorm_sq : ‖IIIa.periodizeC c F x‖ ^ 2 ≤ S * ∑' n : ℤ, v n :=
      (pow_le_pow_left₀ (norm_nonneg _) hnorm_per 2).trans hcs
    rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _),
      ← ENNReal.ofReal_tsum_of_nonneg hv_nonneg hv, ← ENNReal.ofReal_mul hS_pos.le]
    exact ENNReal.ofReal_le_ofReal hnorm_sq
  · have htop : (∑' n : ℤ, ENNReal.ofReal (v n)) = ⊤ := by
      by_contra hne
      apply hv
      have hnn : Summable (fun n : ℤ => (v n).toNNReal) :=
        ENNReal.tsum_coe_ne_top_iff_summable.mp hne
      have hcoe : Summable (fun n : ℤ => ((v n).toNNReal : ℝ)) :=
        NNReal.summable_coe.mpr hnn
      refine hcoe.congr fun n => ?_
      exact Real.coe_toNNReal (v n) (hv_nonneg n)
    rw [htop, ENNReal.mul_top (ENNReal.ofReal_pos.mpr hS_pos).ne']
    exact le_top

/-- **Main theorem (`PartIII-b:IIIb-D3/2/G3/1/4/3/2`)**: `PeriodizePlanarModeXmc`. -/
theorem periodizePlanarModeXmc_of : PeriodizePlanarModeXmc := by
  intro m hm1 hm8
  have hm_nonneg : 0 ≤ m := by linarith
  obtain ⟨C₀, hC₀_pos, hC₀⟩ := UnforcedLeray.Gaussian.rpow_mul_exp_neg_le hm_nonneg
  let K_m : ℝ := 8 ^ m * Real.exp (1 / 8) * C₀
  have hKm_pos : 0 < K_m := by positivity
  let w : ℤ → ℝ := fun n => Real.exp (-(1 / 32 * (n : ℝ) ^ 2))
  have hw_sum : Summable w := pm_summable (1 / 32) (by norm_num)
  let S : ℝ := ∑' n : ℤ, w n
  have hS_pos : 0 < S := by
    have h0 : w 0 ≤ S := hw_sum.le_tsum 0 (fun n _ => (Real.exp_pos _).le)
    have hw0 : w 0 = 1 := by simp [w]
    linarith
  let C_m : ℝ := Real.sqrt (S * K_m / 2)
  refine ⟨C_m, Real.sqrt_nonneg _, fun c hcf hc1 => ?_⟩
  have hc0 : 0 < c := hcf.out
  -- Key bound: for any profile h in MemXG with ContinuousOn h (Ioi 0),
  -- periodizeC c (planarMode h) is in MemLp 2 (cellMeasure c m) with eLpNorm ≤ C_m * gaussianNorm h.
  have hBound : ∀ (h : Profile), MemXG h → ContinuousOn h (Ioi 0) →
      MemLp (IIIa.periodizeC c (IIIa.planarMode h)) 2 (B0579.cellMeasure c m) ∧
      eLpNorm (IIIa.periodizeC c (IIIa.planarMode h)) 2 (B0579.cellMeasure c m) ≤
        ENNReal.ofReal (C_m * gaussianNorm h) := by
    intro h hh hhc
    set F := IIIa.planarMode h
    have hFm : Measurable F := measurable_planarMode hhc
    have hFi : Integrable F volume := integrable_planarMode hh hhc
    have haesm : AEStronglyMeasurable (IIIa.periodizeC c F) (B0579.cellMeasure c m) :=
      aestronglyMeasurable_periodizeC hc0 hFm hFi
    have hjb_bound : ∀ x ∈ B0579.cell c, ∀ n : ℤ,
        B0579.jb x ^ m * Real.exp (1 / 32 * (n : ℝ) ^ 2) ≤
          K_m * Real.exp (((x.1 - n * c) ^ 2 + x.2 ^ 2) / 4) := by
      intro x hx n
      have hs_nonneg : 0 ≤ B0579.jb x / 8 := by linarith [B0579.jb_pos x]
      have habs := hC₀ (B0579.jb x / 8) hs_nonneg
      have hjb_le : B0579.jb x ^ m ≤ K_m * Real.exp ((x.1 ^ 2 + x.2 ^ 2) / 8) := by
        have h1 : (B0579.jb x / 8) ^ m = B0579.jb x ^ m / 8 ^ m :=
          Real.div_rpow (B0579.jb_pos x).le (by norm_num) m
        have h2 : Real.exp (-(B0579.jb x / 8)) * (Real.exp (1 / 8) *
            Real.exp ((x.1 ^ 2 + x.2 ^ 2) / 8)) = 1 := by
          rw [← Real.exp_add, ← Real.exp_add]
          unfold B0579.jb
          have : -((1 + x.1 ^ 2 + x.2 ^ 2) / 8) + (1 / 8 + (x.1 ^ 2 + x.2 ^ 2) / 8) = 0 := by ring
          rw [this, Real.exp_zero]
        have h3 := mul_le_mul_of_nonneg_left habs
          (by positivity : 0 ≤ 8 ^ m * Real.exp (1 / 8) * Real.exp ((x.1 ^ 2 + x.2 ^ 2) / 8))
        rw [h1] at h3
        have h8_ne : (8 : ℝ) ^ m ≠ 0 := (Real.rpow_pos_of_pos (by norm_num) m).ne'
        have h4 : 8 ^ m * Real.exp (1 / 8) * Real.exp ((x.1 ^ 2 + x.2 ^ 2) / 8) *
            (B0579.jb x ^ m / 8 ^ m * Real.exp (-(B0579.jb x / 8))) = B0579.jb x ^ m := by
          calc 8 ^ m * Real.exp (1 / 8) * Real.exp ((x.1 ^ 2 + x.2 ^ 2) / 8) *
                (B0579.jb x ^ m / 8 ^ m * Real.exp (-(B0579.jb x / 8)))
              = (8 ^ m / 8 ^ m) * B0579.jb x ^ m *
                (Real.exp (-(B0579.jb x / 8)) *
                  (Real.exp (1 / 8) * Real.exp ((x.1 ^ 2 + x.2 ^ 2) / 8))) := by ring
            _ = B0579.jb x ^ m := by rw [div_self h8_ne, h2, one_mul, mul_one]
        rw [h4] at h3
        calc B0579.jb x ^ m
            ≤ 8 ^ m * Real.exp (1 / 8) * Real.exp ((x.1 ^ 2 + x.2 ^ 2) / 8) * C₀ := h3
          _ = K_m * Real.exp ((x.1 ^ 2 + x.2 ^ 2) / 8) := by unfold K_m; ring
      have hshift := cell_shift_sq_ge hc1 hx n
      have hexp_le : Real.exp ((x.1 ^ 2 + x.2 ^ 2) / 8) * Real.exp (1 / 32 * (n : ℝ) ^ 2) ≤
          Real.exp (((x.1 - n * c) ^ 2 + x.2 ^ 2) / 4) := by
        rw [← Real.exp_add]
        exact Real.exp_le_exp.mpr (by linarith)
      calc B0579.jb x ^ m * Real.exp (1 / 32 * (n : ℝ) ^ 2)
          ≤ (K_m * Real.exp ((x.1 ^ 2 + x.2 ^ 2) / 8)) * Real.exp (1 / 32 * (n : ℝ) ^ 2) :=
            mul_le_mul_of_nonneg_right hjb_le (Real.exp_pos _).le
        _ = K_m * (Real.exp ((x.1 ^ 2 + x.2 ^ 2) / 8) * Real.exp (1 / 32 * (n : ℝ) ^ 2)) := by
            ring
        _ ≤ K_m * Real.exp (((x.1 - n * c) ^ 2 + x.2 ^ 2) / 4) :=
            mul_le_mul_of_nonneg_left hexp_le hKm_pos.le
    set G : ℝ × ℝ → ℝ≥0∞ := fun y =>
      ‖F y‖ₑ ^ 2 * ENNReal.ofReal (4 * Real.pi * Real.exp ((y.1 ^ 2 + y.2 ^ 2) / 4))
    have hGm : Measurable G := (hFm.enorm.pow_const 2).mul (by fun_prop)
    have hpt_cell : ∀ x ∈ B0579.cell c,
        (B0579.density m x : ℝ≥0∞) * ‖IIIa.periodizeC c F x‖ₑ ^ 2 ≤
          ENNReal.ofReal (S * K_m / (4 * Real.pi)) * UnforcedLeray.Cyl.periodize c G x := by
      intro x hx
      have hdens : (B0579.density m x : ℝ≥0∞) = ENNReal.ofReal (B0579.jb x ^ m) := by
        rw [← B0579.coe_density m x, ENNReal.ofReal_coe_nnreal]
      rw [hdens]
      have hcs := periodizeC_enorm_sq_le c F x
      calc ENNReal.ofReal (B0579.jb x ^ m) * ‖IIIa.periodizeC c F x‖ₑ ^ 2
          ≤ ENNReal.ofReal (B0579.jb x ^ m) *
              (ENNReal.ofReal S * ∑' n : ℤ,
                ENNReal.ofReal (Real.exp (1 / 32 * (n : ℝ) ^ 2)) *
                  ‖F (x.1 - n * c, x.2)‖ₑ ^ 2) := by
            gcongr
        _ = ENNReal.ofReal S * ∑' n : ℤ,
              (ENNReal.ofReal (B0579.jb x ^ m) *
                ENNReal.ofReal (Real.exp (1 / 32 * (n : ℝ) ^ 2))) *
                  ‖F (x.1 - n * c, x.2)‖ₑ ^ 2 := by
            rw [← mul_assoc, mul_comm (ENNReal.ofReal (B0579.jb x ^ m)), mul_assoc,
              ← ENNReal.tsum_mul_left]
            congr 1; refine tsum_congr fun n => ?_; ring
        _ ≤ ENNReal.ofReal S * ∑' n : ℤ,
              ENNReal.ofReal (K_m / (4 * Real.pi)) * G (x.1 - n * c, x.2) := by
            have htsum : (∑' n : ℤ, (ENNReal.ofReal (B0579.jb x ^ m) *
                ENNReal.ofReal (Real.exp (1 / 32 * (n : ℝ) ^ 2))) *
                  ‖F (x.1 - n * c, x.2)‖ₑ ^ 2) ≤
                ∑' n : ℤ, ENNReal.ofReal (K_m / (4 * Real.pi)) * G (x.1 - n * c, x.2) := by
              refine ENNReal.tsum_le_tsum fun n => ?_
              have hjb_n := hjb_bound x hx n
              have h0 : 0 ≤ B0579.jb x ^ m := Real.rpow_nonneg (B0579.jb_pos x).le m
              rw [← ENNReal.ofReal_mul h0]
              have hle : ENNReal.ofReal (B0579.jb x ^ m * Real.exp (1 / 32 * (n : ℝ) ^ 2)) ≤
                  ENNReal.ofReal (K_m / (4 * Real.pi)) *
                    ENNReal.ofReal (4 * Real.pi * Real.exp (((x.1 - n * c) ^ 2 + x.2 ^ 2) / 4)) := by
                rw [← ENNReal.ofReal_mul (by positivity)]
                refine ENNReal.ofReal_le_ofReal ?_
                have : K_m / (4 * Real.pi) *
                    (4 * Real.pi * Real.exp (((x.1 - n * c) ^ 2 + x.2 ^ 2) / 4)) =
                    K_m * Real.exp (((x.1 - n * c) ^ 2 + x.2 ^ 2) / 4) := by
                  field_simp
                rw [this]
                exact hjb_n
              calc ENNReal.ofReal (B0579.jb x ^ m * Real.exp (1 / 32 * (n : ℝ) ^ 2)) *
                    ‖F (x.1 - n * c, x.2)‖ₑ ^ 2
                  ≤ (ENNReal.ofReal (K_m / (4 * Real.pi)) *
                      ENNReal.ofReal (4 * Real.pi * Real.exp (((x.1 - n * c) ^ 2 + x.2 ^ 2) / 4))) *
                    ‖F (x.1 - n * c, x.2)‖ₑ ^ 2 := by gcongr
                _ = ENNReal.ofReal (K_m / (4 * Real.pi)) * G (x.1 - n * c, x.2) := by
                    unfold G; ring
            gcongr
        _ = ENNReal.ofReal (S * K_m / (4 * Real.pi)) * UnforcedLeray.Cyl.periodize c G x := by
            rw [ENNReal.tsum_mul_left, ← mul_assoc, ← ENNReal.ofReal_mul hS_pos.le,
              mul_div_assoc']
            rfl
    have hlint : ∫⁻ x in B0579.cell c, (B0579.density m x : ℝ≥0∞) * ‖IIIa.periodizeC c F x‖ₑ ^ 2 ≤
        ENNReal.ofReal ((C_m * gaussianNorm h) ^ 2) := by
      calc ∫⁻ x in B0579.cell c, (B0579.density m x : ℝ≥0∞) * ‖IIIa.periodizeC c F x‖ₑ ^ 2
          ≤ ∫⁻ x in B0579.cell c,
              ENNReal.ofReal (S * K_m / (4 * Real.pi)) * UnforcedLeray.Cyl.periodize c G x :=
            setLIntegral_mono' (B0579.measurableSet_cell c) hpt_cell
        _ = ENNReal.ofReal (S * K_m / (4 * Real.pi)) *
              ∫⁻ x in UnforcedLeray.Cyl.cell c, UnforcedLeray.Cyl.periodize c G x := by
            rw [cell_eq_cylCell, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        _ = ENNReal.ofReal (S * K_m / (4 * Real.pi)) * ∫⁻ y, G y := by
            rw [UnforcedLeray.Cyl.lintegral_cell_periodize hc0 hGm]
        _ = ENNReal.ofReal (S * K_m / (4 * Real.pi)) *
              ENNReal.ofReal (2 * Real.pi * gaussianNorm h ^ 2) := by
            rw [lintegral_planarMode_gauss hh]
        _ = ENNReal.ofReal ((C_m * gaussianNorm h) ^ 2) := by
            rw [← ENNReal.ofReal_mul (by positivity)]
            congr 1
            have hSK : 0 ≤ S * K_m / 2 := by positivity
            have hCm_sq : C_m ^ 2 = S * K_m / 2 := Real.sq_sqrt hSK
            calc S * K_m / (4 * Real.pi) * (2 * Real.pi * gaussianNorm h ^ 2)
                = (S * K_m / 2) * gaussianNorm h ^ 2 := by field_simp; ring
              _ = C_m ^ 2 * gaussianNorm h ^ 2 := by rw [hCm_sq]
              _ = (C_m * gaussianNorm h) ^ 2 := by ring
    have heLp : eLpNorm (IIIa.periodizeC c F) 2 (B0579.cellMeasure c m) ≤
        ENNReal.ofReal (C_m * gaussianNorm h) := by
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num),
        B0579.cellMeasure,
        lintegral_withDensity_eq_lintegral_mul_non_measurable _
          (B0579.measurable_density m).coe_nnreal_ennreal
          (Eventually.of_forall fun _ => ENNReal.coe_lt_top)]
      simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two, one_div]
      calc (∫⁻ x in B0579.cell c, (B0579.density m x : ℝ≥0∞) * ‖IIIa.periodizeC c F x‖ₑ ^ 2) ^
            (2 : ℝ)⁻¹
          ≤ (ENNReal.ofReal ((C_m * gaussianNorm h) ^ 2)) ^ (2 : ℝ)⁻¹ :=
            ENNReal.rpow_le_rpow hlint (by positivity)
        _ = ENNReal.ofReal (C_m * gaussianNorm h) := by
            have h0 : 0 ≤ C_m * gaussianNorm h :=
              mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
            rw [ENNReal.ofReal_rpow_of_nonneg (sq_nonneg _) (by positivity)]
            congr 1
            rw [← one_div, ← Real.sqrt_eq_rpow, Real.sqrt_sq h0]
    exact ⟨⟨haesm, lt_of_le_of_lt heLp ENNReal.ofReal_lt_top⟩, heLp⟩
  refine ⟨?_, ?_⟩
  -- Part 1: Existence of qf : Xmc c m
  · intro f hf hfc
    have hMemLp := (hBound f hf hfc).1
    have hFi : Integrable (IIIa.planarMode f) volume := integrable_planarMode hf hfc
    have hcirc : ∫ x in B0579.cell c, IIIa.periodizeC c (IIIa.planarMode f) x = 0 := by
      rw [periodizeIntegral c (IIIa.planarMode f) hc0 hFi, integral_planarMode_eq_zero f]
    have heven : ∀ x,
        IIIa.periodizeC c (IIIa.planarMode f) (-x) =
          IIIa.periodizeC c (IIIa.planarMode f) x :=
      periodizeC_even c (IIIa.planarMode f) (planarMode_even f)
    exact exists_elem (IIIa.planarMode f) hMemLp hcirc heven
  -- Part 2: Lipschitz bound ‖qf - qg‖ ≤ C_m * gaussianNorm (fun r => f r - g r)
  · intro f g hf hfc hg hgc qf qg hqf hqg
    have hsub_mem : MemXG (fun r => f r - g r) := memXG_sub hf hg
    have hsub_cont : ContinuousOn (fun r => f r - g r) (Ioi 0) := hfc.sub hgc
    have heLp_sub := (hBound (fun r => f r - g r) hsub_mem hsub_cont).2
    have hsum_f := ae_summable_periodizeC hc0 (measurable_planarMode hfc)
      (integrable_planarMode hf hfc)
    have hsum_g := ae_summable_periodizeC hc0 (measurable_planarMode hgc)
      (integrable_planarMode hg hgc)
    have hae_cell : xFn (qf - qg) =ᵐ[volume.restrict (B0579.cell c)]
        IIIa.periodizeC c (IIIa.planarMode (fun r => f r - g r)) := by
      filter_upwards [xFn_sub qf qg, hqf, hqg, hsum_f, hsum_g] with x hx hxf hxg hsf hsg
      rw [hx, hxf, hxg]
      unfold IIIa.periodizeC
      rw [← hsf.tsum_sub hsg]
      refine tsum_congr fun n => ?_
      exact (planarMode_sub f g (x.1 - n * c, x.2)).symm
    have hae_cm : xFn (qf - qg) =ᵐ[B0579.cellMeasure c m]
        IIIa.periodizeC c (IIIa.planarMode (fun r => f r - g r)) :=
      ae_cellMeasure_of_ae_cell hae_cell
    have hnorm_eq : ‖qf - qg‖ =
        (eLpNorm (IIIa.periodizeC c (IIIa.planarMode (fun r => f r - g r))) 2
          (B0579.cellMeasure c m)).toReal := by
      change ‖((qf - qg : Xmc c m) : XAmb c m)‖ = _
      rw [Lp.norm_def]
      exact congrArg ENNReal.toReal (eLpNorm_congr_ae hae_cm)
    rw [hnorm_eq]
    exact ENNReal.toReal_le_of_le_ofReal
      (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) heLp_sub

end UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif.G3
