import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GradL2pIBP.Slice.Cut
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GradL2pIBP.SliceDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Integral.Bochner.Basic

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete.GradSlice

open MeasureTheory Set Filter Topology

variable {E V : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasureSpace E]
    [BorelSpace E] [FiniteDimensional ℝ E] [SecondCountableTopology E]
    [Measure.IsAddHaarMeasure (volume : Measure E)]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Integration by parts against a compactly supported `C¹` field, real inner product. -/
theorem integral_inner_fderiv_eq_neg_c1
    {F u : E → V} (hF : ContDiff ℝ 1 F) (hu : ContDiff ℝ 1 u)
    (hcs : HasCompactSupport u) (v : E) :
    ∫ y, inner ℝ (F y) (fderiv ℝ u y v) = - ∫ y, inner ℝ (fderiv ℝ F y v) (u y) := by
  have hFc : Continuous F := hF.continuous
  have hdF : Continuous (fun y => fderiv ℝ F y) := hF.continuous_fderiv one_ne_zero
  have hdu : Continuous (fun y => fderiv ℝ u y) := hu.continuous_fderiv one_ne_zero
  have huc : Continuous u := hu.continuous
  have i1 : Integrable (fun y => innerSL ℝ (fderiv ℝ F y v) (u y)) := by
    simp only [innerSL_apply_apply]
    refine Continuous.integrable_of_hasCompactSupport ?_ (hasCompactSupport_inner_snd hcs)
    exact (hdF.clm_apply continuous_const).inner huc
  have i2 : Integrable (fun y => innerSL ℝ (F y) (fderiv ℝ u y v)) := by
    simp only [innerSL_apply_apply]
    exact Continuous.integrable_of_hasCompactSupport (hFc.inner (hdu.clm_apply continuous_const))
      (hasCompactSupport_inner_snd (hcs.fderiv_apply (𝕜 := ℝ) v))
  have i3 : Integrable (fun y => innerSL ℝ (F y) (u y)) := by
    simp only [innerSL_apply_apply]
    exact Continuous.integrable_of_hasCompactSupport (hFc.inner huc) (hasCompactSupport_inner_snd hcs)
  exact integral_bilinear_fderiv_right_eq_neg_left_of_integrable (μ := volume)
    (B := innerSL ℝ) (f := F) (g := u) (v := v) i1 i2 i3
    (fun x _ => hF.differentiable one_ne_zero x)
    (fun x _ => hu.differentiable one_ne_zero x)

theorem rpow_two_add (x s : ℝ) (hx : 0 ≤ x) (hs : 0 < s) : x ^ s * x ^ 2 = x ^ (s + 2) := by
  have := Real.rpow_add_natCast' hx (y := s) (n := 2) (by positivity)
  simpa using this.symm

theorem rpow_one_add (x s : ℝ) (hx : 0 ≤ x) (hs : 0 < s) : x ^ s * x = x ^ (s + 1) := by
  have := Real.rpow_add_natCast' hx (y := s) (n := 1) (by positivity)
  simpa using this.symm

/-- The cutoff slice inequality (real IBP, then `lintegral`). -/
theorem slice_cut {s : ℝ} (hs : 1 < s) {M : ℝ} (hM : 0 ≤ M) (e : E)
    {w : E → V} {g : E → V} {h : E → V} {χ : E → ℝ} {c : ℝ}
    (hw : ContDiff ℝ 1 w) (hg : ContDiff ℝ 1 g) (hwM : ∀ y, ‖w y‖ ≤ M)
    (hgw : ∀ y, fderiv ℝ w y e = g y) (hgh : ∀ y, fderiv ℝ g y e = h y)
    (hχ : ContDiff ℝ 1 χ) (hχcs : HasCompactSupport χ) (hχ0 : ∀ y, 0 ≤ χ y)
    (hχ1 : ∀ y, χ y ≤ 1) (hc : ∀ y, ‖fderiv ℝ χ y e‖ ≤ c) :
    ∫⁻ y, ENNReal.ofReal (χ y * ‖g y‖ ^ (s + 2)) ≤
      ENNReal.ofReal ((s + 1) * M) * (∫⁻ y, ENNReal.ofReal (‖g y‖ ^ s * ‖h y‖)) +
      ENNReal.ofReal (c * M) * ∫⁻ y, ENNReal.ofReal (‖g y‖ ^ (s + 1)) := by
  have hs0 : 0 < s := by linarith
  have hc0 : 0 ≤ c := (norm_nonneg _).trans (hc 0)
  set N : V → V := fun x => ‖x‖ ^ s • x with hNdef
  have hN : ContDiff ℝ 1 N := (contDiff_norm_rpow hs).smul contDiff_id
  set F : E → V := fun y => N (g y) with hFdef
  have hF : ContDiff ℝ 1 F := hN.comp hg
  have hdF : ∀ y, fderiv ℝ F y e = fderiv ℝ N (g y) (h y) := by
    intro y
    have : F = N ∘ g := rfl
    rw [this, fderiv_comp y (hN.differentiable one_ne_zero _) (hg.differentiable one_ne_zero y)]
    simp [hgh]
  set u : E → V := fun y => χ y • w y with hudef
  have hu : ContDiff ℝ 1 u := hχ.smul hw
  have hucs : HasCompactSupport u := by
    refine HasCompactSupport.intro hχcs fun y hy => ?_
    have : χ y = 0 := image_eq_zero_of_notMem_tsupport hy
    simp [hudef, this]
  have hdu : ∀ y, fderiv ℝ u y e = (fderiv ℝ χ y e) • w y + χ y • g y := by
    intro y
    have := fderiv_smul (hχ.differentiable one_ne_zero y) (hw.differentiable one_ne_zero y)
    show fderiv ℝ (χ • w) y e = _
    rw [this]
    simp [hgw]
    abel
  have hFn : ∀ y, ‖F y‖ = ‖g y‖ ^ (s + 1) := by
    intro y
    simp only [hFdef, hNdef, norm_smul, Real.norm_eq_abs]
    rw [abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    exact rpow_one_add _ _ (norm_nonneg _) hs0
  have hFg : ∀ y, inner ℝ (F y) (g y) = ‖g y‖ ^ (s + 2) := by
    intro y
    simp only [hFdef, hNdef, real_inner_smul_left, real_inner_self_eq_norm_sq]
    exact rpow_two_add _ _ (norm_nonneg _) hs0
  -- continuity
  have hgc : Continuous g := hg.continuous
  have hhc : Continuous h := by
    have : h = fun y => fderiv ℝ g y e := funext fun y => (hgh y).symm
    rw [this]; exact (hg.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hχc : Continuous χ := hχ.continuous
  have hdχ : Continuous (fun y => fderiv ℝ χ y e) :=
    (hχ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hKc : HasCompactSupport (fun y => fderiv ℝ χ y e) := hχcs.fderiv_apply (𝕜 := ℝ) e
  have hwc : Continuous w := hw.continuous
  have hFc : Continuous F := hF.continuous
  have hdFc : Continuous (fun y => fderiv ℝ F y e) :=
    (hF.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hgp : ∀ r : ℝ, 0 ≤ r → Continuous (fun y => ‖g y‖ ^ r) := fun r hr =>
    hgc.norm.rpow_const (fun _ => Or.inr hr)
  -- the functions
  set a : E → ℝ := fun y => χ y * ‖g y‖ ^ (s + 2) with hadef
  set b : E → ℝ := fun y => fderiv ℝ χ y e * inner ℝ (F y) (w y) with hbdef
  have hac : Continuous a := hχc.mul (hgp _ (by linarith))
  have hbc : Continuous b := hdχ.mul (hFc.inner hwc)
  have hacs : HasCompactSupport a := by
    refine HasCompactSupport.intro hχcs fun y hy => ?_
    have : χ y = 0 := image_eq_zero_of_notMem_tsupport hy
    simp [hadef, this]
  have hbcs : HasCompactSupport b := by
    refine HasCompactSupport.intro hKc fun y hy => ?_
    have : fderiv ℝ χ y e = 0 :=
      image_eq_zero_of_notMem_tsupport (f := fun y => fderiv ℝ χ y e) hy
    simp [hbdef, this]
  have hai : Integrable a := hac.integrable_of_hasCompactSupport (μ := volume) hacs
  have hbi : Integrable b := hbc.integrable_of_hasCompactSupport (μ := volume) hbcs
  have hpt : ∀ y, inner ℝ (F y) (fderiv ℝ u y e) = a y + b y := by
    intro y
    rw [hdu, inner_add_right, real_inner_smul_right, real_inner_smul_right, hFg]
    simp only [hadef, hbdef]; ring
  have hibp := integral_inner_fderiv_eq_neg_c1 hF hu hucs e
  have hd1c : Continuous (fun y => inner ℝ (fderiv ℝ F y e) (u y)) :=
    hdFc.inner (hχc.smul hwc)
  have hd1cs : HasCompactSupport (fun y => inner ℝ (fderiv ℝ F y e) (u y)) :=
    hasCompactSupport_inner_snd hucs
  have hd1i := hd1c.integrable_of_hasCompactSupport (μ := volume) hd1cs
  have hint : ∫ y, a y = (∫ y, -inner ℝ (fderiv ℝ F y e) (u y)) + ∫ y, -b y := by
    have h1 : ∫ y, (a y + b y) = -∫ y, inner ℝ (fderiv ℝ F y e) (u y) := by
      rw [← hibp]; exact integral_congr_ae (Eventually.of_forall fun y => (hpt y).symm)
    rw [integral_add hai hbi] at h1
    rw [integral_neg, integral_neg]; linarith
  -- bounds
  set B1 : E → ℝ := fun y => χ y * ((s + 1) * M * (‖g y‖ ^ s * ‖h y‖)) with hB1
  set B2 : E → ℝ := fun y => ‖fderiv ℝ χ y e‖ * (M * ‖g y‖ ^ (s + 1)) with hB2
  have hB1c : Continuous B1 := hχc.mul (continuous_const.mul ((hgp _ hs0.le).mul hhc.norm))
  have hB2c : Continuous (fun y => ‖fderiv ℝ χ y e‖ * (M * ‖g y‖ ^ (s + 1))) :=
    hdχ.norm.mul (continuous_const.mul (hgp _ (by linarith)))
  have hB1cs : HasCompactSupport B1 := by
    refine HasCompactSupport.intro hχcs fun y hy => ?_
    have : χ y = 0 := image_eq_zero_of_notMem_tsupport hy
    simp [hB1, this]
  have hB2cs : HasCompactSupport B2 := by
    refine HasCompactSupport.intro hKc fun y hy => ?_
    have : fderiv ℝ χ y e = 0 :=
      image_eq_zero_of_notMem_tsupport (f := fun y => fderiv ℝ χ y e) hy
    simp [hB2, this]
  have hB1i := hB1c.integrable_of_hasCompactSupport (μ := volume) hB1cs
  have hB2i := hB2c.integrable_of_hasCompactSupport (μ := volume) hB2cs
  have hb1 : ∀ y, -inner ℝ (fderiv ℝ F y e) (u y) ≤ B1 y := by
    intro y
    rw [hdF]
    have h1 := norm_fderiv_normPow_smul_le (g y) (h y) hs
    have h2 : ‖u y‖ ≤ χ y * M := by
      simp only [hudef, norm_smul, Real.norm_eq_abs, abs_of_nonneg (hχ0 y)]
      exact mul_le_mul_of_nonneg_left (hwM y) (hχ0 y)
    calc -inner ℝ (fderiv ℝ N (g y) (h y)) (u y)
        ≤ ‖fderiv ℝ N (g y) (h y)‖ * ‖u y‖ := by
          have := real_inner_le_norm (fderiv ℝ N (g y) (h y)) (u y)
          have h3 := abs_real_inner_le_norm (fderiv ℝ N (g y) (h y)) (u y)
          linarith [neg_abs_le (inner ℝ (fderiv ℝ N (g y) (h y)) (u y))]
      _ ≤ ((s + 1) * ‖g y‖ ^ s * ‖h y‖) * (χ y * M) :=
          mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
      _ = B1 y := by simp only [hB1]; ring
  have hb2 : ∀ y, -b y ≤ B2 y := by
    intro y
    have h3 := abs_real_inner_le_norm (F y) (w y)
    have h4 : ‖F y‖ * ‖w y‖ ≤ ‖g y‖ ^ (s + 1) * M := by
      rw [hFn]; exact mul_le_mul_of_nonneg_left (hwM y) (Real.rpow_nonneg (norm_nonneg _) _)
    calc -b y ≤ |b y| := neg_le_abs _
      _ = ‖fderiv ℝ χ y e‖ * |inner ℝ (F y) (w y)| := by
          simp only [hbdef, abs_mul, Real.norm_eq_abs]
      _ ≤ ‖fderiv ℝ χ y e‖ * (‖g y‖ ^ (s + 1) * M) :=
          mul_le_mul_of_nonneg_left (h3.trans h4) (norm_nonneg _)
      _ = B2 y := by simp only [hB2]; ring
  have hle : ∫ y, a y ≤ ∫ y, (B1 y + B2 y) := by
    rw [hint, integral_add hB1i hB2i]
    exact add_le_add (integral_mono hd1i.neg hB1i hb1) (integral_mono hbi.neg hB2i hb2)
  -- to lintegral
  have hlhs : ∫⁻ y, ENNReal.ofReal (a y) = ENNReal.ofReal (∫ y, a y) :=
    (ofReal_integral_eq_lintegral_ofReal hai
      (Eventually.of_forall fun y => mul_nonneg (hχ0 y) (Real.rpow_nonneg (norm_nonneg _) _))).symm
  have hB1nn : ∀ y, 0 ≤ B1 y := fun y => by
    simp only [hB1]; exact mul_nonneg (hχ0 y) (by positivity)
  have hB2nn : ∀ y, 0 ≤ B2 y := fun y => by
    simp only [hB2]; exact mul_nonneg (norm_nonneg _) (by positivity)
  have hsum : ENNReal.ofReal (∫ y, (B1 y + B2 y)) = (∫⁻ y, ENNReal.ofReal (B1 y)) +
      ∫⁻ y, ENNReal.ofReal (B2 y) := by
    rw [← lintegral_add_left (hB1c.measurable.ennreal_ofReal)]
    have hsi : Integrable (fun y => B1 y + B2 y) := hB1i.add hB2i
    rw [ofReal_integral_eq_lintegral_ofReal hsi
      (Eventually.of_forall fun y => add_nonneg (hB1nn y) (hB2nn y))]
    exact lintegral_congr fun y => ENNReal.ofReal_add (hB1nn y) (hB2nn y)
  have hm1 : ∫⁻ y, ENNReal.ofReal (B1 y) ≤
      ENNReal.ofReal ((s + 1) * M) * ∫⁻ y, ENNReal.ofReal (‖g y‖ ^ s * ‖h y‖) := by
    have hme : Measurable (fun y => ENNReal.ofReal (‖g y‖ ^ s * ‖h y‖)) :=
      ((hgp _ hs0.le).mul hhc.norm).measurable.ennreal_ofReal
    rw [← lintegral_const_mul _ hme]
    refine lintegral_mono fun y => ?_
    rw [← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    simp only [hB1]
    have : 0 ≤ (s + 1) * M * (‖g y‖ ^ s * ‖h y‖) := by positivity
    nlinarith [hχ0 y, hχ1 y]
  have hm2 : ∫⁻ y, ENNReal.ofReal (B2 y) ≤
      ENNReal.ofReal (c * M) * ∫⁻ y, ENNReal.ofReal (‖g y‖ ^ (s + 1)) := by
    have hme : Measurable (fun y => ENNReal.ofReal (‖g y‖ ^ (s + 1))) :=
      (hgp _ (by linarith)).measurable.ennreal_ofReal
    rw [← lintegral_const_mul _ hme]
    refine lintegral_mono fun y => ?_
    rw [← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    simp only [hB2]
    have : 0 ≤ M * ‖g y‖ ^ (s + 1) := by positivity
    have := mul_le_mul_of_nonneg_right (hc y) this
    linarith
  calc ∫⁻ y, ENNReal.ofReal (χ y * ‖g y‖ ^ (s + 2)) = ∫⁻ y, ENNReal.ofReal (a y) := rfl
    _ = ENNReal.ofReal (∫ y, a y) := hlhs
    _ ≤ ENNReal.ofReal (∫ y, (B1 y + B2 y)) := ENNReal.ofReal_le_ofReal hle
    _ = _ := hsum
    _ ≤ _ := add_le_add hm1 hm2

end UnforcedLeray.Short.PartIIIb.Concrete.GradSlice
