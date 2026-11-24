import UnforcedLeray.Short.PartIIa.Sub.PartIIa_F16
import UnforcedLeray.Lib.LerayLp.Cutoff
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Distribution.TemperedDistribution
import Mathlib.Analysis.Fourier.LpSpace

/-!
# Part II-a, task `PartII-a:F16/d`: `tensorDivRiesz`

Source `the November 2 reference manuscript`
lines 1596-1598 (`div = ν^{-1/2} A^{1/2} 𝒬`, `D^{-1/2} A^{1/2}` bounded, Leray commutes with `A`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open Set MeasureTheory Filter Topology SchwartzMap FourierTransform LineDeriv Real
open scoped ENNReal NNReal ContDiff InnerProductSpace ComplexConjugate

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.RieszLp UnforcedLeray.Infra

/-! ### Section L1: Fourier form of the Leray projection and commutation with `phaseD0` -/

private def piVec (ξ : Space) (v : CVec3) : CVec3 :=
  v - ((∑ j : Fin 3, (ξ j : ℂ) * v j) / ((‖ξ‖ : ℂ) ^ 2)) •
    (WithLp.toLp 2 fun i : Fin 3 => (ξ i : ℂ))

private lemma piVec_smul (ξ : Space) (c : ℂ) (v : CVec3) :
    piVec ξ (c • v) = c • piVec ξ v := by
  ext i
  simp only [piVec, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  have hsum : (∑ j : Fin 3, (ξ j : ℂ) * (c * v j)) = c * ∑ j : Fin 3, (ξ j : ℂ) * v j := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => by ring
  rw [hsum]
  ring

private lemma sum_mul_piVec (ξ : Space) (v : CVec3) :
    ∑ i : Fin 3, (ξ i : ℂ) * piVec ξ v i = 0 := by
  by_cases hξ : ‖ξ‖ = 0
  · have h0 : ∀ i : Fin 3, (ξ i : ℂ) = 0 := fun i => by
      have : ξ = 0 := norm_eq_zero.mp hξ
      simp [this]
    simp [h0]
  · simp only [piVec, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul,
      mul_sub, Finset.sum_sub_distrib]
    have hsq : ∑ i : Fin 3, (ξ i : ℂ) * ((∑ j : Fin 3, (ξ j : ℂ) * v j) / (‖ξ‖ : ℂ) ^ 2 * (ξ i : ℂ)) =
        ((∑ j : Fin 3, (ξ j : ℂ) * v j) / (‖ξ‖ : ℂ) ^ 2) * ∑ i : Fin 3, (ξ i : ℂ) ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => by ring
    have hnorm : (∑ i : Fin 3, (ξ i : ℂ) ^ 2) = (‖ξ‖ : ℂ) ^ 2 := by
      have h1 : ‖ξ‖ ^ 2 = ∑ i : Fin 3, (ξ i) ^ 2 := by
        rw [PiLp.norm_sq_eq_of_L2]
        refine Finset.sum_congr rfl fun i _ => by rw [Real.norm_eq_abs, sq_abs]
      have h2 : (‖ξ‖ : ℂ) ^ 2 = ((‖ξ‖ ^ 2 : ℝ) : ℂ) := by push_cast; ring
      rw [h2, h1]
      push_cast
      rfl
    have hne : (‖ξ‖ : ℂ) ^ 2 ≠ 0 := pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr hξ)
    rw [hsq, hnorm, div_mul_cancel₀ _ hne, sub_self]

private lemma inner_sub_piVec_eq_zero {ξ : Space} (v u : CVec3)
    (hu : ∑ i : Fin 3, (ξ i : ℂ) * u i = 0) :
    ⟪v - piVec ξ v, u⟫_ℂ = 0 := by
  have hsub : v - piVec ξ v =
      (((∑ j : Fin 3, (ξ j : ℂ) * v j) / ((‖ξ‖ : ℂ) ^ 2))) •
        (WithLp.toLp 2 fun i : Fin 3 => (ξ i : ℂ)) := by
    unfold piVec
    abel
  rw [hsub, inner_smul_left]
  have hinner : ⟪(WithLp.toLp 2 fun i : Fin 3 => (ξ i : ℂ)), u⟫_ℂ =
      ∑ i : Fin 3, (ξ i : ℂ) * u i := by
    simp only [PiLp.inner_apply, RCLike.inner_apply, Complex.conj_ofReal]
    refine Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [hinner, hu, mul_zero]

private lemma norm_piVec_le (ξ : Space) (v : CVec3) : ‖piVec ξ v‖ ≤ ‖v‖ := by
  have horth : ⟪piVec ξ v, v - piVec ξ v⟫_ℂ = 0 := by
    rw [← inner_conj_symm, inner_sub_piVec_eq_zero v (piVec ξ v) (sum_mul_piVec ξ v), map_zero]
  have hadd : piVec ξ v + (v - piVec ξ v) = v := add_sub_cancel _ _
  have hpyth := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (piVec ξ v) (v - piVec ξ v) horth
  rw [hadd] at hpyth
  have hle : ‖piVec ξ v‖ ^ 2 ≤ ‖v‖ ^ 2 := by
    nlinarith [sq_nonneg ‖v - piVec ξ v‖]
  exact nonneg_le_nonneg_of_sq_le_sq (norm_nonneg _) (by nlinarith)

private lemma integrable_schwartz_smul_lp (g : 𝓢(Space, ℂ))
    (w : Lp CVec3 2 (volume : Measure Space)) :
    Integrable (fun x : Space => g x • (w x : CVec3)) volume :=
  memLp_one_iff_integrable.mp ((Lp.memLp w).smul (r := 1) (g.memLp 2 volume))

private lemma fourier_div_schwartz (w : Lp CVec3 2 (volume : Measure Space)) (φ : 𝓢(Space, ℂ)) :
    ∫ ξ : Space, φ ξ * ((2 * Real.pi * Complex.I) *
        ∑ i : Fin 3, (ξ i : ℂ) * ((𝓕 w : Lp CVec3 2 volume) ξ i)) =
      - ∫ x : Space, ∑ i : Fin 3, (w x i) * (∂_{coordinateVector i} (𝓕 φ) x) := by
  have hcoord : ∀ i : Fin 3,
      ∫ ξ : Space, φ ξ * ((2 * Real.pi * Complex.I) * ((ξ i : ℂ) * ((𝓕 w : Lp CVec3 2 volume) ξ i))) =
        - ∫ x : Space, (w x i) * (∂_{coordinateVector i} (𝓕 φ) x) := by
    intro i
    have htemp : (fun x : Space => ((inner ℝ x (coordinateVector i) : ℝ) : ℂ)).HasTemperateGrowth := by
      fun_prop
    have h1 := congrArg (fun T : 𝓢'(Space, CVec3) => (EuclideanSpace.proj i : CVec3 →L[ℂ] ℂ) (T φ))
      (TemperedDistribution.fourier_lineDerivOp_eq (w : 𝓢'(Space, CVec3)) (coordinateVector i))
    rw [Lp.fourier_toTemperedDistribution_eq] at h1
    simp only [TemperedDistribution.fourier_apply, TemperedDistribution.lineDerivOp_apply_apply,
      smul_apply, TemperedDistribution.smulLeftCLM_apply_apply,
      Lp.toTemperedDistribution_apply] at h1
    rw [map_smul, ← (EuclideanSpace.proj i : CVec3 →L[ℂ] ℂ).integral_comp_comm
        (integrable_schwartz_smul_lp (-∂_{coordinateVector i} (𝓕 φ)) w),
      ← (EuclideanSpace.proj i : CVec3 →L[ℂ] ℂ).integral_comp_comm
        (integrable_schwartz_smul_lp
          (SchwartzMap.smulLeftCLM ℂ (fun x : Space => ((inner ℝ x (coordinateVector i) : ℝ) : ℂ)) φ)
          (𝓕 w : Lp CVec3 2 volume)),
      ← integral_smul] at h1
    have hL : (∫ x : Space, (EuclideanSpace.proj i : CVec3 →L[ℂ] ℂ)
        ((-∂_{coordinateVector i} (𝓕 φ)) x • (w x : CVec3))) =
        - ∫ x : Space, (w x i) * (∂_{coordinateVector i} (𝓕 φ) x) := by
      rw [← integral_neg]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      change ((-∂_{coordinateVector i} (𝓕 φ)) x • (w x : CVec3)) i =
        -((w x i) * (∂_{coordinateVector i} (𝓕 φ) x))
      simp only [neg_apply, PiLp.smul_apply, smul_eq_mul]
      ring
    have hR : (∫ x : Space, (2 * Real.pi * Complex.I) • (EuclideanSpace.proj i : CVec3 →L[ℂ] ℂ)
        ((SchwartzMap.smulLeftCLM ℂ (fun x : Space => ((inner ℝ x (coordinateVector i) : ℝ) : ℂ)) φ x) •
          ((𝓕 w : Lp CVec3 2 volume) x : CVec3))) =
        ∫ ξ : Space, φ ξ * ((2 * Real.pi * Complex.I) * ((ξ i : ℂ) * ((𝓕 w : Lp CVec3 2 volume) ξ i))) := by
      refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
      have hxi : inner ℝ ξ (coordinateVector i) = ξ i := by
        simp [coordinateVector, EuclideanSpace.inner_single_right]
      change (2 * Real.pi * Complex.I) *
          (((SchwartzMap.smulLeftCLM ℂ (fun x : Space => ((inner ℝ x (coordinateVector i) : ℝ) : ℂ)) φ ξ) •
            ((𝓕 w : Lp CVec3 2 volume) ξ : CVec3)) i) =
        φ ξ * ((2 * Real.pi * Complex.I) * ((ξ i : ℂ) * ((𝓕 w : Lp CVec3 2 volume) ξ i)))
      simp only [SchwartzMap.smulLeftCLM_apply_apply htemp, hxi,
        PiLp.smul_apply, smul_eq_mul]
      ring
    rw [hL, hR] at h1
    exact h1.symm
  have hint1 : ∀ i ∈ (Finset.univ : Finset (Fin 3)),
      Integrable (fun ξ : Space => φ ξ * ((2 * Real.pi * Complex.I) *
        ((ξ i : ℂ) * ((𝓕 w : Lp CVec3 2 volume) ξ i)))) volume := by
    intro i _
    have htemp : (fun x : Space => ((inner ℝ x (coordinateVector i) : ℝ) : ℂ)).HasTemperateGrowth := by
      fun_prop
    have hi := ((EuclideanSpace.proj i : CVec3 →L[ℂ] ℂ).integrable_comp
      (integrable_schwartz_smul_lp
        (SchwartzMap.smulLeftCLM ℂ (fun x : Space => ((inner ℝ x (coordinateVector i) : ℝ) : ℂ)) φ)
        (𝓕 w : Lp CVec3 2 volume))).const_mul (2 * Real.pi * Complex.I)
    refine hi.congr (Eventually.of_forall fun ξ => ?_)
    have hxi : inner ℝ ξ (coordinateVector i) = ξ i := by
      simp [coordinateVector, EuclideanSpace.inner_single_right]
    change (2 * Real.pi * Complex.I) *
        (((SchwartzMap.smulLeftCLM ℂ (fun x : Space => ((inner ℝ x (coordinateVector i) : ℝ) : ℂ)) φ ξ) •
          ((𝓕 w : Lp CVec3 2 volume) ξ : CVec3)) i) =
      φ ξ * ((2 * Real.pi * Complex.I) * ((ξ i : ℂ) * ((𝓕 w : Lp CVec3 2 volume) ξ i)))
    simp only [SchwartzMap.smulLeftCLM_apply_apply htemp, hxi,
      PiLp.smul_apply, smul_eq_mul]
    ring
  have hint2 : ∀ i ∈ (Finset.univ : Finset (Fin 3)),
      Integrable (fun x : Space => (w x i) * (∂_{coordinateVector i} (𝓕 φ) x)) volume := by
    intro i _
    have hi := (EuclideanSpace.proj i : CVec3 →L[ℂ] ℂ).integrable_comp
      (integrable_schwartz_smul_lp (∂_{coordinateVector i} (𝓕 φ)) w)
    refine hi.congr (Eventually.of_forall fun x => ?_)
    change ((∂_{coordinateVector i} (𝓕 φ)) x • (w x : CVec3)) i =
      (w x i) * (∂_{coordinateVector i} (𝓕 φ) x)
    simp only [PiLp.smul_apply, smul_eq_mul]
    ring
  have hsumL : (fun ξ : Space => φ ξ * ((2 * Real.pi * Complex.I) *
      ∑ i : Fin 3, (ξ i : ℂ) * ((𝓕 w : Lp CVec3 2 volume) ξ i))) =
      fun ξ : Space => ∑ i : Fin 3, φ ξ * ((2 * Real.pi * Complex.I) *
        ((ξ i : ℂ) * ((𝓕 w : Lp CVec3 2 volume) ξ i))) := by
    funext ξ
    rw [Finset.mul_sum, Finset.mul_sum]
  rw [hsumL, integral_finsetSum _ hint1, integral_finsetSum _ hint2, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => hcoord i

private lemma solenoidal_schwartz_real {F : Lp Space 2 (volume : Measure Space)}
    (hF : F ∈ Leray.solenoidalSubspace) {ψ : Space → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hψ2 : MemLp ψ 2 volume) (hdψ2 : ∀ i : Fin 3, MemLp (spatialTestDerivative i ψ) 2 volume) :
    ∫ x : Space, ∑ i : Fin 3, F x i * spatialTestDerivative i ψ x = 0 := by
  have h1 : Integrable (fun x : Space => ‖F x‖ * ‖gradField ψ x‖) volume := by
    have hsum : Integrable (fun x : Space => ∑ i : Fin 3, ‖F x‖ * ‖spatialTestDerivative i ψ x‖) volume :=
      integrable_finsetSum _ fun i _ => (Lp.memLp F).norm.integrable_mul (hdψ2 i).norm
    refine hsum.mono' ((Lp.aestronglyMeasurable F).norm.mul
      (continuous_gradField hψ).aestronglyMeasurable.norm) (Eventually.of_forall fun x => ?_)
    rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)), ← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    refine (norm_sum_smul_coordinateVector_le _).trans ?_
    refine Finset.sum_le_sum fun i _ => ?_
    rw [Real.norm_eq_abs]
  have h2 : Integrable (fun x : Space => ‖F x‖ * |ψ x| * (1 + ‖x‖)⁻¹) volume := by
    have hmul : Integrable (fun x : Space => ‖F x‖ * ‖ψ x‖) volume :=
      (Lp.memLp F).norm.integrable_mul hψ2.norm
    have hmeas : AEStronglyMeasurable (fun x : Space => ‖F x‖ * |ψ x| * (1 + ‖x‖)⁻¹) volume := by
      have hinv : Continuous (fun x : Space => (1 + ‖x‖)⁻¹) :=
        (continuous_const.add continuous_norm).inv₀ fun x => by dsimp; positivity
      exact ((Lp.aestronglyMeasurable F).norm.mul hψ.continuous.abs.aestronglyMeasurable).mul
        hinv.aestronglyMeasurable
    refine hmul.mono' hmeas (Eventually.of_forall fun x => ?_)
    have hpos : 0 ≤ (1 + ‖x‖)⁻¹ := by positivity
    have hle1 : (1 + ‖x‖)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith [norm_nonneg x])
    rw [Real.norm_of_nonneg (by positivity), ← Real.norm_eq_abs]
    exact mul_le_of_le_one_right (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hle1
  have h0 := integral_inner_gradField_eq_zero ((Leray.mem_solenoidalSubspace_iff F).mp hF)
    (Lp.aestronglyMeasurable F) hψ h1 h2
  rw [← h0]
  exact integral_congr_ae (Eventually.of_forall fun x => (inner_gradField (F x) ψ x).symm)

private lemma solenoidalC_schwartz {w : Lp CVec3 2 (volume : Measure Space)}
    (hw : w ∈ B0414.solenoidalC) (g : 𝓢(Space, ℂ)) :
    ∫ x : Space, ∑ i : Fin 3, (w x i) * (∂_{coordinateVector i} g x) = 0 := by
  set gr : Space → ℝ := fun x => (g x).re with hgr
  set gi : Space → ℝ := fun x => (g x).im with hgi
  have hgs : ContDiff ℝ ∞ g := g.smooth ⊤
  have hgr_s : ContDiff ℝ ∞ gr := Complex.reCLM.contDiff.comp hgs
  have hgi_s : ContDiff ℝ ∞ gi := Complex.imCLM.contDiff.comp hgs
  have hdgr : ∀ i x, spatialTestDerivative i gr x = (∂_{coordinateVector i} g x).re := by
    intro i x
    rw [spatialTestDerivative, SchwartzMap.lineDerivOp_apply_eq_fderiv]
    have : HasFDerivAt gr (Complex.reCLM.comp (fderiv ℝ g x)) x :=
      Complex.reCLM.hasFDerivAt.comp x g.differentiableAt.hasFDerivAt
    rw [this.fderiv]; rfl
  have hdgi : ∀ i x, spatialTestDerivative i gi x = (∂_{coordinateVector i} g x).im := by
    intro i x
    rw [spatialTestDerivative, SchwartzMap.lineDerivOp_apply_eq_fderiv]
    have : HasFDerivAt gi (Complex.imCLM.comp (fderiv ℝ g x)) x :=
      Complex.imCLM.hasFDerivAt.comp x g.differentiableAt.hasFDerivAt
    rw [this.fderiv]; rfl
  have hgL : MemLp (g : Space → ℂ) 2 volume := g.memLp 2 volume
  have mr : MemLp gr 2 volume := hgL.of_le hgr_s.continuous.aestronglyMeasurable
    (Eventually.of_forall fun x => by simp only [hgr, Real.norm_eq_abs]; exact Complex.abs_re_le_norm _)
  have mi : MemLp gi 2 volume := hgL.of_le hgi_s.continuous.aestronglyMeasurable
    (Eventually.of_forall fun x => by simp only [hgi, Real.norm_eq_abs]; exact Complex.abs_im_le_norm _)
  have mdr : ∀ i, MemLp (spatialTestDerivative i gr) 2 volume := fun i =>
    ((∂_{coordinateVector i} g).memLp 2 volume).of_le
      (by rw [funext (hdgr i)]; exact (Complex.continuous_re.comp (∂_{coordinateVector i} g).continuous).aestronglyMeasurable)
      (Eventually.of_forall fun x => by rw [hdgr, Real.norm_eq_abs]; exact Complex.abs_re_le_norm _)
  have mdi : ∀ i, MemLp (spatialTestDerivative i gi) 2 volume := fun i =>
    ((∂_{coordinateVector i} g).memLp 2 volume).of_le
      (by rw [funext (hdgi i)]; exact (Complex.continuous_im.comp (∂_{coordinateVector i} g).continuous).aestronglyMeasurable)
      (Eventually.of_forall fun x => by rw [hdgi, Real.norm_eq_abs]; exact Complex.abs_im_le_norm _)
  have hreal : ∀ (ψ : Space → ℝ), ContDiff ℝ ∞ ψ → MemLp ψ 2 volume →
      (∀ i, MemLp (spatialTestDerivative i ψ) 2 volume) →
      Integrable (fun x : Space => ∑ i : Fin 3, w x i * (spatialTestDerivative i ψ x : ℂ)) volume ∧
      (∫ x : Space, ∑ i : Fin 3, w x i * (spatialTestDerivative i ψ x : ℂ)) = 0 := by
    intro ψ hψ hψ2 hdψ2
    have hint : Integrable (fun x : Space => ∑ i : Fin 3, w x i * (spatialTestDerivative i ψ x : ℂ)) volume := by
      refine integrable_finsetSum _ fun i _ => ?_
      have hmul := (Lp.memLp w).norm.integrable_mul (hdψ2 i).norm
      have hmeas : AEStronglyMeasurable (fun x : Space => w x i * (spatialTestDerivative i ψ x : ℂ)) volume := by
        have hw_i : AEStronglyMeasurable (fun x : Space => w x i) volume :=
          (EuclideanSpace.proj i : CVec3 →L[ℂ] ℂ).continuous.comp_aestronglyMeasurable (Lp.aestronglyMeasurable w)
        exact hw_i.mul (Complex.continuous_ofReal.comp_aestronglyMeasurable (hdψ2 i).1)
      refine hmul.mono' hmeas (Eventually.of_forall fun x => ?_)
      rw [norm_mul, Complex.norm_real]
      exact mul_le_mul_of_nonneg_right (PiLp.norm_apply_le (w x) i) (norm_nonneg _)
    have hre_ae := reV.coeFn_compLpL (μ := (volume : Measure Space)) (p := 2) w
    have him_ae := imV.coeFn_compLpL (μ := (volume : Measure Space)) (p := 2) w
    refine ⟨hint, ?_⟩
    apply Complex.ext
    · have h1 := integral_re hint
      simp only [RCLike.re_to_complex] at h1
      rw [← h1]
      have h2 : (∫ x : Space, (∑ i : Fin 3, w x i * (spatialTestDerivative i ψ x : ℂ)).re) =
          ∫ x : Space, ∑ i : Fin 3, (reV.compLpL 2 volume w x) i * spatialTestDerivative i ψ x := by
        refine integral_congr_ae ?_
        filter_upwards [hre_ae] with x hx
        rw [B0414.re_divPairing, hx]
      rw [h2]
      exact solenoidal_schwartz_real hw.1 hψ hψ2 hdψ2
    · have h1 := integral_im hint
      simp only [RCLike.im_to_complex] at h1
      rw [← h1]
      have h2 : (∫ x : Space, (∑ i : Fin 3, w x i * (spatialTestDerivative i ψ x : ℂ)).im) =
          ∫ x : Space, ∑ i : Fin 3, (imV.compLpL 2 volume w x) i * spatialTestDerivative i ψ x := by
        refine integral_congr_ae ?_
        filter_upwards [him_ae] with x hx
        rw [B0414.im_divPairing, hx]
      rw [h2]
      exact solenoidal_schwartz_real hw.2 hψ hψ2 hdψ2
  obtain ⟨hint_r, h0_r⟩ := hreal gr hgr_s mr mdr
  obtain ⟨hint_i, h0_i⟩ := hreal gi hgi_s mi mdi
  have heq : (fun x : Space => ∑ i : Fin 3, (w x i) * (∂_{coordinateVector i} g x)) =
      fun x : Space => (∑ i : Fin 3, w x i * (spatialTestDerivative i gr x : ℂ)) +
        Complex.I * (∑ i : Fin 3, w x i * (spatialTestDerivative i gi x : ℂ)) := by
    funext x
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hdg : ∂_{coordinateVector i} g x =
        (spatialTestDerivative i gr x : ℂ) + (spatialTestDerivative i gi x : ℂ) * Complex.I := by
      rw [hdgr, hdgi]
      exact (Complex.re_add_im (∂_{coordinateVector i} g x)).symm
    rw [hdg]
    ring
  rw [heq, integral_add hint_r (hint_i.const_mul Complex.I), integral_const_mul, h0_r, h0_i]
  simp

private lemma mem_solenoidalC_iff_fourier (w : Lp CVec3 2 (volume : Measure Space)) :
    w ∈ B0414.solenoidalC ↔
      ∀ᵐ ξ ∂(volume : Measure Space),
        ∑ i : Fin 3, (ξ i : ℂ) * ((𝓕 w : Lp CVec3 2 volume) ξ i) = 0 := by
  constructor
  · intro hw
    set f : Space → ℂ := fun ξ =>
      (2 * Real.pi * Complex.I) * ∑ i : Fin 3, (ξ i : ℂ) * ((𝓕 w : Lp CVec3 2 volume) ξ i)
    have hfloc : LocallyIntegrable f volume := by
      have hsum : LocallyIntegrable (fun ξ : Space =>
          ∑ i : Fin 3, ((2 * Real.pi * Complex.I) * (ξ i : ℂ)) •
            ((EuclideanSpace.proj i : CVec3 →L[ℂ] ℂ) ((𝓕 w : Lp CVec3 2 volume) ξ))) volume := by
        refine locallyIntegrable_finsetSum _ fun i _ => ?_
        have hwloc : LocallyIntegrable (fun ξ : Space => (EuclideanSpace.proj i : CVec3 →L[ℂ] ℂ)
            ((𝓕 w : Lp CVec3 2 volume) ξ)) volume := by
          change LocallyIntegrable (⇑(EuclideanSpace.proj i : CVec3 →L[ℂ] ℂ) ∘
            ((𝓕 w : Lp CVec3 2 volume) : Space → CVec3)) volume
          exact ((EuclideanSpace.proj i : CVec3 →L[ℂ] ℂ).comp_memLp (p := 2)
            (𝓕 w : Lp CVec3 2 volume)).locallyIntegrable one_le_two
        have hcont : Continuous (fun ξ : Space => (2 * Real.pi * Complex.I) * (ξ i : ℂ)) :=
          continuous_const.mul (Complex.continuous_ofReal.comp (PiLp.continuous_apply 2 _ i))
        exact hwloc.continuous_smul hcont
      refine hsum.congr (Eventually.of_forall fun ξ => ?_)
      change ∑ i : Fin 3, ((2 * Real.pi * Complex.I) * (ξ i : ℂ)) * ((𝓕 w : Lp CVec3 2 volume) ξ i) =
        (2 * Real.pi * Complex.I) * ∑ i : Fin 3, (ξ i : ℂ) * ((𝓕 w : Lp CVec3 2 volume) ξ i)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => by ring
    have hae : f =ᵐ[volume] 0 := by
      refine ae_eq_zero_of_integral_contDiff_smul_eq_zero hfloc fun φ hφ hφc => ?_
      have hφc' : HasCompactSupport (fun x : Space => (φ x : ℂ)) := hφc.comp_left Complex.ofReal_zero
      have hφd : ContDiff ℝ ∞ (fun x : Space => (φ x : ℂ)) := Complex.ofRealCLM.contDiff.comp hφ
      set ψ : 𝓢(Space, ℂ) := hφc'.toSchwartzMap hφd
      have hψ : ∀ ξ : Space, φ ξ • f ξ = ψ ξ * f ξ := fun ξ => by
        change φ ξ • f ξ = (φ ξ : ℂ) * f ξ
        exact Complex.real_smul
      simp_rw [hψ]
      rw [fourier_div_schwartz w ψ, solenoidalC_schwartz hw (𝓕 ψ), neg_zero]
    filter_upwards [hae] with ξ hξ
    have hne : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    exact (mul_eq_zero.mp hξ).resolve_left hne
  · intro h0
    rw [B0414.mem_solenoidalC_iff]
    have hboth : ∀ φ : Space → ℝ, IsSpatialTest φ →
        Integrable (fun x : Space => ∑ i : Fin 3, w x i * (spatialTestDerivative i φ x : ℂ)) volume ∧
          (∫ x : Space, ∑ i : Fin 3, w x i * (spatialTestDerivative i φ x : ℂ)) = 0 := by
      intro φ hφ
      have hφc' : HasCompactSupport (fun x : Space => (φ x : ℂ)) := hφ.2.comp_left Complex.ofReal_zero
      have hφd : ContDiff ℝ ∞ (fun x : Space => (φ x : ℂ)) := Complex.ofRealCLM.contDiff.comp hφ.1
      let ψ : 𝓢(Space, ℂ) := hφc'.toSchwartzMap hφd
      have hψf : (ψ : Space → ℂ) = fun y : Space => (φ y : ℂ) := funext fun _ => rfl
      have hd : ∀ i x, (spatialTestDerivative i φ x : ℂ) = ∂_{coordinateVector i} ψ x := by
        intro i x
        rw [spatialTestDerivative, SchwartzMap.lineDerivOp_apply_eq_fderiv, hψf]
        have hfd : HasFDerivAt (fun y : Space => (φ y : ℂ))
            (Complex.ofRealCLM.comp (fderiv ℝ φ x)) x :=
          Complex.ofRealCLM.hasFDerivAt.comp x (hφ.1.differentiable (by simp) x).hasFDerivAt
        rw [hfd.fderiv]; rfl
      refine ⟨?_, ?_⟩
      · refine integrable_finsetSum _ fun i _ => ?_
        have hi := (EuclideanSpace.proj i : CVec3 →L[ℂ] ℂ).integrable_comp
          (integrable_schwartz_smul_lp (∂_{coordinateVector i} ψ) w)
        refine hi.congr (Eventually.of_forall fun x => ?_)
        change ((∂_{coordinateVector i} ψ) x • (w x : CVec3)) i = w x i * (spatialTestDerivative i φ x : ℂ)
        rw [hd i x]
        simp only [PiLp.smul_apply, smul_eq_mul]
        ring
      · have heq : (∫ x : Space, ∑ i : Fin 3, w x i * (spatialTestDerivative i φ x : ℂ)) =
            ∫ x : Space, ∑ i : Fin 3, w x i * (∂_{coordinateVector i} (𝓕 (𝓕⁻ ψ)) x) := by
          refine integral_congr_ae (Eventually.of_forall fun x => ?_)
          refine Finset.sum_congr rfl fun i _ => by rw [fourier_fourierInv_eq, hd i x]
        rw [heq, ← neg_eq_zero, ← fourier_div_schwartz w (𝓕⁻ ψ)]
        refine integral_eq_zero_of_ae ?_
        filter_upwards [h0] with ξ hξ
        simp [hξ]
    exact ⟨fun φ hφ => (hboth φ hφ).1, fun φ hφ => (hboth φ hφ).2⟩

private lemma aestronglyMeasurable_piVec {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {g : α → Space} (hg : Measurable g) {f : α → CVec3} (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (fun a : α => piVec (g a) (f a)) μ := by
  have hcoord : ∀ j : Fin 3, AEStronglyMeasurable (fun a : α => f a j) μ := fun j =>
    (EuclideanSpace.proj j : CVec3 →L[ℂ] ℂ).continuous.comp_aestronglyMeasurable hf
  have hxi : ∀ j : Fin 3, AEStronglyMeasurable (fun a : α => (g a j : ℂ)) μ := fun j =>
    (Complex.measurable_ofReal.comp ((PiLp.continuous_apply 2 _ j).measurable.comp hg)).aestronglyMeasurable
  have hnorm_inv : AEStronglyMeasurable (fun a : α => (((‖g a‖ : ℂ) ^ 2))⁻¹) μ :=
    (((Complex.measurable_ofReal.comp (continuous_norm.measurable.comp hg)).pow_const 2).inv).aestronglyMeasurable
  have hsum : AEStronglyMeasurable (fun a : α =>
      (∑ j : Fin 3, (g a j : ℂ) * f a j) / ((‖g a‖ : ℂ) ^ 2)) μ := by
    simp only [div_eq_mul_inv]
    exact (Finset.univ.aestronglyMeasurable_sum fun j _ => (hxi j).mul (hcoord j)).mul hnorm_inv
  have hvec_cont : Continuous (fun x : Space => (WithLp.toLp 2 fun i : Fin 3 => (x i : ℂ) : CVec3)) :=
    (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℂ)).comp
      (continuous_pi fun i => Complex.continuous_ofReal.comp (PiLp.continuous_apply 2 _ i))
  have hvec : AEStronglyMeasurable (fun a : α =>
      (WithLp.toLp 2 fun i : Fin 3 => (g a i : ℂ) : CVec3)) μ :=
    (hvec_cont.measurable.comp hg).aestronglyMeasurable
  exact hf.sub (hsum.smul hvec)

private lemma fourier_lerayC_two (F : Lp CVec3 2 (volume : Measure Space)) :
    ((𝓕 (lerayC 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top F) : Lp CVec3 2 volume) : Space → CVec3) =ᵐ[volume]
      fun ξ : Space => piVec ξ ((𝓕 F : Lp CVec3 2 volume) ξ) := by
  set g_hat_fn : Space → CVec3 := fun ξ => piVec ξ ((𝓕 F : Lp CVec3 2 volume) ξ)
  have hg_hat_lp : MemLp g_hat_fn 2 volume :=
    (Lp.memLp (𝓕 F : Lp CVec3 2 volume)).of_le
      (aestronglyMeasurable_piVec measurable_id (Lp.aestronglyMeasurable _))
      (Eventually.of_forall fun ξ => norm_piVec_le ξ _)
  set g_hat : Lp CVec3 2 volume := hg_hat_lp.toLp g_hat_fn
  set g : Lp CVec3 2 volume := 𝓕⁻ g_hat
  have hfg : (𝓕 g : Lp CVec3 2 volume) = g_hat := fourier_fourierInv_eq g_hat
  have hg_sol : g ∈ B0414.solenoidalC := by
    rw [mem_solenoidalC_iff_fourier, hfg]
    filter_upwards [hg_hat_lp.coeFn_toLp] with ξ hξ
    rw [hξ]
    exact sum_mul_piVec ξ _
  have hg_orth : ∀ w ∈ B0414.solenoidalC, ⟪F - g, w⟫_ℂ = 0 := by
    intro w hw
    rw [← (Lp.fourierTransformₗᵢ Space CVec3).inner_map_map (F - g) w, map_sub]
    change ⟪(𝓕 F : Lp CVec3 2 volume) - (𝓕 g : Lp CVec3 2 volume), (𝓕 w : Lp CVec3 2 volume)⟫_ℂ = 0
    rw [hfg, L2.inner_def]
    refine integral_eq_zero_of_ae ?_
    filter_upwards [Lp.coeFn_sub (𝓕 F : Lp CVec3 2 volume) g_hat, hg_hat_lp.coeFn_toLp,
      (mem_solenoidalC_iff_fourier w).mp hw] with ξ hsub hgh hwξ
    rw [Pi.sub_apply] at hsub
    rw [hsub, hgh]
    exact inner_sub_piVec_eq_zero _ _ hwξ
  have hleray : lerayC 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top F = g := by
    rw [B0414.lerayC_two]
    exact Submodule.eq_starProjection_of_mem_of_inner_eq_zero hg_sol hg_orth
  rw [hleray, hfg]
  exact hg_hat_lp.coeFn_toLp

private lemma phaseFourier_lerayY_ae {P : ℝ} [Fact (0 < P)] (u : Yq P 2) :
    (FreeStress.phaseFourier P (lerayY P 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top u) :
        AddCircle P × Space → CVec3) =ᵐ[FreeStress.phaseVol P]
      fun z => piVec z.2 (FreeStress.phaseFourier P u z) := by
  have hmL := Lp.aestronglyMeasurable
    (FreeStress.phaseFourier P (lerayY P 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top u))
  have hmR : AEStronglyMeasurable (fun z : AddCircle P × Space =>
      piVec z.2 (FreeStress.phaseFourier P u z)) (FreeStress.phaseVol P) :=
    aestronglyMeasurable_piVec measurable_snd (Lp.aestronglyMeasurable (FreeStress.phaseFourier P u))
  rw [FreeStress.ae_eq_prod_iff hmL hmR]
  filter_upwards [FreeStress.phaseFourier_slice_ae P
      (lerayY P 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top u),
    FreeStress.phaseFourier_slice_ae P u,
    coeFn_lerayY ENNReal.one_lt_two ENNReal.ofNat_ne_top u] with τ h1 h2 h3
  have hfourier : (Lp.fourierTransformₗᵢ Space CVec3
      (lerayY P 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top u τ) : Space → CVec3) =ᵐ[volume]
      fun ξ : Space => piVec ξ ((Lp.fourierTransformₗᵢ Space CVec3 (u τ) : Lp CVec3 2 volume) ξ) := by
    rw [h3]
    exact fourier_lerayC_two (u τ)
  filter_upwards [h1, h2, hfourier] with ξ e1 e2 e3
  rw [e1, e3, e2]

private lemma phaseD0_hasPow_lerayY {P : ℝ} [Fact (0 < P)] {ν : ℝ} (hν : 0 ≤ ν)
    (s : ℝ) {u v : Yq P 2} (h : (FreeStress.phaseD0 P ν hν).HasPow s u v) :
    (FreeStress.phaseD0 P ν hν).HasPow s
      (lerayY P 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top u)
      (lerayY P 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top v) := by
  unfold FreeStress.MulRep.HasPow at h ⊢
  filter_upwards [phaseFourier_lerayY_ae u, phaseFourier_lerayY_ae v, h] with z hu hv hz
  change (FreeStress.phaseFourier P (lerayY P 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top v) :
      AddCircle P × Space → CVec3) z =
    (((FreeStress.phaseD0 P ν hν).sym z ^ s : ℝ) : ℂ) •
      (FreeStress.phaseFourier P (lerayY P 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top u) :
        AddCircle P × Space → CVec3) z
  rw [hv, hu, ← piVec_smul]
  exact congrArg (piVec z.2) hz

/-! ### Section L2: Bounded Riesz-divergence multiplier `rieszDivOp` -/

private def coordSwap (i j : Fin 3) : CVec3 →L[ℂ] CVec3 :=
  LinearMap.mkContinuous
    { toFun := fun v => WithLp.toLp 2 fun k : Fin 3 => if k = i then v j else 0
      map_add' := fun u v => by ext k; simp [ite_add_zero]
      map_smul' := fun c v => by ext k; simp }
    1 fun v => by
      rw [one_mul]
      change ‖(WithLp.toLp 2 fun k : Fin 3 => if k = i then v j else 0 : CVec3)‖ ≤ ‖v‖
      have h1 : ‖(WithLp.toLp 2 fun k : Fin 3 => if k = i then v j else 0 : CVec3)‖ ^ 2 = ‖v j‖ ^ 2 := by
        rw [PiLp.norm_sq_eq_of_L2]
        simp [apply_ite norm, Finset.sum_ite_eq']
      have h2 : ‖v j‖ ≤ ‖v‖ := PiLp.norm_apply_le v j
      refine nonneg_le_nonneg_of_sq_le_sq (norm_nonneg _) ?_
      rw [← sq, ← sq, h1]
      exact sq_le_sq.mpr (by rw [abs_norm, abs_norm]; exact h2)

private lemma coordSwap_apply (i j k : Fin 3) (v : CVec3) :
    coordSwap i j v k = if k = i then v j else 0 := rfl

private lemma norm_coordSwap_le (i j : Fin 3) : ‖coordSwap i j‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

private def divSym (P : ℝ) (ν : ℝ) (j : Fin 3) (z : AddCircle P × Space) : ℂ :=
  (((1 + FreeStress.laplaceSym ν z.2) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
    (2 * Real.pi * Complex.I * (z.2 j : ℂ))

private lemma aestronglyMeasurable_divSym (P : ℝ) [Fact (0 < P)] (ν : ℝ) (hν : 0 < ν) (j : Fin 3) :
    AEStronglyMeasurable (divSym P ν j) (FreeStress.phaseVol P) := by
  have hm1 : Measurable fun z : AddCircle P × Space =>
      (((1 + FreeStress.laplaceSym ν z.2) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) :=
    Complex.measurable_ofReal.comp
      ((measurable_const.add (FreeStress.laplaceRepY P ν hν.le).measurable_sym).pow_const _)
  have hm2 : Measurable fun z : AddCircle P × Space => 2 * Real.pi * Complex.I * (z.2 j : ℂ) :=
    measurable_const.mul (Complex.measurable_ofReal.comp
      ((PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) j).measurable.comp measurable_snd))
  exact (hm1.mul hm2).aestronglyMeasurable

private lemma norm_divSym_le (P : ℝ) [Fact (0 < P)] {ν : ℝ} (hν : 0 < ν) (j : Fin 3)
    (z : AddCircle P × Space) :
    ‖divSym P ν j z‖ ≤ ν ^ (-(1 / 2 : ℝ)) := by
  set L : ℝ := FreeStress.laplaceSym ν z.2
  have hL : 0 ≤ L := (FreeStress.laplaceRepY P ν hν.le).sym_nonneg z
  have h1L : 0 < 1 + L := by linarith
  have hrpow_pos : 0 ≤ (1 + L) ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg h1L.le _
  have hnorm : ‖divSym P ν j z‖ = (1 + L) ^ (-(1 / 2 : ℝ)) * (2 * Real.pi * ‖z.2 j‖) := by
    unfold divSym
    rw [norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_of_nonneg hrpow_pos,
      Complex.norm_ofNat, Complex.norm_of_nonneg Real.pi_pos.le, Complex.norm_I, mul_one,
      Complex.norm_real]
  rw [hnorm]
  have hsq : ∀ a : ℝ, 0 < a → (a ^ (-(1 / 2 : ℝ))) ^ 2 = a⁻¹ := fun a ha => by
    rw [sq, ← Real.rpow_add ha, show -(1 / 2 : ℝ) + -(1 / 2 : ℝ) = -1 by ring, Real.rpow_neg_one]
  refine nonneg_le_nonneg_of_sq_le_sq (Real.rpow_nonneg hν.le _) ?_
  rw [← sq, ← sq, mul_pow, hsq (1 + L) h1L, hsq ν hν]
  have hj : (2 * Real.pi * ‖z.2 j‖) ^ 2 * ν ≤ 1 + L := by
    have hle : ‖z.2 j‖ ^ 2 ≤ ‖z.2‖ ^ 2 :=
      sq_le_sq.mpr (by rw [abs_norm, abs_norm]; exact PiLp.norm_apply_le z.2 j)
    have hmul : ν * (2 * Real.pi) ^ 2 * ‖z.2 j‖ ^ 2 ≤ L := by
      change ν * (2 * Real.pi) ^ 2 * ‖z.2 j‖ ^ 2 ≤ ν * ((2 * Real.pi) ^ 2 * ‖z.2‖ ^ 2)
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_left hle (by positivity)
    linarith
  have h1 : ((1 + L)⁻¹ * (2 * Real.pi * ‖z.2 j‖) ^ 2) * (1 + L) * ν =
      (2 * Real.pi * ‖z.2 j‖) ^ 2 * ν := by
    calc ((1 + L)⁻¹ * (2 * Real.pi * ‖z.2 j‖) ^ 2) * (1 + L) * ν
        = ((1 + L)⁻¹ * (1 + L)) * (2 * Real.pi * ‖z.2 j‖) ^ 2 * ν := by ring
      _ = (2 * Real.pi * ‖z.2 j‖) ^ 2 * ν := by rw [inv_mul_cancel₀ h1L.ne', one_mul]
  have h2 : ν⁻¹ * (1 + L) * ν = 1 + L := by
    calc ν⁻¹ * (1 + L) * ν = (ν⁻¹ * ν) * (1 + L) := by ring
      _ = 1 + L := by rw [inv_mul_cancel₀ hν.ne', one_mul]
  exact le_of_mul_le_mul_right (le_of_mul_le_mul_right (by linarith) hν) h1L

private lemma ae_norm_divSym_le (P : ℝ) [Fact (0 < P)] {ν : ℝ} (hν : 0 < ν) (j : Fin 3) :
    ∀ᵐ z ∂(FreeStress.phaseVol P), ‖divSym P ν j z‖ ≤ ν ^ (-(1 / 2 : ℝ)) :=
  Eventually.of_forall (norm_divSym_le P hν j)

private def rieszTermHat (P : ℝ) [Fact (0 < P)] (ν : ℝ) (hν : 0 < ν) (i j : Fin 3) :
    Y2Sym P →L[ℂ] Lp CVec3 2 (FreeStress.phaseVol P) :=
  (((coordSwap i j).compLpL 2 (FreeStress.phaseVol P)).comp
    (Mult.mulOp (E := CVec3) (p := 2) (divSym P ν j)
      (aestronglyMeasurable_divSym P ν hν j) (ae_norm_divSym_le P hν j))).comp
    ((FreeStress.phaseFourier P).toLinearIsometry.toContinuousLinearMap.comp
      (PiLp.proj 2 (fun _ : Fin 3 => Yq P 2) i))

private lemma norm_rieszTermHat_apply_le (P : ℝ) [Fact (0 < P)] {ν : ℝ} (hν : 0 < ν)
    (i j : Fin 3) (T : Y2Sym P) :
    ‖rieszTermHat P ν hν i j T‖ ≤ ν ^ (-(1 / 2 : ℝ)) * ‖T‖ := by
  dsimp [rieszTermHat]
  set v : Lp CVec3 2 (FreeStress.phaseVol P) :=
    Mult.mulOp (E := CVec3) (p := 2) (divSym P ν j) (aestronglyMeasurable_divSym P ν hν j)
      (ae_norm_divSym_le P hν j) (FreeStress.phaseFourier P (T i))
  have h1 : ‖(coordSwap i j).compLpL 2 (FreeStress.phaseVol P) v‖ ≤ ‖v‖ := by
    calc ‖(coordSwap i j).compLpL 2 (FreeStress.phaseVol P) v‖
        ≤ ‖(coordSwap i j).compLpL 2 (FreeStress.phaseVol P)‖ * ‖v‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * ‖v‖ := mul_le_mul_of_nonneg_right
          ((ContinuousLinearMap.norm_compLpL_le (coordSwap i j)).trans (norm_coordSwap_le i j))
          (norm_nonneg _)
      _ = ‖v‖ := one_mul _
  have h2 : ‖v‖ ≤ ν ^ (-(1 / 2 : ℝ)) * ‖T‖ := by
    have hpos : 0 ≤ ν ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hν.le _
    calc ‖v‖ ≤ ‖(Mult.mulOp (E := CVec3) (p := 2) (divSym P ν j)
          (aestronglyMeasurable_divSym P ν hν j) (ae_norm_divSym_le P hν j) :
            Lp CVec3 2 (FreeStress.phaseVol P) →L[ℂ] Lp CVec3 2 (FreeStress.phaseVol P))‖ *
          ‖FreeStress.phaseFourier P (T i)‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ max (ν ^ (-(1 / 2 : ℝ))) 0 * ‖T i‖ := by
          rw [(FreeStress.phaseFourier P).norm_map]
          exact mul_le_mul_of_nonneg_right (Mult.norm_mulOp_le _ _) (norm_nonneg _)
      _ = ν ^ (-(1 / 2 : ℝ)) * ‖T i‖ := by rw [max_eq_left hpos]
      _ ≤ ν ^ (-(1 / 2 : ℝ)) * ‖T‖ :=
          mul_le_mul_of_nonneg_left (PiLp.norm_apply_le T i) hpos
  exact h1.trans h2

private def rieszRawOp (P : ℝ) [Fact (0 < P)] (ν : ℝ) (hν : 0 < ν) :
    Y2Sym P →L[ℂ] Yq P 2 :=
  (FreeStress.phaseFourier P).symm.toLinearIsometry.toContinuousLinearMap.comp
    (∑ i : Fin 3, ∑ j : Fin 3, rieszTermHat P ν hν i j)

private def rieszDivOp (P : ℝ) [Fact (0 < P)] (ν : ℝ) (hν : 0 < ν) :
    symY2 P →L[ℂ] Yq P 2 :=
  ((lerayY P 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top).comp (rieszRawOp P ν hν)).comp
    (symY2 P).subtypeL

private lemma norm_rieszDivOp_le (P : ℝ) [Fact (0 < P)] {ν : ℝ} (hν : 0 < ν) :
    ‖rieszDivOp P ν hν‖ ≤ 9 * ν ^ (-(1 / 2 : ℝ)) := by
  have hpos : 0 ≤ 9 * ν ^ (-(1 / 2 : ℝ)) := by positivity
  refine ContinuousLinearMap.opNorm_le_bound _ hpos fun T => ?_
  dsimp [rieszDivOp, rieszRawOp]
  set S := ∑ i : Fin 3, ∑ j : Fin 3, rieszTermHat P ν hν i j (T : Y2Sym P)
  have h1 : ‖lerayY P 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top
      ((FreeStress.phaseFourier P).symm S)‖ ≤ ‖S‖ := by
    calc ‖lerayY P 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top
          ((FreeStress.phaseFourier P).symm S)‖
        ≤ ‖lerayY P 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top‖ *
            ‖(FreeStress.phaseFourier P).symm S‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * ‖S‖ := by
          rw [(FreeStress.phaseFourier P).symm.norm_map]
          exact mul_le_mul_of_nonneg_right B0414.norm_lerayY_two_le (norm_nonneg _)
      _ = ‖S‖ := one_mul _
  have h2 : ‖S‖ ≤ ∑ i : Fin 3, ∑ j : Fin 3, ν ^ (-(1 / 2 : ℝ)) * ‖(T : Y2Sym P)‖ := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ =>
      norm_rieszTermHat_apply_le P hν i j (T : Y2Sym P))
  have h3 : (∑ _i : Fin 3, ∑ _j : Fin 3, ν ^ (-(1 / 2 : ℝ)) * ‖(T : Y2Sym P)‖) =
      9 * ν ^ (-(1 / 2 : ℝ)) * ‖T‖ := by
    change (∑ _i : Fin 3, ∑ _j : Fin 3, ν ^ (-(1 / 2 : ℝ)) * ‖T‖) = _
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  exact (h1.trans h2).trans_eq h3

/-! ### Section L3: Smooth tensor divergence identity and `tensorDivRiesz` -/

private lemma coeFn_sum_fin3 {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (f : Fin 3 → Lp CVec3 2 μ) :
    ((∑ i : Fin 3, f i : Lp CVec3 2 μ) : α → CVec3) =ᵐ[μ] fun a => ∑ i : Fin 3, f i a := by
  simp only [Fin.sum_univ_three]
  filter_upwards [Lp.coeFn_add (f 0 + f 1) (f 2), Lp.coeFn_add (f 0) (f 1)] with a h1 h2
  rw [Pi.add_apply] at h1 h2
  rw [h1, h2]

private lemma phaseFourier_rieszRawOp_ae (P : ℝ) [Fact (0 < P)] {ν : ℝ} (hν : 0 < ν)
    (T : Y2Sym P) :
    (FreeStress.phaseFourier P (rieszRawOp P ν hν T) : AddCircle P × Space → CVec3) =ᵐ[FreeStress.phaseVol P]
      fun z => WithLp.toLp 2 fun i : Fin 3 =>
        ∑ j : Fin 3, divSym P ν j z * (FreeStress.phaseFourier P (T i) z j) := by
  have hsymm : FreeStress.phaseFourier P (rieszRawOp P ν hν T) =
      ∑ i : Fin 3, ∑ j : Fin 3, rieszTermHat P ν hν i j T := by
    dsimp [rieszRawOp]
    rw [(FreeStress.phaseFourier P).apply_symm_apply]
    simp only [FunLike.coe_sum, Finset.sum_apply]
  rw [hsymm]
  have hterm : ∀ i j : Fin 3,
      (rieszTermHat P ν hν i j T : AddCircle P × Space → CVec3) =ᵐ[FreeStress.phaseVol P]
        fun z => coordSwap i j (divSym P ν j z • FreeStress.phaseFourier P (T i) z) := by
    intro i j
    filter_upwards [ContinuousLinearMap.coeFn_compLpL (coordSwap i j)
        (Mult.mulOp (E := CVec3) (p := 2) (divSym P ν j) (aestronglyMeasurable_divSym P ν hν j)
          (ae_norm_divSym_le P hν j) (FreeStress.phaseFourier P (T i))),
      Mult.coeFn_mulOp (E := CVec3) (p := 2) (aestronglyMeasurable_divSym P ν hν j)
        (ae_norm_divSym_le P hν j) (FreeStress.phaseFourier P (T i))] with z h1 h2
    change ((coordSwap i j).compLpL 2 (FreeStress.phaseVol P)
      (Mult.mulOp (E := CVec3) (p := 2) (divSym P ν j) (aestronglyMeasurable_divSym P ν hν j)
        (ae_norm_divSym_le P hν j) (FreeStress.phaseFourier P (T i))) :
      AddCircle P × Space → CVec3) z = _
    rw [h1, h2]
  have hrow : ∀ i : Fin 3,
      ((∑ j : Fin 3, rieszTermHat P ν hν i j T : Lp CVec3 2 (FreeStress.phaseVol P)) :
        AddCircle P × Space → CVec3) =ᵐ[FreeStress.phaseVol P]
        fun z => ∑ j : Fin 3, coordSwap i j (divSym P ν j z • FreeStress.phaseFourier P (T i) z) := by
    intro i
    filter_upwards [coeFn_sum_fin3 (fun j => rieszTermHat P ν hν i j T),
      hterm i 0, hterm i 1, hterm i 2] with z hs h0 h1 h2
    rw [hs]
    refine Finset.sum_congr rfl fun j _ => ?_
    fin_cases j <;> assumption
  filter_upwards [coeFn_sum_fin3 (fun i => ∑ j : Fin 3, rieszTermHat P ν hν i j T),
    hrow 0, hrow 1, hrow 2] with z hs h0 h1 h2
  rw [hs]
  have hsum : (∑ i : Fin 3, (∑ j : Fin 3, rieszTermHat P ν hν i j T :
      Lp CVec3 2 (FreeStress.phaseVol P)) z) =
      ∑ i : Fin 3, ∑ j : Fin 3, coordSwap i j (divSym P ν j z • FreeStress.phaseFourier P (T i) z) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    fin_cases i <;> assumption
  rw [hsum]
  ext k
  simp only [Fin.sum_univ_three, PiLp.add_apply, coordSwap_apply, PiLp.smul_apply, smul_eq_mul]
  fin_cases k <;> simp

private lemma isPhaseTest_tensorDiv {P : ℝ} {G : Fin 3 → ℝ × Space → CVec3}
    (hG : ∀ i : Fin 3, IsPhaseTest P (G i)) :
    IsPhaseTest P (tensorDiv G) := by
  have heq : tensorDiv G =
      ∑ i : Fin 3, ∑ j : Fin 3, fun p => (coordSwap i j).restrictScalars ℝ (dy j (G i) p) := by
    funext p; ext k
    simp only [tensorDiv, Finset.sum_apply, Fin.sum_univ_three, PiLp.add_apply]
    change dy 0 (G k) p 0 + dy 1 (G k) p 1 + dy 2 (G k) p 2 =
      ((coordSwap 0 0 (dy 0 (G 0) p) k + coordSwap 0 1 (dy 1 (G 0) p) k + coordSwap 0 2 (dy 2 (G 0) p) k) +
       (coordSwap 1 0 (dy 0 (G 1) p) k + coordSwap 1 1 (dy 1 (G 1) p) k + coordSwap 1 2 (dy 2 (G 1) p) k)) +
       (coordSwap 2 0 (dy 0 (G 2) p) k + coordSwap 2 1 (dy 1 (G 2) p) k + coordSwap 2 2 (dy 2 (G 2) p) k)
    simp only [coordSwap_apply]
    fin_cases k <;> simp
  rw [heq]
  exact IsPhaseTest.sum _ fun i _ => IsPhaseTest.sum _ fun j _ =>
    ((hG i).dy j).clm_comp ((coordSwap i j).restrictScalars ℝ)

private def sliceSchwartz {P : ℝ} {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ) (t : ℝ) :
    𝓢(Space, CVec3) :=
  (hΦ.hasCompactSupport_slice t).toSchwartzMap (hΦ.smooth.comp (contDiff_const.prodMk contDiff_id))

private lemma sliceSchwartz_apply {P : ℝ} {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ)
    (t : ℝ) (y : Space) :
    sliceSchwartz hΦ t y = Φ (t, y) := rfl

private lemma sliceSchwartz_dy {P : ℝ} {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ)
    (j : Fin 3) (t : ℝ) :
    sliceSchwartz (hΦ.dy j) t = ∂_{coordinateVector j} (sliceSchwartz hΦ t) := by
  ext y
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv, sliceSchwartz_apply]
  have hfun : (sliceSchwartz hΦ t : Space → CVec3) = fun y' : Space => Φ (t, y') :=
    funext fun _ => rfl
  rw [hfun, dy]
  have h1 : HasFDerivAt Φ (fderiv ℝ Φ (t, y)) (t, y) :=
    (hΦ.smooth.differentiable (by simp) (t, y)).hasFDerivAt
  have h2 : HasFDerivAt (fun y' : Space => ((t, y') : ℝ × Space))
      (ContinuousLinearMap.inr ℝ ℝ Space) y :=
    (hasFDerivAt_const t y).prodMk (hasFDerivAt_id y)
  have hcomp : HasFDerivAt (fun y' : Space => Φ (t, y'))
      ((fderiv ℝ Φ (t, y)).comp (ContinuousLinearMap.inr ℝ ℝ Space)) y :=
    h1.comp y h2
  rw [hcomp.fderiv]
  rfl

private lemma fourier_sliceMap_ae {P : ℝ} {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ) (t : ℝ) :
    ((Lp.fourierTransformₗᵢ Space CVec3 (sliceMap (hΦ.isSliceTest 2).2 t) : Lp CVec3 2 volume) :
        Space → CVec3) =ᵐ[volume]
      fun ξ : Space => 𝓕 (sliceSchwartz hΦ t) ξ := by
  have htoLp : sliceMap (hΦ.isSliceTest 2).2 t = (sliceSchwartz hΦ t).toLp 2 volume :=
    MemLp.toLp_congr _ _ (Eventually.of_forall fun _ => rfl)
  rw [htoLp]
  change ((𝓕 ((sliceSchwartz hΦ t).toLp 2 volume) : Lp CVec3 2 volume) : Space → CVec3) =ᵐ[volume] _
  rw [SchwartzMap.toLp_fourier_eq]
  exact (𝓕 (sliceSchwartz hΦ t)).coeFn_toLp 2 volume

private lemma schwartz_fourier_coord (f : 𝓢(Space, CVec3)) (i : Fin 3) (ξ : Space) :
    (𝓕 f ξ) i = ∫ y : Space, Real.fourierChar (-⟪y, ξ⟫_ℝ) • (f y i) := by
  have hint := (Real.fourierIntegral_convergent_iff ξ).mpr (f.integrable (μ := volume))
  have h := (EuclideanSpace.proj i : CVec3 →L[ℂ] ℂ).integral_comp_comm hint
  exact h.symm

private lemma fourier_sliceSchwartz_tensorDiv {P : ℝ} {G : Fin 3 → ℝ × Space → CVec3}
    (hG : ∀ i : Fin 3, IsPhaseTest P (G i)) (t : ℝ) (ξ : Space) (i : Fin 3) :
    (𝓕 (sliceSchwartz (isPhaseTest_tensorDiv hG) t) ξ) i =
      ∑ j : Fin 3, (2 * Real.pi * Complex.I * (ξ j : ℂ)) *
        (𝓕 (sliceSchwartz (hG i) t) ξ j) := by
  rw [schwartz_fourier_coord]
  have hint : ∀ j ∈ (Finset.univ : Finset (Fin 3)),
      Integrable (fun y : Space => Real.fourierChar (-⟪y, ξ⟫_ℝ) •
        (sliceSchwartz ((hG i).dy j) t y j)) volume := by
    intro j _
    have h1 := (Real.fourierIntegral_convergent_iff ξ).mpr
      ((sliceSchwartz ((hG i).dy j) t).integrable (μ := volume))
    exact (EuclideanSpace.proj j : CVec3 →L[ℂ] ℂ).integrable_comp h1
  have hsum : (fun y : Space => Real.fourierChar (-⟪y, ξ⟫_ℝ) •
      (sliceSchwartz (isPhaseTest_tensorDiv hG) t y i)) =
      fun y : Space => ∑ j : Fin 3, Real.fourierChar (-⟪y, ξ⟫_ℝ) •
        (sliceSchwartz ((hG i).dy j) t y j) := by
    funext y
    change Real.fourierChar (-⟪y, ξ⟫_ℝ) • (∑ j : Fin 3, dy j (G i) (t, y) j) = _
    rw [Finset.smul_sum]
    rfl
  rw [hsum, integral_finsetSum _ hint]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← schwartz_fourier_coord (sliceSchwartz ((hG i).dy j) t) j ξ, sliceSchwartz_dy (hG i) j t,
    SchwartzMap.fourier_lineDerivOp_eq]
  have htemp : (fun x : Space => (inner ℝ x (coordinateVector j) : ℝ)).HasTemperateGrowth := by
    fun_prop
  have hxi : inner ℝ ξ (coordinateVector j) = ξ j := by
    simp [coordinateVector, EuclideanSpace.inner_single_right]
  change ((2 * Real.pi * Complex.I) •
      (SchwartzMap.smulLeftCLM CVec3 (fun x : Space => inner ℝ x (coordinateVector j))
        (𝓕 (sliceSchwartz (hG i) t)) ξ)) j = _
  simp only [SchwartzMap.smulLeftCLM_apply_apply htemp, hxi, PiLp.smul_apply,
    Complex.real_smul, smul_eq_mul]
  ring

private lemma phaseFourier_tensorDiv_ae {P : ℝ} [Fact (0 < P)] {G : Fin 3 → ℝ × Space → CVec3}
    (hG : ∀ i : Fin 3, IsPhaseTest P (G i)) :
    (FreeStress.phaseFourier P (testElem P 2 (tensorDiv G)) :
        AddCircle P × Space → CVec3) =ᵐ[FreeStress.phaseVol P]
      fun z => WithLp.toLp 2 fun i : Fin 3 =>
        ∑ j : Fin 3, (2 * Real.pi * Complex.I * (z.2 j : ℂ)) *
          (FreeStress.phaseFourier P (testElem P 2 (G i)) z j) := by
  have hDiv := isPhaseTest_tensorDiv hG
  have hmL := Lp.aestronglyMeasurable (FreeStress.phaseFourier P (testElem P 2 (tensorDiv G)))
  have hmR : AEStronglyMeasurable (fun z : AddCircle P × Space =>
      WithLp.toLp 2 fun i : Fin 3 =>
        ∑ j : Fin 3, (2 * Real.pi * Complex.I * (z.2 j : ℂ)) *
          (FreeStress.phaseFourier P (testElem P 2 (G i)) z j)) (FreeStress.phaseVol P) := by
    have heq : (fun z : AddCircle P × Space => WithLp.toLp 2 fun i : Fin 3 =>
        ∑ j : Fin 3, (2 * Real.pi * Complex.I * (z.2 j : ℂ)) *
          (FreeStress.phaseFourier P (testElem P 2 (G i)) z j)) =
        fun z => ∑ i : Fin 3, ∑ j : Fin 3,
          coordSwap i j ((2 * Real.pi * Complex.I * (z.2 j : ℂ)) •
            FreeStress.phaseFourier P (testElem P 2 (G i)) z) := by
      funext z; ext k
      simp only [Fin.sum_univ_three, PiLp.add_apply, coordSwap_apply, PiLp.smul_apply, smul_eq_mul]
      fin_cases k <;> simp
    rw [heq]
    refine Finset.univ.aestronglyMeasurable_fun_sum fun i _ =>
      Finset.univ.aestronglyMeasurable_fun_sum fun j _ => ?_
    have hm1 : Measurable fun z : AddCircle P × Space => 2 * Real.pi * Complex.I * (z.2 j : ℂ) :=
      measurable_const.mul (Complex.measurable_ofReal.comp
        ((PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) j).measurable.comp measurable_snd))
    exact (coordSwap i j).continuous.comp_aestronglyMeasurable
      (hm1.aestronglyMeasurable.smul
        (Lp.aestronglyMeasurable (FreeStress.phaseFourier P (testElem P 2 (G i)))))
  rw [FreeStress.ae_eq_prod_iff hmL hmR]
  have hte_div : (testElem P 2 (tensorDiv G) : AddCircle P → Lp CVec3 2 volume) =ᵐ[AddCircle.haarAddCircle]
      circleSlice (hDiv.isSliceTest 2) := by
    rw [testElem_of (hDiv.isSliceTest 2)]
    exact ContinuousMap.coeFn_toLp AddCircle.haarAddCircle (circleSlice (hDiv.isSliceTest 2))
  have hte_row : ∀ i : Fin 3,
      (testElem P 2 (G i) : AddCircle P → Lp CVec3 2 volume) =ᵐ[AddCircle.haarAddCircle]
        circleSlice ((hG i).isSliceTest 2) := fun i => by
    rw [testElem_of ((hG i).isSliceTest 2)]
    exact ContinuousMap.coeFn_toLp AddCircle.haarAddCircle (circleSlice ((hG i).isSliceTest 2))
  filter_upwards [FreeStress.phaseFourier_slice_ae P (testElem P 2 (tensorDiv G)),
    FreeStress.phaseFourier_slice_ae P (testElem P 2 (G 0)),
    FreeStress.phaseFourier_slice_ae P (testElem P 2 (G 1)),
    FreeStress.phaseFourier_slice_ae P (testElem P 2 (G 2)),
    hte_div, hte_row 0, hte_row 1, hte_row 2] with τ hsd hs0 hs1 hs2 htd ht0 ht1 ht2
  induction τ using QuotientAddGroup.induction_on with
  | H t =>
    rw [htd, circleSlice_coe] at hsd
    rw [ht0, circleSlice_coe] at hs0
    rw [ht1, circleSlice_coe] at hs1
    rw [ht2, circleSlice_coe] at hs2
    filter_upwards [hsd, hs0, hs1, hs2,
      fourier_sliceMap_ae hDiv t,
      fourier_sliceMap_ae (hG 0) t,
      fourier_sliceMap_ae (hG 1) t,
      fourier_sliceMap_ae (hG 2) t] with ξ ed e0 e1 e2 fd f0 f1 f2
    rw [ed, fd]
    ext i
    rw [fourier_sliceSchwartz_tensorDiv hG t ξ i]
    change _ = ∑ j : Fin 3, (2 * Real.pi * Complex.I * (ξ j : ℂ)) *
      (FreeStress.phaseFourier P (testElem P 2 (G i)) (t, ξ) j)
    fin_cases i
    · simp only [Fin.zero_eta]; refine Finset.sum_congr rfl fun j _ => by rw [e0, f0]
    · simp only [Fin.mk_one]; refine Finset.sum_congr rfl fun j _ => by rw [e1, f1]
    · simp only [Fin.reduceFinMk]; refine Finset.sum_congr rfl fun j _ => by rw [e2, f2]

/-- **Part II-a, task `PartII-a:F16/d`** (`tensorDivRiesz`). -/
theorem tensorDivRiesz : TensorDivRiesz := by
  refine ⟨9, by positivity, fun P _ _ ν hν => ⟨rieszDivOp P ν hν, norm_rieszDivOp_le P hν, ?_⟩⟩
  intro T G hG _ hTG
  refine phaseD0_hasPow_lerayY hν.le (1 / 2) ?_
  change (FreeStress.phaseD0 P ν hν.le).HasPow (1 / 2)
    (rieszRawOp P ν hν (T : Y2Sym P)) (testElem P 2 (tensorDiv G))
  rw [← hTG]
  unfold FreeStress.MulRep.HasPow
  have hrow : ∀ i : Fin 3, (smoothTensor P G) i = testElem P 2 (G i) := fun _ => rfl
  filter_upwards [phaseFourier_rieszRawOp_ae P hν (smoothTensor P G),
    phaseFourier_tensorDiv_ae hG] with z hraw hdiv
  change (FreeStress.phaseFourier P (testElem P 2 (tensorDiv G)) :
      AddCircle P × Space → CVec3) z =
    (((1 + FreeStress.laplaceSym ν z.2) ^ (1 / 2 : ℝ) : ℝ) : ℂ) •
      (FreeStress.phaseFourier P (rieszRawOp P ν hν (smoothTensor P G)) :
        AddCircle P × Space → CVec3) z
  rw [hdiv, hraw]
  ext i
  simp only [PiLp.smul_apply, smul_eq_mul, hrow i, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  unfold divSym
  have hpos : 0 < 1 + FreeStress.laplaceSym ν z.2 := by
    have : 0 ≤ FreeStress.laplaceSym ν z.2 :=
      (FreeStress.laplaceRepY P ν hν.le).sym_nonneg z
    linarith
  have hcancel : ((1 + FreeStress.laplaceSym ν z.2) ^ (1 / 2 : ℝ)) *
      ((1 + FreeStress.laplaceSym ν z.2) ^ (-(1 / 2 : ℝ))) = 1 := by
    rw [← Real.rpow_add hpos, add_neg_cancel, Real.rpow_zero]
  have hcancelC : (((1 + FreeStress.laplaceSym ν z.2) ^ (1 / 2 : ℝ) : ℝ) : ℂ) *
      (((1 + FreeStress.laplaceSym ν z.2) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) = 1 := by
    exact_mod_cast hcancel
  calc (2 * Real.pi * Complex.I * (z.2 j : ℂ)) *
        (FreeStress.phaseFourier P (testElem P 2 (G i)) z j)
      = 1 * ((2 * Real.pi * Complex.I * (z.2 j : ℂ)) *
          (FreeStress.phaseFourier P (testElem P 2 (G i)) z j)) := (one_mul _).symm
    _ = ((((1 + FreeStress.laplaceSym ν z.2) ^ (1 / 2 : ℝ) : ℝ) : ℂ) *
          (((1 + FreeStress.laplaceSym ν z.2) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) *
          ((2 * Real.pi * Complex.I * (z.2 j : ℂ)) *
            (FreeStress.phaseFourier P (testElem P 2 (G i)) z j)) := by rw [hcancelC]
    _ = _ := by ring

end UnforcedLeray.Short.PartIIa
