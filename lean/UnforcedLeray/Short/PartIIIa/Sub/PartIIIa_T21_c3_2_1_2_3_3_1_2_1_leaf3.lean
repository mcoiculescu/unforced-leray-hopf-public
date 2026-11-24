import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_2_3_3_1_L2_1
import UnforcedLeray.Short.PartIIIa.Clock.FrameStableProof.ShortBlock.OscillatorForce
import UnforcedLeray.Short.PartIIIa.Clock.FrameStableProof.ShortBlock.EulerError.Residual
import UnforcedLeray.Lib.CylinderB.Periodize
import UnforcedLeray.Lib.Cylinder.IBP
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# `PartIII-a:T21/c3/2/1/2/3/3/1/2/1/3`: Leaf C (`FrameDualCore`)

Source of record: `the November 2 reference manuscript` (SP), lines 2898-2918
(frame identities, `(ΛW)' = H₀W`), 2937-2945 (`\bar F_{rel}`), and 2074-2105 (backward cylinder
duality).

Proves `frameDualCore`: along `[0, τ] ⊆ [0, B]`, `σ ↦ dualPair P ν t₁ τ φ σ (frameEFun κ ν t₁ j σ)`
is the primitive of `σ ↦ dualPair P ν t₁ τ φ σ (frameRFun κ P ν tr t₁ j σ)`. Unfolding `perSum d`
against the `d`-periodic test `y ↦ φ(s, √a y)` and train velocity `movingTrainV` via
`Cyl.integral_cell_periodize_mul` and rescaling `x = √a • y` expresses the `frameEFun` pairing as
`N(s,t)⁻¹ ∫_{ℝ²} φ(s,x) g(s,x) dx` with `g(s) = Gaussian.heatDilation (clockA ν s) (κ.e j)`.
Differentiating under the integral (`hasDerivAt_integral_of_dominated_loc_of_deriv_le`), integrating
`ν Δφ + v · ∇φ` by parts on `ℝ²` (`div v = 0`), applying `Gaussian.laplacian_heatDilation` and
`Gaussian.hasDerivAt_heatDilation_param`, and integrating on `[0, σ₀]` via
`intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le` yields the identity.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Metric UnforcedLeray.Blueprint.Planar
open scoped ENNReal ComplexConjugate ContDiff InnerProductSpace

namespace UnforcedLeray.Short.IIIa

open FrameShortBlockSub FrameBlockContractSub CompactDuhamelGapSub BlockPropagatorSub VariationOfConstantsSub VariationOfConstantsMildSub

namespace ComplMildTestedSplit

namespace FrameDuhamelSub

section Helpers

/-- Integrability of `exp(-(x₁² + x₂²)/(8A))` on `ℝ × ℝ` for `A > 0`. -/
private lemma integrable_gauss_plane {A : ℝ} (hA : 0 < A) :
    Integrable (fun x : ℝ × ℝ => Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (8 * A))) volume := by
  have h0 : Integrable (fun y : ℝ × ℝ => Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8)) volume := by
    refine (integrable_jb_gauss (le_rfl : (0 : ℝ) ≤ 0)).congr (Eventually.of_forall fun y => ?_)
    simp
  have hsq : 0 < Real.sqrt A := Real.sqrt_pos.2 hA
  have hR : (Real.sqrt A)⁻¹ ≠ 0 := inv_ne_zero hsq.ne'
  have h1 := (integrable_comp_smul_iff volume
    (fun y : ℝ × ℝ => Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8)) hR).2 h0
  refine h1.congr (Eventually.of_forall fun x => ?_)
  dsimp only
  congr 1
  simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  have hA2 : Real.sqrt A ^ 2 = A := Real.sq_sqrt hA.le
  calc -(((Real.sqrt A)⁻¹ * x.1) ^ 2 + ((Real.sqrt A)⁻¹ * x.2) ^ 2) / 8
      = -(x.1 ^ 2 + x.2 ^ 2) / (8 * Real.sqrt A ^ 2) := by field_simp [hsq.ne']
    _ = -(x.1 ^ 2 + x.2 ^ 2) / (8 * A) := by rw [hA2]

private lemma integrable_of_gauss_plane {A K : ℝ} (hA : 0 < A) {F : ℝ × ℝ → ℂ}
    (hF_meas : AEStronglyMeasurable F volume)
    (hF_bd : ∀ x : ℝ × ℝ, ‖F x‖ ≤ K * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (8 * A))) :
    Integrable F volume :=
  ((integrable_gauss_plane hA).const_mul K).mono' hF_meas (Eventually.of_forall hF_bd)

/-- Change of variables `x = √a • y` on `ℝ × ℝ`: `∫ x, H x = a * ∫ y, H(√a y)`. -/
private lemma integral_plane_eq_smul {a : ℝ} (ha : 0 < a) (H : ℝ × ℝ → ℂ) :
    ∫ x : ℝ × ℝ, H x = ((a : ℝ) : ℂ) * ∫ y : ℝ × ℝ, H (Real.sqrt a * y.1, Real.sqrt a * y.2) := by
  have hfr : Module.finrank ℝ (ℝ × ℝ) = 2 := by simp
  have key : ∫ y : ℝ × ℝ, H (Real.sqrt a • y) =
      |((Real.sqrt a ^ Module.finrank ℝ (ℝ × ℝ))⁻¹)| • ∫ x : ℝ × ℝ, H x :=
    MeasureTheory.Measure.integral_comp_smul volume H (Real.sqrt a)
  rw [hfr, Real.sq_sqrt ha.le, abs_of_pos (inv_pos.mpr ha), Complex.real_smul] at key
  have hpt : (fun y : ℝ × ℝ => H (Real.sqrt a * y.1, Real.sqrt a * y.2)) =
      fun y => H (Real.sqrt a • y) := by
    funext y; rfl
  rw [← hpt] at key
  rw [key, ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ ha.ne', Complex.ofReal_one, one_mul]

/-- Reduction of `dualPair` on a `cellZeroExt` field to a cell integral on `B0579.cell (dOf ν t₁ σ)`. -/
private lemma dualPair_cellZeroExt (P : PlanarData) (ν t₁ τ : ℝ)
    (φ : ℝ → B0579.Plane → ℝ) (σ : ℝ) (W : ℝ × ℝ → ℂ) :
    dualPair P ν t₁ τ φ σ (fun z => cellZeroExt (dOf ν t₁ σ) W (cToPlane z)) =
      (((clockN P ν (ageAt ν t₁ σ) (ageAt ν t₁ τ))⁻¹ *
          (clockA ν (ageAt ν t₁ σ))⁻¹ : ℝ) : ℂ) *
        ∫ y in B0579.cell (dOf ν t₁ σ),
          ((φ (ageAt ν t₁ σ) (Real.sqrt (clockA ν (ageAt ν t₁ σ)) * y.1,
            Real.sqrt (clockA ν (ageAt ν t₁ σ)) * y.2) : ℝ) : ℂ) * W y := by
  unfold dualPair cellZeroExt
  congr 1
  set d := dOf ν t₁ σ
  set s := ageAt ν t₁ σ
  set a := clockA ν s
  set G : ℝ × ℝ → ℂ := fun y => ((φ s (Real.sqrt a * y.1, Real.sqrt a * y.2) : ℝ) : ℂ) * W y
  have hind : ∀ z : ℂ,
      (B0579.cell d).indicator (fun y => ((φ s (Real.sqrt a * y.1, Real.sqrt a * y.2) : ℝ) : ℂ))
        (cToPlane z) * (B0579.cell d).indicator W (cToPlane z) =
      (B0579.cell d).indicator G (cToPlane z) := by
    intro z
    by_cases hz : cToPlane z ∈ B0579.cell d
    · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz, Set.indicator_of_mem hz]
    · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz, Set.indicator_of_notMem hz,
        zero_mul]
  simp_rw [hind]
  have hmp := Complex.volume_preserving_equiv_real_prod
  have hcomp : ∫ z : ℂ, (B0579.cell d).indicator G (cToPlane z) =
      ∫ y : ℝ × ℝ, (B0579.cell d).indicator G y :=
    hmp.integral_comp Complex.measurableEquivRealProd.measurableEmbedding
      (fun y => (B0579.cell d).indicator G y)
  rw [hcomp, integral_indicator (B0579.measurableSet_cell d)]

/-- Unfolding `∫_{C_d} g * perSum d f = ∫_{ℝ²} g * f` together with cell integrability for `d ≥ 1`. -/
private lemma integrableOn_and_integral_cell_mul_perSum {d : ℝ} (hd1 : 1 ≤ d) {f g : ℝ × ℝ → ℂ}
    (hf : Continuous f) (hg : Continuous g) (hper : UnforcedLeray.Cyl.IsPeriodic d g)
    {Cf Cg : ℝ} (hCf0 : 0 ≤ Cf) (hCg0 : 0 ≤ Cg)
    (hf_bd : ∀ y, ‖f y‖ ≤ Cf * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8))
    (hg_bd : ∀ y, ‖g y‖ ≤ Cg) :
    IntegrableOn (fun y => g y * perSum d f y) (B0579.cell d) ∧
      Integrable (fun y => g y * f y) volume ∧
      ∫ y in B0579.cell d, g y * perSum d f y = ∫ y : ℝ × ℝ, g y * f y := by
  have hd0 : 0 < d := lt_of_lt_of_le zero_lt_one hd1
  have hgf_int : Integrable (fun y => g y * f y) volume := by
    refine integrable_of_gauss_plane (A := 1) (K := Cg * Cf) one_pos
      (hg.mul hf).aestronglyMeasurable fun y => ?_
    rw [mul_one, norm_mul]
    calc ‖g y‖ * ‖f y‖ ≤ Cg * (Cf * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8)) :=
          mul_le_mul (hg_bd y) (hf_bd y) (norm_nonneg _) hCg0
      _ = (Cg * Cf) * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8) := by ring
  have hps_cont : Continuous (perSum d f) := by
    refine FrameCont.perSum_continuous hf (C := 16 * Cf) (fun z => (hf_bd z).trans ?_) hd0.ne'
    calc Cf * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8)
        ≤ Cf * (16 * (1 + |z.1|) ^ (-(2 : ℝ))) :=
          mul_le_mul_of_nonneg_left (FrameCont.exp_le_translate_weight z.1 z.2) hCf0
      _ = (16 * Cf) * (1 + |z.1|) ^ (-(2 : ℝ)) := by ring
  obtain ⟨M, _hM0, hM⟩ := OscillatorForceSub.perSum_pointwise_of_gauss hCf0 hf_bd
  have hcell_int : IntegrableOn (fun y => g y * perSum d f y) (B0579.cell d) := by
    have hdom : IntegrableOn (fun y : ℝ × ℝ =>
        (Cg * M) * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / (8 * 2))) (B0579.cell d) :=
      ((integrable_gauss_plane (by norm_num : (0 : ℝ) < 2)).const_mul (Cg * M)).integrableOn
    refine hdom.mono' (hg.mul hps_cont).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem (B0579.measurableSet_cell d)] with y hy
    rw [norm_mul, show (8 : ℝ) * 2 = 16 by norm_num]
    calc ‖g y‖ * ‖perSum d f y‖
        ≤ Cg * (M * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16)) :=
          mul_le_mul (hg_bd y) (hM d hd1 y hy) (norm_nonneg _) hCg0
      _ = (Cg * M) * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16) := by ring
  have hperSum_eq : ∀ y, perSum d f y = UnforcedLeray.Cyl.periodize d f y := by
    intro y
    unfold perSum UnforcedLeray.Cyl.periodize
    rw [← (Equiv.neg ℤ).tsum_eq]
    refine tsum_congr fun n => ?_
    congr 1
    ext <;> simp [sub_eq_add_neg]
  have hcell_eq : B0579.cell d = UnforcedLeray.Cyl.cell d := by
    ext y
    simp [B0579.cell, UnforcedLeray.Cyl.cell, neg_div]
  have hfg_int : Integrable (fun y => f y * g y) volume := by
    refine hgf_int.congr (Eventually.of_forall fun y => mul_comm _ _)
  have hunf := UnforcedLeray.Cyl.integral_cell_periodize_mul hd0
    hf.stronglyMeasurable hg.stronglyMeasurable hper hfg_int
  refine ⟨hcell_int, hgf_int, ?_⟩
  rw [hcell_eq]
  calc ∫ y in UnforcedLeray.Cyl.cell d, g y * perSum d f y
      = ∫ y in UnforcedLeray.Cyl.cell d, UnforcedLeray.Cyl.periodize d f y * g y := by
        refine setIntegral_congr_fun (by rw [← hcell_eq]; exact B0579.measurableSet_cell d)
          fun y _ => ?_
        rw [hperSum_eq y, mul_comm]
    _ = ∫ y : ℝ × ℝ, f y * g y := hunf
    _ = ∫ y : ℝ × ℝ, g y * f y := integral_congr_ae (Eventually.of_forall fun y => mul_comm _ _)

/-- Algebraic decomposition of `movFreeRes` into `-movOscRes` and transport. -/
private lemma movFreeRes_eq_neg_movOscRes_add (κ : PlanarFrameKernels) {ν : ℝ}
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (r : ℝ) (j : Fin 2)
    (y : ℝ × ℝ) :
    movFreeRes κ tr r j y =
      -movOscRes κ ν r j y +
        (((movingTrainV tr r y 0 : ℝ) : ℂ) *
            pdCx 0 (perE κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) j) y +
          ((movingTrainV tr r y 1 : ℝ) : ℂ) *
            pdCx 1 (perE κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) j) y) := by
  unfold movFreeRes movOscRes
  ring

/-- Strict monotonicity of `ageAt ν t₁` on `[0, B]`. -/
private lemma ageAt_lt_on_block {ν t₁ t₂ B σ τ : ℝ}
    (hν : 0 < ν) (ht₁ : 0 ≤ t₁) (ht₂ : 0 ≤ t₂) (hB : movingZ ν t₂ - movingZ ν t₁ = B)
    (hσ0 : 0 ≤ σ) (hστ : σ < τ) (hτB : τ ≤ B) :
    ageAt ν t₁ σ < ageAt ν t₁ τ := by
  refine lt_of_le_of_ne (ageAt_mono_on_block hν ht₁ ht₂ hB hσ0 hστ.le hτB) fun heq => ?_
  have h1 := movingZ_ageAt_sub hν ht₂ hB (hστ.le.trans hτB)
  have h2 := movingZ_ageAt_sub hν ht₂ hB hτB
  rw [heq] at h1
  linarith

/-- `ds/dσ = a(s)²` on the block. -/
private lemma hasDerivAt_ageAt_block {ν t₁ t₂ B σ : ℝ}
    (hν : 0 < ν) (ht₂ : 0 ≤ t₂) (hB : movingZ ν t₂ - movingZ ν t₁ = B) (hσB : σ ≤ B) :
    HasDerivAt (ageAt ν t₁) ((clockA ν (ageAt ν t₁ σ)) ^ 2) σ := by
  have hlt : ν * (movingZ ν t₁ + σ) < 1 := nu_mul_movingZ_add_lt_one hν ht₂ hB hσB
  have hz : 0 < 1 - ν * (movingZ ν t₁ + σ) := by linarith
  have h1 : HasDerivAt (fun x : ℝ => movingZ ν t₁ + x) 1 σ := (hasDerivAt_id σ).const_add _
  have h2 : HasDerivAt (fun x : ℝ => 1 - ν * (movingZ ν t₁ + x)) (-(ν * 1)) σ := by
    simpa using (h1.const_mul ν).const_sub 1
  have h3 := h1.div h2 hz.ne'
  have heq : ageAt ν t₁ = fun x : ℝ => (movingZ ν t₁ + x) / (1 - ν * (movingZ ν t₁ + x)) := by
    funext x; rfl
  rw [heq]
  refine h3.congr_deriv ?_
  unfold clockA
  field_simp
  ring

private lemma clockN_inv_eq_swap (P : PlanarData) {ν s t : ℝ}
    (hν : 0 < ν) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    (clockN P ν s t)⁻¹ = clockN P ν t s := by
  have hself : clockN P ν t t = 1 := by
    unfold clockN
    simp [div_self (theta_pos hν ht).ne']
  have hmul := FrameStableSub.clockN_mul P hν ht hs ht
  rw [hself] at hmul
  have hne : clockN P ν s t ≠ 0 := by
    unfold clockN
    exact (mul_pos (Real.exp_pos _)
      (Real.rpow_pos_of_pos (div_pos (theta_pos hν hs) (theta_pos hν ht)) _)).ne'
  exact inv_eq_of_mul_eq_one_left hmul.symm

/-- `d/dσ ((clockN P ν (ageAt ν t₁ σ) t)⁻¹) = movBeta0 P ν s * (clockN P ν s t)⁻¹` for `σ ∈ (0, τ)`. -/
private lemma hasDerivAt_clockN_inv_ageAt (P : PlanarData) {ν t₁ t₂ B τ σ : ℝ}
    (hν : 0 < ν) (ht₁ : 0 ≤ t₁) (ht₂ : 0 ≤ t₂) (hB : movingZ ν t₂ - movingZ ν t₁ = B)
    (hτB : τ ≤ B) (hσ0 : 0 < σ) (hστ : σ ≤ τ) :
    HasDerivAt (fun σ' => (((clockN P ν (ageAt ν t₁ σ') (ageAt ν t₁ τ))⁻¹ : ℝ) : ℂ))
      (((movBeta0 P ν (ageAt ν t₁ σ) *
        (clockN P ν (ageAt ν t₁ σ) (ageAt ν t₁ τ))⁻¹ : ℝ) : ℂ)) σ := by
  set t := ageAt ν t₁ τ
  set s := ageAt ν t₁ σ
  have ht0 : 0 ≤ t := by
    have h := ageAt_mono_on_block hν ht₁ ht₂ hB le_rfl (hσ0.le.trans hστ) hτB
    rw [CompactDuhamelGapSub.ageAt_zero hν ht₁] at h
    exact ht₁.trans h
  have hs_gt : t₁ < s := by
    have := ageAt_lt_on_block hν ht₁ ht₂ hB le_rfl hσ0 (hστ.trans hτB)
    rwa [CompactDuhamelGapSub.ageAt_zero hν ht₁] at this
  have hs_pos : 0 < s := lt_of_le_of_lt ht₁ hs_gt
  have hev : (fun r => (clockN P ν r t)⁻¹) =ᶠ[𝓝 s] clockN P ν t := by
    filter_upwards [Ioi_mem_nhds hs_pos] with r hr
    exact clockN_inv_eq_swap P hν (le_of_lt hr) ht0
  have hd_s : HasDerivAt (fun r => (clockN P ν r t)⁻¹)
      ((clockA ν s) ^ (-2 : ℝ) * movBeta0 P ν s * (clockN P ν s t)⁻¹) s := by
    have h1 := (CompactDuhamelGapSub.hasDerivAt_clockN_movBeta0 P hν ht0 hs_pos.le).congr_of_eventuallyEq hev
    rwa [← clockN_inv_eq_swap P hν hs_pos.le ht0] at h1
  have hd_age := hasDerivAt_ageAt_block hν ht₂ hB (hστ.trans hτB)
  have hd_comp := hd_s.comp σ hd_age
  have ha0 : 0 < clockA ν s := lt_of_lt_of_le zero_lt_one (one_le_clockA hν.le hs_pos.le)
  have hreal : HasDerivAt (fun σ' => (clockN P ν (ageAt ν t₁ σ') t)⁻¹)
      (movBeta0 P ν s * (clockN P ν s t)⁻¹) σ := by
    refine hd_comp.congr_deriv ?_
    have ha_cancel : (clockA ν s) ^ (-2 : ℝ) * (clockA ν s) ^ 2 = 1 := by
      rw [← Real.rpow_natCast (clockA ν s) 2, ← Real.rpow_add ha0]
      norm_num
    calc ((clockA ν s) ^ (-2 : ℝ) * movBeta0 P ν s * (clockN P ν s t)⁻¹) * (clockA ν s) ^ 2
        = ((clockA ν s) ^ (-2 : ℝ) * (clockA ν s) ^ 2) * (movBeta0 P ν s * (clockN P ν s t)⁻¹) := by ring
      _ = movBeta0 P ν s * (clockN P ν s t)⁻¹ := by rw [ha_cancel, one_mul]
  exact Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt σ hreal

/-- First-order integration by parts on `ℝ × ℝ` for real `f` and complex `g`. -/
private lemma integral_plane_pd_mul (k : Fin 2) {f : ℝ × ℝ → ℝ} {g : ℝ × ℝ → ℂ}
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (h0 : Integrable (fun x : ℝ × ℝ => ((f x : ℝ) : ℂ) * g x) volume)
    (h1 : Integrable (fun x : ℝ × ℝ => ((B0579.pd k f x : ℝ) : ℂ) * g x) volume)
    (h2 : Integrable (fun x : ℝ × ℝ => ((f x : ℝ) : ℂ) * pdCx k g x) volume) :
    ∫ x : ℝ × ℝ, ((B0579.pd k f x : ℝ) : ℂ) * g x =
      -∫ x : ℝ × ℝ, ((f x : ℝ) : ℂ) * pdCx k g x := by
  set H : ℝ × ℝ → ℂ := fun x => ((f x : ℝ) : ℂ) * g x
  set H' : ℝ × ℝ → ℂ := fun x => ((B0579.pd k f x : ℝ) : ℂ) * g x + ((f x : ℝ) : ℂ) * pdCx k g x
  have hzero : ∫ x : ℝ × ℝ, H' x = 0 := by
    have h12 : Integrable H' volume := h1.add h2
    fin_cases k
    · have hd0 : ∀ q η : ℝ, HasDerivAt (fun q' => H (q', η)) (H' (q, η)) q := by
        intro q η
        have hin : HasDerivAt (fun q' : ℝ => ((q', η) : ℝ × ℝ)) ((1 : ℝ), (0 : ℝ)) q :=
          (hasDerivAt_id q).prodMk (hasDerivAt_const q η)
        have hdf : HasDerivAt (fun q' => f (q', η)) (B0579.pd 0 f (q, η)) q :=
          (hf (q, η)).hasFDerivAt.comp_hasDerivAt q hin
        have hdg : HasDerivAt (fun q' => g (q', η)) (pdCx 0 g (q, η)) q :=
          (hg (q, η)).hasFDerivAt.comp_hasDerivAt q hin
        exact (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt q hdf).mul hdg
      rw [Measure.volume_eq_prod] at h0 h12 ⊢
      rw [MeasureTheory.integral_prod_symm _ h12]
      have hae : ∀ᵐ η : ℝ ∂volume, ∫ q : ℝ, H' (q, η) = 0 := by
        filter_upwards [h0.prod_left_ae, h12.prod_left_ae] with η hH hH'
        exact integral_eq_zero_of_hasDerivAt_of_integrable (fun q => hd0 q η) hH' hH
      rw [integral_congr_ae hae, integral_zero]
    · have hd1 : ∀ q η : ℝ, HasDerivAt (fun η' => H (q, η')) (H' (q, η)) η := by
        intro q η
        have hin : HasDerivAt (fun η' : ℝ => ((q, η') : ℝ × ℝ)) ((0 : ℝ), (1 : ℝ)) η :=
          (hasDerivAt_const η q).prodMk (hasDerivAt_id η)
        have hdf : HasDerivAt (fun η' => f (q, η')) (B0579.pd 1 f (q, η)) η :=
          (hf (q, η)).hasFDerivAt.comp_hasDerivAt η hin
        have hdg : HasDerivAt (fun η' => g (q, η')) (pdCx 1 g (q, η)) η :=
          (hg (q, η)).hasFDerivAt.comp_hasDerivAt η hin
        exact (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt η hdf).mul hdg
      rw [Measure.volume_eq_prod] at h0 h12 ⊢
      rw [MeasureTheory.integral_prod _ h12]
      have hae : ∀ᵐ q : ℝ ∂volume, ∫ η : ℝ, H' (q, η) = 0 := by
        filter_upwards [h0.prod_right_ae, h12.prod_right_ae] with q hH hH'
        exact integral_eq_zero_of_hasDerivAt_of_integrable (fun η => hd1 q η) hH' hH
      rw [integral_congr_ae hae, integral_zero]
  rw [integral_add h1 h2] at hzero
  exact eq_neg_of_add_eq_zero_left hzero

/-- Partial derivative formula and Gaussian decay for `Gaussian.heatDilation a e`. -/
private lemma pdCx_heatDilation {a : ℝ} {e : ℝ × ℝ → ℂ} (he : Differentiable ℝ e)
    (k : Fin 2) (x : ℝ × ℝ) :
    pdCx k (UnforcedLeray.Gaussian.heatDilation a e) x =
      (a⁻¹ ^ 2 * (Real.sqrt a)⁻¹) • pdCx k e ((Real.sqrt a)⁻¹ • x) := by
  have hin : HasFDerivAt (fun z : ℝ × ℝ => (Real.sqrt a)⁻¹ • z)
      ((Real.sqrt a)⁻¹ • ContinuousLinearMap.id ℝ (ℝ × ℝ)) x :=
    (hasFDerivAt_id x).const_smul (Real.sqrt a)⁻¹
  have hcomp : HasFDerivAt (UnforcedLeray.Gaussian.heatDilation a e)
      ((a⁻¹ ^ 2) • ((fderiv ℝ e ((Real.sqrt a)⁻¹ • x)).comp
        ((Real.sqrt a)⁻¹ • ContinuousLinearMap.id ℝ (ℝ × ℝ)))) x := by
    rw [UnforcedLeray.Gaussian.heatDilation_eq_fun]
    exact ((he ((Real.sqrt a)⁻¹ • x)).hasFDerivAt.comp x hin).const_smul (a⁻¹ ^ 2)
  unfold pdCx
  rw [hcomp.fderiv]
  simp [smul_smul]

/-- Gaussian exponent monotone under `1 ≤ a ≤ A`. -/
private lemma exp_dilated_le {a A : ℝ} (ha : 0 < a) (haA : a ≤ A) (x : ℝ × ℝ) :
    Real.exp (-((((Real.sqrt a)⁻¹ • x).1) ^ 2 + (((Real.sqrt a)⁻¹ • x).2) ^ 2) / 8) ≤
      Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (8 * A)) := by
  have hA : 0 < A := ha.trans_le haA
  have hsq : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha.le
  have hsum : (((Real.sqrt a)⁻¹ • x).1) ^ 2 + (((Real.sqrt a)⁻¹ • x).2) ^ 2 =
      (x.1 ^ 2 + x.2 ^ 2) / a := by
    simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    calc ((Real.sqrt a)⁻¹ * x.1) ^ 2 + ((Real.sqrt a)⁻¹ * x.2) ^ 2
        = (x.1 ^ 2 + x.2 ^ 2) / Real.sqrt a ^ 2 := by field_simp [(Real.sqrt_pos.2 ha).ne']
      _ = (x.1 ^ 2 + x.2 ^ 2) / a := by rw [hsq]
  rw [hsum]
  refine Real.exp_le_exp.mpr ?_
  have hnn : 0 ≤ x.1 ^ 2 + x.2 ^ 2 := by positivity
  have hdiv : (x.1 ^ 2 + x.2 ^ 2) / (8 * A) ≤ (x.1 ^ 2 + x.2 ^ 2) / (8 * a) :=
    div_le_div_of_nonneg_left hnn (by positivity) (by linarith)
  have heq : -((x.1 ^ 2 + x.2 ^ 2) / a) / 8 = -((x.1 ^ 2 + x.2 ^ 2) / (8 * a)) := by ring
  have heq2 : -(x.1 ^ 2 + x.2 ^ 2) / (8 * A) = -((x.1 ^ 2 + x.2 ^ 2) / (8 * A)) := by ring
  rw [heq, heq2]
  linarith

private def cut1 (u : ℝ) : ℝ := Real.smoothTransition (2 - u ^ 2)

private lemma cut1_contDiff : ContDiff ℝ ∞ cut1 :=
  Real.smoothTransition.contDiff.comp (contDiff_const.sub (contDiff_id.pow 2))

private lemma cut1_nonneg (u : ℝ) : 0 ≤ cut1 u := Real.smoothTransition.nonneg _

private lemma cut1_le_one (u : ℝ) : cut1 u ≤ 1 := Real.smoothTransition.le_one _

private lemma cut1_eq_one {u : ℝ} (hu : |u| ≤ 1) : cut1 u = 1 :=
  Real.smoothTransition.one_of_one_le (by nlinarith [sq_abs u, abs_nonneg u])

private lemma cut1_eq_zero {u : ℝ} (hu : 2 ≤ |u|) : cut1 u = 0 :=
  Real.smoothTransition.zero_of_nonpos (by nlinarith [sq_abs u, abs_nonneg u])

private lemma exists_deriv_cut1_bound : ∃ K : ℝ, 0 ≤ K ∧ ∀ u : ℝ, |deriv cut1 u| ≤ K := by
  have hcs : HasCompactSupport cut1 := by
    refine HasCompactSupport.intro (isCompact_Icc (a := (-2 : ℝ)) (b := 2)) fun u hu => ?_
    apply cut1_eq_zero
    by_contra hlt
    have habs : |u| < 2 := not_le.1 hlt
    exact hu ⟨(abs_lt.1 habs).1.le, (abs_lt.1 habs).2.le⟩
  have hdc : Continuous (deriv cut1) := (contDiff_infty_iff_deriv.1 cut1_contDiff).2.continuous
  obtain ⟨K, hK⟩ := hdc.bounded_above_of_compact_support hcs.deriv
  refine ⟨max K 0, le_max_right _ _, fun u => ?_⟩
  have h := hK u
  rw [Real.norm_eq_abs] at h
  exact h.trans (le_max_left _ _)

private def cut2 (R : ℝ) (x : ℝ × ℝ) : ℝ := cut1 (R⁻¹ * x.1) * cut1 (R⁻¹ * x.2)

private lemma cut2_contDiff (R : ℝ) : ContDiff ℝ ∞ (cut2 R) :=
  (cut1_contDiff.comp (contDiff_const.mul contDiff_fst)).mul
    (cut1_contDiff.comp (contDiff_const.mul contDiff_snd))

private lemma cut2_nonneg (R : ℝ) (x : ℝ × ℝ) : 0 ≤ cut2 R x :=
  mul_nonneg (cut1_nonneg _) (cut1_nonneg _)

private lemma cut2_le_one (R : ℝ) (x : ℝ × ℝ) : cut2 R x ≤ 1 :=
  mul_le_one₀ (cut1_le_one _) (cut1_nonneg _) (cut1_le_one _)

private lemma cut2_eq_one {R : ℝ} (hR : 0 < R) {x : ℝ × ℝ} (hx1 : |x.1| ≤ R) (hx2 : |x.2| ≤ R) :
    cut2 R x = 1 := by
  unfold cut2
  have h1 : |R⁻¹ * x.1| ≤ 1 := by
    rw [abs_mul, abs_of_pos (inv_pos.2 hR), inv_mul_le_iff₀ hR]; linarith
  have h2 : |R⁻¹ * x.2| ≤ 1 := by
    rw [abs_mul, abs_of_pos (inv_pos.2 hR), inv_mul_le_iff₀ hR]; linarith
  rw [cut1_eq_one h1, cut1_eq_one h2, mul_one]

private lemma cut2_hasCompactSupport {R : ℝ} (hR : 0 < R) : HasCompactSupport (cut2 R) := by
  refine HasCompactSupport.intro
    ((isCompact_Icc (a := -(2 * R)) (b := 2 * R)).prod
      (isCompact_Icc (a := -(2 * R)) (b := 2 * R))) fun x hx => ?_
  unfold cut2
  by_cases h1 : 2 * R ≤ |x.1|
  · have : 2 ≤ |R⁻¹ * x.1| := by
      rw [abs_mul, abs_of_pos (inv_pos.2 hR), le_inv_mul_iff₀ hR]; linarith
    rw [cut1_eq_zero this, zero_mul]
  · have h2 : 2 * R ≤ |x.2| := by
      by_contra h2
      have a1 : |x.1| < 2 * R := not_le.1 h1
      have a2 : |x.2| < 2 * R := not_le.1 h2
      exact hx ⟨⟨(abs_lt.1 a1).1.le, (abs_lt.1 a1).2.le⟩,
        ⟨(abs_lt.1 a2).1.le, (abs_lt.1 a2).2.le⟩⟩
    have : 2 ≤ |R⁻¹ * x.2| := by
      rw [abs_mul, abs_of_pos (inv_pos.2 hR), le_inv_mul_iff₀ hR]; linarith
    rw [cut1_eq_zero this, mul_zero]

private lemma pd_cut2_bound {K : ℝ} (hK0 : 0 ≤ K) (hK : ∀ u, |deriv cut1 u| ≤ K)
    {R : ℝ} (hR : 0 < R) (k : Fin 2) (x : ℝ × ℝ) :
    |B0579.pd k (cut2 R) x| ≤ K * R⁻¹ := by
  have hc1d : Differentiable ℝ cut1 := cut1_contDiff.differentiable (by simp)
  have hc2d : Differentiable ℝ (cut2 R) := (cut2_contDiff R).differentiable (by simp)
  have hk : k = 0 ∨ k = 1 := by fin_cases k <;> [exact Or.inl rfl; exact Or.inr rfl]
  rcases hk with rfl | rfl
  · have hd_lhs : HasDerivAt (fun t : ℝ => cut2 R (t, x.2)) (B0579.pd 0 (cut2 R) x) x.1 := by
      have hin : HasDerivAt (fun t : ℝ => ((t, x.2) : ℝ × ℝ)) ((1 : ℝ), (0 : ℝ)) x.1 :=
        (hasDerivAt_id x.1).prodMk (hasDerivAt_const x.1 x.2)
      exact (hc2d x).hasFDerivAt.comp_hasDerivAt x.1 hin
    have hd_rhs : HasDerivAt (fun t : ℝ => cut2 R (t, x.2))
        ((deriv cut1 (R⁻¹ * x.1) * R⁻¹) * cut1 (R⁻¹ * x.2)) x.1 := by
      unfold cut2
      have hlin : HasDerivAt (fun t : ℝ => R⁻¹ * t) R⁻¹ x.1 := by
        simpa using (hasDerivAt_id x.1).const_mul R⁻¹
      exact ((hc1d (R⁻¹ * x.1)).hasDerivAt.comp x.1 hlin).mul_const (cut1 (R⁻¹ * x.2))
    rw [hd_lhs.unique hd_rhs, abs_mul, abs_mul, abs_of_pos (inv_pos.2 hR),
      abs_of_nonneg (cut1_nonneg _)]
    calc (|deriv cut1 (R⁻¹ * x.1)| * R⁻¹) * cut1 (R⁻¹ * x.2)
        ≤ (K * R⁻¹) * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_right (hK _) (inv_nonneg.2 hR.le))
            (cut1_le_one _) (cut1_nonneg _) (mul_nonneg hK0 (inv_nonneg.2 hR.le))
      _ = K * R⁻¹ := mul_one _
  · have hd_lhs : HasDerivAt (fun t : ℝ => cut2 R (x.1, t)) (B0579.pd 1 (cut2 R) x) x.2 := by
      have hin : HasDerivAt (fun t : ℝ => ((x.1, t) : ℝ × ℝ)) ((0 : ℝ), (1 : ℝ)) x.2 :=
        (hasDerivAt_const x.2 x.1).prodMk (hasDerivAt_id x.2)
      exact (hc2d x).hasFDerivAt.comp_hasDerivAt x.2 hin
    have hd_rhs : HasDerivAt (fun t : ℝ => cut2 R (x.1, t))
        (cut1 (R⁻¹ * x.1) * (deriv cut1 (R⁻¹ * x.2) * R⁻¹)) x.2 := by
      unfold cut2
      have hlin : HasDerivAt (fun t : ℝ => R⁻¹ * t) R⁻¹ x.2 := by
        simpa using (hasDerivAt_id x.2).const_mul R⁻¹
      exact ((hc1d (R⁻¹ * x.2)).hasDerivAt.comp x.2 hlin).const_mul (cut1 (R⁻¹ * x.1))
    rw [hd_lhs.unique hd_rhs, abs_mul, abs_mul, abs_of_pos (inv_pos.2 hR),
      abs_of_nonneg (cut1_nonneg _)]
    calc cut1 (R⁻¹ * x.1) * (|deriv cut1 (R⁻¹ * x.2)| * R⁻¹)
        ≤ 1 * (K * R⁻¹) :=
          mul_le_mul (cut1_le_one _)
            (mul_le_mul_of_nonneg_right (hK _) (inv_nonneg.2 hR.le))
            (by positivity) zero_le_one
      _ = K * R⁻¹ := one_mul _

private lemma pdCx_ofReal_mul (k : Fin 2) {χ : ℝ × ℝ → ℝ} {h : ℝ × ℝ → ℂ}
    (hχ : Differentiable ℝ χ) (hh : Differentiable ℝ h) (x : ℝ × ℝ) :
    pdCx k (fun z => ((χ z : ℝ) : ℂ) * h z) x =
      ((B0579.pd k χ x : ℝ) : ℂ) * h x + ((χ x : ℝ) : ℂ) * pdCx k h x := by
  have h1 : HasFDerivAt (fun z => ((χ z : ℝ) : ℂ))
      (Complex.ofRealCLM.comp (fderiv ℝ χ x)) x :=
    Complex.ofRealCLM.hasFDerivAt.comp x (hχ x).hasFDerivAt
  have h2 := h1.mul (hh x).hasFDerivAt
  unfold pdCx B0579.pd
  change fderiv ℝ ((fun z => ((χ z : ℝ) : ℂ)) * h) x (B0579.dir k) = _
  rw [h2.fderiv]
  simp only [add_apply, smul_apply, ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply,
    smul_eq_mul]
  ring

private lemma pd_mul_real (k : Fin 2) {f₁ f₂ : ℝ × ℝ → ℝ}
    (hf₁ : Differentiable ℝ f₁) (hf₂ : Differentiable ℝ f₂) (x : ℝ × ℝ) :
    B0579.pd k (fun z => f₁ z * f₂ z) x =
      B0579.pd k f₁ x * f₂ x + f₁ x * B0579.pd k f₂ x := by
  have h := (hf₁ x).hasFDerivAt.mul (hf₂ x).hasFDerivAt
  unfold B0579.pd
  change fderiv ℝ (f₁ * f₂) x (B0579.dir k) = _
  rw [h.fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

private lemma integrable_of_cs_mul {χ : ℝ × ℝ → ℝ} (hχ_c : Continuous χ)
    (hχ_cs : HasCompactSupport χ) {u : ℝ × ℝ → ℂ} (hu_c : Continuous u) :
    Integrable (fun x : ℝ × ℝ => ((χ x : ℝ) : ℂ) * u x) volume := by
  have hcs : HasCompactSupport ((fun x : ℝ × ℝ => ((χ x : ℝ) : ℂ)) * u) :=
    (hχ_cs.comp_left Complex.ofReal_zero).mul_right
  exact ((Complex.continuous_ofReal.comp hχ_c).mul hu_c).integrable_of_hasCompactSupport hcs

/-- Second-order Laplacian integration by parts on `ℝ × ℝ` when only `ψ`, `∇ψ`, and `lapP ψ`
(not the individual second partials `∂_q² ψ`, `∂_η² ψ`) are bounded at infinity. -/
private lemma integral_plane_lapP_mul {ψ : ℝ × ℝ → ℝ} {g : ℝ × ℝ → ℂ} {A Cψ C0 C1 C2 : ℝ}
    (hA : 0 < A) (hCψ : 0 ≤ Cψ) (_hC0 : 0 ≤ C0) (_hC1 : 0 ≤ C1) (_hC2 : 0 ≤ C2)
    (hψ : ContDiff ℝ ∞ ψ) (hg : ContDiff ℝ ∞ g)
    (hψ_bd : ∀ x, |ψ x| ≤ Cψ)
    (hpd_ψ_bd : ∀ k : Fin 2, ∀ x, |B0579.pd k ψ x| ≤ Cψ)
    (hlap_ψ_bd : ∀ x, |UnforcedLeray.Short.IIb.lapP ψ x| ≤ Cψ)
    (hg_bd : ∀ x, ‖g x‖ ≤ C0 * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (8 * A)))
    (hpd_g_bd : ∀ k : Fin 2, ∀ x, ‖pdCx k g x‖ ≤ C1 * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (8 * A)))
    (hpd2_g_bd : ∀ k : Fin 2, ∀ x,
      ‖pdCx k (pdCx k g) x‖ ≤ C2 * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (8 * A))) :
    ∫ x : ℝ × ℝ, ((UnforcedLeray.Short.IIb.lapP ψ x : ℝ) : ℂ) * g x =
      ∫ x : ℝ × ℝ, ((ψ x : ℝ) : ℂ) * UnforcedLeray.Cyl.laplacian g x := by
  have hψ_diff : Differentiable ℝ ψ := hψ.differentiable (by simp)
  have hg_diff : Differentiable ℝ g := hg.differentiable (by simp)
  have hpd_ψ_cd : ∀ k : Fin 2, ContDiff ℝ ∞ (B0579.pd k ψ) := fun k => by
    unfold B0579.pd
    exact (hψ.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const
  have hpd2_ψ_c : ∀ k : Fin 2, Continuous (B0579.pd k (B0579.pd k ψ)) := fun k => by
    unfold B0579.pd
    exact (((hpd_ψ_cd k).fderiv_right (m := (1 : ℕ)) (by simp)).clm_apply contDiff_const).continuous
  have hpd_g_cd : ∀ k : Fin 2, ContDiff ℝ ∞ (pdCx k g) := fun k => by
    unfold pdCx
    exact (hg.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const
  have hpd2_g_c : ∀ k : Fin 2, Continuous (pdCx k (pdCx k g)) := fun k => by
    unfold pdCx
    exact (((hpd_g_cd k).fderiv_right (m := (1 : ℕ)) (by simp)).clm_apply contDiff_const).continuous
  have hlap_g_eq : ∀ x : ℝ × ℝ,
      UnforcedLeray.Cyl.laplacian g x = pdCx 0 (pdCx 0 g) x + pdCx 1 (pdCx 1 g) x := by
    intro x
    have hpQ : UnforcedLeray.Cyl.partialQ g = pdCx 0 g := by
      funext z; rw [UnforcedLeray.Cyl.partialQ_eq_fderiv hg_diff z]; rfl
    have hpE : UnforcedLeray.Cyl.partialEta g = pdCx 1 g := by
      funext z; rw [UnforcedLeray.Cyl.partialEta_eq_fderiv hg_diff z]; rfl
    unfold UnforcedLeray.Cyl.laplacian
    rw [hpQ, hpE,
      UnforcedLeray.Cyl.partialQ_eq_fderiv ((hpd_g_cd 0).differentiable (by simp)) x,
      UnforcedLeray.Cyl.partialEta_eq_fderiv ((hpd_g_cd 1).differentiable (by simp)) x]
    rfl
  -- Step A: Cutoff identity for every `R > 0`
  have hcut_id : ∀ R : ℝ, 0 < R → ∀ k : Fin 2,
      ∫ x : ℝ × ℝ, ((cut2 R x : ℝ) : ℂ) * (((B0579.pd k (B0579.pd k ψ) x : ℝ) : ℂ) * g x) =
        (∫ x : ℝ × ℝ, ((cut2 R x : ℝ) : ℂ) * (((ψ x : ℝ) : ℂ) * pdCx k (pdCx k g) x)) +
          ∫ x : ℝ × ℝ, ((B0579.pd k (cut2 R) x : ℝ) : ℂ) *
            (((ψ x : ℝ) : ℂ) * pdCx k g x - ((B0579.pd k ψ x : ℝ) : ℂ) * g x) := by
    intro R hR k
    set χ := cut2 R
    have hχ_cd : ContDiff ℝ ∞ χ := cut2_contDiff R
    have hχ_diff : Differentiable ℝ χ := hχ_cd.differentiable (by simp)
    have hχ_cs : HasCompactSupport χ := cut2_hasCompactSupport hR
    have hpdχ_c : Continuous (B0579.pd k χ) := by
      unfold B0579.pd
      exact ((hχ_cd.fderiv_right (m := (1 : ℕ)) (by simp)).clm_apply contDiff_const).continuous
    have hpdχ_cs : HasCompactSupport (B0579.pd k χ) := hχ_cs.fderiv_apply ℝ (B0579.dir k)
    set g₁ : ℝ × ℝ → ℂ := fun z => ((χ z : ℝ) : ℂ) * g z
    set g₂ : ℝ × ℝ → ℂ := fun z => ((χ z : ℝ) : ℂ) * pdCx k g z
    have hg₁_diff : Differentiable ℝ g₁ :=
      (Complex.ofRealCLM.differentiable.comp hχ_diff).mul hg_diff
    have hg₂_diff : Differentiable ℝ g₂ :=
      (Complex.ofRealCLM.differentiable.comp hχ_diff).mul ((hpd_g_cd k).differentiable (by simp))
    have hpd_g₁ : ∀ x, pdCx k g₁ x =
        ((B0579.pd k χ x : ℝ) : ℂ) * g x + ((χ x : ℝ) : ℂ) * pdCx k g x :=
      pdCx_ofReal_mul k hχ_diff hg_diff
    have hpd_g₂ : ∀ x, pdCx k g₂ x =
        ((B0579.pd k χ x : ℝ) : ℂ) * pdCx k g x + ((χ x : ℝ) : ℂ) * pdCx k (pdCx k g) x :=
      pdCx_ofReal_mul k hχ_diff ((hpd_g_cd k).differentiable (by simp))
    -- First IBP: `f = pd k ψ`, `g = g₁`
    have i1_0 : Integrable (fun x => ((B0579.pd k ψ x : ℝ) : ℂ) * g₁ x) volume := by
      refine (integrable_of_cs_mul hχ_cd.continuous hχ_cs
        ((Complex.continuous_ofReal.comp (hpd_ψ_cd k).continuous).mul hg.continuous)).congr
        (Eventually.of_forall fun x => ?_)
      simp only [g₁, Pi.mul_apply, Function.comp_apply]; ring
    have i1_1 : Integrable (fun x => ((B0579.pd k (B0579.pd k ψ) x : ℝ) : ℂ) * g₁ x) volume := by
      refine (integrable_of_cs_mul hχ_cd.continuous hχ_cs
        ((Complex.continuous_ofReal.comp (hpd2_ψ_c k)).mul hg.continuous)).congr
        (Eventually.of_forall fun x => ?_)
      simp only [g₁, Pi.mul_apply, Function.comp_apply]; ring
    have i1_2a : Integrable (fun x => ((B0579.pd k χ x : ℝ) : ℂ) *
        (((B0579.pd k ψ x : ℝ) : ℂ) * g x)) volume :=
      integrable_of_cs_mul hpdχ_c hpdχ_cs
        ((Complex.continuous_ofReal.comp (hpd_ψ_cd k).continuous).mul hg.continuous)
    have i1_2b : Integrable (fun x => ((B0579.pd k ψ x : ℝ) : ℂ) * g₂ x) volume := by
      refine (integrable_of_cs_mul hχ_cd.continuous hχ_cs
        ((Complex.continuous_ofReal.comp (hpd_ψ_cd k).continuous).mul (hpd_g_cd k).continuous)).congr
        (Eventually.of_forall fun x => ?_)
      simp only [g₂, Pi.mul_apply, Function.comp_apply]; ring
    have i1_2 : Integrable (fun x => ((B0579.pd k ψ x : ℝ) : ℂ) * pdCx k g₁ x) volume := by
      refine (i1_2a.add i1_2b).congr (Eventually.of_forall fun x => ?_)
      simp only [Pi.add_apply, g₂]
      rw [hpd_g₁ x]; ring
    have hibp1 := integral_plane_pd_mul k ((hpd_ψ_cd k).differentiable (by simp)) hg₁_diff
      i1_0 i1_1 i1_2
    -- Second IBP: `f = ψ`, `g = g₂`
    have i2_0 : Integrable (fun x => ((ψ x : ℝ) : ℂ) * g₂ x) volume := by
      refine (integrable_of_cs_mul hχ_cd.continuous hχ_cs
        ((Complex.continuous_ofReal.comp hψ.continuous).mul (hpd_g_cd k).continuous)).congr
        (Eventually.of_forall fun x => ?_)
      simp only [g₂, Pi.mul_apply, Function.comp_apply]; ring
    have i2_2a : Integrable (fun x => ((B0579.pd k χ x : ℝ) : ℂ) *
        (((ψ x : ℝ) : ℂ) * pdCx k g x)) volume :=
      integrable_of_cs_mul hpdχ_c hpdχ_cs
        ((Complex.continuous_ofReal.comp hψ.continuous).mul (hpd_g_cd k).continuous)
    have i2_2b : Integrable (fun x => ((χ x : ℝ) : ℂ) *
        (((ψ x : ℝ) : ℂ) * pdCx k (pdCx k g) x)) volume :=
      integrable_of_cs_mul hχ_cd.continuous hχ_cs
        ((Complex.continuous_ofReal.comp hψ.continuous).mul (hpd2_g_c k))
    have i2_2 : Integrable (fun x => ((ψ x : ℝ) : ℂ) * pdCx k g₂ x) volume := by
      refine (i2_2a.add i2_2b).congr (Eventually.of_forall fun x => ?_)
      simp only [Pi.add_apply]
      rw [hpd_g₂ x]; ring
    have hibp2 := integral_plane_pd_mul k hψ_diff hg₂_diff i2_0 i1_2b i2_2
    -- Combine both IBPs
    have hlhs : ∫ x : ℝ × ℝ, ((χ x : ℝ) : ℂ) * (((B0579.pd k (B0579.pd k ψ) x : ℝ) : ℂ) * g x) =
        ∫ x : ℝ × ℝ, ((B0579.pd k (B0579.pd k ψ) x : ℝ) : ℂ) * g₁ x :=
      integral_congr_ae (Eventually.of_forall fun x => by dsimp only [g₁]; ring)
    have hrhs1 : ∫ x : ℝ × ℝ, ((B0579.pd k ψ x : ℝ) : ℂ) * pdCx k g₁ x =
        (∫ x : ℝ × ℝ, ((B0579.pd k χ x : ℝ) : ℂ) * (((B0579.pd k ψ x : ℝ) : ℂ) * g x)) +
          ∫ x : ℝ × ℝ, ((B0579.pd k ψ x : ℝ) : ℂ) * g₂ x := by
      rw [← integral_add i1_2a i1_2b]
      exact integral_congr_ae (Eventually.of_forall fun x => by
        dsimp only [g₂]; rw [hpd_g₁ x]; ring)
    have hrhs2 : ∫ x : ℝ × ℝ, ((ψ x : ℝ) : ℂ) * pdCx k g₂ x =
        (∫ x : ℝ × ℝ, ((B0579.pd k χ x : ℝ) : ℂ) * (((ψ x : ℝ) : ℂ) * pdCx k g x)) +
          ∫ x : ℝ × ℝ, ((χ x : ℝ) : ℂ) * (((ψ x : ℝ) : ℂ) * pdCx k (pdCx k g) x) := by
      rw [← integral_add i2_2a i2_2b]
      exact integral_congr_ae (Eventually.of_forall fun x => by
        dsimp only; rw [hpd_g₂ x]; ring)
    have herr : (∫ x : ℝ × ℝ, ((B0579.pd k χ x : ℝ) : ℂ) * (((ψ x : ℝ) : ℂ) * pdCx k g x)) -
        (∫ x : ℝ × ℝ, ((B0579.pd k χ x : ℝ) : ℂ) * (((B0579.pd k ψ x : ℝ) : ℂ) * g x)) =
        ∫ x : ℝ × ℝ, ((B0579.pd k χ x : ℝ) : ℂ) *
          (((ψ x : ℝ) : ℂ) * pdCx k g x - ((B0579.pd k ψ x : ℝ) : ℂ) * g x) := by
      rw [← integral_sub i2_2a i1_2a]
      exact integral_congr_ae (Eventually.of_forall fun x => by dsimp only; ring)
    rw [hlhs, hibp1, hrhs1, hibp2, hrhs2]
    linear_combination herr
  -- Step B: Sum `k = 0, 1` at `R = (n : ℝ) + 1` and pass to the limit `n → ∞`
  have hsum_id : ∀ n : ℕ,
      ∫ x : ℝ × ℝ, ((cut2 ((n : ℝ) + 1) x : ℝ) : ℂ) *
          (((UnforcedLeray.Short.IIb.lapP ψ x : ℝ) : ℂ) * g x) =
        (∫ x : ℝ × ℝ, ((cut2 ((n : ℝ) + 1) x : ℝ) : ℂ) *
          (((ψ x : ℝ) : ℂ) * UnforcedLeray.Cyl.laplacian g x)) +
          (∫ x : ℝ × ℝ, ((B0579.pd 0 (cut2 ((n : ℝ) + 1)) x : ℝ) : ℂ) *
            (((ψ x : ℝ) : ℂ) * pdCx 0 g x - ((B0579.pd 0 ψ x : ℝ) : ℂ) * g x)) +
          (∫ x : ℝ × ℝ, ((B0579.pd 1 (cut2 ((n : ℝ) + 1)) x : ℝ) : ℂ) *
            (((ψ x : ℝ) : ℂ) * pdCx 1 g x - ((B0579.pd 1 ψ x : ℝ) : ℂ) * g x)) := by
    intro n
    set R : ℝ := (n : ℝ) + 1
    have hR : 0 < R := by positivity
    have hχ_c := (cut2_contDiff R).continuous
    have hχ_cs := cut2_hasCompactSupport hR
    have il0 : Integrable (fun x : ℝ × ℝ =>
        ((cut2 R x : ℝ) : ℂ) * (((B0579.pd 0 (B0579.pd 0 ψ) x : ℝ) : ℂ) * g x)) volume :=
      integrable_of_cs_mul hχ_c hχ_cs
        ((Complex.continuous_ofReal.comp (hpd2_ψ_c 0)).mul hg.continuous)
    have il1 : Integrable (fun x : ℝ × ℝ =>
        ((cut2 R x : ℝ) : ℂ) * (((B0579.pd 1 (B0579.pd 1 ψ) x : ℝ) : ℂ) * g x)) volume :=
      integrable_of_cs_mul hχ_c hχ_cs
        ((Complex.continuous_ofReal.comp (hpd2_ψ_c 1)).mul hg.continuous)
    have ir0 : Integrable (fun x : ℝ × ℝ =>
        ((cut2 R x : ℝ) : ℂ) * (((ψ x : ℝ) : ℂ) * pdCx 0 (pdCx 0 g) x)) volume :=
      integrable_of_cs_mul hχ_c hχ_cs
        ((Complex.continuous_ofReal.comp hψ.continuous).mul (hpd2_g_c 0))
    have ir1 : Integrable (fun x : ℝ × ℝ =>
        ((cut2 R x : ℝ) : ℂ) * (((ψ x : ℝ) : ℂ) * pdCx 1 (pdCx 1 g) x)) volume :=
      integrable_of_cs_mul hχ_c hχ_cs
        ((Complex.continuous_ofReal.comp hψ.continuous).mul (hpd2_g_c 1))
    have hl : ∫ x : ℝ × ℝ, ((cut2 R x : ℝ) : ℂ) *
          (((UnforcedLeray.Short.IIb.lapP ψ x : ℝ) : ℂ) * g x) =
        (∫ x : ℝ × ℝ, ((cut2 R x : ℝ) : ℂ) * (((B0579.pd 0 (B0579.pd 0 ψ) x : ℝ) : ℂ) * g x)) +
          ∫ x : ℝ × ℝ, ((cut2 R x : ℝ) : ℂ) * (((B0579.pd 1 (B0579.pd 1 ψ) x : ℝ) : ℂ) * g x) := by
      rw [← integral_add il0 il1]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      dsimp only
      unfold UnforcedLeray.Short.IIb.lapP
      push_cast; ring
    have hr : ∫ x : ℝ × ℝ, ((cut2 R x : ℝ) : ℂ) *
          (((ψ x : ℝ) : ℂ) * UnforcedLeray.Cyl.laplacian g x) =
        (∫ x : ℝ × ℝ, ((cut2 R x : ℝ) : ℂ) * (((ψ x : ℝ) : ℂ) * pdCx 0 (pdCx 0 g) x)) +
          ∫ x : ℝ × ℝ, ((cut2 R x : ℝ) : ℂ) * (((ψ x : ℝ) : ℂ) * pdCx 1 (pdCx 1 g) x) := by
      rw [← integral_add ir0 ir1]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      dsimp only
      rw [hlap_g_eq x]; ring
    rw [hl, hcut_id R hR 0, hcut_id R hR 1, hr]
    ring
  -- Dominated convergence for `∫ cut2 (n+1) * U → ∫ U`
  have htend_cut : ∀ {U : ℝ × ℝ → ℂ} {CU : ℝ}, Continuous U →
      (∀ x, ‖U x‖ ≤ CU * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (8 * A))) →
      Tendsto (fun n : ℕ => ∫ x : ℝ × ℝ, ((cut2 ((n : ℝ) + 1) x : ℝ) : ℂ) * U x)
        atTop (𝓝 (∫ x : ℝ × ℝ, U x)) := by
    intro U CU hUc hUb
    refine tendsto_integral_of_dominated_convergence
      (fun x : ℝ × ℝ => CU * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (8 * A)))
      (fun n => ((Complex.continuous_ofReal.comp (cut2_contDiff _).continuous).mul
        hUc).aestronglyMeasurable)
      ((integrable_gauss_plane hA).const_mul CU)
      (fun n => Eventually.of_forall fun x => ?_)
      (Eventually.of_forall fun x => ?_)
    · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (cut2_nonneg _ _)]
      exact (mul_le_of_le_one_left (norm_nonneg _) (cut2_le_one _ _)).trans (hUb x)
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop ⌈max |x.1| |x.2|⌉₊] with n hn
      have hm : max |x.1| |x.2| ≤ (n : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hn)
      have hc1 : cut2 ((n : ℝ) + 1) x = 1 :=
        cut2_eq_one (by positivity) ((le_max_left _ _).trans (by linarith))
          ((le_max_right _ _).trans (by linarith))
      simp [hc1]
  have hlap_ψ_c : Continuous (UnforcedLeray.Short.IIb.lapP ψ) :=
    (hpd2_ψ_c 0).add (hpd2_ψ_c 1)
  have hlap_g_c : Continuous (UnforcedLeray.Cyl.laplacian g) := by
    rw [funext hlap_g_eq]; exact (hpd2_g_c 0).add (hpd2_g_c 1)
  have htend_lhs := htend_cut
    (U := fun x : ℝ × ℝ => ((UnforcedLeray.Short.IIb.lapP ψ x : ℝ) : ℂ) * g x)
    (CU := Cψ * C0)
    ((Complex.continuous_ofReal.comp hlap_ψ_c).mul hg.continuous) fun x => by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc |UnforcedLeray.Short.IIb.lapP ψ x| * ‖g x‖
        ≤ Cψ * (C0 * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (8 * A))) :=
          mul_le_mul (hlap_ψ_bd x) (hg_bd x) (norm_nonneg _) hCψ
      _ = (Cψ * C0) * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (8 * A)) := by ring
  have htend_rhs0 := htend_cut
    (U := fun x : ℝ × ℝ => ((ψ x : ℝ) : ℂ) * UnforcedLeray.Cyl.laplacian g x)
    (CU := Cψ * (2 * C2))
    ((Complex.continuous_ofReal.comp hψ.continuous).mul hlap_g_c) fun x => by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, hlap_g_eq x]
    have hlg : ‖pdCx 0 (pdCx 0 g) x + pdCx 1 (pdCx 1 g) x‖ ≤
        (2 * C2) * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (8 * A)) := by
      calc ‖pdCx 0 (pdCx 0 g) x + pdCx 1 (pdCx 1 g) x‖
          ≤ ‖pdCx 0 (pdCx 0 g) x‖ + ‖pdCx 1 (pdCx 1 g) x‖ := norm_add_le _ _
        _ ≤ C2 * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (8 * A)) +
              C2 * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (8 * A)) :=
            add_le_add (hpd2_g_bd 0 x) (hpd2_g_bd 1 x)
        _ = (2 * C2) * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (8 * A)) := by ring
    calc |ψ x| * ‖pdCx 0 (pdCx 0 g) x + pdCx 1 (pdCx 1 g) x‖
        ≤ Cψ * ((2 * C2) * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (8 * A))) :=
          mul_le_mul (hψ_bd x) hlg (norm_nonneg _) hCψ
      _ = (Cψ * (2 * C2)) * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (8 * A)) := by ring
  -- Error integrals vanish as `n → ∞`
  obtain ⟨K, hK0, hK⟩ := exists_deriv_cut1_bound
  have htend_err : ∀ k : Fin 2,
      Tendsto (fun n : ℕ => ∫ x : ℝ × ℝ, ((B0579.pd k (cut2 ((n : ℝ) + 1)) x : ℝ) : ℂ) *
        (((ψ x : ℝ) : ℂ) * pdCx k g x - ((B0579.pd k ψ x : ℝ) : ℂ) * g x))
        atTop (𝓝 0) := by
    intro k
    set CE : ℝ := Cψ * C1 + Cψ * C0
    have hdom_int : Integrable (fun x : ℝ × ℝ =>
        CE * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (8 * A))) volume :=
      (integrable_gauss_plane hA).const_mul CE
    set I_dom : ℝ := ∫ x : ℝ × ℝ, CE * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (8 * A))
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hbd_n : ∀ n : ℕ,
        ‖∫ x : ℝ × ℝ, ((B0579.pd k (cut2 ((n : ℝ) + 1)) x : ℝ) : ℂ) *
          (((ψ x : ℝ) : ℂ) * pdCx k g x - ((B0579.pd k ψ x : ℝ) : ℂ) * g x)‖ ≤
        (K * I_dom) * ((n : ℝ) + 1)⁻¹ := by
      intro n
      set R : ℝ := (n : ℝ) + 1
      have hR : 0 < R := by positivity
      have hpdχ_c : Continuous (B0579.pd k (cut2 R)) := by
        unfold B0579.pd
        exact (((cut2_contDiff R).fderiv_right (m := (1 : ℕ)) (by simp)).clm_apply
          contDiff_const).continuous
      have hpdχ_cs : HasCompactSupport (B0579.pd k (cut2 R)) :=
        (cut2_hasCompactSupport hR).fderiv_apply ℝ (B0579.dir k)
      have hint_n : Integrable (fun x : ℝ × ℝ => ((B0579.pd k (cut2 R) x : ℝ) : ℂ) *
          (((ψ x : ℝ) : ℂ) * pdCx k g x - ((B0579.pd k ψ x : ℝ) : ℂ) * g x)) volume :=
        integrable_of_cs_mul hpdχ_c hpdχ_cs
          (((Complex.continuous_ofReal.comp hψ.continuous).mul (hpd_g_cd k).continuous).sub
            ((Complex.continuous_ofReal.comp (hpd_ψ_cd k).continuous).mul hg.continuous))
      calc ‖∫ x : ℝ × ℝ, ((B0579.pd k (cut2 R) x : ℝ) : ℂ) *
              (((ψ x : ℝ) : ℂ) * pdCx k g x - ((B0579.pd k ψ x : ℝ) : ℂ) * g x)‖
          ≤ ∫ x : ℝ × ℝ, ‖((B0579.pd k (cut2 R) x : ℝ) : ℂ) *
              (((ψ x : ℝ) : ℂ) * pdCx k g x - ((B0579.pd k ψ x : ℝ) : ℂ) * g x)‖ :=
            norm_integral_le_integral_norm _
        _ ≤ ∫ x : ℝ × ℝ, (K * R⁻¹) * (CE * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (8 * A))) := by
            refine integral_mono hint_n.norm (hdom_int.const_mul (K * R⁻¹)) fun x => ?_
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
            have hsub : ‖((ψ x : ℝ) : ℂ) * pdCx k g x - ((B0579.pd k ψ x : ℝ) : ℂ) * g x‖ ≤
                CE * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (8 * A)) := by
              calc ‖((ψ x : ℝ) : ℂ) * pdCx k g x - ((B0579.pd k ψ x : ℝ) : ℂ) * g x‖
                  ≤ ‖((ψ x : ℝ) : ℂ) * pdCx k g x‖ + ‖((B0579.pd k ψ x : ℝ) : ℂ) * g x‖ :=
                    norm_sub_le _ _
                _ ≤ Cψ * (C1 * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (8 * A))) +
                      Cψ * (C0 * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (8 * A))) := by
                    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
                      Real.norm_eq_abs, Real.norm_eq_abs]
                    exact add_le_add (mul_le_mul (hψ_bd x) (hpd_g_bd k x) (norm_nonneg _) hCψ)
                      (mul_le_mul (hpd_ψ_bd k x) (hg_bd x) (norm_nonneg _) hCψ)
                _ = CE * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (8 * A)) := by ring
            exact mul_le_mul (pd_cut2_bound hK0 hK hR k x) hsub (norm_nonneg _)
              (mul_nonneg hK0 (inv_nonneg.2 hR.le))
        _ = (K * I_dom) * ((n : ℝ) + 1)⁻¹ := by
            rw [integral_const_mul]
            dsimp only [R, I_dom]
            ring
    refine squeeze_zero (fun _ => norm_nonneg _) hbd_n ?_
    have hinv0 : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
    simpa [mul_zero] using hinv0.const_mul (K * I_dom)
  have htend_rhs : Tendsto (fun n : ℕ =>
      (∫ x : ℝ × ℝ, ((cut2 ((n : ℝ) + 1) x : ℝ) : ℂ) *
        (((ψ x : ℝ) : ℂ) * UnforcedLeray.Cyl.laplacian g x)) +
        (∫ x : ℝ × ℝ, ((B0579.pd 0 (cut2 ((n : ℝ) + 1)) x : ℝ) : ℂ) *
          (((ψ x : ℝ) : ℂ) * pdCx 0 g x - ((B0579.pd 0 ψ x : ℝ) : ℂ) * g x)) +
        (∫ x : ℝ × ℝ, ((B0579.pd 1 (cut2 ((n : ℝ) + 1)) x : ℝ) : ℂ) *
          (((ψ x : ℝ) : ℂ) * pdCx 1 g x - ((B0579.pd 1 ψ x : ℝ) : ℂ) * g x)))
      atTop (𝓝 (∫ x : ℝ × ℝ, ((ψ x : ℝ) : ℂ) * UnforcedLeray.Cyl.laplacian g x)) := by
    simpa using (htend_rhs0.add (htend_err 0)).add (htend_err 1)
  exact tendsto_nhds_unique htend_lhs (htend_rhs.congr fun n => (hsum_id n).symm)

private def rawDPhi (ν : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)))
    (φ : ℝ → B0579.Plane → ℝ) (r : ℝ) (x : B0579.Plane) : ℝ :=
  -(ν * UnforcedLeray.Short.IIb.lapP (φ r) x +
    (tr.v r x 0 * B0579.pd 0 (φ r) x + tr.v r x 1 * B0579.pd 1 (φ r) x))

private def rawDHeat (ν : ℝ) (e : ℝ × ℝ → ℂ) (r : ℝ) (x : ℝ × ℝ) : ℂ :=
  ν • (-(clockA ν r)⁻¹ •
    UnforcedLeray.Gaussian.heatDilation (clockA ν r) (UnforcedLeray.Gaussian.dilationDrift e) x)

private def rawIFun (ν : ℝ) (φ : ℝ → B0579.Plane → ℝ) (e : ℝ × ℝ → ℂ) (r : ℝ) : ℂ :=
  ∫ x : ℝ × ℝ, ((φ r x : ℝ) : ℂ) * UnforcedLeray.Gaussian.heatDilation (clockA ν r) e x

private def rawFInt' (ν : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)))
    (φ : ℝ → B0579.Plane → ℝ) (e : ℝ × ℝ → ℂ) (r : ℝ) (x : ℝ × ℝ) : ℂ :=
  ((rawDPhi ν tr φ r x : ℝ) : ℂ) * UnforcedLeray.Gaussian.heatDilation (clockA ν r) e x +
    ((φ r x : ℝ) : ℂ) * rawDHeat ν e r x

private def rawFE (P : PlanarData) (ν t₁ t : ℝ) (φ : ℝ → B0579.Plane → ℝ)
    (e : ℝ × ℝ → ℂ) (σ : ℝ) : ℂ :=
  (((clockN P ν (ageAt ν t₁ σ) t)⁻¹ : ℝ) : ℂ) * rawIFun ν φ e (ageAt ν t₁ σ)

private def rawFR (P : PlanarData) (ν : ℝ)
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (t₁ t : ℝ)
    (φ : ℝ → B0579.Plane → ℝ) (e : ℝ × ℝ → ℂ) (σ : ℝ) : ℂ :=
  let s := ageAt ν t₁ σ
  let a := clockA ν s
  (((clockN P ν s t)⁻¹ * a⁻¹ : ℝ) : ℂ) *
    ∫ y : ℝ × ℝ, ((φ s (Real.sqrt a * y.1, Real.sqrt a * y.2) : ℝ) : ℂ) *
      (-(clockTheta ν s : ℂ)⁻¹ * movD e y +
        (((movingTrainV tr s y 0 : ℝ) : ℂ) * pdCx 0 e y +
          ((movingTrainV tr s y 1 : ℝ) : ℂ) * pdCx 1 e y) +
        ((movBeta0 P ν s : ℝ) : ℂ) * e y)

private structure SeedBounds (e : ℝ × ℝ → ℂ) where
  he_inf : ContDiff ℝ ∞ e
  he_cd2 : ContDiff ℝ 2 e
  he_diff : Differentiable ℝ e
  Ce0 : ℝ
  Ce1 : ℝ
  Ce2 : ℝ
  CD : ℝ
  hCe0 : 0 ≤ Ce0
  hCe1 : 0 ≤ Ce1
  hCe2 : 0 ≤ Ce2
  hCD0 : 0 ≤ CD
  he_val_bd : ∀ y : ℝ × ℝ, ‖e y‖ ≤ Ce0 * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8)
  he_pd_cont : ∀ k : Fin 2, Continuous (pdCx k e)
  he_pd_bd : ∀ k : Fin 2, ∀ y : ℝ × ℝ, ‖pdCx k e y‖ ≤ Ce1 * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8)
  he_pd2_bd : ∀ k : Fin 2, ∀ y : ℝ × ℝ,
    ‖pdCx k (pdCx k e) y‖ ≤ Ce2 * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8)
  hcont_movD : Continuous (movD e)
  hCD : ∀ y : ℝ × ℝ, ‖movD e y‖ ≤ CD * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8)
  hdilationDrift_bd : ∀ y : ℝ × ℝ,
    ‖UnforcedLeray.Gaussian.dilationDrift e y‖ ≤
      (2 * Ce0 + Ce1) * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8)

private structure PhiTrainBounds (ν t₁ t : ℝ)
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)))
    (φ : ℝ → B0579.Plane → ℝ) where
  hφsp : UnforcedLeray.Short.IIb.CylEtaSpatial (ν ^ (-2 : ℝ)) t₁ t φ
  hφ_cd : ∀ r ∈ Icc t₁ t, ContDiff ℝ ∞ (φ r)
  hφpde : ∀ r ∈ Ioo t₁ t, ∀ x : B0579.Plane,
    HasDerivAt (fun r' => φ r' x) (rawDPhi ν tr φ r x) r
  Cφ : ℝ
  V₀ : ℝ
  V₁ : ℝ
  hCφ0 : 0 ≤ Cφ
  hV₀0 : 0 ≤ V₀
  hV₁0 : 0 ≤ V₁
  hφ_bd : ∀ r ∈ Icc t₁ t, ∀ x : B0579.Plane,
    |φ r x| + |B0579.pd 0 (φ r) x| + |B0579.pd 1 (φ r) x| +
      |UnforcedLeray.Short.IIb.lapP (φ r) x| ≤ Cφ
  hv_bd : ∀ r ∈ Icc t₁ t, ∀ x : B0579.Plane, ∀ k : Fin 2, |tr.v r x k| ≤ V₀
  hv_pd_bd : ∀ r ∈ Icc t₁ t, ∀ x : B0579.Plane, ∀ k l : Fin 2,
    |B0579.pd l (fun w => tr.v r w k) x| ≤ V₁

private lemma exists_seedBounds {κ : PlanarFrameKernels}
    (hκ : IsSeedKernels κ) (j : Fin 2) :
    Nonempty (SeedBounds (κ.e j)) := by
  set e : ℝ × ℝ → ℂ := κ.e j
  have he_inf : ContDiff ℝ ∞ e := (OscillatorForceSub.seed_e_smooth_decay hκ).1 j
  have he_cd2 : ContDiff ℝ 2 e := he_inf.of_le (by simp)
  have he_diff : Differentiable ℝ e := he_cd2.differentiable (by norm_num)
  obtain ⟨Ce0, hCe0, he0_bd⟩ := (OscillatorForceSub.seed_e_smooth_decay hκ).2 j 0
  obtain ⟨Ce1, hCe1, he1_bd⟩ := (OscillatorForceSub.seed_e_smooth_decay hκ).2 j 1
  obtain ⟨Ce2, hCe2, he2_bd⟩ := (OscillatorForceSub.seed_e_smooth_decay hκ).2 j 2
  obtain ⟨hcont_movD, CD, hCD0, hCD⟩ := OscillatorForceSub.movD_seed_decay hκ j
  have he_val_bd : ∀ y : ℝ × ℝ, ‖e y‖ ≤ Ce0 * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8) := by
    intro y
    have h := he0_bd y
    rw [norm_iteratedFDeriv_zero] at h
    exact (le_mul_of_one_le_left (norm_nonneg _) (by linarith [norm_nonneg y])).trans h
  have he_pd_bd : ∀ k : Fin 2, ∀ y : ℝ × ℝ,
      ‖pdCx k e y‖ ≤ Ce1 * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8) := by
    intro k y
    have h := he1_bd y
    rw [norm_iteratedFDeriv_one] at h
    have hdir : ‖B0579.dir k‖ ≤ 1 := by fin_cases k <;> simp [B0579.dir]
    have h1 : ‖pdCx k e y‖ ≤ ‖fderiv ℝ e y‖ :=
      ((fderiv ℝ e y).le_opNorm _).trans (mul_le_of_le_one_right (norm_nonneg _) hdir)
    exact (h1.trans (le_mul_of_one_le_left (norm_nonneg _) (by linarith [norm_nonneg y]))).trans h
  have he_pd_cont : ∀ k : Fin 2, Continuous (pdCx k e) := fun k => by
    unfold pdCx
    exact ((he_inf.fderiv_right (m := (1 : ℕ)) (by simp)).clm_apply contDiff_const).continuous
  have he_pd2_bd : ∀ k : Fin 2, ∀ y : ℝ × ℝ,
      ‖pdCx k (pdCx k e) y‖ ≤ Ce2 * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8) := by
    intro k y
    have h := he2_bd y
    have hd2 : Differentiable ℝ (fderiv ℝ e) :=
      (he_cd2.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
    have heq : pdCx k (pdCx k e) y = iteratedFDeriv ℝ 2 e y ![B0579.dir k, B0579.dir k] := by
      unfold pdCx
      rw [iteratedFDeriv_two_apply, fderiv_clm_apply (hd2 y) (differentiableAt_const _)]
      simp
    rw [heq]
    have hdir : ∀ i : Fin 2, ‖![B0579.dir k, B0579.dir k] i‖ ≤ 1 := by
      intro i; fin_cases i <;> (fin_cases k <;> simp [B0579.dir])
    have hop : ‖iteratedFDeriv ℝ 2 e y ![B0579.dir k, B0579.dir k]‖ ≤ ‖iteratedFDeriv ℝ 2 e y‖ := by
      refine ((iteratedFDeriv ℝ 2 e y).le_opNorm _).trans ?_
      rw [Fin.prod_univ_two]
      exact mul_le_of_le_one_right (norm_nonneg _)
        (mul_le_one₀ (hdir 0) (norm_nonneg _) (hdir 1))
    exact (hop.trans (le_mul_of_one_le_left (norm_nonneg _) (by linarith [norm_nonneg y]))).trans h
  have hdilationDrift_bd : ∀ y : ℝ × ℝ,
      ‖UnforcedLeray.Gaussian.dilationDrift e y‖ ≤
        (2 * Ce0 + Ce1) * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8) := by
    intro y
    unfold UnforcedLeray.Gaussian.dilationDrift
    have h1 : ‖(2 : ℝ) • e y‖ ≤ 2 * Ce0 * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8) := by
      rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      linarith [he_val_bd y]
    have h2 : ‖(1 / 2 : ℝ) • fderiv ℝ e y y‖ ≤ Ce1 * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8) := by
      rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      have h := he1_bd y
      rw [norm_iteratedFDeriv_one] at h
      have hop : ‖fderiv ℝ e y y‖ ≤ (1 + ‖y‖) * ‖fderiv ℝ e y‖ := by
        refine ((fderiv ℝ e y).le_opNorm y).trans ?_
        nlinarith [norm_nonneg (fderiv ℝ e y), norm_nonneg y]
      have := hop.trans h
      linarith [norm_nonneg (fderiv ℝ e y y)]
    calc ‖(2 : ℝ) • e y + (1 / 2 : ℝ) • fderiv ℝ e y y‖
        ≤ ‖(2 : ℝ) • e y‖ + ‖(1 / 2 : ℝ) • fderiv ℝ e y y‖ := norm_add_le _ _
      _ ≤ 2 * Ce0 * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8) +
            Ce1 * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8) := add_le_add h1 h2
      _ = (2 * Ce0 + Ce1) * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8) := by ring
  exact ⟨⟨he_inf, he_cd2, he_diff, Ce0, Ce1, Ce2, CD, hCe0, hCe1, hCe2, hCD0,
    he_val_bd, he_pd_cont, he_pd_bd, he_pd2_bd, hcont_movD, hCD, hdilationDrift_bd⟩⟩

private lemma exists_phiTrainBounds {ν t₁ t₂ t : ℝ}
    {tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))}
    {φ : ℝ → B0579.Plane → ℝ}
    (htr : UnforcedLeray.Short.PartI.IsBUCTrain tr)
    (hφsp : UnforcedLeray.Short.IIb.CylEtaSpatial (ν ^ (-2 : ℝ)) t₁ t φ)
    (hφpde : ∀ r ∈ Ioo t₁ t, ∀ x : B0579.Plane,
      HasDerivAt (fun r' => φ r' x) (rawDPhi ν tr φ r x) r)
    (ht₁ : 0 ≤ t₁) (ht₂ : 0 ≤ t₂) (ht_mem : t ∈ Icc t₁ t₂) :
    Nonempty (PhiTrainBounds ν t₁ t tr φ) := by
  have hφ_cd : ∀ r ∈ Icc t₁ t, ContDiff ℝ ∞ (φ r) := by
    intro r hr
    have h := hφsp.smooth.comp (contDiff_const.prodMk contDiff_id).contDiffOn
      (s := univ) (fun x _ => ⟨hr, mem_univ x⟩)
    rwa [contDiffOn_univ] at h
  obtain ⟨Cφ_raw, hCφ_raw⟩ := hφsp.decay 0
  set Cφ : ℝ := max Cφ_raw 0
  have hCφ0 : 0 ≤ Cφ := le_max_right _ _
  have hφ_bd : ∀ r ∈ Icc t₁ t, ∀ x : B0579.Plane,
      |φ r x| + |B0579.pd 0 (φ r) x| + |B0579.pd 1 (φ r) x| +
        |UnforcedLeray.Short.IIb.lapP (φ r) x| ≤ Cφ := by
    intro r hr x
    have h := hCφ_raw r hr x
    rw [Real.rpow_zero, mul_one] at h
    exact h.trans (le_max_left _ _)
  obtain ⟨V0_raw, hV0_raw⟩ := htr.sup_bound ht₂
  obtain ⟨V1_raw, hV1_raw⟩ := htr.deriv_bound ht₂ 1
  set V₀ : ℝ := max V0_raw 0
  set V₁ : ℝ := max V1_raw 0
  have hV₀0 : 0 ≤ V₀ := le_max_right _ _
  have hV₁0 : 0 ≤ V₁ := le_max_right _ _
  have hv_bd : ∀ r ∈ Icc t₁ t, ∀ x : B0579.Plane, ∀ k : Fin 2, |tr.v r x k| ≤ V₀ := by
    intro r hr x k
    have hr2 : r ∈ Icc 0 t₂ := ⟨ht₁.trans hr.1, hr.2.trans ht_mem.2⟩
    exact ((PiLp.norm_apply_le (tr.v r x) k).trans (hV0_raw r hr2 x)).trans (le_max_left _ _)
  have hv_pd_bd : ∀ r ∈ Icc t₁ t, ∀ x : B0579.Plane, ∀ k l : Fin 2,
      |B0579.pd l (fun w => tr.v r w k) x| ≤ V₁ := by
    intro r hr x k l
    have hr0 : 0 ≤ r := ht₁.trans hr.1
    have hr2 : r ∈ Icc 0 t₂ := ⟨hr0, hr.2.trans ht_mem.2⟩
    have hv_diff : Differentiable ℝ (tr.v r) :=
      (UnforcedLeray.B0238.contDiff_Vc tr hr0).differentiable (by simp)
    have hproj : HasFDerivAt (fun w => tr.v r w k)
        ((EuclideanSpace.proj k : UnforcedLeray.Train.Vec →L[ℝ] ℝ).comp (fderiv ℝ (tr.v r) x)) x :=
      (EuclideanSpace.proj k : UnforcedLeray.Train.Vec →L[ℝ] ℝ).hasFDerivAt.comp x
        (hv_diff x).hasFDerivAt
    have hdir : ‖B0579.dir l‖ ≤ 1 := by fin_cases l <;> simp [B0579.dir]
    unfold B0579.pd
    rw [hproj.fderiv, ContinuousLinearMap.comp_apply, ← Real.norm_eq_abs]
    have h1 : ‖(EuclideanSpace.proj k : UnforcedLeray.Train.Vec →L[ℝ] ℝ)
        (fderiv ℝ (tr.v r) x (B0579.dir l))‖ ≤ ‖fderiv ℝ (tr.v r) x (B0579.dir l)‖ :=
      PiLp.norm_apply_le _ k
    have h2 : ‖fderiv ℝ (tr.v r) x (B0579.dir l)‖ ≤ ‖fderiv ℝ (tr.v r) x‖ :=
      ((fderiv ℝ (tr.v r) x).le_opNorm _).trans (mul_le_of_le_one_right (norm_nonneg _) hdir)
    have h3 : ‖fderiv ℝ (tr.v r) x‖ ≤ V₁ := by
      have := hV1_raw r hr2 x
      rw [norm_iteratedFDeriv_one] at this
      exact this.trans (le_max_left _ _)
    exact h1.trans (h2.trans h3)
  exact ⟨⟨hφsp, hφ_cd, hφpde, Cφ, V₀, V₁, hCφ0, hV₀0, hV₁0, hφ_bd, hv_bd, hv_pd_bd⟩⟩

private lemma dualPair_eq_rawFE_and_rawFR {κ : PlanarFrameKernels} (P : PlanarData) {ν : ℝ}
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (t₁ τ : ℝ)
    (φ : ℝ → B0579.Plane → ℝ) (j : Fin 2)
    (hκ : IsSeedKernels κ) (hν : 0 < ν) (ht₁ : 0 ≤ t₁)
    (hage_Icc : ∀ σ ∈ Icc (0 : ℝ) τ, ageAt ν t₁ σ ∈ Icc t₁ (ageAt ν t₁ τ))
    (hd_ge1 : ∀ σ ∈ Icc (0 : ℝ) τ, 1 ≤ dOf ν t₁ σ)
    (sb : SeedBounds (κ.e j)) (pb : PhiTrainBounds ν t₁ (ageAt ν t₁ τ) tr φ) :
    (∀ σ ∈ Icc (0 : ℝ) τ,
        dualPair P ν t₁ τ φ σ (frameEFun κ ν t₁ j σ) =
          rawFE P ν t₁ (ageAt ν t₁ τ) φ (κ.e j) σ) ∧
      (∀ σ ∈ Icc (0 : ℝ) τ,
        dualPair P ν t₁ τ φ σ (frameRFun κ P ν tr t₁ j σ) =
          rawFR P ν tr t₁ (ageAt ν t₁ τ) φ (κ.e j) σ) := by
  rcases sb with ⟨he_inf, _he_cd2, _he_diff, Ce0, Ce1, _Ce2, CD, hCe0, hCe1, _hCe2, hCD0,
    he_val_bd, he_pd_cont, he_pd_bd, _he_pd2_bd, hcont_movD, hCD, _hdilationDrift_bd⟩
  rcases pb with ⟨hφsp, hφ_cd, _hφpde, Cφ, V₀, _V₁, hCφ0, hV₀0, _hV₁0, hφ_bd, hv_bd, _hv_pd_bd⟩
  set t := ageAt ν t₁ τ
  set e : ℝ × ℝ → ℂ := κ.e j
  unfold rawFE rawIFun rawFR
  set IFun : ℝ → ℂ := fun r =>
    ∫ x : ℝ × ℝ, ((φ r x : ℝ) : ℂ) * UnforcedLeray.Gaussian.heatDilation (clockA ν r) e x
  set FE : ℝ → ℂ := fun σ =>
    (((clockN P ν (ageAt ν t₁ σ) t)⁻¹ : ℝ) : ℂ) * IFun (ageAt ν t₁ σ)
  set FR : ℝ → ℂ := fun σ =>
    let s := ageAt ν t₁ σ
    let a := clockA ν s
    (((clockN P ν s t)⁻¹ * a⁻¹ : ℝ) : ℂ) *
      ∫ y : ℝ × ℝ, ((φ s (Real.sqrt a * y.1, Real.sqrt a * y.2) : ℝ) : ℂ) *
        (-(clockTheta ν s : ℂ)⁻¹ * movD e y +
          (((movingTrainV tr s y 0 : ℝ) : ℂ) * pdCx 0 e y +
            ((movingTrainV tr s y 1 : ℝ) : ℂ) * pdCx 1 e y) +
          ((movBeta0 P ν s : ℝ) : ℂ) * e y)
  have hFE_eq : ∀ σ ∈ Icc (0 : ℝ) τ,
      dualPair P ν t₁ τ φ σ (frameEFun κ ν t₁ j σ) = FE σ := by
    intro σ hσ
    set s := ageAt ν t₁ σ
    set a := clockA ν s
    set d := dOf ν t₁ σ
    have hs : s ∈ Icc t₁ t := hage_Icc σ hσ
    have hs0 : 0 ≤ s := ht₁.trans hs.1
    have ha1 : 1 ≤ a := one_le_clockA hν.le hs0
    have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha1
    have hsq : 0 < Real.sqrt a := Real.sqrt_pos.2 ha0
    have hd1 : 1 ≤ d := hd_ge1 σ hσ
    have hg_cont : Continuous (fun y : ℝ × ℝ =>
        ((φ s (Real.sqrt a * y.1, Real.sqrt a * y.2) : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp
        ((hφ_cd s hs).continuous.comp ((continuous_const.mul continuous_fst).prodMk
          (continuous_const.mul continuous_snd)))
    have hg_per : UnforcedLeray.Cyl.IsPeriodic d
        (fun y : ℝ × ℝ => ((φ s (Real.sqrt a * y.1, Real.sqrt a * y.2) : ℝ) : ℂ)) := by
      intro y
      dsimp only
      have hd_mul : Real.sqrt a * (y.1 + d) = Real.sqrt a * y.1 + ν ^ (-2 : ℝ) := by
        change Real.sqrt a * (y.1 + ν ^ (-2 : ℝ) / Real.sqrt a) = Real.sqrt a * y.1 + ν ^ (-2 : ℝ)
        rw [mul_add, mul_div_cancel₀ _ hsq.ne']
      rw [hd_mul, hφsp.periodic s hs (Real.sqrt a * y.1, Real.sqrt a * y.2)]
    have hg_bd : ∀ y : ℝ × ℝ, ‖((φ s (Real.sqrt a * y.1, Real.sqrt a * y.2) : ℝ) : ℂ)‖ ≤ Cφ := by
      intro y
      rw [Complex.norm_real, Real.norm_eq_abs]
      have h := hφ_bd s hs (Real.sqrt a * y.1, Real.sqrt a * y.2)
      linarith [abs_nonneg (B0579.pd 0 (φ s) (Real.sqrt a * y.1, Real.sqrt a * y.2)),
        abs_nonneg (B0579.pd 1 (φ s) (Real.sqrt a * y.1, Real.sqrt a * y.2)),
        abs_nonneg (UnforcedLeray.Short.IIb.lapP (φ s) (Real.sqrt a * y.1, Real.sqrt a * y.2))]
    have hunf := (integrableOn_and_integral_cell_mul_perSum hd1 he_inf.continuous hg_cont hg_per
      hCe0 hCφ0 he_val_bd hg_bd).2.2
    have hFE_raw : dualPair P ν t₁ τ φ σ (frameEFun κ ν t₁ j σ) =
        (((clockN P ν s t)⁻¹ * a⁻¹ : ℝ) : ℂ) *
          ∫ y : ℝ × ℝ, ((φ s (Real.sqrt a * y.1, Real.sqrt a * y.2) : ℝ) : ℂ) * e y := by
      unfold frameEFun
      rw [dualPair_cellZeroExt]
      unfold perE
      rw [hunf]
    rw [hFE_raw]
    change _ = (((clockN P ν s t)⁻¹ : ℝ) : ℂ) *
      ∫ x : ℝ × ℝ, ((φ s x : ℝ) : ℂ) * UnforcedLeray.Gaussian.heatDilation a e x
    have hcov := integral_plane_eq_smul ha0
      (fun x => ((φ s x : ℝ) : ℂ) * UnforcedLeray.Gaussian.heatDilation a e x)
    rw [hcov]
    have hpt : ∀ y : ℝ × ℝ,
        ((φ s (Real.sqrt a * y.1, Real.sqrt a * y.2) : ℝ) : ℂ) *
          UnforcedLeray.Gaussian.heatDilation a e (Real.sqrt a * y.1, Real.sqrt a * y.2) =
        ((a⁻¹ ^ 2 : ℝ) : ℂ) *
          (((φ s (Real.sqrt a * y.1, Real.sqrt a * y.2) : ℝ) : ℂ) * e y) := by
      intro y
      rw [UnforcedLeray.Gaussian.heatDilation_apply, Complex.real_smul]
      have hinv : (Real.sqrt a)⁻¹ • ((Real.sqrt a * y.1, Real.sqrt a * y.2) : ℝ × ℝ) = y := by
        ext <;> simp [smul_eq_mul, inv_mul_cancel_left₀ hsq.ne']
      rw [hinv]
      ring
    simp_rw [hpt]
    rw [integral_const_mul]
    push_cast
    field_simp [ha0.ne']
  have hFR_eq : ∀ σ ∈ Icc (0 : ℝ) τ,
      dualPair P ν t₁ τ φ σ (frameRFun κ P ν tr t₁ j σ) = FR σ := by
    intro σ hσ
    set s := ageAt ν t₁ σ
    set a := clockA ν s
    set d := dOf ν t₁ σ
    have hs : s ∈ Icc t₁ t := hage_Icc σ hσ
    have hs0 : 0 ≤ s := ht₁.trans hs.1
    have ha1 : 1 ≤ a := one_le_clockA hν.le hs0
    have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha1
    have hsq : 0 < Real.sqrt a := Real.sqrt_pos.2 ha0
    have hd1 : 1 ≤ d := hd_ge1 σ hσ
    have hd0 : 0 < d := lt_of_lt_of_le zero_lt_one hd1
    unfold frameRFun
    rw [dualPair_cellZeroExt]
    dsimp only [FR]
    congr 1
    change (∫ y in B0579.cell d,
        ((φ s (Real.sqrt a * y.1, Real.sqrt a * y.2) : ℝ) : ℂ) *
          (movFreeRes κ tr s j y + ((movBeta0 P ν s : ℝ) : ℂ) * perE κ d j y)) =
      ∫ y : ℝ × ℝ, ((φ s (Real.sqrt a * y.1, Real.sqrt a * y.2) : ℝ) : ℂ) *
        (-(clockTheta ν s : ℂ)⁻¹ * movD e y +
          (((movingTrainV tr s y 0 : ℝ) : ℂ) * pdCx 0 e y +
            ((movingTrainV tr s y 1 : ℝ) : ℂ) * pdCx 1 e y) +
          ((movBeta0 P ν s : ℝ) : ℂ) * e y)
    set g1 : ℝ × ℝ → ℂ := fun y =>
      -(clockTheta ν s : ℂ)⁻¹ * ((φ s (Real.sqrt a * y.1, Real.sqrt a * y.2) : ℝ) : ℂ)
    set g2 : ℝ × ℝ → ℂ := fun y =>
      ((φ s (Real.sqrt a * y.1, Real.sqrt a * y.2) : ℝ) : ℂ) * ((movingTrainV tr s y 0 : ℝ) : ℂ)
    set g3 : ℝ × ℝ → ℂ := fun y =>
      ((φ s (Real.sqrt a * y.1, Real.sqrt a * y.2) : ℝ) : ℂ) * ((movingTrainV tr s y 1 : ℝ) : ℂ)
    set g4 : ℝ × ℝ → ℂ := fun y =>
      ((movBeta0 P ν s : ℝ) : ℂ) * ((φ s (Real.sqrt a * y.1, Real.sqrt a * y.2) : ℝ) : ℂ)
    -- Rewrite `movFreeRes` and `pdCx k (perE)` as `perSum d` terms
    have hrew : ∀ y : ℝ × ℝ,
        ((φ s (Real.sqrt a * y.1, Real.sqrt a * y.2) : ℝ) : ℂ) *
          (movFreeRes κ tr s j y + ((movBeta0 P ν s : ℝ) : ℂ) * perE κ d j y) =
        (g1 y * perSum d (movD e) y +
          (g2 y * perSum d (pdCx 0 e) y + g3 y * perSum d (pdCx 1 e) y)) +
        g4 y * perSum d e y := by
      intro y
      rw [movFreeRes_eq_neg_movOscRes_add,
        OscillatorForceSub.movOscRes_eq_perSum_movD hκ hν hs0 j y,
        EulerErrorTail.pdCx_perE_eq hκ hd0 j 0 y,
        EulerErrorTail.pdCx_perE_eq hκ hd0 j 1 y]
      unfold perE
      dsimp only [g1, g2, g3, g4, e, d, dOf, s, a]
      ring
    simp_rw [hrew]
    -- Continuity, periodicity, and bounds of the four multipliers
    have hφs_cont : Continuous (fun y : ℝ × ℝ =>
        ((φ s (Real.sqrt a * y.1, Real.sqrt a * y.2) : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp
        ((hφ_cd s hs).continuous.comp ((continuous_const.mul continuous_fst).prodMk
          (continuous_const.mul continuous_snd)))
    have hφs_per : ∀ y : ℝ × ℝ,
        ((φ s (Real.sqrt a * (y.1 + d), Real.sqrt a * y.2) : ℝ) : ℂ) =
          ((φ s (Real.sqrt a * y.1, Real.sqrt a * y.2) : ℝ) : ℂ) := by
      intro y
      have hd_mul : Real.sqrt a * (y.1 + d) = Real.sqrt a * y.1 + ν ^ (-2 : ℝ) := by
        change Real.sqrt a * (y.1 + ν ^ (-2 : ℝ) / Real.sqrt a) = Real.sqrt a * y.1 + ν ^ (-2 : ℝ)
        rw [mul_add, mul_div_cancel₀ _ hsq.ne']
      rw [hd_mul, hφsp.periodic s hs (Real.sqrt a * y.1, Real.sqrt a * y.2)]
    have hφs_bd : ∀ y : ℝ × ℝ,
        ‖((φ s (Real.sqrt a * y.1, Real.sqrt a * y.2) : ℝ) : ℂ)‖ ≤ Cφ := by
      intro y
      rw [Complex.norm_real, Real.norm_eq_abs]
      have h := hφ_bd s hs (Real.sqrt a * y.1, Real.sqrt a * y.2)
      linarith [abs_nonneg (B0579.pd 0 (φ s) (Real.sqrt a * y.1, Real.sqrt a * y.2)),
        abs_nonneg (B0579.pd 1 (φ s) (Real.sqrt a * y.1, Real.sqrt a * y.2)),
        abs_nonneg (UnforcedLeray.Short.IIb.lapP (φ s) (Real.sqrt a * y.1, Real.sqrt a * y.2))]
    have hV_per : ∀ (k : Fin 2) (y : ℝ × ℝ),
        ((movingTrainV tr s (y.1 + d, y.2) k : ℝ) : ℂ) =
          ((movingTrainV tr s y k : ℝ) : ℂ) := by
      intro k y
      dsimp only [movingTrainV]
      have hd_mul : Real.sqrt a * (y.1 + d) = Real.sqrt a * y.1 + ν ^ (-2 : ℝ) := by
        change Real.sqrt a * (y.1 + ν ^ (-2 : ℝ) / Real.sqrt a) = Real.sqrt a * y.1 + ν ^ (-2 : ℝ)
        rw [mul_add, mul_div_cancel₀ _ hsq.ne']
      rw [hd_mul]
      have hper := tr.isTrain.periodic_v s hs0 (Real.sqrt a * y.1, Real.sqrt a * y.2)
      exact congrArg (fun u : UnforcedLeray.Train.Vec =>
        ((a ^ (3 / 2 : ℝ) * u k : ℝ) : ℂ)) hper
    have hV_bd : ∀ k : Fin 2, ∀ y : ℝ × ℝ,
        ‖((movingTrainV tr s y k : ℝ) : ℂ)‖ ≤ a ^ (3 / 2 : ℝ) * V₀ := by
      intro k y
      rw [Complex.norm_real, Real.norm_eq_abs]
      unfold movingTrainV
      rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg ha0.le _)]
      exact mul_le_mul_of_nonneg_left (hv_bd s hs _ k) (Real.rpow_nonneg ha0.le _)
    obtain ⟨c1, i1, e1⟩ := integrableOn_and_integral_cell_mul_perSum (g := g1) hd1 hcont_movD
      (continuous_const.mul hφs_cont)
      (fun y => by dsimp only [g1]; rw [hφs_per y])
      hCD0 (mul_nonneg (norm_nonneg (-(clockTheta ν s : ℂ)⁻¹)) hCφ0) hCD
      (fun y => by dsimp only [g1]; rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hφs_bd y) (norm_nonneg _))
    obtain ⟨c2, i2, e2⟩ := integrableOn_and_integral_cell_mul_perSum (g := g2) hd1 (he_pd_cont 0)
      (hφs_cont.mul (Complex.continuous_ofReal.comp (EulerErrorSub.continuous_movingTrainV tr hs0 0)))
      (fun y => by dsimp only [g2]; rw [hφs_per y, hV_per 0 y])
      hCe1 (mul_nonneg hCφ0 (mul_nonneg (Real.rpow_nonneg ha0.le _) hV₀0)) (he_pd_bd 0)
      (fun y => by
        dsimp only [g2]; rw [norm_mul]
        exact mul_le_mul (hφs_bd y) (hV_bd 0 y) (norm_nonneg _) hCφ0)
    obtain ⟨c3, i3, e3⟩ := integrableOn_and_integral_cell_mul_perSum (g := g3) hd1 (he_pd_cont 1)
      (hφs_cont.mul (Complex.continuous_ofReal.comp (EulerErrorSub.continuous_movingTrainV tr hs0 1)))
      (fun y => by dsimp only [g3]; rw [hφs_per y, hV_per 1 y])
      hCe1 (mul_nonneg hCφ0 (mul_nonneg (Real.rpow_nonneg ha0.le _) hV₀0)) (he_pd_bd 1)
      (fun y => by
        dsimp only [g3]; rw [norm_mul]
        exact mul_le_mul (hφs_bd y) (hV_bd 1 y) (norm_nonneg _) hCφ0)
    obtain ⟨c4, i4, e4⟩ := integrableOn_and_integral_cell_mul_perSum (g := g4) hd1 he_inf.continuous
      (continuous_const.mul hφs_cont)
      (fun y => by dsimp only [g4]; rw [hφs_per y])
      hCe0 (mul_nonneg (norm_nonneg ((movBeta0 P ν s : ℝ) : ℂ)) hCφ0) he_val_bd
      (fun y => by dsimp only [g4]; rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hφs_bd y) (norm_nonneg _))
    have c23 : IntegrableOn
        (fun y => g2 y * perSum d (pdCx 0 e) y + g3 y * perSum d (pdCx 1 e) y)
        (B0579.cell d) volume := c2.add c3
    have c123 : IntegrableOn
        (fun y => g1 y * perSum d (movD e) y +
          (g2 y * perSum d (pdCx 0 e) y + g3 y * perSum d (pdCx 1 e) y))
        (B0579.cell d) volume := c1.add c23
    have i23 : Integrable (fun y => g2 y * pdCx 0 e y + g3 y * pdCx 1 e y) volume := i2.add i3
    have i123 : Integrable
        (fun y => g1 y * movD e y + (g2 y * pdCx 0 e y + g3 y * pdCx 1 e y)) volume :=
      i1.add i23
    rw [integral_add c123 c4, integral_add c1 c23, integral_add c2 c3,
      e1, e2, e3, e4, ← integral_add i2 i3, ← integral_add i1 i23, ← integral_add i123 i4]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    dsimp only [g1, g2, g3, g4]
    ring
  exact ⟨hFE_eq, hFR_eq⟩

private lemma continuousOn_rawFE_and_rawFR (P : PlanarData) {B ν : ℝ}
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (t₁ t₂ τ : ℝ)
    (φ : ℝ → B0579.Plane → ℝ) (e : ℝ × ℝ → ℂ)
    (hν : 0 < ν) (ht₁ : 0 ≤ t₁) (ht₂ : 0 ≤ t₂) (hBe : movingZ ν t₂ - movingZ ν t₁ = B)
    (hτ : τ ∈ Icc (0 : ℝ) B) (ht_mem : ageAt ν t₁ τ ∈ Icc t₁ t₂)
    (hage_Icc : ∀ σ ∈ Icc (0 : ℝ) τ, ageAt ν t₁ σ ∈ Icc t₁ (ageAt ν t₁ τ))
    (sb : SeedBounds e) (pb : PhiTrainBounds ν t₁ (ageAt ν t₁ τ) tr φ) :
    ContinuousOn (rawFE P ν t₁ (ageAt ν t₁ τ) φ e) (Icc (0 : ℝ) τ) ∧
      ContinuousOn (rawFR P ν tr t₁ (ageAt ν t₁ τ) φ e) (Icc (0 : ℝ) τ) := by
  rcases sb with ⟨he_inf, he_cd2, _he_diff, Ce0, Ce1, _Ce2, CD, hCe0, _hCe1, _hCe2, _hCD0,
    he_val_bd, he_pd_cont, he_pd_bd, _he_pd2_bd, hcont_movD, hCD, _hdilationDrift_bd⟩
  rcases pb with ⟨hφsp, hφ_cd, _hφpde, Cφ, V₀, _V₁, hCφ0, _hV₀0, _hV₁0, hφ_bd, hv_bd, _hv_pd_bd⟩
  set t := ageAt ν t₁ τ
  have ht0 : 0 ≤ t := ht₁.trans ht_mem.1
  set A := clockA ν t
  have hA1 : 1 ≤ A := one_le_clockA hν.le ht0
  have hA0 : 0 < A := lt_of_lt_of_le zero_lt_one hA1
  unfold rawFE rawIFun rawFR
  set IFun : ℝ → ℂ := fun r =>
    ∫ x : ℝ × ℝ, ((φ r x : ℝ) : ℂ) * UnforcedLeray.Gaussian.heatDilation (clockA ν r) e x
  set FE : ℝ → ℂ := fun σ =>
    (((clockN P ν (ageAt ν t₁ σ) t)⁻¹ : ℝ) : ℂ) * IFun (ageAt ν t₁ σ)
  set FR : ℝ → ℂ := fun σ =>
    let s := ageAt ν t₁ σ
    let a := clockA ν s
    (((clockN P ν s t)⁻¹ * a⁻¹ : ℝ) : ℂ) *
      ∫ y : ℝ × ℝ, ((φ s (Real.sqrt a * y.1, Real.sqrt a * y.2) : ℝ) : ℂ) *
        (-(clockTheta ν s : ℂ)⁻¹ * movD e y +
          (((movingTrainV tr s y 0 : ℝ) : ℂ) * pdCx 0 e y +
            ((movingTrainV tr s y 1 : ℝ) : ℂ) * pdCx 1 e y) +
          ((movBeta0 P ν s : ℝ) : ℂ) * e y)
  -- Step 2: Continuity of `FE` and `FR` on `Icc 0 τ` via dominated convergence.
  have hage_cont : ContinuousOn (ageAt ν t₁) (Icc (0 : ℝ) τ) := by
    refine ContinuousOn.div (continuousOn_const.add continuousOn_id)
      (continuousOn_const.sub (continuousOn_const.mul (continuousOn_const.add continuousOn_id)))
      fun σ hσ => ?_
    have hlt := nu_mul_movingZ_add_lt_one hν ht₂ hBe (hσ.2.trans hτ.2)
    linarith
  have hNinv_cont : ContinuousOn (fun σ => (((clockN P ν (ageAt ν t₁ σ) t)⁻¹ : ℝ) : ℂ))
      (Icc (0 : ℝ) τ) := by
    have hswap_eq : EqOn (fun σ => (((clockN P ν (ageAt ν t₁ σ) t)⁻¹ : ℝ) : ℂ))
        (fun σ => ((clockN P ν t (ageAt ν t₁ σ) : ℝ) : ℂ)) (Icc (0 : ℝ) τ) := by
      intro σ hσ
      dsimp only
      rw [clockN_inv_eq_swap P hν (ht₁.trans (hage_Icc σ hσ).1) ht0]
    refine ContinuousOn.congr ?_ hswap_eq
    have hθ_cont : ContinuousOn (fun σ => clockTheta ν (ageAt ν t₁ σ)) (Icc (0 : ℝ) τ) := by
      unfold clockTheta clockA
      refine ContinuousOn.inv₀
        (continuousOn_const.mul (continuousOn_const.add (continuousOn_const.mul hage_cont)))
        fun σ hσ => ?_
      have hs0 : 0 ≤ ageAt ν t₁ σ := ht₁.trans (hage_Icc σ hσ).1
      positivity
    refine Complex.continuous_ofReal.comp_continuousOn ?_
    unfold clockN
    refine (Real.continuous_exp.comp_continuousOn
      (continuousOn_const.mul (continuousOn_const.sub hθ_cont))).mul ?_
    refine ContinuousOn.rpow_const (continuousOn_const.div hθ_cont fun σ hσ =>
      (theta_pos hν (ht₁.trans (hage_Icc σ hσ).1)).ne') fun σ hσ => Or.inl ?_
    exact (div_pos (theta_pos hν ht0) (theta_pos hν (ht₁.trans (hage_Icc σ hσ).1))).ne'
  have hIFun_cont : ContinuousOn IFun (Icc t₁ t) := by
    refine MeasureTheory.continuousOn_of_dominated
      (bound := fun x : ℝ × ℝ => (Cφ * Ce0) * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (8 * A)))
      ?meas ?bd ?bint ?cont
    case meas =>
      intro r hr
      have ha_cd := UnforcedLeray.Gaussian.contDiff_heatDilation he_cd2 (clockA ν r)
      exact ((Complex.continuous_ofReal.comp (hφ_cd r hr).continuous).mul
        ha_cd.continuous).aestronglyMeasurable
    case bd =>
      intro r hr
      have hr0 : 0 ≤ r := ht₁.trans hr.1
      have ha1 : 1 ≤ clockA ν r := one_le_clockA hν.le hr0
      have ha0 : 0 < clockA ν r := lt_of_lt_of_le zero_lt_one ha1
      have haA : clockA ν r ≤ A := by
        dsimp only [A]; unfold clockA
        linarith [mul_le_mul_of_nonneg_left hr.2 hν.le]
      refine Eventually.of_forall fun x => ?_
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, UnforcedLeray.Gaussian.heatDilation_apply,
        norm_smul, Real.norm_of_nonneg (sq_nonneg _)]
      have hφx : |φ r x| ≤ Cφ := by
        have h := hφ_bd r hr x
        linarith [abs_nonneg (B0579.pd 0 (φ r) x), abs_nonneg (B0579.pd 1 (φ r) x),
          abs_nonneg (UnforcedLeray.Short.IIb.lapP (φ r) x)]
      have hainv : (clockA ν r)⁻¹ ^ 2 ≤ 1 :=
        pow_le_one₀ (inv_nonneg.mpr ha0.le) (inv_le_one_of_one_le₀ ha1)
      have hex : ‖e ((Real.sqrt (clockA ν r))⁻¹ • x)‖ ≤
          Ce0 * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (8 * A)) :=
        (he_val_bd _).trans
          (mul_le_mul_of_nonneg_left (exp_dilated_le ha0 haA x) hCe0)
      have hhd : (clockA ν r)⁻¹ ^ 2 * ‖e ((Real.sqrt (clockA ν r))⁻¹ • x)‖ ≤
          Ce0 * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (8 * A)) := by
        calc (clockA ν r)⁻¹ ^ 2 * ‖e ((Real.sqrt (clockA ν r))⁻¹ • x)‖
            ≤ 1 * (Ce0 * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (8 * A))) :=
              mul_le_mul hainv hex (norm_nonneg _) zero_le_one
          _ = Ce0 * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (8 * A)) := one_mul _
      calc |φ r x| * ((clockA ν r)⁻¹ ^ 2 * ‖e ((Real.sqrt (clockA ν r))⁻¹ • x)‖)
          ≤ Cφ * (Ce0 * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (8 * A))) :=
            mul_le_mul hφx hhd (by positivity) hCφ0
        _ = (Cφ * Ce0) * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (8 * A)) := by ring
    case bint =>
      exact (integrable_gauss_plane hA0).const_mul (Cφ * Ce0)
    case cont =>
      refine Eventually.of_forall fun x => ?_
      have hφ_c : ContinuousOn (fun r => ((φ r x : ℝ) : ℂ)) (Icc t₁ t) :=
        Complex.continuous_ofReal.comp_continuousOn
          (hφsp.smooth.continuousOn.comp (continuousOn_id.prodMk continuousOn_const)
            fun r hr => ⟨hr, mem_univ x⟩)
      have hA_c : ContinuousOn (clockA ν) (Icc t₁ t) := by unfold clockA; fun_prop
      have hhd_c : ContinuousOn (fun r => UnforcedLeray.Gaussian.heatDilation (clockA ν r) e x)
          (Icc t₁ t) := by
        simp only [UnforcedLeray.Gaussian.heatDilation_apply, Complex.real_smul]
        refine ContinuousOn.mul ?_ ?_
        · refine Complex.continuous_ofReal.comp_continuousOn ?_
          exact (ContinuousOn.inv₀ hA_c fun r hr =>
            (lt_of_lt_of_le zero_lt_one (one_le_clockA hν.le (ht₁.trans hr.1))).ne').pow 2
        · refine he_inf.continuous.comp_continuousOn ?_
          exact (ContinuousOn.inv₀ (hA_c.sqrt) fun r hr =>
            (Real.sqrt_pos.2 (lt_of_lt_of_le zero_lt_one
              (one_le_clockA hν.le (ht₁.trans hr.1)))).ne').smul continuousOn_const
      exact hφ_c.mul hhd_c
  have hFE_cont : ContinuousOn FE (Icc (0 : ℝ) τ) :=
    hNinv_cont.mul (hIFun_cont.comp hage_cont hage_Icc)
  -- Continuity of `FR` on `Icc 0 τ`
  have hβ_cont : Continuous (movBeta0 P ν) := by
    have h : movBeta0 P ν = fun r => P.eigenvalue.re + P.kappa.re * (ν * clockA ν r) := by
      funext r; unfold movBeta0 clockTheta; rw [div_inv_eq_mul]
    rw [h]; unfold clockA; fun_prop
  obtain ⟨B_raw, hB_raw⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hβ_cont.continuousOn (s := Icc t₁ t))
  set B₀ : ℝ := max B_raw 0
  have hB₀0 : 0 ≤ B₀ := le_max_right _ _
  have hFR_cont : ContinuousOn FR (Icc (0 : ℝ) τ) := by
    set KR : ℝ := Cφ * (ν * A * CD + 2 * (A ^ (3 / 2 : ℝ) * V₀) * Ce1 + B₀ * Ce0)
    have hAinv_cont : ContinuousOn (fun σ => (((clockA ν (ageAt ν t₁ σ))⁻¹ : ℝ) : ℂ))
        (Icc (0 : ℝ) τ) := by
      refine Complex.continuous_ofReal.comp_continuousOn ?_
      refine ContinuousOn.inv₀ ?_ fun σ hσ =>
        (lt_of_lt_of_le zero_lt_one (one_le_clockA hν.le (ht₁.trans (hage_Icc σ hσ).1))).ne'
      unfold clockA
      exact continuousOn_const.add (continuousOn_const.mul hage_cont)
    have hint_cont : ContinuousOn (fun σ =>
        let s := ageAt ν t₁ σ
        let a := clockA ν s
        ∫ y : ℝ × ℝ, ((φ s (Real.sqrt a * y.1, Real.sqrt a * y.2) : ℝ) : ℂ) *
          (-(clockTheta ν s : ℂ)⁻¹ * movD e y +
            (((movingTrainV tr s y 0 : ℝ) : ℂ) * pdCx 0 e y +
              ((movingTrainV tr s y 1 : ℝ) : ℂ) * pdCx 1 e y) +
            ((movBeta0 P ν s : ℝ) : ℂ) * e y)) (Icc (0 : ℝ) τ) := by
      refine MeasureTheory.continuousOn_of_dominated
        (bound := fun y : ℝ × ℝ => KR * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8))
        ?meas ?bd ?bint ?cont
      case meas =>
        intro σ hσ
        set s := ageAt ν t₁ σ
        set a := clockA ν s
        have hs : s ∈ Icc t₁ t := hage_Icc σ hσ
        have hs0 : 0 ≤ s := ht₁.trans hs.1
        have hφs_c : Continuous (fun y : ℝ × ℝ =>
            ((φ s (Real.sqrt a * y.1, Real.sqrt a * y.2) : ℝ) : ℂ)) :=
          Complex.continuous_ofReal.comp
            ((hφ_cd s hs).continuous.comp ((continuous_const.mul continuous_fst).prodMk
              (continuous_const.mul continuous_snd)))
        have hV0_c := Complex.continuous_ofReal.comp (EulerErrorSub.continuous_movingTrainV tr hs0 0)
        have hV1_c := Complex.continuous_ofReal.comp (EulerErrorSub.continuous_movingTrainV tr hs0 1)
        exact (hφs_c.mul (((continuous_const.mul hcont_movD).add
          ((hV0_c.mul (he_pd_cont 0)).add (hV1_c.mul (he_pd_cont 1)))).add
          (continuous_const.mul he_inf.continuous))).aestronglyMeasurable
      case bd =>
        intro σ hσ
        set s := ageAt ν t₁ σ
        set a := clockA ν s
        have hs : s ∈ Icc t₁ t := hage_Icc σ hσ
        have hs0 : 0 ≤ s := ht₁.trans hs.1
        have ha1 : 1 ≤ a := one_le_clockA hν.le hs0
        have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha1
        have haA : a ≤ A := by
          dsimp only [a, A]; unfold clockA
          linarith [mul_le_mul_of_nonneg_left hs.2 hν.le]
        have hθ_inv : ‖-(clockTheta ν s : ℂ)⁻¹‖ ≤ ν * A := by
          rw [norm_neg, norm_inv, Complex.norm_of_nonneg (theta_pos hν hs0).le]
          unfold clockTheta
          rw [inv_inv]
          exact mul_le_mul_of_nonneg_left haA hν.le
        have hApow : a ^ (3 / 2 : ℝ) ≤ A ^ (3 / 2 : ℝ) :=
          Real.rpow_le_rpow ha0.le haA (by norm_num)
        have hβs : |movBeta0 P ν s| ≤ B₀ := (hB_raw s hs).trans (le_max_left _ _)
        refine Eventually.of_forall fun y => ?_
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        have hφy : |φ s (Real.sqrt a * y.1, Real.sqrt a * y.2)| ≤ Cφ := by
          have h := hφ_bd s hs (Real.sqrt a * y.1, Real.sqrt a * y.2)
          linarith [abs_nonneg (B0579.pd 0 (φ s) (Real.sqrt a * y.1, Real.sqrt a * y.2)),
            abs_nonneg (B0579.pd 1 (φ s) (Real.sqrt a * y.1, Real.sqrt a * y.2)),
            abs_nonneg (UnforcedLeray.Short.IIb.lapP (φ s) (Real.sqrt a * y.1, Real.sqrt a * y.2))]
        have hVy : ∀ k : Fin 2, |movingTrainV tr s y k| ≤ A ^ (3 / 2 : ℝ) * V₀ := by
          intro k
          unfold movingTrainV
          rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg ha0.le _)]
          exact mul_le_mul hApow (hv_bd s hs _ k) (abs_nonneg _) (by positivity)
        have hb1 : ‖-(clockTheta ν s : ℂ)⁻¹ * movD e y‖ ≤
            (ν * A * CD) * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8) := by
          rw [norm_mul]
          calc ‖-(clockTheta ν s : ℂ)⁻¹‖ * ‖movD e y‖
              ≤ (ν * A) * (CD * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8)) :=
                mul_le_mul hθ_inv (hCD y) (norm_nonneg _) (by positivity)
            _ = (ν * A * CD) * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8) := by ring
        have hb2 : ∀ k : Fin 2, ‖((movingTrainV tr s y k : ℝ) : ℂ) * pdCx k e y‖ ≤
            (A ^ (3 / 2 : ℝ) * V₀ * Ce1) * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8) := by
          intro k
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          calc |movingTrainV tr s y k| * ‖pdCx k e y‖
              ≤ (A ^ (3 / 2 : ℝ) * V₀) * (Ce1 * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8)) :=
                mul_le_mul (hVy k) (he_pd_bd k y) (norm_nonneg _) (by positivity)
            _ = (A ^ (3 / 2 : ℝ) * V₀ * Ce1) * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8) := by ring
        have hb3 : ‖((movBeta0 P ν s : ℝ) : ℂ) * e y‖ ≤
            (B₀ * Ce0) * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8) := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          calc |movBeta0 P ν s| * ‖e y‖
              ≤ B₀ * (Ce0 * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8)) :=
                mul_le_mul hβs (he_val_bd y) (norm_nonneg _) hB₀0
            _ = (B₀ * Ce0) * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8) := by ring
        have hsum_bd : ‖-(clockTheta ν s : ℂ)⁻¹ * movD e y +
            (((movingTrainV tr s y 0 : ℝ) : ℂ) * pdCx 0 e y +
              ((movingTrainV tr s y 1 : ℝ) : ℂ) * pdCx 1 e y) +
            ((movBeta0 P ν s : ℝ) : ℂ) * e y‖ ≤
            (ν * A * CD + 2 * (A ^ (3 / 2 : ℝ) * V₀) * Ce1 + B₀ * Ce0) *
              Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8) := by
          calc _ ≤ ‖-(clockTheta ν s : ℂ)⁻¹ * movD e y‖ +
                (‖((movingTrainV tr s y 0 : ℝ) : ℂ) * pdCx 0 e y‖ +
                  ‖((movingTrainV tr s y 1 : ℝ) : ℂ) * pdCx 1 e y‖) +
                ‖((movBeta0 P ν s : ℝ) : ℂ) * e y‖ :=
              (norm_add_le _ _).trans
                (add_le_add ((norm_add_le _ _).trans (add_le_add le_rfl (norm_add_le _ _))) le_rfl)
            _ ≤ (ν * A * CD) * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8) +
                ((A ^ (3 / 2 : ℝ) * V₀ * Ce1) * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8) +
                  (A ^ (3 / 2 : ℝ) * V₀ * Ce1) * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8)) +
                (B₀ * Ce0) * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8) :=
              add_le_add (add_le_add hb1 (add_le_add (hb2 0) (hb2 1))) hb3
            _ = _ := by ring
        calc |φ s (Real.sqrt a * y.1, Real.sqrt a * y.2)| * _
            ≤ Cφ * ((ν * A * CD + 2 * (A ^ (3 / 2 : ℝ) * V₀) * Ce1 + B₀ * Ce0) *
                Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8)) :=
              mul_le_mul hφy hsum_bd (norm_nonneg _) hCφ0
          _ = KR * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8) := by ring
      case bint =>
        simpa [mul_one] using (integrable_gauss_plane one_pos).const_mul KR
      case cont =>
        refine Eventually.of_forall fun y => ?_
        have hA_sig : ContinuousOn (fun σ => clockA ν (ageAt ν t₁ σ)) (Icc (0 : ℝ) τ) := by
          unfold clockA; exact continuousOn_const.add (continuousOn_const.mul hage_cont)
        have hpt_sig : ContinuousOn (fun σ =>
            (ageAt ν t₁ σ, (Real.sqrt (clockA ν (ageAt ν t₁ σ)) * y.1,
              Real.sqrt (clockA ν (ageAt ν t₁ σ)) * y.2))) (Icc (0 : ℝ) τ) :=
          hage_cont.prodMk ((hA_sig.sqrt.mul continuousOn_const).prodMk
            (hA_sig.sqrt.mul continuousOn_const))
        have hφ_sig : ContinuousOn (fun σ =>
            ((φ (ageAt ν t₁ σ) (Real.sqrt (clockA ν (ageAt ν t₁ σ)) * y.1,
              Real.sqrt (clockA ν (ageAt ν t₁ σ)) * y.2) : ℝ) : ℂ)) (Icc (0 : ℝ) τ) :=
          Complex.continuous_ofReal.comp_continuousOn
            (hφsp.smooth.continuousOn.comp hpt_sig fun σ hσ => ⟨hage_Icc σ hσ, mem_univ _⟩)
        have hθinv_sig : ContinuousOn (fun σ => -(clockTheta ν (ageAt ν t₁ σ) : ℂ)⁻¹)
            (Icc (0 : ℝ) τ) := by
          have heq : EqOn (fun σ => -(clockTheta ν (ageAt ν t₁ σ) : ℂ)⁻¹)
              (fun σ => -(((ν * clockA ν (ageAt ν t₁ σ) : ℝ) : ℂ))) (Icc (0 : ℝ) τ) := by
            intro σ _
            unfold clockTheta
            push_cast
            rw [inv_inv]
          exact (Complex.continuous_ofReal.comp_continuousOn
            (continuousOn_const.mul hA_sig)).neg.congr heq
        have hV_sig : ∀ k : Fin 2, ContinuousOn (fun σ =>
            ((movingTrainV tr (ageAt ν t₁ σ) y k : ℝ) : ℂ)) (Icc (0 : ℝ) τ) := by
          intro k
          unfold movingTrainV
          refine Complex.continuous_ofReal.comp_continuousOn ?_
          refine (ContinuousOn.rpow_const hA_sig fun σ hσ => Or.inl
            (lt_of_lt_of_le zero_lt_one
              (one_le_clockA hν.le (ht₁.trans (hage_Icc σ hσ).1))).ne').mul ?_
          exact ((PiLp.continuous_apply 2 _ k).comp_continuousOn
            tr.isTrain.smooth_v.continuousOn).comp hpt_sig
            fun σ hσ => ⟨mem_Ici.2 (ht₁.trans (hage_Icc σ hσ).1), mem_univ _⟩
        have hβ_sig : ContinuousOn (fun σ => ((movBeta0 P ν (ageAt ν t₁ σ) : ℝ) : ℂ))
            (Icc (0 : ℝ) τ) :=
          Complex.continuous_ofReal.comp_continuousOn (hβ_cont.comp_continuousOn hage_cont)
        exact hφ_sig.mul (((hθinv_sig.mul continuousOn_const).add
          (((hV_sig 0).mul continuousOn_const).add ((hV_sig 1).mul continuousOn_const))).add
          (hβ_sig.mul continuousOn_const))
    have hmul := (hNinv_cont.mul hAinv_cont).mul hint_cont
    refine hmul.congr fun σ _ => ?_
    simp only [FR, Pi.mul_apply, Complex.ofReal_mul]
  exact ⟨hFE_cont, hFR_cont⟩

private lemma hasDerivAt_rawIFun {ν : ℝ}
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (t₁ t : ℝ)
    (φ : ℝ → B0579.Plane → ℝ) (e : ℝ × ℝ → ℂ) (s : ℝ)
    (hν : 0 < ν) (ht₁ : 0 ≤ t₁) (ht0 : 0 ≤ t) (hs_Ioo : s ∈ Ioo t₁ t)
    (sb : SeedBounds e) (pb : PhiTrainBounds ν t₁ t tr φ) :
    HasDerivAt (rawIFun ν φ e) (∫ x : ℝ × ℝ, rawFInt' ν tr φ e s x) s := by
      rcases sb with ⟨he_inf, he_cd2, he_diff, Ce0, Ce1, _Ce2, _CD, hCe0, _hCe1, _hCe2, _hCD0,
        he_val_bd, _he_pd_cont, _he_pd_bd, _he_pd2_bd, _hcont_movD, _hCD, hdilationDrift_bd⟩
      rcases pb with ⟨_hφsp, hφ_cd, hφpde, Cφ, V₀, _V₁, hCφ0, hV₀0, _hV₁0, hφ_bd, hv_bd, _hv_pd_bd⟩
      have hs_Icc : s ∈ Icc t₁ t := Ioo_subset_Icc_self hs_Ioo
      have hs0 : 0 ≤ s := ht₁.trans hs_Icc.1
      set a := clockA ν s
      have ha1 : 1 ≤ a := one_le_clockA hν.le hs0
      have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha1
      set A := clockA ν t
      have hA1 : 1 ≤ A := one_le_clockA hν.le ht0
      have hA0 : 0 < A := lt_of_lt_of_le zero_lt_one hA1
      have haA : a ≤ A := by
        dsimp only [a, A]; unfold clockA
        linarith [mul_le_mul_of_nonneg_left hs_Icc.2 hν.le]
      unfold rawIFun rawFInt' rawDPhi rawDHeat
      set dφ : ℝ → B0579.Plane → ℝ := fun r x =>
        -(ν * UnforcedLeray.Short.IIb.lapP (φ r) x +
          (tr.v r x 0 * B0579.pd 0 (φ r) x + tr.v r x 1 * B0579.pd 1 (φ r) x))
      set dHeat : ℝ → ℝ × ℝ → ℂ := fun r x =>
        ν • (-(clockA ν r)⁻¹ •
          UnforcedLeray.Gaussian.heatDilation (clockA ν r) (UnforcedLeray.Gaussian.dilationDrift e) x)
      set F_int' : ℝ → ℝ × ℝ → ℂ := fun r x =>
        ((dφ r x : ℝ) : ℂ) * UnforcedLeray.Gaussian.heatDilation (clockA ν r) e x +
          ((φ r x : ℝ) : ℂ) * dHeat r x
      set KD : ℝ := ((ν + 2 * V₀) * Cφ * Ce0 + Cφ * ν * (2 * Ce0 + Ce1))
      refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (s := Ioo t₁ t)
        (F := fun r x => ((φ r x : ℝ) : ℂ) * UnforcedLeray.Gaussian.heatDilation (clockA ν r) e x)
        (F' := F_int')
        (bound := fun x : ℝ × ℝ => KD * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (8 * A)))
        (Ioo_mem_nhds hs_Ioo.1 hs_Ioo.2) ?meas ?fint ?dmeas ?dbd ?bint ?diff).2
      case meas =>
        filter_upwards [Ioo_mem_nhds hs_Ioo.1 hs_Ioo.2] with r hr
        have ha_cd := UnforcedLeray.Gaussian.contDiff_heatDilation he_cd2 (clockA ν r)
        exact ((Complex.continuous_ofReal.comp (hφ_cd r (Ioo_subset_Icc_self hr)).continuous).mul
          ha_cd.continuous).aestronglyMeasurable
      case fint =>
        refine integrable_of_gauss_plane hA0 (K := Cφ * Ce0)
          ((Complex.continuous_ofReal.comp (hφ_cd s hs_Icc).continuous).mul
            (UnforcedLeray.Gaussian.contDiff_heatDilation he_cd2 a).continuous).aestronglyMeasurable
          fun x => ?_
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          UnforcedLeray.Gaussian.heatDilation_apply, norm_smul, Real.norm_of_nonneg (sq_nonneg _)]
        have hφx : |φ s x| ≤ Cφ := by
          have h := hφ_bd s hs_Icc x
          linarith [abs_nonneg (B0579.pd 0 (φ s) x), abs_nonneg (B0579.pd 1 (φ s) x),
            abs_nonneg (UnforcedLeray.Short.IIb.lapP (φ s) x)]
        have hainv : a⁻¹ ^ 2 ≤ 1 :=
          pow_le_one₀ (inv_nonneg.mpr ha0.le) (inv_le_one_of_one_le₀ ha1)
        have hex : ‖e ((Real.sqrt a)⁻¹ • x)‖ ≤ Ce0 * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (8 * A)) :=
          (he_val_bd _).trans (mul_le_mul_of_nonneg_left (exp_dilated_le ha0 haA x) hCe0)
        calc |φ s x| * (a⁻¹ ^ 2 * ‖e ((Real.sqrt a)⁻¹ • x)‖)
            ≤ Cφ * (1 * (Ce0 * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (8 * A)))) :=
              mul_le_mul hφx (mul_le_mul hainv hex (norm_nonneg _) zero_le_one) (by positivity) hCφ0
          _ = (Cφ * Ce0) * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (8 * A)) := by ring
      case dmeas =>
        have hφs := hφ_cd s hs_Icc
        have hpd_c : ∀ k : Fin 2, Continuous (B0579.pd k (φ s)) := fun k => by
          unfold B0579.pd
          exact ((hφs.fderiv_right (m := (1 : ℕ)) (by simp)).clm_apply contDiff_const).continuous
        have hpd2_c : ∀ k : Fin 2, Continuous (B0579.pd k (B0579.pd k (φ s))) := fun k => by
          have h1 : ContDiff ℝ (2 : ℕ) (B0579.pd k (φ s)) := by
            unfold B0579.pd
            exact (hφs.fderiv_right (m := (2 : ℕ)) (by simp)).clm_apply contDiff_const
          unfold B0579.pd
          exact ((h1.fderiv_right (m := (1 : ℕ)) (by norm_num)).clm_apply contDiff_const).continuous
        have hlap_c : Continuous (UnforcedLeray.Short.IIb.lapP (φ s)) :=
          (hpd2_c 0).add (hpd2_c 1)
        have hv_c : ∀ k : Fin 2, Continuous (fun x => tr.v s x k) := fun k =>
          (PiLp.continuous_apply 2 _ k).comp (UnforcedLeray.B0238.contDiff_Vc tr hs0).continuous
        have hdφ_c : Continuous (dφ s) :=
          ((continuous_const.mul hlap_c).add (((hv_c 0).mul (hpd_c 0)).add
            ((hv_c 1).mul (hpd_c 1)))).neg
        have hdrift_c : Continuous (UnforcedLeray.Gaussian.dilationDrift e) := by
          unfold UnforcedLeray.Gaussian.dilationDrift
          have hf_c : Continuous (fun y : ℝ × ℝ => fderiv ℝ e y y) :=
            (he_inf.fderiv_right (m := (1 : ℕ)) (by simp)).continuous.clm_apply continuous_id
          exact (he_inf.continuous.const_smul _).add (hf_c.const_smul _)
        have hdHeat_c : Continuous (dHeat s) := by
          dsimp only [dHeat, UnforcedLeray.Gaussian.heatDilation_apply]
          exact (continuous_const : Continuous fun _ : ℝ × ℝ => ν).smul
            ((continuous_const : Continuous fun _ : ℝ × ℝ => -(clockA ν s)⁻¹).smul
              ((continuous_const : Continuous fun _ : ℝ × ℝ => (clockA ν s)⁻¹ ^ 2).smul
                (hdrift_c.comp ((continuous_const : Continuous fun _ : ℝ × ℝ =>
                  (Real.sqrt (clockA ν s))⁻¹).smul continuous_id))))
        exact (((Complex.continuous_ofReal.comp hdφ_c).mul
          (UnforcedLeray.Gaussian.contDiff_heatDilation he_cd2 a).continuous).add
          ((Complex.continuous_ofReal.comp hφs.continuous).mul hdHeat_c)).aestronglyMeasurable
      case dbd =>
        refine Eventually.of_forall fun x r hr => ?_
        have hrI : r ∈ Icc t₁ t := Ioo_subset_Icc_self hr
        have hr0 : 0 ≤ r := ht₁.trans hrI.1
        have har1 : 1 ≤ clockA ν r := one_le_clockA hν.le hr0
        have har0 : 0 < clockA ν r := lt_of_lt_of_le zero_lt_one har1
        have harA : clockA ν r ≤ A := by
          dsimp only [A]; unfold clockA
          linarith [mul_le_mul_of_nonneg_left hrI.2 hν.le]
        have hφ_all := hφ_bd r hrI x
        have hφx : |φ r x| ≤ Cφ := by
          linarith [abs_nonneg (B0579.pd 0 (φ r) x), abs_nonneg (B0579.pd 1 (φ r) x),
            abs_nonneg (UnforcedLeray.Short.IIb.lapP (φ r) x)]
        have hdφx : |dφ r x| ≤ (ν + 2 * V₀) * Cφ := by
          dsimp only [dφ]
          rw [abs_neg]
          have hv0 := hv_bd r hrI x 0
          have hv1 := hv_bd r hrI x 1
          have hlapx : |UnforcedLeray.Short.IIb.lapP (φ r) x| ≤ Cφ := by
            linarith [abs_nonneg (φ r x), abs_nonneg (B0579.pd 0 (φ r) x),
              abs_nonneg (B0579.pd 1 (φ r) x)]
          have hpd0x : |B0579.pd 0 (φ r) x| ≤ Cφ := by
            linarith [abs_nonneg (φ r x), abs_nonneg (B0579.pd 1 (φ r) x),
              abs_nonneg (UnforcedLeray.Short.IIb.lapP (φ r) x)]
          have hpd1x : |B0579.pd 1 (φ r) x| ≤ Cφ := by
            linarith [abs_nonneg (φ r x), abs_nonneg (B0579.pd 0 (φ r) x),
              abs_nonneg (UnforcedLeray.Short.IIb.lapP (φ r) x)]
          have e1 : |ν * UnforcedLeray.Short.IIb.lapP (φ r) x| ≤ ν * Cφ := by
            rw [abs_mul, abs_of_nonneg hν.le]
            exact mul_le_mul_of_nonneg_left hlapx hν.le
          have e2 : |tr.v r x 0 * B0579.pd 0 (φ r) x| ≤ V₀ * Cφ := by
            rw [abs_mul]; exact mul_le_mul hv0 hpd0x (abs_nonneg _) hV₀0
          have e3 : |tr.v r x 1 * B0579.pd 1 (φ r) x| ≤ V₀ * Cφ := by
            rw [abs_mul]; exact mul_le_mul hv1 hpd1x (abs_nonneg _) hV₀0
          have t1 := abs_add_le (ν * UnforcedLeray.Short.IIb.lapP (φ r) x)
            (tr.v r x 0 * B0579.pd 0 (φ r) x + tr.v r x 1 * B0579.pd 1 (φ r) x)
          have t2 := abs_add_le (tr.v r x 0 * B0579.pd 0 (φ r) x) (tr.v r x 1 * B0579.pd 1 (φ r) x)
          linarith
        have har_inv : (clockA ν r)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ har1
        have har_inv2 : (clockA ν r)⁻¹ ^ 2 ≤ 1 := pow_le_one₀ (inv_nonneg.mpr har0.le) har_inv
        have hhd_x : ‖UnforcedLeray.Gaussian.heatDilation (clockA ν r) e x‖ ≤
            Ce0 * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (8 * A)) := by
          rw [UnforcedLeray.Gaussian.heatDilation_apply, norm_smul,
            Real.norm_of_nonneg (sq_nonneg _)]
          calc (clockA ν r)⁻¹ ^ 2 * ‖e ((Real.sqrt (clockA ν r))⁻¹ • x)‖
              ≤ 1 * (Ce0 * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (8 * A))) :=
                mul_le_mul har_inv2 ((he_val_bd _).trans
                  (mul_le_mul_of_nonneg_left (exp_dilated_le har0 harA x) hCe0))
                  (norm_nonneg _) zero_le_one
            _ = Ce0 * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (8 * A)) := one_mul _
        have hdHeat_x : ‖dHeat r x‖ ≤
            ν * (2 * Ce0 + Ce1) * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (8 * A)) := by
          dsimp only [dHeat]
          rw [norm_smul, Real.norm_of_nonneg hν.le, norm_smul, Real.norm_eq_abs, abs_neg,
            abs_of_pos (inv_pos.mpr har0), UnforcedLeray.Gaussian.heatDilation_apply, norm_smul,
            Real.norm_of_nonneg (sq_nonneg _)]
          have hdr : ‖UnforcedLeray.Gaussian.dilationDrift e ((Real.sqrt (clockA ν r))⁻¹ • x)‖ ≤
              (2 * Ce0 + Ce1) * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (8 * A)) :=
            (hdilationDrift_bd _).trans
              (mul_le_mul_of_nonneg_left (exp_dilated_le har0 harA x) (by positivity))
          have h1 : (clockA ν r)⁻¹ * ((clockA ν r)⁻¹ ^ 2 *
              ‖UnforcedLeray.Gaussian.dilationDrift e ((Real.sqrt (clockA ν r))⁻¹ • x)‖) ≤
              (2 * Ce0 + Ce1) * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (8 * A)) := by
            calc _ ≤ 1 * (1 * ((2 * Ce0 + Ce1) * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (8 * A)))) :=
                  mul_le_mul har_inv (mul_le_mul har_inv2 hdr (norm_nonneg _) zero_le_one)
                    (by positivity) zero_le_one
              _ = _ := by ring
          calc ν * _ ≤ ν * ((2 * Ce0 + Ce1) * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (8 * A))) :=
                mul_le_mul_of_nonneg_left h1 hν.le
            _ = _ := by ring
        dsimp only [F_int']
        calc ‖((dφ r x : ℝ) : ℂ) * UnforcedLeray.Gaussian.heatDilation (clockA ν r) e x +
                ((φ r x : ℝ) : ℂ) * dHeat r x‖
            ≤ ‖((dφ r x : ℝ) : ℂ) * UnforcedLeray.Gaussian.heatDilation (clockA ν r) e x‖ +
                ‖((φ r x : ℝ) : ℂ) * dHeat r x‖ := norm_add_le _ _
          _ ≤ ((ν + 2 * V₀) * Cφ) * (Ce0 * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (8 * A))) +
                Cφ * (ν * (2 * Ce0 + Ce1) * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (8 * A))) := by
              rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
                Real.norm_eq_abs]
              exact add_le_add (mul_le_mul hdφx hhd_x (norm_nonneg _) (by positivity))
                (mul_le_mul hφx hdHeat_x (norm_nonneg _) hCφ0)
          _ = KD * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (8 * A)) := by ring
      case bint =>
        exact (integrable_gauss_plane hA0).const_mul KD
      case diff =>
        refine Eventually.of_forall fun x r hr => ?_
        have hr0 : 0 ≤ r := ht₁.trans hr.1.le
        have har0 : 0 < clockA ν r := lt_of_lt_of_le zero_lt_one (one_le_clockA hν.le hr0)
        have hd1 : HasDerivAt (fun r' => ((φ r' x : ℝ) : ℂ)) ((dφ r x : ℝ) : ℂ) r :=
          Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt r (hφpde r hr x)
        have hd2 : HasDerivAt (fun r' => UnforcedLeray.Gaussian.heatDilation (clockA ν r') e x)
            (dHeat r x) r :=
          (UnforcedLeray.Gaussian.hasDerivAt_heatDilation_param he_diff har0 x).scomp r
            (FrameAmplSub.hasDerivAt_clockA ν r)
        exact hd1.mul hd2

private lemma eval_rawFInt'_rescaled {ν : ℝ}
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (t₁ t : ℝ)
    (φ : ℝ → B0579.Plane → ℝ) (e : ℝ × ℝ → ℂ) (s : ℝ)
    (hν : 0 < ν) (ht₁ : 0 ≤ t₁) (ht0 : 0 ≤ t) (hs_Icc : s ∈ Icc t₁ t)
    (sb : SeedBounds e) (pb : PhiTrainBounds ν t₁ t tr φ) :
    rawIFun ν φ e s = (((clockA ν s)⁻¹ : ℝ) : ℂ) *
        (∫ y : ℝ × ℝ, ((φ s (Real.sqrt (clockA ν s) * y.1,
          Real.sqrt (clockA ν s) * y.2) : ℝ) : ℂ) * e y) ∧
      ((clockA ν s ^ 2 : ℝ) : ℂ) * (∫ x : ℝ × ℝ, rawFInt' ν tr φ e s x) =
        (((clockA ν s)⁻¹ : ℝ) : ℂ) *
          ∫ y : ℝ × ℝ, ((φ s (Real.sqrt (clockA ν s) * y.1,
            Real.sqrt (clockA ν s) * y.2) : ℝ) : ℂ) *
            (-(clockTheta ν s : ℂ)⁻¹ * movD e y +
              (((movingTrainV tr s y 0 : ℝ) : ℂ) * pdCx 0 e y +
                ((movingTrainV tr s y 1 : ℝ) : ℂ) * pdCx 1 e y)) := by
    rcases sb with ⟨he_inf, he_cd2, he_diff, Ce0, Ce1, Ce2, _CD, hCe0, hCe1, hCe2, _hCD0,
      he_val_bd, _he_pd_cont, he_pd_bd, he_pd2_bd, _hcont_movD, _hCD, hdilationDrift_bd⟩
    rcases pb with ⟨_hφsp, hφ_cd, _hφpde, Cφ, V₀, V₁, hCφ0, hV₀0, hV₁0, hφ_bd, hv_bd, hv_pd_bd⟩
    have hs0 : 0 ≤ s := ht₁.trans hs_Icc.1
    set a := clockA ν s
    have ha1 : 1 ≤ a := one_le_clockA hν.le hs0
    have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha1
    set A := clockA ν t
    have hA1 : 1 ≤ A := one_le_clockA hν.le ht0
    have hA0 : 0 < A := lt_of_lt_of_le zero_lt_one hA1
    have haA : a ≤ A := by
      dsimp only [a, A]; unfold clockA
      linarith [mul_le_mul_of_nonneg_left hs_Icc.2 hν.le]
    unfold rawIFun rawFInt' rawDPhi rawDHeat
    set dφ : ℝ → B0579.Plane → ℝ := fun r x =>
      -(ν * UnforcedLeray.Short.IIb.lapP (φ r) x +
        (tr.v r x 0 * B0579.pd 0 (φ r) x + tr.v r x 1 * B0579.pd 1 (φ r) x))
    set dHeat : ℝ → ℝ × ℝ → ℂ := fun r x =>
      ν • (-(clockA ν r)⁻¹ •
        UnforcedLeray.Gaussian.heatDilation (clockA ν r) (UnforcedLeray.Gaussian.dilationDrift e) x)
    set IFun : ℝ → ℂ := fun r =>
      ∫ x : ℝ × ℝ, ((φ r x : ℝ) : ℂ) * UnforcedLeray.Gaussian.heatDilation (clockA ν r) e x
    set F_int' : ℝ → ℝ × ℝ → ℂ := fun r x =>
      ((dφ r x : ℝ) : ℂ) * UnforcedLeray.Gaussian.heatDilation (clockA ν r) e x +
        ((φ r x : ℝ) : ℂ) * dHeat r x
    -- Step 3b: Evaluate `∫ x, F_int' s x` by integration by parts on `ℝ × ℝ` and rescaling `x = √a y`.
    set gS : ℝ × ℝ → ℂ := UnforcedLeray.Gaussian.heatDilation a e
    have hgS_cd2 : ContDiff ℝ 2 gS := UnforcedLeray.Gaussian.contDiff_heatDilation he_cd2 a
    have hgS_diff : Differentiable ℝ gS := hgS_cd2.differentiable (by norm_num)
    have hpd_gS_diff : ∀ k : Fin 2, Differentiable ℝ (pdCx k gS) := fun k => by
      have h11 : ContDiff ℝ (1 + 1) gS := by rwa [one_add_one_eq_two]
      unfold pdCx
      exact ((h11.fderiv_right le_rfl).clm_apply contDiff_const).differentiable (by simp)
    have hφs_cd : ContDiff ℝ ∞ (φ s) := hφ_cd s hs_Icc
    have hφs_diff : Differentiable ℝ (φ s) := hφs_cd.differentiable (by simp)
    have hpd_φs_diff : ∀ k : Fin 2, Differentiable ℝ (B0579.pd k (φ s)) := fun k => by
      unfold B0579.pd
      exact ((hφs_cd.fderiv_right (m := (1 : ℕ)) (by simp)).clm_apply
        contDiff_const).differentiable (by simp)
    -- Pointwise Gaussian bounds on `gS`, `pdCx k gS`, `pdCx k (pdCx k gS)`, `dHeat s`
    have hainv : a⁻¹ ≤ 1 := inv_le_one_of_one_le₀ ha1
    have hainv2 : a⁻¹ ^ 2 ≤ 1 := pow_le_one₀ (inv_nonneg.mpr ha0.le) hainv
    have hsq_inv : (Real.sqrt a)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (Real.one_le_sqrt.2 ha1)
    have hgS_bd : ∀ x : ℝ × ℝ, ‖gS x‖ ≤ Ce0 * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (8 * A)) := by
      intro x
      dsimp only [gS]
      rw [UnforcedLeray.Gaussian.heatDilation_apply, norm_smul, Real.norm_of_nonneg (sq_nonneg _)]
      calc a⁻¹ ^ 2 * ‖e ((Real.sqrt a)⁻¹ • x)‖
          ≤ 1 * (Ce0 * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (8 * A))) :=
            mul_le_mul hainv2 ((he_val_bd _).trans
              (mul_le_mul_of_nonneg_left (exp_dilated_le ha0 haA x) hCe0))
              (norm_nonneg _) zero_le_one
        _ = Ce0 * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (8 * A)) := one_mul _
    have hpd_gS_bd : ∀ k : Fin 2, ∀ x : ℝ × ℝ,
        ‖pdCx k gS x‖ ≤ Ce1 * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (8 * A)) := by
      intro k x
      dsimp only [gS]
      rw [pdCx_heatDilation he_diff k x, norm_smul, Real.norm_of_nonneg (by positivity)]
      have hc_le : a⁻¹ ^ 2 * (Real.sqrt a)⁻¹ ≤ 1 :=
        mul_le_one₀ hainv2 (inv_nonneg.mpr (Real.sqrt_nonneg a)) hsq_inv
      calc (a⁻¹ ^ 2 * (Real.sqrt a)⁻¹) * ‖pdCx k e ((Real.sqrt a)⁻¹ • x)‖
          ≤ 1 * (Ce1 * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (8 * A))) :=
            mul_le_mul hc_le ((he_pd_bd k _).trans
              (mul_le_mul_of_nonneg_left (exp_dilated_le ha0 haA x) hCe1))
              (norm_nonneg _) zero_le_one
        _ = Ce1 * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (8 * A)) := one_mul _
    have hpd2_gS_eq : ∀ k : Fin 2, ∀ x : ℝ × ℝ,
        pdCx k (pdCx k gS) x = (a⁻¹ ^ 2 * (Real.sqrt a)⁻¹ ^ 2) •
          pdCx k (pdCx k e) ((Real.sqrt a)⁻¹ • x) := by
      intro k x
      have h1 : pdCx k gS = fun z => (a⁻¹ ^ 2 * (Real.sqrt a)⁻¹) • pdCx k e ((Real.sqrt a)⁻¹ • z) :=
        funext (pdCx_heatDilation he_diff k)
      have hin : ∀ z, HasFDerivAt (fun w : ℝ × ℝ => (Real.sqrt a)⁻¹ • w)
          ((Real.sqrt a)⁻¹ • ContinuousLinearMap.id ℝ (ℝ × ℝ)) z :=
        fun z => (hasFDerivAt_id z).const_smul (Real.sqrt a)⁻¹
      have hpde_diff : Differentiable ℝ (pdCx k e) := by
        unfold pdCx
        exact ((he_inf.fderiv_right (m := (1 : ℕ)) (by simp)).clm_apply
          contDiff_const).differentiable (by simp)
      have hcomp : HasFDerivAt (pdCx k gS)
          ((a⁻¹ ^ 2 * (Real.sqrt a)⁻¹) • ((fderiv ℝ (pdCx k e) ((Real.sqrt a)⁻¹ • x)).comp
            ((Real.sqrt a)⁻¹ • ContinuousLinearMap.id ℝ (ℝ × ℝ)))) x := by
        rw [h1]
        exact (((hpde_diff ((Real.sqrt a)⁻¹ • x)).hasFDerivAt.comp x (hin x)).const_smul
          (a⁻¹ ^ 2 * (Real.sqrt a)⁻¹))
      change (fderiv ℝ (pdCx k gS) x) (B0579.dir k) = _
      rw [hcomp.fderiv]
      unfold pdCx
      simp [smul_smul, sq, mul_assoc]
    have hpd2_gS_bd : ∀ k : Fin 2, ∀ x : ℝ × ℝ,
        ‖pdCx k (pdCx k gS) x‖ ≤ Ce2 * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (8 * A)) := by
      intro k x
      rw [hpd2_gS_eq k x, norm_smul, Real.norm_of_nonneg (by positivity)]
      have hc_le : a⁻¹ ^ 2 * (Real.sqrt a)⁻¹ ^ 2 ≤ 1 :=
        mul_le_one₀ hainv2 (sq_nonneg _) (pow_le_one₀ (inv_nonneg.mpr (Real.sqrt_nonneg a)) hsq_inv)
      calc (a⁻¹ ^ 2 * (Real.sqrt a)⁻¹ ^ 2) * ‖pdCx k (pdCx k e) ((Real.sqrt a)⁻¹ • x)‖
          ≤ 1 * (Ce2 * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (8 * A))) :=
            mul_le_mul hc_le ((he_pd2_bd k _).trans
              (mul_le_mul_of_nonneg_left (exp_dilated_le ha0 haA x) hCe2))
              (norm_nonneg _) zero_le_one
        _ = Ce2 * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (8 * A)) := one_mul _
    -- Helper to get `Integrable (fun x => ((f x : ℝ) : ℂ) * h x)` from bounded continuous `f` and Gaussian `h`
    have hint_mul : ∀ {f : ℝ × ℝ → ℝ} {h : ℝ × ℝ → ℂ} {Cf Ch : ℝ},
        0 ≤ Cf → Continuous f → Continuous h → (∀ x, |f x| ≤ Cf) →
        (∀ x, ‖h x‖ ≤ Ch * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (8 * A))) →
        Integrable (fun x : ℝ × ℝ => ((f x : ℝ) : ℂ) * h x) volume := by
      intro f h Cf Ch hCf0 hf_c hh_c hf_b hh_b
      refine integrable_of_gauss_plane hA0 (K := Cf * Ch)
        ((Complex.continuous_ofReal.comp hf_c).mul hh_c).aestronglyMeasurable fun x => ?_
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      calc |f x| * ‖h x‖ ≤ Cf * (Ch * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (8 * A))) :=
            mul_le_mul (hf_b x) (hh_b x) (norm_nonneg _) hCf0
        _ = (Cf * Ch) * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (8 * A)) := by ring
    have hφs_b0 : ∀ x, |φ s x| ≤ Cφ := fun x => by
      have h := hφ_bd s hs_Icc x
      linarith [abs_nonneg (B0579.pd 0 (φ s) x), abs_nonneg (B0579.pd 1 (φ s) x),
        abs_nonneg (UnforcedLeray.Short.IIb.lapP (φ s) x)]
    have hpd_φs_b : ∀ k : Fin 2, ∀ x, |B0579.pd k (φ s) x| ≤ Cφ := fun k x => by
      have h := hφ_bd s hs_Icc x
      have hk : k = 0 ∨ k = 1 := by fin_cases k <;> [exact Or.inl rfl; exact Or.inr rfl]
      rcases hk with rfl | rfl <;>
        linarith [abs_nonneg (φ s x), abs_nonneg (B0579.pd 0 (φ s) x),
          abs_nonneg (B0579.pd 1 (φ s) x), abs_nonneg (UnforcedLeray.Short.IIb.lapP (φ s) x)]
    have hpd2_φs_c : ∀ k : Fin 2, Continuous (B0579.pd k (B0579.pd k (φ s))) := fun k => by
      have h1 : ContDiff ℝ (2 : ℕ) (B0579.pd k (φ s)) := by
        unfold B0579.pd
        exact (hφs_cd.fderiv_right (m := (2 : ℕ)) (by simp)).clm_apply contDiff_const
      unfold B0579.pd
      exact ((h1.fderiv_right (m := (1 : ℕ)) (by norm_num)).clm_apply contDiff_const).continuous
    -- Diffusion IBP: `∫ ((lapP (φ s) x) : ℂ) * gS x = ∫ ((φ s x) : ℂ) * Cyl.laplacian gS x`
    have hgS_inf : ContDiff ℝ ∞ gS := UnforcedLeray.Gaussian.contDiff_heatDilation he_inf a
    have hlap_φs_b : ∀ x, |UnforcedLeray.Short.IIb.lapP (φ s) x| ≤ Cφ := fun x => by
      have h := hφ_bd s hs_Icc x
      linarith [abs_nonneg (φ s x), abs_nonneg (B0579.pd 0 (φ s) x),
        abs_nonneg (B0579.pd 1 (φ s) x)]
    have hlap_ibp : ∫ x : ℝ × ℝ, ((UnforcedLeray.Short.IIb.lapP (φ s) x : ℝ) : ℂ) * gS x =
        ∫ x : ℝ × ℝ, ((φ s x : ℝ) : ℂ) * UnforcedLeray.Cyl.laplacian gS x :=
      integral_plane_lapP_mul hA0 hCφ0 hCe0 hCe1 hCe2 hφs_cd hgS_inf hφs_b0 hpd_φs_b hlap_φs_b
        hgS_bd hpd_gS_bd hpd2_gS_bd
    -- Solenoidal transport IBP: `∫ ((v · ∇φ) : ℂ) * gS = -∫ ((φ s) : ℂ) * (v · ∇gS)`
    have hv_diff_k : ∀ k : Fin 2, Differentiable ℝ (fun w => tr.v s w k) := fun k =>
      (EuclideanSpace.proj k : UnforcedLeray.Train.Vec →L[ℝ] ℝ).differentiable.comp
        ((UnforcedLeray.B0238.contDiff_Vc tr hs0).differentiable (by simp))
    have hv_div0 : ∀ x : ℝ × ℝ,
        B0579.pd 0 (fun w => tr.v s w 0) x + B0579.pd 1 (fun w => tr.v s w 1) x = 0 := by
      intro x
      have h0 : B0579.pd 0 (fun w => tr.v s w 0) x =
          UnforcedLeray.Cyl.partialQ (fun w => tr.v s w 0) x := by
        rw [UnforcedLeray.Cyl.partialQ_eq_fderiv (hv_diff_k 0) x]; rfl
      have h1 : B0579.pd 1 (fun w => tr.v s w 1) x =
          UnforcedLeray.Cyl.partialEta (fun w => tr.v s w 1) x := by
        rw [UnforcedLeray.Cyl.partialEta_eq_fderiv (hv_diff_k 1) x]; rfl
      rw [h0, h1]
      exact tr.isTrain.solenoidal s hs0 x
    have htrans_ibp :
        ∫ x : ℝ × ℝ,
          (((tr.v s x 0 * B0579.pd 0 (φ s) x + tr.v s x 1 * B0579.pd 1 (φ s) x : ℝ) : ℂ) * gS x) =
        -∫ x : ℝ × ℝ, ((φ s x : ℝ) : ℂ) *
          (((tr.v s x 0 : ℝ) : ℂ) * pdCx 0 gS x + ((tr.v s x 1 : ℝ) : ℂ) * pdCx 1 gS x) := by
      set fk : Fin 2 → ℝ × ℝ → ℝ := fun k w => φ s w * tr.v s w k
      have hfk_diff : ∀ k : Fin 2, Differentiable ℝ (fk k) := fun k =>
        hφs_diff.mul (hv_diff_k k)
      have hfk_c : ∀ k : Fin 2, Continuous (fk k) := fun k => (hfk_diff k).continuous
      have hfk_b : ∀ k : Fin 2, ∀ x, |fk k x| ≤ Cφ * V₀ := fun k x => by
        dsimp only [fk]; rw [abs_mul]
        exact mul_le_mul (hφs_b0 x) (hv_bd s hs_Icc x k) (abs_nonneg _) hCφ0
      have hpdfk_eq : ∀ k : Fin 2, ∀ x,
          B0579.pd k (fk k) x =
            B0579.pd k (φ s) x * tr.v s x k + φ s x * B0579.pd k (fun w => tr.v s w k) x :=
        fun k x => pd_mul_real k hφs_diff (hv_diff_k k) x
      have hpdfk_c : ∀ k : Fin 2, Continuous (B0579.pd k (fk k)) := fun k => by
        rw [funext (hpdfk_eq k)]
        have hpd_φ_c : Continuous (B0579.pd k (φ s)) := (hpd_φs_diff k).continuous
        have hv_c : Continuous (fun w => tr.v s w k) := (hv_diff_k k).continuous
        have hpdv_c : Continuous (B0579.pd k (fun w => tr.v s w k)) := by
          unfold B0579.pd
          have hv_cd : ContDiff ℝ ∞ (fun w => tr.v s w k) :=
            (EuclideanSpace.proj k : UnforcedLeray.Train.Vec →L[ℝ] ℝ).contDiff.comp
              (UnforcedLeray.B0238.contDiff_Vc tr hs0)
          exact ((hv_cd.fderiv_right (m := (1 : ℕ)) (by simp)).clm_apply contDiff_const).continuous
        exact (hpd_φ_c.mul hv_c).add (hφs_cd.continuous.mul hpdv_c)
      have hpdfk_b : ∀ k : Fin 2, ∀ x, |B0579.pd k (fk k) x| ≤ Cφ * V₀ + Cφ * V₁ := fun k x => by
        rw [hpdfk_eq k x]
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_mul]
        exact add_le_add (mul_le_mul (hpd_φs_b k x) (hv_bd s hs_Icc x k) (abs_nonneg _) hCφ0)
          (mul_le_mul (hφs_b0 x) (hv_pd_bd s hs_Icc x k k) (abs_nonneg _) hCφ0)
      have hpd_gS_c : ∀ k : Fin 2, Continuous (pdCx k gS) := fun k => (hpd_gS_diff k).continuous
      have hCV0 : 0 ≤ Cφ * V₀ := mul_nonneg hCφ0 hV₀0
      have hCV01 : 0 ≤ Cφ * V₀ + Cφ * V₁ := add_nonneg hCV0 (mul_nonneg hCφ0 hV₁0)
      have il0 := hint_mul hCV01 (hpdfk_c 0) hgS_inf.continuous (hpdfk_b 0) hgS_bd
      have il1 := hint_mul hCV01 (hpdfk_c 1) hgS_inf.continuous (hpdfk_b 1) hgS_bd
      have ir0 := hint_mul hCV0 (hfk_c 0) (hpd_gS_c 0) (hfk_b 0) (hpd_gS_bd 0)
      have ir1 := hint_mul hCV0 (hfk_c 1) (hpd_gS_c 1) (hfk_b 1) (hpd_gS_bd 1)
      have it0 := integral_plane_pd_mul 0 (hfk_diff 0) hgS_diff
        (hint_mul hCV0 (hfk_c 0) hgS_inf.continuous (hfk_b 0) hgS_bd) il0 ir0
      have it1 := integral_plane_pd_mul 1 (hfk_diff 1) hgS_diff
        (hint_mul hCV0 (hfk_c 1) hgS_inf.continuous (hfk_b 1) hgS_bd) il1 ir1
      have hlhs_eq : ∫ x : ℝ × ℝ,
          (((tr.v s x 0 * B0579.pd 0 (φ s) x + tr.v s x 1 * B0579.pd 1 (φ s) x : ℝ) : ℂ) * gS x) =
          (∫ x : ℝ × ℝ, ((B0579.pd 0 (fk 0) x : ℝ) : ℂ) * gS x) +
            ∫ x : ℝ × ℝ, ((B0579.pd 1 (fk 1) x : ℝ) : ℂ) * gS x := by
        rw [← integral_add il0 il1]
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        dsimp only
        have hsum_real : tr.v s x 0 * B0579.pd 0 (φ s) x + tr.v s x 1 * B0579.pd 1 (φ s) x =
            B0579.pd 0 (fk 0) x + B0579.pd 1 (fk 1) x := by
          rw [hpdfk_eq 0 x, hpdfk_eq 1 x]
          linear_combination -(φ s x) * hv_div0 x
        rw [hsum_real]
        push_cast; ring
      have hrhs_eq : ∫ x : ℝ × ℝ, ((φ s x : ℝ) : ℂ) *
            (((tr.v s x 0 : ℝ) : ℂ) * pdCx 0 gS x + ((tr.v s x 1 : ℝ) : ℂ) * pdCx 1 gS x) =
          (∫ x : ℝ × ℝ, ((fk 0 x : ℝ) : ℂ) * pdCx 0 gS x) +
            ∫ x : ℝ × ℝ, ((fk 1 x : ℝ) : ℂ) * pdCx 1 gS x := by
        rw [← integral_add ir0 ir1]
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        dsimp only [fk]; push_cast; ring
      rw [hlhs_eq, it0, it1, hrhs_eq]
      ring
    -- Assemble `∫ x, F_int' s x` and rescale `x = √a y`
    have hlap_g_c : Continuous (UnforcedLeray.Cyl.laplacian gS) := by
      have hpQ : UnforcedLeray.Cyl.partialQ gS = pdCx 0 gS := by
        funext z; rw [UnforcedLeray.Cyl.partialQ_eq_fderiv hgS_diff z]; rfl
      have hpE : UnforcedLeray.Cyl.partialEta gS = pdCx 1 gS := by
        funext z; rw [UnforcedLeray.Cyl.partialEta_eq_fderiv hgS_diff z]; rfl
      have hd0 := hpd_gS_diff 0
      have hd1 := hpd_gS_diff 1
      have h0c : Continuous (pdCx 0 (pdCx 0 gS)) := by
        unfold pdCx
        exact (((hgS_inf.fderiv_right (m := (2 : ℕ)) (by simp)).clm_apply
          contDiff_const |>.fderiv_right (m := (1 : ℕ)) (by norm_num)).clm_apply
          contDiff_const).continuous
      have h1c : Continuous (pdCx 1 (pdCx 1 gS)) := by
        unfold pdCx
        exact (((hgS_inf.fderiv_right (m := (2 : ℕ)) (by simp)).clm_apply
          contDiff_const |>.fderiv_right (m := (1 : ℕ)) (by norm_num)).clm_apply
          contDiff_const).continuous
      have heq : UnforcedLeray.Cyl.laplacian gS = fun x =>
          pdCx 0 (pdCx 0 gS) x + pdCx 1 (pdCx 1 gS) x := by
        funext x
        unfold UnforcedLeray.Cyl.laplacian
        rw [hpQ, hpE, UnforcedLeray.Cyl.partialQ_eq_fderiv hd0 x,
          UnforcedLeray.Cyl.partialEta_eq_fderiv hd1 x]
        rfl
      rw [heq]; exact h0c.add h1c
    have hdrift_c : Continuous (UnforcedLeray.Gaussian.dilationDrift e) := by
      unfold UnforcedLeray.Gaussian.dilationDrift
      have hf_c : Continuous (fun y : ℝ × ℝ => fderiv ℝ e y y) :=
        (he_inf.fderiv_right (m := (1 : ℕ)) (by simp)).continuous.clm_apply continuous_id
      exact (he_inf.continuous.const_smul _).add (hf_c.const_smul _)
    have hdHeat_c : Continuous (dHeat s) := by
      dsimp only [dHeat, UnforcedLeray.Gaussian.heatDilation_apply]
      exact (continuous_const : Continuous fun _ : ℝ × ℝ => ν).smul
        ((continuous_const : Continuous fun _ : ℝ × ℝ => -(clockA ν s)⁻¹).smul
          ((continuous_const : Continuous fun _ : ℝ × ℝ => (clockA ν s)⁻¹ ^ 2).smul
            (hdrift_c.comp ((continuous_const : Continuous fun _ : ℝ × ℝ =>
              (Real.sqrt (clockA ν s))⁻¹).smul continuous_id))))
    have hdHeat_bd : ∀ x : ℝ × ℝ,
        ‖dHeat s x‖ ≤ (ν * (2 * Ce0 + Ce1)) * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (8 * A)) := by
      intro x
      dsimp only [dHeat]
      rw [norm_smul, Real.norm_of_nonneg hν.le, norm_smul, Real.norm_eq_abs, abs_neg,
        abs_of_pos (inv_pos.mpr ha0), UnforcedLeray.Gaussian.heatDilation_apply, norm_smul,
        Real.norm_of_nonneg (sq_nonneg _)]
      have hdr : ‖UnforcedLeray.Gaussian.dilationDrift e ((Real.sqrt a)⁻¹ • x)‖ ≤
          (2 * Ce0 + Ce1) * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (8 * A)) :=
        (hdilationDrift_bd _).trans
          (mul_le_mul_of_nonneg_left (exp_dilated_le ha0 haA x) (by positivity))
      have h1 : a⁻¹ * (a⁻¹ ^ 2 * ‖UnforcedLeray.Gaussian.dilationDrift e ((Real.sqrt a)⁻¹ • x)‖) ≤
          (2 * Ce0 + Ce1) * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (8 * A)) := by
        calc _ ≤ 1 * (1 * ((2 * Ce0 + Ce1) * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (8 * A)))) :=
              mul_le_mul hainv (mul_le_mul hainv2 hdr (norm_nonneg _) zero_le_one)
                (by positivity) zero_le_one
          _ = _ := by ring
      calc ν * _ ≤ ν * ((2 * Ce0 + Ce1) * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (8 * A))) :=
            mul_le_mul_of_nonneg_left h1 hν.le
        _ = _ := by ring
    have i_lap : Integrable (fun x : ℝ × ℝ =>
        ((UnforcedLeray.Short.IIb.lapP (φ s) x : ℝ) : ℂ) * gS x) volume :=
      hint_mul hCφ0 ((hpd2_φs_c 0).add (hpd2_φs_c 1)) hgS_inf.continuous hlap_φs_b hgS_bd
    have i_tr : Integrable (fun x : ℝ × ℝ =>
        ((tr.v s x 0 * B0579.pd 0 (φ s) x + tr.v s x 1 * B0579.pd 1 (φ s) x : ℝ) : ℂ) * gS x)
        volume := by
      refine hint_mul (Cf := 2 * V₀ * Cφ) (mul_nonneg (mul_nonneg zero_le_two hV₀0) hCφ0)
        (((hv_diff_k 0).continuous.mul (hpd_φs_diff 0).continuous).add
          ((hv_diff_k 1).continuous.mul (hpd_φs_diff 1).continuous))
        hgS_inf.continuous (fun x => ?_) hgS_bd
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul]
      have b0 := mul_le_mul (hv_bd s hs_Icc x 0) (hpd_φs_b 0 x) (abs_nonneg _) hV₀0
      have b1 := mul_le_mul (hv_bd s hs_Icc x 1) (hpd_φs_b 1 x) (abs_nonneg _) hV₀0
      linarith
    have i_dh : Integrable (fun x : ℝ × ℝ => ((φ s x : ℝ) : ℂ) * dHeat s x) volume :=
      hint_mul hCφ0 hφs_cd.continuous hdHeat_c hφs_b0 hdHeat_bd
    have i_φlap : Integrable (fun x : ℝ × ℝ =>
        ((φ s x : ℝ) : ℂ) * UnforcedLeray.Cyl.laplacian gS x) volume := by
      refine hint_mul (Ch := 2 * Ce2) hCφ0 hφs_cd.continuous hlap_g_c hφs_b0 fun x => ?_
      have hpQ : UnforcedLeray.Cyl.partialQ gS = pdCx 0 gS := by
        funext z; rw [UnforcedLeray.Cyl.partialQ_eq_fderiv hgS_diff z]; rfl
      have hpE : UnforcedLeray.Cyl.partialEta gS = pdCx 1 gS := by
        funext z; rw [UnforcedLeray.Cyl.partialEta_eq_fderiv hgS_diff z]; rfl
      have heq : UnforcedLeray.Cyl.laplacian gS x =
          pdCx 0 (pdCx 0 gS) x + pdCx 1 (pdCx 1 gS) x := by
        unfold UnforcedLeray.Cyl.laplacian
        rw [hpQ, hpE, UnforcedLeray.Cyl.partialQ_eq_fderiv (hpd_gS_diff 0) x,
          UnforcedLeray.Cyl.partialEta_eq_fderiv (hpd_gS_diff 1) x]
        rfl
      rw [heq]
      calc ‖pdCx 0 (pdCx 0 gS) x + pdCx 1 (pdCx 1 gS) x‖
          ≤ ‖pdCx 0 (pdCx 0 gS) x‖ + ‖pdCx 1 (pdCx 1 gS) x‖ := norm_add_le _ _
        _ ≤ Ce2 * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (8 * A)) +
              Ce2 * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (8 * A)) :=
            add_le_add (hpd2_gS_bd 0 x) (hpd2_gS_bd 1 x)
        _ = (2 * Ce2) * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (8 * A)) := by ring
    have i_φvg : Integrable (fun x : ℝ × ℝ => ((φ s x : ℝ) : ℂ) *
        (((tr.v s x 0 : ℝ) : ℂ) * pdCx 0 gS x + ((tr.v s x 1 : ℝ) : ℂ) * pdCx 1 gS x)) volume := by
      have i0 := hint_mul (Cf := Cφ * V₀) (mul_nonneg hCφ0 hV₀0)
        (hφs_cd.continuous.mul (hv_diff_k 0).continuous) (hpd_gS_diff 0).continuous
        (fun x => by
          simp only [Pi.mul_apply, abs_mul]
          exact mul_le_mul (hφs_b0 x) (hv_bd s hs_Icc x 0) (abs_nonneg _) hCφ0)
        (hpd_gS_bd 0)
      have i1 := hint_mul (Cf := Cφ * V₀) (mul_nonneg hCφ0 hV₀0)
        (hφs_cd.continuous.mul (hv_diff_k 1).continuous) (hpd_gS_diff 1).continuous
        (fun x => by
          simp only [Pi.mul_apply, abs_mul]
          exact mul_le_mul (hφs_b0 x) (hv_bd s hs_Icc x 1) (abs_nonneg _) hCφ0)
        (hpd_gS_bd 1)
      refine (i0.add i1).congr (Eventually.of_forall fun x => ?_)
      simp only [Pi.add_apply, Pi.mul_apply]
      push_cast; ring
    have hF_split : ∫ x : ℝ × ℝ, F_int' s x =
        -((ν : ℂ) * ∫ x : ℝ × ℝ, ((UnforcedLeray.Short.IIb.lapP (φ s) x : ℝ) : ℂ) * gS x) -
          (∫ x : ℝ × ℝ,
            ((tr.v s x 0 * B0579.pd 0 (φ s) x + tr.v s x 1 * B0579.pd 1 (φ s) x : ℝ) : ℂ) * gS x) +
          ∫ x : ℝ × ℝ, ((φ s x : ℝ) : ℂ) * dHeat s x := by
      have i_lap_c : Integrable (fun x : ℝ × ℝ =>
          -(ν : ℂ) * (((UnforcedLeray.Short.IIb.lapP (φ s) x : ℝ) : ℂ) * gS x)) volume :=
        i_lap.const_mul (-(ν : ℂ))
      have i_diff : Integrable (fun x : ℝ × ℝ =>
          -(ν : ℂ) * (((UnforcedLeray.Short.IIb.lapP (φ s) x : ℝ) : ℂ) * gS x) -
            (((tr.v s x 0 * B0579.pd 0 (φ s) x + tr.v s x 1 * B0579.pd 1 (φ s) x : ℝ) : ℂ) * gS x))
          volume :=
        i_lap_c.sub i_tr
      have h1 : ∀ x, F_int' s x =
          (-(ν : ℂ) * (((UnforcedLeray.Short.IIb.lapP (φ s) x : ℝ) : ℂ) * gS x) -
            (((tr.v s x 0 * B0579.pd 0 (φ s) x + tr.v s x 1 * B0579.pd 1 (φ s) x : ℝ) : ℂ) * gS x)) +
          ((φ s x : ℝ) : ℂ) * dHeat s x := by
        intro x
        dsimp only [F_int', dφ, gS]
        push_cast; ring
      simp_rw [h1]
      rw [integral_add i_diff i_dh, integral_sub i_lap_c i_tr, integral_const_mul, neg_mul]
    have hF_ibp : ∫ x : ℝ × ℝ, F_int' s x =
        ∫ x : ℝ × ℝ, ((φ s x : ℝ) : ℂ) *
          (-(ν : ℂ) * UnforcedLeray.Cyl.laplacian gS x + dHeat s x +
            (((tr.v s x 0 : ℝ) : ℂ) * pdCx 0 gS x + ((tr.v s x 1 : ℝ) : ℂ) * pdCx 1 gS x)) := by
      rw [hF_split, hlap_ibp, htrans_ibp, sub_neg_eq_add, ← neg_mul,
        ← integral_const_mul (-(ν : ℂ))]
      have ia : Integrable (fun x : ℝ × ℝ =>
          (-(ν : ℂ)) * (((φ s x : ℝ) : ℂ) * UnforcedLeray.Cyl.laplacian gS x)) volume :=
        i_φlap.const_mul (-(ν : ℂ))
      have ia_vg : Integrable (fun x : ℝ × ℝ =>
          (-(ν : ℂ)) * (((φ s x : ℝ) : ℂ) * UnforcedLeray.Cyl.laplacian gS x) +
            ((φ s x : ℝ) : ℂ) *
              (((tr.v s x 0 : ℝ) : ℂ) * pdCx 0 gS x + ((tr.v s x 1 : ℝ) : ℂ) * pdCx 1 gS x)) volume :=
        ia.add i_φvg
      rw [← integral_add ia i_φvg, ← integral_add ia_vg i_dh]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      dsimp only; ring
    -- Rescale `∫ x, F_int' s x` and `IFun s` to `y`-coordinates (`x = √a y`)
    have hsq : 0 < Real.sqrt a := Real.sqrt_pos.2 ha0
    have ha32 : a ^ (3 / 2 : ℝ) = a * Real.sqrt a := by
      calc a ^ (3 / 2 : ℝ) = a ^ ((1 : ℝ) + 1 / 2) := by norm_num
        _ = a ^ (1 : ℝ) * a ^ (1 / 2 : ℝ) := Real.rpow_add ha0 1 (1 / 2)
        _ = a * Real.sqrt a := by rw [Real.rpow_one, Real.sqrt_eq_rpow]
    have hIFun_y : IFun s = (((a⁻¹ : ℝ) : ℂ)) *
        ∫ y : ℝ × ℝ, ((φ s (Real.sqrt a * y.1, Real.sqrt a * y.2) : ℝ) : ℂ) * e y := by
      dsimp only [IFun]
      rw [show clockA ν s = a from rfl, integral_plane_eq_smul ha0]
      have hpt : ∀ y : ℝ × ℝ,
          ((φ s (Real.sqrt a * y.1, Real.sqrt a * y.2) : ℝ) : ℂ) *
            UnforcedLeray.Gaussian.heatDilation a e (Real.sqrt a * y.1, Real.sqrt a * y.2) =
          ((a⁻¹ ^ 2 : ℝ) : ℂ) *
            (((φ s (Real.sqrt a * y.1, Real.sqrt a * y.2) : ℝ) : ℂ) * e y) := by
        intro y
        rw [UnforcedLeray.Gaussian.heatDilation_apply, Complex.real_smul]
        have hinv : (Real.sqrt a)⁻¹ • ((Real.sqrt a * y.1, Real.sqrt a * y.2) : ℝ × ℝ) = y := by
          ext <;> simp [smul_eq_mul, inv_mul_cancel_left₀ hsq.ne']
        rw [hinv]; ring
      simp_rw [hpt]
      rw [integral_const_mul]
      push_cast; field_simp [ha0.ne']
    have hF_y : ((a ^ 2 : ℝ) : ℂ) * ∫ x : ℝ × ℝ, F_int' s x =
        (((a⁻¹ : ℝ) : ℂ)) * ∫ y : ℝ × ℝ, ((φ s (Real.sqrt a * y.1, Real.sqrt a * y.2) : ℝ) : ℂ) *
          (-(clockTheta ν s : ℂ)⁻¹ * movD e y +
            (((movingTrainV tr s y 0 : ℝ) : ℂ) * pdCx 0 e y +
              ((movingTrainV tr s y 1 : ℝ) : ℂ) * pdCx 1 e y)) := by
      rw [hF_ibp, integral_plane_eq_smul ha0, ← mul_assoc, ← integral_const_mul]
      rw [← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun y => ?_)
      dsimp only
      set z : ℝ × ℝ := (Real.sqrt a * y.1, Real.sqrt a * y.2)
      have hz_inv : (Real.sqrt a)⁻¹ • z = y := by
        ext <;> simp [z, smul_eq_mul, inv_mul_cancel_left₀ hsq.ne']
      have hlap_z : UnforcedLeray.Cyl.laplacian gS z =
          ((a⁻¹ * a⁻¹ ^ 2 : ℝ) : ℂ) * UnforcedLeray.Cyl.laplacian e y := by
        dsimp only [gS]
        rw [UnforcedLeray.Gaussian.laplacian_heatDilation he_cd2 ha0 z,
          UnforcedLeray.Gaussian.heatDilation_apply, hz_inv, smul_smul, Complex.real_smul]
      have hdHeat_z : dHeat s z =
          -((ν * (a⁻¹ * a⁻¹ ^ 2) : ℝ) : ℂ) * UnforcedLeray.Gaussian.dilationDrift e y := by
        dsimp only [dHeat]
        rw [UnforcedLeray.Gaussian.heatDilation_apply, hz_inv, smul_smul, smul_smul,
          Complex.real_smul]
        push_cast; ring
      have hpd_z : ∀ k : Fin 2, pdCx k gS z =
          ((a⁻¹ ^ 2 * (Real.sqrt a)⁻¹ : ℝ) : ℂ) * pdCx k e y := by
        intro k
        dsimp only [gS]
        rw [pdCx_heatDilation he_diff k z, hz_inv, Complex.real_smul]
      have hmovD_y : movD e y = UnforcedLeray.Cyl.laplacian e y +
          UnforcedLeray.Gaussian.dilationDrift e y := by
        rw [OscillatorForceSub.movD_eq_dilationGen he_cd2 y]
        rfl
      have hθ_s : (clockTheta ν s : ℂ)⁻¹ = ((ν * a : ℝ) : ℂ) := by
        unfold clockTheta
        push_cast; rw [inv_inv]
      have hV_y : ∀ k : Fin 2, ((movingTrainV tr s y k : ℝ) : ℂ) =
          ((a * Real.sqrt a : ℝ) : ℂ) * ((tr.v s z k : ℝ) : ℂ) := by
        intro k
        unfold movingTrainV
        rw [ha32]
        push_cast; rfl
      have hsc_osc : ((a ^ 2 : ℝ) : ℂ) * ((a : ℝ) : ℂ) * ((a⁻¹ * a⁻¹ ^ 2 : ℝ) : ℂ) =
          ((a⁻¹ : ℝ) : ℂ) * ((a : ℝ) : ℂ) := by
        push_cast; field_simp [ha0.ne']
      have hsc_tr : ((a ^ 2 : ℝ) : ℂ) * ((a : ℝ) : ℂ) * ((a⁻¹ ^ 2 * (Real.sqrt a)⁻¹ : ℝ) : ℂ) =
          ((a⁻¹ : ℝ) : ℂ) * ((a * Real.sqrt a : ℝ) : ℂ) := by
        have hreal : a ^ 2 * a * (a⁻¹ ^ 2 * (Real.sqrt a)⁻¹) = a⁻¹ * (a * Real.sqrt a) := by
          field_simp [ha0.ne', hsq.ne']
          rw [Real.sq_sqrt ha0.le]
        exact_mod_cast hreal
      rw [hlap_z, hdHeat_z, hpd_z 0, hpd_z 1, hmovD_y, hθ_s, hV_y 0, hV_y 1]
      dsimp only [z]
      push_cast at hsc_osc hsc_tr ⊢
      linear_combination
        -((ν : ℂ) * ((φ s (Real.sqrt a * y.1, Real.sqrt a * y.2) : ℝ) : ℂ) *
          (UnforcedLeray.Cyl.laplacian e y + UnforcedLeray.Gaussian.dilationDrift e y)) * hsc_osc +
        (((φ s (Real.sqrt a * y.1, Real.sqrt a * y.2) : ℝ) : ℂ) *
          (((tr.v s (Real.sqrt a * y.1, Real.sqrt a * y.2) 0 : ℝ) : ℂ) * pdCx 0 e y +
            ((tr.v s (Real.sqrt a * y.1, Real.sqrt a * y.2) 1 : ℝ) : ℂ) * pdCx 1 e y)) * hsc_tr
    exact ⟨hIFun_y, hF_y⟩

private lemma hasDerivAt_rawFE (P : PlanarData) {B ν : ℝ}
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (t₁ t₂ τ σ₀ : ℝ)
    (φ : ℝ → B0579.Plane → ℝ) (e : ℝ × ℝ → ℂ)
    (hν : 0 < ν) (ht₁ : 0 ≤ t₁) (ht₂ : 0 ≤ t₂) (hBe : movingZ ν t₂ - movingZ ν t₁ = B)
    (hτ : τ ∈ Icc (0 : ℝ) B) (ht_mem : ageAt ν t₁ τ ∈ Icc t₁ t₂)
    (hσ₀ : σ₀ ∈ Icc (0 : ℝ) τ)
    (sb : SeedBounds e) (pb : PhiTrainBounds ν t₁ (ageAt ν t₁ τ) tr φ)
    (σ : ℝ) (hσ_Ioo : σ ∈ Ioo (0 : ℝ) σ₀) :
    HasDerivAt (rawFE P ν t₁ (ageAt ν t₁ τ) φ e)
      (rawFR P ν tr t₁ (ageAt ν t₁ τ) φ e σ) σ := by
    rcases sb with ⟨he_inf, he_cd2, he_diff, Ce0, Ce1, Ce2, CD, hCe0, hCe1, hCe2, hCD0,
      he_val_bd, he_pd_cont, he_pd_bd, he_pd2_bd, hcont_movD, hCD, hdilationDrift_bd⟩
    rcases pb with ⟨hφsp, hφ_cd, hφpde, Cφ, V₀, V₁, hCφ0, hV₀0, hV₁0, hφ_bd, hv_bd, hv_pd_bd⟩
    set t := ageAt ν t₁ τ
    have ht0 : 0 ≤ t := ht₁.trans ht_mem.1
    set s := ageAt ν t₁ σ
    set a := clockA ν s
    have hs_Ioo : s ∈ Ioo t₁ t :=
      ⟨by simpa [CompactDuhamelGapSub.ageAt_zero hν ht₁] using
          ageAt_lt_on_block hν ht₁ ht₂ hBe le_rfl hσ_Ioo.1 (hσ_Ioo.2.le.trans (hσ₀.2.trans hτ.2)),
        ageAt_lt_on_block hν ht₁ ht₂ hBe hσ_Ioo.1.le (lt_of_lt_of_le hσ_Ioo.2 hσ₀.2) hτ.2⟩
    have hs_Icc : s ∈ Icc t₁ t := Ioo_subset_Icc_self hs_Ioo
    have hs0 : 0 ≤ s := ht₁.trans hs_Icc.1
    have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one (one_le_clockA hν.le hs0)
    have hφs_cd : ContDiff ℝ ∞ (φ s) := hφ_cd s hs_Icc
    have hφs_b0 : ∀ x, |φ s x| ≤ Cφ := fun x => by
      have h := hφ_bd s hs_Icc x
      linarith [abs_nonneg (B0579.pd 0 (φ s) x), abs_nonneg (B0579.pd 1 (φ s) x),
        abs_nonneg (UnforcedLeray.Short.IIb.lapP (φ s) x)]
    have hIFun_deriv := hasDerivAt_rawIFun tr t₁ t φ e s hν ht₁ ht0 hs_Ioo
      ⟨he_inf, he_cd2, he_diff, Ce0, Ce1, Ce2, CD, hCe0, hCe1, hCe2, hCD0,
        he_val_bd, he_pd_cont, he_pd_bd, he_pd2_bd, hcont_movD, hCD, hdilationDrift_bd⟩
      ⟨hφsp, hφ_cd, hφpde, Cφ, V₀, V₁, hCφ0, hV₀0, hV₁0, hφ_bd, hv_bd, hv_pd_bd⟩
    obtain ⟨hIFun_y, hF_y⟩ := eval_rawFInt'_rescaled tr t₁ t φ e s hν ht₁ ht0 hs_Icc
      ⟨he_inf, he_cd2, he_diff, Ce0, Ce1, Ce2, CD, hCe0, hCe1, hCe2, hCD0,
        he_val_bd, he_pd_cont, he_pd_bd, he_pd2_bd, hcont_movD, hCD, hdilationDrift_bd⟩
      ⟨hφsp, hφ_cd, hφpde, Cφ, V₀, V₁, hCφ0, hV₀0, hV₁0, hφ_bd, hv_bd, hv_pd_bd⟩
    unfold rawFE rawFR
    set IFun := rawIFun ν φ e
    set F_int' := rawFInt' ν tr φ e
    -- Chain rule + product rule for `FE` at `σ`
    have hdN := hasDerivAt_clockN_inv_ageAt P hν ht₁ ht₂ hBe hτ.2 hσ_Ioo.1
      (hσ_Ioo.2.le.trans hσ₀.2)
    have hdAge := hasDerivAt_ageAt_block hν ht₂ hBe (hσ_Ioo.2.le.trans (hσ₀.2.trans hτ.2))
    have hdI : HasDerivAt (fun σ' => IFun (ageAt ν t₁ σ'))
        (((a ^ 2 : ℝ) : ℂ) * ∫ x : ℝ × ℝ, F_int' s x) σ := by
      refine (hIFun_deriv.scomp σ hdAge).congr_deriv ?_
      dsimp only [a, s]
      rw [Complex.real_smul]
    refine (hdN.mul hdI).congr_deriv ?_
    rw [hIFun_y, hF_y]
    dsimp only [s, a]
    -- Combine the two `y`-integrals into `FR σ`
    have hφy_c : Continuous (fun y : ℝ × ℝ =>
        ((φ s (Real.sqrt a * y.1, Real.sqrt a * y.2) : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp
        (hφs_cd.continuous.comp ((continuous_const.mul continuous_fst).prodMk
          (continuous_const.mul continuous_snd)))
    have hφy_b : ∀ y : ℝ × ℝ,
        ‖((φ s (Real.sqrt a * y.1, Real.sqrt a * y.2) : ℝ) : ℂ)‖ ≤ Cφ := by
      intro y; rw [Complex.norm_real, Real.norm_eq_abs]; exact hφs_b0 _
    have iy_e : Integrable (fun y : ℝ × ℝ =>
        ((φ s (Real.sqrt a * y.1, Real.sqrt a * y.2) : ℝ) : ℂ) * e y) volume := by
      refine integrable_of_gauss_plane one_pos (K := Cφ * Ce0)
        (hφy_c.mul he_inf.continuous).aestronglyMeasurable fun y => ?_
      rw [mul_one, norm_mul]
      calc ‖((φ s (Real.sqrt a * y.1, Real.sqrt a * y.2) : ℝ) : ℂ)‖ * ‖e y‖
          ≤ Cφ * (Ce0 * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8)) :=
            mul_le_mul (hφy_b y) (he_val_bd y) (norm_nonneg _) hCφ0
        _ = (Cφ * Ce0) * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8) := by ring
    have iy_osc : Integrable (fun y : ℝ × ℝ =>
        ((φ s (Real.sqrt a * y.1, Real.sqrt a * y.2) : ℝ) : ℂ) *
          (-(clockTheta ν s : ℂ)⁻¹ * movD e y +
            (((movingTrainV tr s y 0 : ℝ) : ℂ) * pdCx 0 e y +
              ((movingTrainV tr s y 1 : ℝ) : ℂ) * pdCx 1 e y))) volume := by
      have hV0_c := Complex.continuous_ofReal.comp (EulerErrorSub.continuous_movingTrainV tr hs0 0)
      have hV1_c := Complex.continuous_ofReal.comp (EulerErrorSub.continuous_movingTrainV tr hs0 1)
      have hθ_nm : ‖-(clockTheta ν s : ℂ)⁻¹‖ ≤ ν * a := by
        rw [norm_neg, norm_inv, Complex.norm_of_nonneg (theta_pos hν hs0).le]
        unfold clockTheta; rw [inv_inv]
      refine integrable_of_gauss_plane one_pos
        (K := Cφ * (ν * a * CD + 2 * (a ^ (3 / 2 : ℝ) * V₀ * Ce1)))
        (hφy_c.mul ((continuous_const.mul hcont_movD).add
          ((hV0_c.mul (he_pd_cont 0)).add (hV1_c.mul (he_pd_cont 1))))).aestronglyMeasurable
        fun y => ?_
      rw [mul_one, norm_mul]
      have hVy : ∀ k : Fin 2, ‖((movingTrainV tr s y k : ℝ) : ℂ)‖ ≤ a ^ (3 / 2 : ℝ) * V₀ := by
        intro k
        rw [Complex.norm_real, Real.norm_eq_abs]; unfold movingTrainV
        rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg ha0.le _)]
        exact mul_le_mul_of_nonneg_left (hv_bd s hs_Icc _ k) (Real.rpow_nonneg ha0.le _)
      have b1 : ‖-(clockTheta ν s : ℂ)⁻¹ * movD e y‖ ≤
          (ν * a * CD) * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8) := by
        rw [norm_mul]
        calc ‖-(clockTheta ν s : ℂ)⁻¹‖ * ‖movD e y‖
            ≤ (ν * a) * (CD * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8)) :=
              mul_le_mul hθ_nm (hCD y) (norm_nonneg _) (mul_nonneg hν.le ha0.le)
          _ = _ := by ring
      have b2 : ∀ k : Fin 2, ‖((movingTrainV tr s y k : ℝ) : ℂ) * pdCx k e y‖ ≤
          (a ^ (3 / 2 : ℝ) * V₀ * Ce1) * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8) := by
        intro k; rw [norm_mul]
        calc ‖((movingTrainV tr s y k : ℝ) : ℂ)‖ * ‖pdCx k e y‖
            ≤ (a ^ (3 / 2 : ℝ) * V₀) * (Ce1 * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8)) :=
              mul_le_mul (hVy k) (he_pd_bd k y) (norm_nonneg _)
                (mul_nonneg (Real.rpow_nonneg ha0.le _) hV₀0)
          _ = _ := by ring
      have bsum : ‖-(clockTheta ν s : ℂ)⁻¹ * movD e y +
          (((movingTrainV tr s y 0 : ℝ) : ℂ) * pdCx 0 e y +
            ((movingTrainV tr s y 1 : ℝ) : ℂ) * pdCx 1 e y)‖ ≤
          (ν * a * CD + 2 * (a ^ (3 / 2 : ℝ) * V₀ * Ce1)) *
            Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8) := by
        calc _ ≤ ‖-(clockTheta ν s : ℂ)⁻¹ * movD e y‖ +
              (‖((movingTrainV tr s y 0 : ℝ) : ℂ) * pdCx 0 e y‖ +
                ‖((movingTrainV tr s y 1 : ℝ) : ℂ) * pdCx 1 e y‖) :=
            (norm_add_le _ _).trans (add_le_add le_rfl (norm_add_le _ _))
          _ ≤ (ν * a * CD) * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8) +
              ((a ^ (3 / 2 : ℝ) * V₀ * Ce1) * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8) +
                (a ^ (3 / 2 : ℝ) * V₀ * Ce1) * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8)) :=
            add_le_add b1 (add_le_add (b2 0) (b2 1))
          _ = _ := by ring
      calc ‖((φ s (Real.sqrt a * y.1, Real.sqrt a * y.2) : ℝ) : ℂ)‖ * _
          ≤ Cφ * ((ν * a * CD + 2 * (a ^ (3 / 2 : ℝ) * V₀ * Ce1)) *
              Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8)) :=
            mul_le_mul (hφy_b y) bsum (norm_nonneg _) hCφ0
        _ = _ := by ring
    have hcomb : (((movBeta0 P ν s : ℝ) : ℂ) *
          ∫ y : ℝ × ℝ, ((φ s (Real.sqrt a * y.1, Real.sqrt a * y.2) : ℝ) : ℂ) * e y) +
        (∫ y : ℝ × ℝ, ((φ s (Real.sqrt a * y.1, Real.sqrt a * y.2) : ℝ) : ℂ) *
          (-(clockTheta ν s : ℂ)⁻¹ * movD e y +
            (((movingTrainV tr s y 0 : ℝ) : ℂ) * pdCx 0 e y +
              ((movingTrainV tr s y 1 : ℝ) : ℂ) * pdCx 1 e y))) =
        ∫ y : ℝ × ℝ, ((φ s (Real.sqrt a * y.1, Real.sqrt a * y.2) : ℝ) : ℂ) *
          (-(clockTheta ν s : ℂ)⁻¹ * movD e y +
            (((movingTrainV tr s y 0 : ℝ) : ℂ) * pdCx 0 e y +
              ((movingTrainV tr s y 1 : ℝ) : ℂ) * pdCx 1 e y) +
            ((movBeta0 P ν s : ℝ) : ℂ) * e y) := by
      rw [← integral_const_mul, ← integral_add (iy_e.const_mul _) iy_osc]
      exact integral_congr_ae (Eventually.of_forall fun y => by ring)
    rw [Complex.ofReal_mul (movBeta0 P ν s), Complex.ofReal_mul (clockN P ν s t)⁻¹]
    linear_combination (((clockN P ν s t)⁻¹ : ℝ) : ℂ) * (((a⁻¹ : ℝ) : ℂ)) * hcomb

end Helpers

/-- **Leaf C (`FrameDualCore`, SP 2898-2918)**: `σ ↦ dualPair σ (frameEFun σ)` is the primitive
of `σ ↦ dualPair σ (frameRFun σ)` along `[0, τ]`. -/
theorem frameDualCore (κ : UnforcedLeray.Short.IIIa.PlanarFrameKernels) :
    UnforcedLeray.Short.IIIa.ComplMildTestedSplit.FrameDuhamelSub.FrameDualCore κ := by
  intro P m K B b ν tr t₁ t₂ ctx τ hτ χ _hχ φ hφ j σ₀ hσ₀
  have ⟨hκ, _hP, _hm, _hB, hb, hν, _hF, htr, ht₁, h12, hbt, hBe⟩ := ctx
  have ht₂ : 0 ≤ t₂ := ht₁.trans h12
  obtain ⟨_hφt, hφsp, hφpde⟩ := hφ
  set t := ageAt ν t₁ τ
  have ht_mem : t ∈ Icc t₁ t₂ := ageAt_mem_Icc hν ht₁ h12 hBe hτ
  rcases eq_or_lt_of_le hσ₀.1 with rfl | hσ₀_pos
  · simp
  have hage_Icc : ∀ σ ∈ Icc (0 : ℝ) τ, ageAt ν t₁ σ ∈ Icc t₁ t := fun σ hσ =>
    ⟨by simpa [CompactDuhamelGapSub.ageAt_zero hν ht₁] using
        ageAt_mono_on_block hν ht₁ ht₂ hBe le_rfl hσ.1 (hσ.2.trans hτ.2),
      ageAt_mono_on_block hν ht₁ ht₂ hBe hσ.1 hσ.2 hτ.2⟩
  have hd_ge1 : ∀ σ ∈ Icc (0 : ℝ) τ, 1 ≤ dOf ν t₁ σ := by
    intro σ hσ
    have hs := hage_Icc σ hσ
    have hs0 : 0 ≤ ageAt ν t₁ σ := ht₁.trans hs.1
    have hs2 : ageAt ν t₁ σ ≤ t₂ := hs.2.trans ht_mem.2
    have hbs : b ≤ clockTheta ν (ageAt ν t₁ σ) := hbt.trans (clockTheta_le_of_le hν hs0 hs2)
    exact ComplMildYAux.cellLen_one_le_of_theta hν hs0 hb hbs
  obtain ⟨sb⟩ := exists_seedBounds hκ j
  obtain ⟨pb⟩ := exists_phiTrainBounds htr hφsp hφpde ht₁ ht₂ ht_mem
  obtain ⟨hFE_eq, hFR_eq⟩ := dualPair_eq_rawFE_and_rawFR P tr t₁ τ φ j hκ hν ht₁
    hage_Icc hd_ge1 sb pb
  obtain ⟨hFE_cont, hFR_cont⟩ := continuousOn_rawFE_and_rawFR P tr t₁ t₂ τ φ (κ.e j)
    hν ht₁ ht₂ hBe hτ ht_mem hage_Icc sb pb
  have hFE_deriv : ∀ σ ∈ Ioo (0 : ℝ) σ₀,
      HasDerivAt (rawFE P ν t₁ t φ (κ.e j)) (rawFR P ν tr t₁ t φ (κ.e j) σ) σ :=
    fun σ hσ => hasDerivAt_rawFE P tr t₁ t₂ τ σ₀ φ (κ.e j) hν ht₁ ht₂ hBe hτ ht_mem hσ₀ sb pb σ hσ
  have hsub : Icc (0 : ℝ) σ₀ ⊆ Icc (0 : ℝ) τ := Icc_subset_Icc le_rfl hσ₀.2
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hσ₀_pos.le
    (hFE_cont.mono hsub) hFE_deriv ((hFR_cont.mono hsub).intervalIntegrable_of_Icc hσ₀_pos.le)
  have hint_eq : (∫ σ in (0 : ℝ)..σ₀, dualPair P ν t₁ τ φ σ (frameRFun κ P ν tr t₁ j σ)) =
      ∫ σ in (0 : ℝ)..σ₀, rawFR P ν tr t₁ t φ (κ.e j) σ := by
    refine intervalIntegral.integral_congr fun σ hσ => ?_
    rw [uIcc_of_le hσ₀_pos.le] at hσ
    exact hFR_eq σ (hsub hσ)
  rw [hFE_eq σ₀ (hsub ⟨hσ₀_pos.le, le_rfl⟩), hFE_eq 0 (hsub ⟨le_rfl, hσ₀_pos.le⟩),
    hint_eq, hftc]
  ring

end FrameDuhamelSub

end ComplMildTestedSplit

end UnforcedLeray.Short.IIIa
