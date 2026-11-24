import UnforcedLeray.Statement
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Removable point singularities of the divergence (INF25 T25.7; blueprint B0687)

Tex lines 5855–5865 (B0687, `background:eq:2.8`): the background field `a` is smooth away
from the origin, divergence free there, and bounded by `C|x|⁻¹`; "at zero the omitted
spherical divergence flux is `O(r)`, so the field is globally solenoidal distributionally".

`isSolenoidal_of_punctured` proves this in the library's sense (`IsSolenoidal` of
`UnforcedLeray.Statement`: the pairing `∫ f · ∇φ` converges and vanishes for every smooth
compactly supported `φ`). Bypass B25-7 of the scoping note: split `φ = φψ_ε + φ(1 - ψ_ε)`
with a bump `ψ_ε = ψ(·/ε)`. The second piece vanishes near the origin, where classical
integration by parts and `div f = 0` give zero. The first is bounded by
`∫_{|x| ≤ 2ε} C|x|⁻¹ (‖∇φ‖_∞ + 2‖φ‖_∞ ‖∇ψ‖_∞ |x|⁻¹) dx`, which tends to zero because
`|x|⁻²` is integrable near the origin of `ℝ³`.

Hypotheses are those of the manuscript: `C¹` off the origin, zero divergence off the origin,
and the inverse-distance bound. Nothing is assumed at the origin, and no decay at infinity
is needed (tests have compact support).

Status: this proves the solenoidal clause used in B0687; the rest of B0687 is not built here.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Metric
open scoped ENNReal ContDiff

namespace UnforcedLeray.PhaseSpace

/-- The pointwise divergence `∑ᵢ ∂ᵢ fᵢ` of a field on `ℝ³`. -/
def pointDivergence (f : SpatialField) (x : Space) : ℝ :=
  ∑ i : Fin 3, (fderiv ℝ f x (coordinateVector i)) i

/-- The integrand `f · ∇φ` of the distributional divergence. -/
def divPairing (f : SpatialField) (φ : Space → ℝ) (x : Space) : ℝ :=
  ∑ i : Fin 3, (f x) i * spatialTestDerivative i φ x

theorem norm_coordinateVector (i : Fin 3) : ‖coordinateVector i‖ = 1 := by
  simp [coordinateVector]

theorem abs_spatialTestDerivative_le (φ : Space → ℝ) (i : Fin 3) (x : Space) :
    |spatialTestDerivative i φ x| ≤ ‖fderiv ℝ φ x‖ := by
  have h := (fderiv ℝ φ x).le_opNorm (coordinateVector i)
  rw [norm_coordinateVector, mul_one] at h
  simpa [spatialTestDerivative, Real.norm_eq_abs] using h

/-- A field continuous off the origin is a.e. strongly measurable. -/
theorem aestronglyMeasurable_of_continuousOn_compl {E : Type*} [NormedAddCommGroup E]
    {g : Space → E} (hg : ContinuousOn g {0}ᶜ) : AEStronglyMeasurable g volume := by
  have h := hg.aestronglyMeasurable (μ := volume) isOpen_compl_singleton.measurableSet
  rwa [restrict_compl_singleton (μ := (volume : Measure Space))] at h

/-- A product of a function continuous off the origin with a continuous function vanishing
near the origin is continuous. -/
theorem continuous_mul_of_vanish {a b : Space → ℝ} {ε : ℝ} (hε : 0 < ε)
    (ha : ContinuousOn a {0}ᶜ) (hb : Continuous b) (hb0 : ∀ x ∈ ball (0 : Space) ε, b x = 0) :
    Continuous fun x => a x * b x := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  by_cases hx : x = 0
  · subst hx
    have hev : (fun _ : Space => (0 : ℝ)) =ᶠ[𝓝 (0 : Space)] fun x => a x * b x := by
      filter_upwards [ball_mem_nhds (0 : Space) hε] with y hy
      simp [hb0 y hy]
    exact (continuousAt_const (y := (0 : ℝ))).congr hev
  · exact (ha.continuousAt (isOpen_compl_singleton.mem_nhds hx)).mul hb.continuousAt

section

variable {f : SpatialField} {C : ℝ}

/-- Integrability of `f · ∇u` for a compactly supported `u` with bounded first derivatives. -/
theorem integrable_divPairing (hfc : ContinuousOn f {0}ᶜ) (hbd : ∀ x ≠ 0, ‖f x‖ ≤ C * ‖x‖⁻¹)
    {u : Space → ℝ} (hu : Continuous fun x => fderiv ℝ u x) (hus : HasCompactSupport u) :
    Integrable (divPairing f u) := by
  obtain ⟨D, hD⟩ := hu.bounded_above_of_compact_support (hus.fderiv (𝕜 := ℝ))
  obtain ⟨R, hR⟩ := hus.isCompact.isBounded.subset_closedBall (0 : Space)
  have hmeas : AEStronglyMeasurable (divPairing f u) volume := by
    have hf := aestronglyMeasurable_of_continuousOn_compl hfc
    refine Finset.aestronglyMeasurable_fun_sum _ fun i _ => ?_
    refine (((EuclideanSpace.proj i : Space →L[ℝ] ℝ).continuous.comp_aestronglyMeasurable
      hf)).mul ?_
    exact ((hu.clm_apply continuous_const).aestronglyMeasurable)
  have hzero : ∀ x ∉ ball (0 : Space) (R + 1), divPairing f u x = 0 := by
    intro x hx
    have hxs : x ∉ tsupport u := by
      intro h
      have := hR h
      simp only [mem_closedBall, dist_zero_right] at this
      simp only [mem_ball, dist_zero_right, not_lt] at hx
      linarith
    simp [divPairing, spatialTestDerivative, fderiv_of_notMem_tsupport ℝ hxs]
  refine IntegrableOn.integrable_of_forall_notMem_eq_zero ?_ hzero
  refine integrableOn_ball_of_norm_le_rpow (α := 1) (C := 3 * (C * D)) (by simp)
    (by simp) ?_ hmeas
  have hne : ∀ᵐ x ∂(volume.restrict (ball (0 : Space) (R + 1))), x ≠ 0 :=
    ae_restrict_of_ae (compl_mem_ae_iff.mpr (measure_singleton (0 : Space)))
  filter_upwards [hne] with x hx
  rw [Real.rpow_neg_one]
  have hD0 : 0 ≤ D := (norm_nonneg _).trans (hD x)
  have hC0 : 0 ≤ C * ‖x‖⁻¹ := (norm_nonneg _).trans (hbd x hx)
  calc ‖divPairing f u x‖ ≤ ∑ i : Fin 3, ‖(f x) i * spatialTestDerivative i u x‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _i : Fin 3, (C * ‖x‖⁻¹) * D := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [norm_mul]
        refine mul_le_mul ((PiLp.norm_apply_le (f x) i).trans (hbd x hx)) ?_ (norm_nonneg _) hC0
        rw [Real.norm_eq_abs]
        exact (abs_spatialTestDerivative_le u i x).trans (hD x)
    _ = 3 * (C * D) * ‖x‖⁻¹ := by simp; ring

/-- Classical integration by parts away from the origin: for `g` smooth, compactly supported
and zero on `ball 0 ε`, `∫ f · ∇g = -∫ (div f) g = 0`. -/
theorem integral_divPairing_eq_zero_of_vanish (hf : ContDiffOn ℝ 1 f {0}ᶜ)
    (hdiv : ∀ x ≠ 0, pointDivergence f x = 0) {g : Space → ℝ} (hg : ContDiff ℝ ∞ g)
    (hgs : HasCompactSupport g) {ε : ℝ} (hε : 0 < ε) (hg0 : ∀ x ∈ ball (0 : Space) ε, g x = 0) :
    ∫ x, divPairing f g x = 0 := by
  have hfc : ContinuousOn f {0}ᶜ := hf.continuousOn
  have hf' : ContinuousOn (fun x => fderiv ℝ f x) {0}ᶜ :=
    hf.continuousOn_fderiv_of_isOpen isOpen_compl_singleton le_rfl
  have hgd : Differentiable ℝ g := hg.differentiable (by simp)
  have hg' : Continuous fun x => fderiv ℝ g x := hg.continuous_fderiv (by simp)
  have hdg0 : ∀ x ∈ ball (0 : Space) ε, fderiv ℝ g x = 0 := by
    intro x hx
    have hev : g =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [isOpen_ball.mem_nhds hx] with y hy
      exact hg0 y hy
    simp [hev.fderiv_eq]
  have hsupp : ∀ x ∈ tsupport g, x ≠ 0 := by
    intro x hx h0
    subst h0
    have : (0 : Space) ∉ tsupport g := by
      rw [notMem_tsupport_iff_eventuallyEq]
      filter_upwards [ball_mem_nhds (0 : Space) hε] with y hy
      exact hg0 y hy
    exact this hx
  have hdiff : ∀ x ∈ tsupport g, DifferentiableAt ℝ f x := fun x hx =>
    (hf.differentiableOn one_ne_zero x (hsupp x hx)).differentiableAt
      (isOpen_compl_singleton.mem_nhds (hsupp x hx))
  -- coordinate pieces
  let B : Fin 3 → Space →L[ℝ] ℝ →L[ℝ] ℝ := fun i =>
    (ContinuousLinearMap.mul ℝ ℝ).comp (EuclideanSpace.proj i : Space →L[ℝ] ℝ)
  have hB : ∀ i u s, B i u s = u i * s := fun i u s => rfl
  have hI1 : ∀ i : Fin 3, Integrable fun x => (fderiv ℝ f x (coordinateVector i)) i * g x := by
    intro i
    refine (continuous_mul_of_vanish hε ?_ hg.continuous hg0).integrable_of_hasCompactSupport
      (hgs.mul_left)
    exact ((EuclideanSpace.proj i : Space →L[ℝ] ℝ).continuous.comp_continuousOn
      (hf'.clm_apply continuousOn_const))
  have hI2 : ∀ i : Fin 3, Integrable fun x => (f x) i * spatialTestDerivative i g x := by
    intro i
    refine (continuous_mul_of_vanish hε ?_ (hg'.clm_apply continuous_const) ?_).integrable_of_hasCompactSupport
      ((hgs.fderiv_apply (𝕜 := ℝ) (coordinateVector i)).mul_left)
    · exact (EuclideanSpace.proj i : Space →L[ℝ] ℝ).continuous.comp_continuousOn hfc
    · intro x hx
      simp [hdg0 x hx]
  have hI3 : ∀ i : Fin 3, Integrable fun x => (f x) i * g x := by
    intro i
    refine (continuous_mul_of_vanish hε ?_ hg.continuous hg0).integrable_of_hasCompactSupport
      (hgs.mul_left)
    exact (EuclideanSpace.proj i : Space →L[ℝ] ℝ).continuous.comp_continuousOn hfc
  have hpiece : ∀ i : Fin 3,
      ∫ x, (f x) i * spatialTestDerivative i g x =
        -∫ x, (fderiv ℝ f x (coordinateVector i)) i * g x := by
    intro i
    have := integral_bilinear_fderiv_right_eq_neg_left_of_integrable (μ := volume)
      (v := coordinateVector i) (B := B i) (hI1 i) (hI2 i) (hI3 i) hdiff (fun x _ => hgd x)
    simpa [hB, spatialTestDerivative] using this
  have hsum : ∫ x, divPairing f g x = ∑ i : Fin 3, ∫ x, (f x) i * spatialTestDerivative i g x := by
    unfold divPairing
    exact integral_finsetSum _ fun i _ => hI2 i
  have hzero : ∀ x, ∑ i : Fin 3, (fderiv ℝ f x (coordinateVector i)) i * g x = 0 := by
    intro x
    by_cases hx : x = 0
    · subst hx
      simp [hg0 0 (mem_ball_self hε)]
    · rw [← Finset.sum_mul]
      have h := hdiv x hx
      unfold pointDivergence at h
      rw [h, zero_mul]
  rw [hsum, Finset.sum_congr rfl fun i _ => hpiece i, Finset.sum_neg_distrib,
    ← integral_finsetSum _ fun i _ => hI1 i]
  simp [hzero]

/-! ### The scaled bump -/

/-- The fixed bump: `1` on the closed unit ball, `0` outside the ball of radius `2`. -/
def unitBump : ContDiffBump (0 : Space) := ⟨1, 2, one_pos, one_lt_two⟩

theorem unitBump_fderiv_bound : ∃ K, ∀ x, ‖fderiv ℝ unitBump x‖ ≤ K :=
  ((unitBump.contDiff (n := 1)).continuous_fderiv one_ne_zero).bounded_above_of_compact_support
    (unitBump.hasCompactSupport.fderiv (𝕜 := ℝ))

theorem hasFDerivAt_bump_scale (c : ℝ) (x : Space) :
    HasFDerivAt (fun y : Space => unitBump (c • y))
      ((fderiv ℝ unitBump (c • x)).comp (c • ContinuousLinearMap.id ℝ Space)) x := by
  have hd : DifferentiableAt ℝ unitBump (c • x) :=
    (unitBump.contDiff (n := 1)).differentiable one_ne_zero _
  exact hd.hasFDerivAt.comp x ((hasFDerivAt_id x).const_smul c)

theorem bump_scale_eq_one {c : ℝ} (hc : 0 < c) {x : Space} (hx : ‖x‖ ≤ c⁻¹) :
    unitBump (c • x) = 1 := by
  refine unitBump.one_of_mem_closedBall ?_
  rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hc]
  have : c * ‖x‖ ≤ c * c⁻¹ := mul_le_mul_of_nonneg_left hx hc.le
  rw [mul_inv_cancel₀ hc.ne'] at this
  simpa [unitBump] using this

theorem bump_scale_eq_zero {c : ℝ} (hc : 0 < c) {x : Space} (hx : 2 * c⁻¹ ≤ ‖x‖) :
    unitBump (c • x) = 0 := by
  refine unitBump.zero_of_le_dist ?_
  rw [dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hc]
  have : c * (2 * c⁻¹) ≤ c * ‖x‖ := mul_le_mul_of_nonneg_left hx hc.le
  rw [mul_comm 2, ← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul] at this
  simpa [unitBump] using this

theorem fderiv_bump_scale_eq_zero {c : ℝ} (hc : 0 < c) {x : Space} (hx : ‖x‖ < c⁻¹) :
    fderiv ℝ (fun y : Space => unitBump (c • y)) x = 0 := by
  have hev : (fun y : Space => unitBump (c • y)) =ᶠ[𝓝 x] fun _ => 1 := by
    have hopen : IsOpen {y : Space | ‖y‖ < c⁻¹} := isOpen_lt continuous_norm continuous_const
    filter_upwards [hopen.mem_nhds hx] with y hy
    exact bump_scale_eq_one hc (le_of_lt hy)
  simp [hev.fderiv_eq]

theorem abs_fderiv_bump_scale_le {c K : ℝ} (hc : 0 < c) (hK : ∀ x, ‖fderiv ℝ unitBump x‖ ≤ K)
    (x v : Space) :
    |fderiv ℝ (fun y : Space => unitBump (c • y)) x v| ≤ c * K * ‖v‖ := by
  rw [(hasFDerivAt_bump_scale c x).fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply,
    ContinuousLinearMap.id_apply]
  rw [← Real.norm_eq_abs]
  calc ‖(fderiv ℝ unitBump (c • x)) (c • v)‖ ≤ ‖fderiv ℝ unitBump (c • x)‖ * ‖c • v‖ :=
        (fderiv ℝ unitBump (c • x)).le_opNorm _
    _ ≤ K * (c * ‖v‖) := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc]
        exact mul_le_mul_of_nonneg_right (hK _) (by positivity)
    _ = c * K * ‖v‖ := by ring

/-! ### The removable singularity -/

theorem C_nonneg_of_bound (hbd : ∀ x ≠ 0, ‖f x‖ ≤ C * ‖x‖⁻¹) : 0 ≤ C := by
  have hx : (coordinateVector 0 : Space) ≠ 0 := by
    intro h
    have := norm_coordinateVector 0
    rw [h, norm_zero] at this
    exact zero_ne_one this
  have := (norm_nonneg _).trans (hbd _ hx)
  rwa [norm_coordinateVector, inv_one, mul_one] at this

/-- The divergence pairing of `f` with a test vanishes: the cutoff argument. -/
theorem integral_divPairing_eq_zero (hf : ContDiffOn ℝ 1 f {0}ᶜ)
    (hdiv : ∀ x ≠ 0, pointDivergence f x = 0) (hbd : ∀ x ≠ 0, ‖f x‖ ≤ C * ‖x‖⁻¹)
    {φ : Space → ℝ} (hφ : IsSpatialTest φ) : ∫ x, divPairing f φ x = 0 := by
  have hfc : ContinuousOn f {0}ᶜ := hf.continuousOn
  obtain ⟨K, hK⟩ := unitBump_fderiv_bound
  obtain ⟨M, hM⟩ := hφ.smooth.continuous.bounded_above_of_compact_support hφ.compact
  obtain ⟨D, hD⟩ := (hφ.smooth.continuous_fderiv (by simp)).bounded_above_of_compact_support
    (hφ.compact.fderiv (𝕜 := ℝ))
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hD0 : 0 ≤ D := (norm_nonneg _).trans (hD 0)
  have hC0 : 0 ≤ C := C_nonneg_of_bound hbd
  have hφd : Differentiable ℝ φ := hφ.smooth.differentiable (by simp)
  -- the majorant `G`, integrable near the origin
  set G : Space → ℝ := fun x => 3 * (C * ‖x‖⁻¹) * (D + M * (2 * K * ‖x‖⁻¹)) with hG
  have hG0 : ∀ x, 0 ≤ G x := fun x => by positivity
  have hGmeas : Measurable G := by fun_prop
  have hGint : IntegrableOn G (ball (0 : Space) 1) := by
    refine integrableOn_ball_of_norm_le_rpow (α := 2) (C := 3 * C * (D + 2 * M * K))
      (by simp) (by simp only [finrank_euclideanSpace_fin]; norm_num) ?_
      hGmeas.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_ball,
      ae_restrict_of_ae (compl_mem_ae_iff.mpr (measure_singleton (0 : Space)))] with x hx hx0
    have hx0' : x ≠ 0 := hx0
    have hn : 0 < ‖x‖ := norm_pos_iff.2 hx0'
    have hn1 : ‖x‖ < 1 := by simpa using hx
    have hinv : ‖x‖⁻¹ ≤ ‖x‖⁻¹ * ‖x‖⁻¹ := by
      have : 1 ≤ ‖x‖⁻¹ := one_le_inv₀ hn |>.2 hn1.le
      nlinarith [inv_pos.2 hn]
    rw [Real.norm_eq_abs, abs_of_nonneg (hG0 x), Real.rpow_neg (norm_nonneg _),
      Real.rpow_two, sq, mul_inv]
    simp only [hG]
    nlinarith [mul_nonneg hC0 hD0, mul_nonneg (mul_nonneg hC0 hM0) hK0, inv_pos.2 hn]
  set G' : Space → ℝ := (ball (0 : Space) 1).indicator G with hG'def
  have hG' : Integrable G' := hGint.integrable_indicator measurableSet_ball
  -- the bound for each scale
  have hbound : ∀ n : ℕ, ‖∫ x, divPairing f φ x‖ ≤
      ∫ x in closedBall (0 : Space) (2 * ((n : ℝ) + 3)⁻¹), G' x := by
    intro n
    set c : ℝ := (n : ℝ) + 3 with hcdef
    have hc : 0 < c := by positivity
    have hc3 : 3 ≤ c := by simp [hcdef]
    set ψc : Space → ℝ := fun y => unitBump (c • y) with hψc
    set u : Space → ℝ := fun y => φ y * ψc y with hu
    set g : Space → ℝ := fun y => φ y - u y with hg
    have hψs : ContDiff ℝ ∞ ψc := unitBump.contDiff.comp (contDiff_const_smul c)
    have hus : ContDiff ℝ ∞ u := hφ.smooth.mul hψs
    have hgs : ContDiff ℝ ∞ g := hφ.smooth.sub hus
    have hucs : HasCompactSupport u := hφ.compact.mul_right
    have hgcs : HasCompactSupport g := hφ.compact.sub hucs
    have hψd : Differentiable ℝ ψc := hψs.differentiable (by simp)
    have hud : Differentiable ℝ u := hus.differentiable (by simp)
    have hg0 : ∀ x ∈ ball (0 : Space) c⁻¹, g x = 0 := by
      intro x hx
      have hx' : ‖x‖ ≤ c⁻¹ := le_of_lt (by simpa using hx)
      simp [hg, hu, hψc, bump_scale_eq_one hc hx']
    have hIg := integral_divPairing_eq_zero_of_vanish hf hdiv hgs hgcs (inv_pos.2 hc) hg0
    have hgder : ∀ i x, spatialTestDerivative i g x =
        spatialTestDerivative i φ x - spatialTestDerivative i u x := by
      intro i x
      have h := ((hφd x).hasFDerivAt.sub (hud x).hasFDerivAt).fderiv
      simp only [spatialTestDerivative]
      exact congrArg (fun L : Space →L[ℝ] ℝ => L (coordinateVector i)) h
    have hsplit : ∀ x, divPairing f φ x = divPairing f u x + divPairing f g x := by
      intro x
      simp only [divPairing, hgder, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    have hIu : Integrable (divPairing f u) :=
      integrable_divPairing hfc hbd (hus.continuous_fderiv (by simp)) hucs
    have hIg' : Integrable (divPairing f g) :=
      integrable_divPairing hfc hbd (hgs.continuous_fderiv (by simp)) hgcs
    have heq : ∫ x, divPairing f φ x = ∫ x, divPairing f u x := by
      rw [integral_congr_ae (Eventually.of_forall hsplit), integral_add hIu hIg', hIg, add_zero]
    -- pointwise majorant
    have hpt : ∀ x ≠ 0, ‖divPairing f u x‖ ≤
        (closedBall (0 : Space) (2 * c⁻¹)).indicator G' x := by
      intro x hx0
      have hn : 0 < ‖x‖ := norm_pos_iff.2 hx0
      by_cases hxb : ‖x‖ ≤ 2 * c⁻¹
      · have hxc : x ∈ closedBall (0 : Space) (2 * c⁻¹) := by simpa using hxb
        have hx1 : x ∈ ball (0 : Space) 1 := by
          have : 2 * c⁻¹ < 1 := by
            rw [← div_eq_mul_inv, div_lt_one hc]
            linarith
          simpa using lt_of_le_of_lt hxb this
        rw [indicator_of_mem hxc, hG'def, indicator_of_mem hx1]
        -- derivative of `u`
        have hdu : ∀ i : Fin 3, |spatialTestDerivative i u x| ≤ D + M * (2 * K * ‖x‖⁻¹) := by
          intro i
          have hψb : |fderiv ℝ ψc x (coordinateVector i)| ≤ 2 * K * ‖x‖⁻¹ := by
            by_cases hsmall : ‖x‖ < c⁻¹
            · rw [show fderiv ℝ ψc x = 0 from fderiv_bump_scale_eq_zero hc hsmall]
              simp only [ContinuousLinearMap.zero_apply, abs_zero]
              positivity
            · have h1 := abs_fderiv_bump_scale_le hc hK x (coordinateVector i)
              rw [norm_coordinateVector, mul_one] at h1
              refine h1.trans ?_
              have hcx : c * ‖x‖ ≤ 2 := by
                have := mul_le_mul_of_nonneg_left hxb hc.le
                rwa [mul_comm 2, ← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul] at this
              have : c ≤ 2 * ‖x‖⁻¹ := by
                rw [← div_eq_mul_inv, le_div_iff₀ hn]
                exact hcx
              nlinarith
          have hder : spatialTestDerivative i u x =
              φ x * fderiv ℝ ψc x (coordinateVector i) +
                ψc x * fderiv ℝ φ x (coordinateVector i) := by
            simp only [spatialTestDerivative, hu]
            rw [fderiv_fun_mul (hφd x) (hψd x)]
            simp [smul_eq_mul]
          rw [hder]
          have hψ1 : |ψc x| ≤ 1 := by
            rw [abs_of_nonneg unitBump.nonneg]
            exact unitBump.le_one
          have hφM : |φ x| ≤ M := by simpa [Real.norm_eq_abs] using hM x
          have hφD : |fderiv ℝ φ x (coordinateVector i)| ≤ D := by
            simpa [spatialTestDerivative] using
              (abs_spatialTestDerivative_le φ i x).trans (hD x)
          calc |φ x * fderiv ℝ ψc x (coordinateVector i) +
                ψc x * fderiv ℝ φ x (coordinateVector i)|
              ≤ |φ x| * |fderiv ℝ ψc x (coordinateVector i)| +
                  |ψc x| * |fderiv ℝ φ x (coordinateVector i)| := by
                rw [← abs_mul, ← abs_mul]
                exact abs_add_le _ _
            _ ≤ M * (2 * K * ‖x‖⁻¹) + 1 * D := by
                gcongr
            _ = D + M * (2 * K * ‖x‖⁻¹) := by ring
        have hfx : ‖f x‖ ≤ C * ‖x‖⁻¹ := hbd x hx0
        calc ‖divPairing f u x‖ ≤ ∑ i : Fin 3, ‖(f x) i * spatialTestDerivative i u x‖ :=
              norm_sum_le _ _
          _ ≤ ∑ _i : Fin 3, (C * ‖x‖⁻¹) * (D + M * (2 * K * ‖x‖⁻¹)) := by
              refine Finset.sum_le_sum fun i _ => ?_
              rw [norm_mul, Real.norm_eq_abs (spatialTestDerivative i u x)]
              exact mul_le_mul ((PiLp.norm_apply_le (f x) i).trans hfx) (hdu i)
                (abs_nonneg _) (by positivity)
          _ = G x := by simp [hG]; ring
      · have hxc : x ∉ closedBall (0 : Space) (2 * c⁻¹) := by simpa using hxb
        rw [indicator_of_notMem hxc]
        have hev : u =ᶠ[𝓝 x] fun _ => 0 := by
          have hopen : IsOpen {y : Space | 2 * c⁻¹ < ‖y‖} :=
            isOpen_lt continuous_const continuous_norm
          filter_upwards [hopen.mem_nhds (show 2 * c⁻¹ < ‖x‖ from lt_of_not_ge hxb)] with y hy
          simp [hu, hψc, bump_scale_eq_zero hc (le_of_lt hy)]
        simp [divPairing, spatialTestDerivative, hev.fderiv_eq]
    have hmaj : Integrable ((closedBall (0 : Space) (2 * c⁻¹)).indicator G') :=
      hG'.indicator measurableSet_closedBall
    rw [heq, ← integral_indicator measurableSet_closedBall]
    refine norm_integral_le_of_norm_le hmaj ?_
    filter_upwards [compl_mem_ae_iff.mpr (measure_singleton (0 : Space))] with x hx
    exact hpt x hx
  -- the radii tend to zero, hence so do the measures and the integrals
  have hr : Tendsto (fun n : ℕ => 2 * ((n : ℝ) + 3)⁻¹) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => ((n : ℝ) + 3)) atTop atTop :=
      tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
    simpa using (tendsto_inv_atTop_zero.comp h1).const_mul 2
  have hmeas : Tendsto (fun n : ℕ => volume (closedBall (0 : Space) (2 * ((n : ℝ) + 3)⁻¹)))
      atTop (𝓝 0) := by
    have heqv : ∀ n : ℕ, volume (closedBall (0 : Space) (2 * ((n : ℝ) + 3)⁻¹)) =
        ENNReal.ofReal ((2 * ((n : ℝ) + 3)⁻¹) ^ Module.finrank ℝ Space) *
          volume (ball (0 : Space) 1) := fun n =>
      Measure.addHaar_closedBall volume 0 (by positivity)
    simp_rw [heqv]
    have h0 : Tendsto (fun n : ℕ => ENNReal.ofReal ((2 * ((n : ℝ) + 3)⁻¹) ^
        Module.finrank ℝ Space)) atTop (𝓝 0) := by
      have := ENNReal.tendsto_ofReal ((hr.pow (Module.finrank ℝ Space)))
      simpa using this
    simpa using ENNReal.Tendsto.mul_const h0 (Or.inr measure_ball_lt_top.ne)
  have hlim := hG'.tendsto_setIntegral_nhds_zero hmeas
  have hle : ‖∫ x, divPairing f φ x‖ ≤ 0 := ge_of_tendsto' hlim hbound
  exact norm_le_zero_iff.1 hle

/-- **B0687 (solenoidal clause), T25.7.** A field on `ℝ³` that is `C¹` and divergence free
off the origin and satisfies `|f(x)| ≤ C|x|⁻¹` is distributionally solenoidal on all of
`ℝ³` (tex 5863–5864): no condition at the origin is needed. -/
theorem isSolenoidal_of_punctured (hf : ContDiffOn ℝ 1 f {0}ᶜ)
    (hdiv : ∀ x ≠ 0, pointDivergence f x = 0) (hbd : ∀ x ≠ 0, ‖f x‖ ≤ C * ‖x‖⁻¹) :
    IsSolenoidal f where
  integrable φ hφ :=
    integrable_divPairing hf.continuousOn hbd (hφ.smooth.continuous_fderiv (by simp)) hφ.compact
  identity φ hφ := integral_divPairing_eq_zero hf hdiv hbd hφ

end

end UnforcedLeray.PhaseSpace
