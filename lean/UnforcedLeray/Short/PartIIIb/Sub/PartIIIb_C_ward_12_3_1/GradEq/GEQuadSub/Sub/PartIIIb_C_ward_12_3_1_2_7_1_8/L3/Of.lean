import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GEQuadSub.Sub.PartIIIb_C_ward_12_3_1_2_7_1_8
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Topology.Bases

/-!
# `SliceIdAll` from the slice weak identity

Source `the November 2 reference manuscript`
lines 2562-2564 (local Friedrichs argument in `y`), phase tests 2525-2531.

`SliceWeakAeStmt` is the statement of `slice_weak_ae` (task `PartIII-b:C/ward/12/3/1/2/7/1/8/2`):
the weak identity `∂_j f = Df`, tested against `θ(τ) ψ(y)`, holds slice by slice for a.e. `τ`.
`slice_id_all_of` derives `SliceIdAll`:
* a.e. slice of an `L^1_loc` function is locally integrable (Fubini on each `(0,P] × B(0,N)`);
* the slice identity at each point `q` of a countable dense set, from `ψ_q(z) = ρ(q - z)` and the
  change of variables `t = q - z`;
* both sides are convolutions of a locally integrable slice with a continuous compactly supported
  kernel (`HasCompactSupport.continuous_convolution_left`), so the identity extends to all `y`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.SliceIdAllOf

/-- The statement of `slice_weak_ae` (source 2562-2564, phase tests 2525-2531). -/
def SliceWeakAeStmt : Prop :=
  ∀ (P : ℝ) [Fact (0 < P)] (j : Fin 3) (f Df : ℝ × UnforcedLeray.Space → ℂ),
    MemLpLoc P f 1 → MemLpLoc P Df 1 → WeakDyS P j f Df →
    ∀ ψ : UnforcedLeray.Space → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      ∀ᵐ τ ∂(volume.restrict (Ioc (0 : ℝ) P)),
        ∫ z, fderiv ℝ ψ z (UnforcedLeray.coordinateVector j) * f (τ, z) =
          -∫ z, (ψ z : ℂ) * Df (τ, z)

/-- A.e. slice of an `L^1_loc` function on the cell is locally integrable. -/
theorem ae_slice_locallyIntegrable (P : ℝ) (g : ℝ × UnforcedLeray.Space → ℂ)
    (hg : MemLpLoc P g 1) :
    ∀ᵐ τ ∂(volume.restrict (Ioc (0 : ℝ) P)),
      LocallyIntegrable (fun y : UnforcedLeray.Space => g (τ, y)) volume := by
  have hae : ∀ᵐ τ ∂(volume.restrict (Ioc (0 : ℝ) P)), ∀ N : ℕ,
      Integrable (fun y : UnforcedLeray.Space => g (τ, y))
        (volume.restrict (Metric.closedBall 0 (N : ℝ))) := by
    rw [ae_all_iff]
    intro N
    exact Integrable.prod_right_ae (memLp_one_iff_integrable.1 (hg (N : ℝ)))
  filter_upwards [hae] with τ hτ
  intro x
  obtain ⟨N, hN⟩ := exists_nat_gt ‖x‖
  have hxN : x ∈ Metric.ball (0 : UnforcedLeray.Space) (N : ℝ) := by
    rw [mem_ball_zero_iff]
    exact hN
  exact ⟨Metric.ball 0 (N : ℝ), IsOpen.mem_nhds Metric.isOpen_ball hxN,
    IntegrableOn.mono_set (hτ N) Metric.ball_subset_closedBall⟩

/-- The complexified kernel has the real derivative, coerced. -/
theorem fderiv_ofReal_apply (ρ : UnforcedLeray.Space → ℝ) (hρ : Differentiable ℝ ρ)
    (t v : UnforcedLeray.Space) :
    fderiv ℝ (fun s : UnforcedLeray.Space => (ρ s : ℂ)) t v = ((fderiv ℝ ρ t v : ℝ) : ℂ) := by
  have h := (Complex.ofRealCLM.hasFDerivAt (x := ρ t)).comp t (hρ t).hasFDerivAt
  have h' : HasFDerivAt (fun s : UnforcedLeray.Space => (ρ s : ℂ))
      (Complex.ofRealCLM.comp (fderiv ℝ ρ t)) t := h
  rw [h'.fderiv]
  simp

/-- Derivative of the reflected kernel `z ↦ ρ(q - z)`. -/
theorem fderiv_reflect_apply (ρ : UnforcedLeray.Space → ℝ) (hρ : Differentiable ℝ ρ)
    (q z v : UnforcedLeray.Space) :
    fderiv ℝ (fun x : UnforcedLeray.Space => ρ (q - x)) z v = -fderiv ℝ ρ (q - z) v := by
  have h1 : HasFDerivAt (fun x : UnforcedLeray.Space => q - x)
      (-ContinuousLinearMap.id ℝ UnforcedLeray.Space) z :=
    (hasFDerivAt_id z).const_sub q
  have h : HasFDerivAt (fun x : UnforcedLeray.Space => ρ (q - x))
      ((fderiv ℝ ρ (q - z)).comp (-ContinuousLinearMap.id ℝ UnforcedLeray.Space)) z :=
    (hρ (q - z)).hasFDerivAt.comp z h1
  rw [h.fderiv]
  simp

theorem slice_id_all_of (h : SliceWeakAeStmt) : SliceIdAll := by
  intro P _ j ρ hρs hρc f Df hf hDf hW
  have hρd : Differentiable ℝ ρ := hρs.differentiable (by simp)
  set e := UnforcedLeray.coordinateVector j with he
  set K : UnforcedLeray.Space → ℂ := fun t => (ρ t : ℂ) with hK
  set K' : UnforcedLeray.Space → ℂ := fun t => fderiv ℝ K t e with hK'
  have hKC : ContDiff ℝ 1 K := Complex.ofRealCLM.contDiff.comp (hρs.of_le (by simp))
  have hKc : HasCompactSupport K := hρc.comp_left Complex.ofReal_zero
  have hK'c : HasCompactSupport K' := hKc.fderiv_apply (𝕜 := ℝ) e
  have hK'cont : Continuous K' := (hKC.continuous_fderiv (by simp)).clm_apply continuous_const
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense UnforcedLeray.Space
  -- the identity at each point of the countable dense set
  have hq : ∀ q ∈ D, ∀ᵐ τ ∂(volume.restrict (Ioc (0 : ℝ) P)),
      ∫ t, K' t * f (τ, q - t) = ∫ t, K t * Df (τ, q - t) := by
    intro q _
    set ψ : UnforcedLeray.Space → ℝ := fun z => ρ (q - z) with hψ
    have hψs : ContDiff ℝ ∞ ψ := hρs.comp (contDiff_const.sub contDiff_id)
    have hψc : HasCompactSupport ψ := hρc.comp_homeomorph (Homeomorph.subLeft q)
    filter_upwards [h P j f Df hf hDf hW ψ hψs hψc] with τ hτ
    have e1 : ∫ t, K' t * f (τ, q - t) =
        ∫ z, -(((fderiv ℝ ψ z e : ℝ) : ℂ) * f (τ, z)) := by
      rw [← integral_sub_left_eq_self (fun t => K' t * f (τ, q - t)) volume q]
      refine integral_congr_ae (Eventually.of_forall fun z => ?_)
      simp only [hK', hK, fderiv_ofReal_apply ρ hρd, hψ, fderiv_reflect_apply ρ hρd,
        sub_sub_cancel, Complex.ofReal_neg, neg_mul, neg_neg]
    have e2 : ∫ t, K t * Df (τ, q - t) = ∫ z, (ψ z : ℂ) * Df (τ, z) := by
      rw [← integral_sub_left_eq_self (fun t => K t * Df (τ, q - t)) volume q]
      refine integral_congr_ae (Eventually.of_forall fun z => ?_)
      simp only [hK, hψ, sub_sub_cancel]
    rw [e1, e2, integral_neg, hτ, neg_neg]
  have hall : ∀ᵐ τ ∂(volume.restrict (Ioc (0 : ℝ) P)), ∀ q ∈ D,
      ∫ t, K' t * f (τ, q - t) = ∫ t, K t * Df (τ, q - t) := (ae_ball_iff hDc).2 hq
  filter_upwards [ae_slice_locallyIntegrable P f hf, ae_slice_locallyIntegrable P Df hDf, hall]
    with τ h1 h2 h3
  refine ⟨h1, ?_⟩
  have c1 : Continuous (fun y : UnforcedLeray.Space => ∫ t, K' t * f (τ, y - t)) := by
    have := hK'c.continuous_convolution_left (ContinuousLinearMap.mul ℝ ℂ) hK'cont h1
    convert this using 1
    funext y
    rw [convolution_def]
    simp only [ContinuousLinearMap.mul_apply']
  have c2 : Continuous (fun y : UnforcedLeray.Space => ∫ t, K t * Df (τ, y - t)) := by
    have := hKc.continuous_convolution_left (ContinuousLinearMap.mul ℝ ℂ) hKC.continuous h2
    convert this using 1
    funext y
    rw [convolution_def]
    simp only [ContinuousLinearMap.mul_apply']
  intro y
  exact congrFun (Continuous.ext_on hDd c1 c2 fun q hq => h3 q hq) y

end UnforcedLeray.Short.PartIIIb.Concrete.SliceIdAllOf
