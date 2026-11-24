import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.SubKF3
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.Proofs.KF.KF3.PresSmooth
import UnforcedLeray.Analysis.Pressure.Spatial
import UnforcedLeray.Analysis.Pressure.NewtonKernel
import Mathlib.Analysis.Calculus.ContDiff.Convolution

/-!
# `kf3PresGrad : KF3PresGrad` (source 117-120, 3617-3618)

`(∇ₓ p)_i(x, τ) = Σ_j (∂_jN ⋆ ∂_i g_j(·, τ))(x)` with `g_j = (div M)_j(·, τ)`.
Route: `gradX p (x,τ) i = fderiv p (x,τ) (e_i, 0)` (`B0226.inner_gradX`); the slice derivative
`fderiv (p(·, τ)) x e_i`; `p(·, τ) = Σ_j newtonComponent j g_j` by definition; each
`newtonComponent j g_j = ∂_jN ⋆ g_j` is differentiable with derivative
`HasCompactSupport.hasFDerivAt_convolution_right` (`g_j` smooth, compactly supported) and
`convolution_precompR_apply` evaluates it on `e_i`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization

/-- The slice derivative of a smooth function of `(x, τ)` in the `x` variable. -/
theorem kf3g_slice_fderiv (F : Space × ℝ → ℝ) (hF : ContDiff ℝ ∞ F) (x : Space) (τ : ℝ)
    (v : Space) :
    fderiv ℝ (fun x' : Space => F (x', τ)) x v = fderiv ℝ F (x, τ) (v, 0) := by
  have hd : HasFDerivAt (fun x' : Space => (x', τ))
      ((ContinuousLinearMap.id ℝ Space).prod 0) x :=
    (hasFDerivAt_id x).prodMk (hasFDerivAt_const τ x)
  have hFd : HasFDerivAt F (fderiv ℝ F (x, τ)) (x, τ) :=
    (hF.differentiable (by simp) (x, τ)).hasFDerivAt
  have hc := hFd.comp x hd
  show fderiv ℝ (F ∘ (fun x' : Space => (x', τ))) x v = _
  rw [hc.fderiv]
  simp

/-- The Newtonian component of a smooth compactly supported function has the expected
derivative: `∂_v (∂_jN ⋆ g) = ∂_jN ⋆ (∂_v g)`. -/
theorem kf3g_newton_hasFDerivAt (j : Fin 3) {g : Space → ℝ} (hg : ContDiff ℝ ∞ g)
    (hc : HasCompactSupport g) (x : Space) :
    HasFDerivAt (fun x' : Space => UnforcedLeray.PressureAnalysis.newtonComponent j g x')
      (MeasureTheory.convolution (UnforcedLeray.PressureAnalysis.newtonGradientKernel j)
        (fderiv ℝ g) ((ContinuousLinearMap.lsmul ℝ ℝ).precompR Space) volume x) x := by
  have hg1 : ContDiff ℝ 1 g := hg.of_le (by simp)
  have h1 := hc.hasFDerivAt_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ)
    (UnforcedLeray.PressureAnalysis.newtonGradientKernel_locallyIntegrable j) hg1 x
  have hfun : (fun x' : Space => UnforcedLeray.PressureAnalysis.newtonComponent j g x') =
      MeasureTheory.convolution (UnforcedLeray.PressureAnalysis.newtonGradientKernel j) g
        (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
    funext x'
    rw [kf3p_conv_eq]
    rfl
  rw [hfun]
  exact h1

/-- Evaluation of the derivative on a coordinate vector. -/
theorem kf3g_newton_apply (j : Fin 3) {g : Space → ℝ} (hg : ContDiff ℝ ∞ g)
    (hc : HasCompactSupport g) (x v : Space) :
    MeasureTheory.convolution (UnforcedLeray.PressureAnalysis.newtonGradientKernel j)
        (fderiv ℝ g) ((ContinuousLinearMap.lsmul ℝ ℝ).precompR Space) volume x v =
      UnforcedLeray.PressureAnalysis.newtonComponent j (fun z => fderiv ℝ g z v) x := by
  have hg1 : ContDiff ℝ 1 g := hg.of_le (by simp)
  rw [convolution_precompR_apply (ContinuousLinearMap.lsmul ℝ ℝ)
    (UnforcedLeray.PressureAnalysis.newtonGradientKernel_locallyIntegrable j)
    (hc.fderiv ℝ) (hg1.continuous_fderiv one_ne_zero) x v]
  rw [kf3p_conv_eq]
  rfl

/-- The `i`-th partial derivative of `cartDiv M` vanishes outside the support ball. -/
theorem kf3g_cartDiv_far (P : ℝ) (M : Space × ℝ → Matrix (Fin 3) (Fin 3) ℝ)
    (hM : IsOuterTest P M) (r : ℝ) (hr : ∀ y : Space × ℝ, M y ≠ 0 → ‖y.1‖ ≤ r)
    (x : Space) (τ : ℝ) (hx : r < ‖x‖) (i : Fin 3) : cartDiv M (x, τ) i = 0 := by
  have hev : ∀ j : Fin 3, (fun x' : Space => M (x', τ) i j) =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
    intro j
    filter_upwards [(isOpen_lt (continuous_const (y := r)) continuous_norm :
      IsOpen {x'' : Space | r < ‖x''‖}).mem_nhds hx] with x' hx''
    have hx3 : r < ‖x'‖ := hx''
    have hM0 : M (x', τ) = 0 := by
      by_contra hne
      have h1 := hr (x', τ) hne
      have h2 : ‖x'‖ ≤ r := h1
      linarith
    simp [hM0]
  simp only [cartDiv, PiLp.toLp_apply]
  refine Finset.sum_eq_zero (fun j _ => ?_)
  rw [(hev j).fderiv_eq]
  simp

/-- **Leaf: the pressure gradient is the Newtonian convolution of `∇ div M`** (source 117-120,
3617-3618). -/
theorem kf3PresGrad : KF3PresGrad := by
  intro P M hM x τ i
  obtain ⟨r, hr⟩ := hM.bounded
  have hS : ContDiff ℝ ∞ (lerayPres M) := kf3PresSmooth P M hM
  -- the slice `τ` of the Leray pressure is the sum of Newtonian components
  have hgj : ∀ j : Fin 3, ContDiff ℝ ∞ (fun z : Space => cartDiv M (z, τ) j) := by
    intro j
    exact (kf3p_phi_smooth P M hM j).comp (contDiff_const.prodMk contDiff_id)
  have hcs : ∀ j : Fin 3, HasCompactSupport (fun z : Space => cartDiv M (z, τ) j) := by
    intro j
    refine HasCompactSupport.intro (isCompact_closedBall (0 : Space) r) (fun z hz => ?_)
    have hz' : r < ‖z‖ := by
      have : ¬ (‖z‖ ≤ r) := fun h => hz (mem_closedBall_zero_iff.2 h)
      exact not_le.1 this
    exact kf3g_cartDiv_far P M hM r hr z τ hz' j
  have hD : ∀ j : Fin 3, HasFDerivAt
      (fun x' : Space => UnforcedLeray.PressureAnalysis.newtonComponent j
        (fun z => cartDiv M (z, τ) j) x')
      (MeasureTheory.convolution (UnforcedLeray.PressureAnalysis.newtonGradientKernel j)
        (fderiv ℝ (fun z : Space => cartDiv M (z, τ) j))
        ((ContinuousLinearMap.lsmul ℝ ℝ).precompR Space) volume x) x :=
    fun j => kf3g_newton_hasFDerivAt j (hgj j) (hcs j) x
  have hsum : HasFDerivAt (fun x' : Space => ∑ j : Fin 3,
      UnforcedLeray.PressureAnalysis.newtonComponent j (fun z => cartDiv M (z, τ) j) x')
      (∑ j : Fin 3, MeasureTheory.convolution (UnforcedLeray.PressureAnalysis.newtonGradientKernel j)
        (fderiv ℝ (fun z : Space => cartDiv M (z, τ) j))
        ((ContinuousLinearMap.lsmul ℝ ℝ).precompR Space) volume x) x :=
    HasFDerivAt.sum (u := Finset.univ) (fun j _ => hD j)
  have hslice : (fun x' : Space => lerayPres M (x', τ)) =
      fun x' : Space => ∑ j ∈ Finset.univ, UnforcedLeray.PressureAnalysis.newtonComponent j
        (fun z => cartDiv M (z, τ) j) x' := rfl
  have hcomp : fderiv ℝ (fun x' : Space => lerayPres M (x', τ)) x
      (UnforcedLeray.coordinateVector i) =
      ∑ j : Fin 3, UnforcedLeray.PressureAnalysis.newtonComponent j
        (fun z => fderiv ℝ (fun x' : Space => cartDiv M (x', τ) j) z
          (UnforcedLeray.coordinateVector i)) x := by
    rw [hslice, hsum.fderiv, ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    exact kf3g_newton_apply j (hgj j) (hcs j) x (UnforcedLeray.coordinateVector i)
  rw [← hcomp, kf3g_slice_fderiv (lerayPres M) hS x τ]
  have hgrad : UnforcedLeray.B0226.gradX (lerayPres M) (x, τ) i =
      inner ℝ (UnforcedLeray.B0226.gradX (lerayPres M) (x, τ)) (UnforcedLeray.coordinateVector i) := by
    simp [UnforcedLeray.coordinateVector, EuclideanSpace.inner_single_right]
  rw [hgrad, UnforcedLeray.B0226.inner_gradX]

end UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization
