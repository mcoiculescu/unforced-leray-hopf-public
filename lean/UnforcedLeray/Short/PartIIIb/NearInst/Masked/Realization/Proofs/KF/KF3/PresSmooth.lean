import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.SubKF3
import UnforcedLeray.Analysis.Pressure.Spatial
import UnforcedLeray.Analysis.Pressure.NewtonKernel

/-!
# `kf3PresSmooth : KF3PresSmooth` (source 117-120, 3594-3596)

The Leray pressure `lerayPres M` of a smooth outer tensor is `C^∞` jointly in `(x, τ)`.
Route: `newtonComponent i f x = (newtonGradientKernel i ⋆ f)(x)` (substitution `y ↦ x - y`);
`(τ, x) ↦ cartDiv M (x, τ) i` is `C^∞` (partial derivatives of a smooth tensor, through the chain rule
along `x ↦ (x, τ)`); it vanishes for `‖x‖ > r` (`IsOuterTest.bounded`); then
`contDiffOn_convolution_right_with_param` (parameter `τ`, `s = univ`, `k = closedBall 0 r`) and
summation over the three components.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization

/-- The partial derivative in `x` of a smooth tensor entry, along `(x, τ)`. -/
theorem kf3p_partial_eq (P : ℝ) (M : Space × ℝ → Matrix (Fin 3) (Fin 3) ℝ) (hM : IsOuterTest P M)
    (i j : Fin 3) (x : Space) (τ : ℝ) (v : Space) :
    fderiv ℝ (fun x' : Space => M (x', τ) i j) x v =
      fderiv ℝ (fun y : Space × ℝ => M y i j) (x, τ) (v, 0) := by
  have hd : HasFDerivAt (fun x' : Space => (x', τ))
      ((ContinuousLinearMap.id ℝ Space).prod 0) x :=
    (hasFDerivAt_id x).prodMk (hasFDerivAt_const τ x)
  have hMd : HasFDerivAt (fun y : Space × ℝ => M y i j)
      (fderiv ℝ (fun y : Space × ℝ => M y i j) (x, τ)) (x, τ) :=
    ((hM.smooth i j).differentiable (by simp) (x, τ)).hasFDerivAt
  have hc := hMd.comp x hd
  show fderiv ℝ ((fun y : Space × ℝ => M y i j) ∘ (fun x' : Space => (x', τ))) x v = _
  rw [hc.fderiv]
  simp

theorem kf3p_phi_smooth (P : ℝ) (M : Space × ℝ → Matrix (Fin 3) (Fin 3) ℝ) (hM : IsOuterTest P M)
    (i : Fin 3) : ContDiff ℝ ∞ (fun q : ℝ × Space => cartDiv M (q.2, q.1) i) := by
  have hD : ∀ j : Fin 3, ContDiff ℝ ∞ (fderiv ℝ (fun y : Space × ℝ => M y i j)) :=
    fun j => (hM.smooth i j).fderiv_right (m := ∞) (by simp)
  have hform : ∀ q : ℝ × Space, cartDiv M (q.2, q.1) i =
      ∑ j : Fin 3, fderiv ℝ (fun y : Space × ℝ => M y i j) (q.2, q.1)
        (UnforcedLeray.coordinateVector j, 0) := by
    intro q
    simp only [cartDiv, PiLp.toLp_apply]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    exact kf3p_partial_eq P M hM i j q.2 q.1 (UnforcedLeray.coordinateVector j)
  have hsw : ContDiff ℝ ∞ (fun q : ℝ × Space => (q.2, q.1)) :=
    contDiff_snd.prodMk contDiff_fst
  have hterm : ∀ j : Fin 3, ContDiff ℝ ∞ (fun q : ℝ × Space =>
      fderiv ℝ (fun y : Space × ℝ => M y i j) (q.2, q.1)
        (UnforcedLeray.coordinateVector j, 0)) := fun j =>
    ((hD j).comp hsw).clm_apply contDiff_const
  simp only [hform]
  exact ContDiff.sum (fun j _ => hterm j)

theorem kf3p_conv_eq (K f : Space → ℝ) (x : Space) :
    MeasureTheory.convolution K f (ContinuousLinearMap.lsmul ℝ ℝ) volume x =
      ∫ y : Space, K (x - y) * f y := by
  unfold MeasureTheory.convolution
  simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  have h := integral_sub_left_eq_self (μ := volume) (fun t : Space => K t * f (x - t)) x
  simp only [sub_sub_cancel] at h
  exact h.symm

/-- **Leaf: smoothness of the Leray pressure** (source 117-120, 3594-3596). -/
theorem kf3PresSmooth : KF3PresSmooth := by
  intro P M hM
  obtain ⟨r, hr⟩ := hM.bounded
  have hconv : ∀ i : Fin 3, ContDiffOn ℝ ∞ (fun q : ℝ × Space =>
      MeasureTheory.convolution (UnforcedLeray.PressureAnalysis.newtonGradientKernel i)
        ((fun τ x => cartDiv M (x, τ) i) q.1) (ContinuousLinearMap.lsmul ℝ ℝ) volume q.2)
      (univ ×ˢ univ) := by
    intro i
    refine contDiffOn_convolution_right_with_param
      (f := UnforcedLeray.PressureAnalysis.newtonGradientKernel i)
      (g := fun τ x => cartDiv M (x, τ) i) (μ := volume) (ContinuousLinearMap.lsmul ℝ ℝ) (isOpen_univ : IsOpen (univ : Set ℝ))
      (isCompact_closedBall (0 : Space) r) ?_
      (UnforcedLeray.PressureAnalysis.newtonGradientKernel_locallyIntegrable i) ?_
    · intro τ x _ hx
      have hx' : r < ‖x‖ := by
        have : ¬ (‖x‖ ≤ r) := fun h => hx (mem_closedBall_zero_iff.2 h)
        exact not_le.1 this
      have hev : ∀ j : Fin 3, (fun x' : Space => M (x', τ) i j) =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
        intro j
        filter_upwards [(isOpen_lt (continuous_const (y := r)) continuous_norm : IsOpen {x'' : Space | r < ‖x''‖}).mem_nhds hx'] with x' hx''
        have hx3 : r < ‖x'‖ := hx''
        have hM0 : M (x', τ) = 0 := by
          by_contra hne
          have h1 := hr (x', τ) hne
          have h2 : ‖x'‖ ≤ r := h1
          linarith
        simp [hM0]
      have hcoord : cartDiv M (x, τ) i = 0 := by
        simp only [cartDiv, PiLp.toLp_apply]
        refine Finset.sum_eq_zero (fun j _ => ?_)
        rw [(hev j).fderiv_eq]
        simp
      simp [hcoord]
    · exact (kf3p_phi_smooth P M hM i).contDiffOn
  have hsum : ContDiffOn ℝ ∞ (fun q : ℝ × Space => ∑ i : Fin 3,
      MeasureTheory.convolution (UnforcedLeray.PressureAnalysis.newtonGradientKernel i)
        ((fun τ x => cartDiv M (x, τ) i) q.1) (ContinuousLinearMap.lsmul ℝ ℝ) volume q.2)
      (univ ×ˢ univ) :=
    ContDiffOn.sum (fun i _ => hconv i)
  rw [Set.univ_prod_univ] at hsum
  have hU := contDiffOn_univ.1 hsum
  have hEq : lerayPres M = (fun q : ℝ × Space => ∑ i : Fin 3,
      MeasureTheory.convolution (UnforcedLeray.PressureAnalysis.newtonGradientKernel i)
        ((fun τ x => cartDiv M (x, τ) i) q.1) (ContinuousLinearMap.lsmul ℝ ℝ) volume q.2) ∘
        (fun y : Space × ℝ => (y.2, y.1)) := by
    funext y
    simp only [Function.comp, lerayPres]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [kf3p_conv_eq]
    rfl
  rw [hEq]
  exact hU.comp (contDiff_snd.prodMk contDiff_fst)

end UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization
