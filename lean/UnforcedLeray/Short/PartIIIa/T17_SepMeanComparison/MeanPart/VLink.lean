import UnforcedLeray.Short.PartIIIa.T17_SepMeanComparison.MeanPart.VMain

/-!
# Mean part helper: `sepVmu0` is differentiable, with the derivative as a product integral (T17/2)
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- The directional derivative integrand of `V_{μ,0}`. -/
def mpVd (μ : ℂ) (G : ℝ × ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ) (p : ℝ × ((ℝ × ℝ) × ℝ)) (x v : Space)
    (i : Fin 3) : ℂ :=
  -2 * ((p.1 : ℂ) ^ (2 * μ + 2) * ∑ j : Fin 3, ∑ k : Fin 3,
    ((iteratedFDeriv ℝ 2 (fun x => heatLerayK0 i j x) (x - p.1 • mpV3 p.2)
      ![v, coordinateVector k] : ℝ) : ℂ) * ((G p.2.1 p.2.2 j k : ℝ) : ℂ))

theorem mpVF'_apply (μ : ℂ) (G : ℝ × ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ) (p : ℝ × ((ℝ × ℝ) × ℝ))
    (x v : Space) (i : Fin 3) : mpVF' μ G p x i v = mpVd μ G p x v i := by
  simp only [mpVF', mpVd, smul_apply, sum_apply, ContinuousLinearMap.comp_apply,
    Complex.ofRealCLM_apply, smul_eq_mul, ContinuousLinearMap.apply_apply, iteratedFDeriv_two_apply]
  congr 2
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  simp
  ring

theorem mp_V_link (μ : ℂ) (G : ℝ × ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ) (x : Space) (i : Fin 3)
    (h : Integrable (fun p => mpVF μ G p x i) mpRho2) :
    sepVmu0 μ G x i = ∫ p, mpVF μ G p x i ∂mpRho2 := by
  unfold mpVF at h ⊢
  rw [integral_const_mul]
  have h' : Integrable (fun p : ℝ × ((ℝ × ℝ) × ℝ) => (p.1 : ℂ) ^ (2 * μ + 2) * ∑ j : Fin 3, ∑ k : Fin 3,
      ((fderiv ℝ (fun x => heatLerayK0 i j x) (x - p.1 • mpV3 p.2) (coordinateVector k) : ℝ) : ℂ) *
        ((G p.2.1 p.2.2 j k : ℝ) : ℂ)) mpRho2 := by
    have := h.const_mul (-2 : ℂ)⁻¹
    refine this.congr (Eventually.of_forall fun p => ?_)
    simp only
    rw [← mul_assoc, inv_mul_cancel₀ (by norm_num), one_mul]
  unfold mpRho2
  rw [integral_prod _ h']
  unfold sepVmu0
  congr 1
  refine integral_congr_ae ?_
  filter_upwards with l
  exact (integral_const_mul _ _).symm

theorem mp_V_deriv (hK : SepKernelBounds) (μ : ℂ) (hμ : -(1 / 4) < μ.re) (ρo ρi : ℝ) (hρo : 0 ≤ ρo)
    (hρ : ρo < ρi) (G : ℝ × ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ)
    (hGm : ∀ i j, Measurable fun w : (ℝ × ℝ) × ℝ => G w.1 w.2 i j)
    (hGs : ∀ x' Y, ρo < Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2) → G x' Y = 0)
    (hint : Integrable (fun w : (ℝ × ℝ) × ℝ => tensorNorm (G w.1 w.2)) volume)
    (xo : Space) (hxo : ρi ≤ Real.sqrt (xo 0 ^ 2 + xo 1 ^ 2)) :
    DifferentiableAt ℝ (sepVmu0 μ G) xo ∧
      ∀ (v : Space) (i : Fin 3), fderiv ℝ (sepVmu0 μ G) xo v i = ∫ p, mpVd μ G p xo v i ∂mpRho2 ∧
        Integrable (fun p => mpVd μ G p xo v i) mpRho2 := by
  have hD1pos : 0 < (ρi - ρo) / 2 := by linarith
  have hcomp : ∀ i : Fin 3, HasFDerivAt (fun x => sepVmu0 μ G x i)
      (∫ p, mpVF' μ G p xo i ∂mpRho2) xo := by
    intro i
    obtain ⟨hd, hi0, _⟩ := mp_V_diff hK μ hμ ρo ρi hρo hρ G hGm hGs hint xo hxo i
    refine hd.congr_of_eventuallyEq ?_
    filter_upwards [Metric.ball_mem_nhds xo hD1pos] with x hx
    exact mp_V_link μ G x i (hi0 x hx)
  have hdiff : DifferentiableAt ℝ (sepVmu0 μ G) xo :=
    differentiableAt_pi.2 fun i => (hcomp i).differentiableAt
  refine ⟨hdiff, fun v i => ?_⟩
  have hfd : fderiv ℝ (sepVmu0 μ G) xo v i = fderiv ℝ (fun x => sepVmu0 μ G x i) xo v := by
    have := fderiv_pi (𝕜 := ℝ) (φ := fun i x => sepVmu0 μ G x i) (x := xo)
      (fun i => (hcomp i).differentiableAt)
    have h2 : fderiv ℝ (sepVmu0 μ G) xo = ContinuousLinearMap.pi fun i =>
        fderiv ℝ (fun x => sepVmu0 μ G x i) xo := this
    rw [h2]
    rfl
  obtain ⟨_, _, hi1⟩ := mp_V_diff hK μ hμ ρo ρi hρo hρ G hGm hGs hint xo hxo i
  rw [hfd, (hcomp i).fderiv, ContinuousLinearMap.integral_apply hi1 v]
  have hint2 : Integrable (fun p => mpVd μ G p xo v i) mpRho2 := by
    have := (ContinuousLinearMap.apply ℝ ℂ v).integrable_comp hi1
    refine this.congr (Eventually.of_forall fun p => ?_)
    simp [mpVF'_apply]
  refine ⟨?_, hint2⟩
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  exact mpVF'_apply μ G p xo v i

end UnforcedLeray.Short.IIIa

end
