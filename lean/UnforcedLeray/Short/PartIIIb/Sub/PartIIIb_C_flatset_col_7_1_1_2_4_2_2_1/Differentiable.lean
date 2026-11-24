import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_2_1
import UnforcedLeray.Units.B0224.PlaneHeat
import UnforcedLeray.Lib.Gaussian.Kernel
import UnforcedLeray.Lib.Gaussian.IteratedDeriv
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.MeasureTheory.Group.Integral

/-!
# `SFCHeatDifferentiable` (source 3426-3430)

For `θ > 0` and a bounded continuous `u`, `e^{θΔ}u` is Fréchet differentiable at every point.
The derivative is moved onto the Gaussian: `e^{θΔ}u(w) = ∫ G_θ(y + v) u(x₀ - ιy) dy` with
`v = ψ(w - x₀)`, so no bound on `∇u` is needed. The gradient of `G_θ` has a Gaussian envelope
uniform for `‖v‖ < 1`, and dominated differentiation applies at `v = 0`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.Gaussian (Euc gaussKernel)

/-- Linear right inverse of `planeι`: a point `(s,t)` of the plane as a vector of `Euc 2`. -/
def sfcPsiLin : (ℝ × ℝ) →ₗ[ℝ] Euc 2 where
  toFun t := (WithLp.equiv 2 (Fin 2 → ℝ)).symm ![t.1, t.2]
  map_add' a b := by
    ext i; fin_cases i <;> simp
  map_smul' c a := by
    ext i; fin_cases i <;> simp

/-- Continuous linear right inverse of `planeι`. -/
def sfcPsi : (ℝ × ℝ) →L[ℝ] Euc 2 := LinearMap.toContinuousLinearMap sfcPsiLin

theorem planeι_sfcPsi (t : ℝ × ℝ) : UnforcedLeray.B0224.planeι (sfcPsi t) = t := by
  ext <;> simp [sfcPsi, sfcPsiLin, UnforcedLeray.B0224.planeι_apply]

/-- Gaussian envelope of `∇G_θ(y + v)`, uniform in `‖v‖ < 1` (source 3426-3430). -/
theorem sfcGradEnvelope {θ : ℝ} (hθ : 0 < θ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ v y : Euc 2, ‖v‖ < 1 →
      ‖fderiv ℝ (gaussKernel 2 θ) (y + v)‖ ≤ A * Real.exp (-(1 / (16 * θ)) * ‖y‖ ^ 2) := by
  obtain ⟨C, hC0, hC⟩ := UnforcedLeray.Gaussian.norm_iteratedFDeriv_gaussKernel_le 2 1
  refine ⟨C * θ ^ (-((((2 : ℕ) : ℝ) + ((1 : ℕ) : ℝ)) / 2)) * Real.exp (1 / (8 * θ)),
    by positivity, ?_⟩
  intro v y hv
  have h1 := hC hθ (y + v)
  rw [norm_iteratedFDeriv_one] at h1
  have hyz : ‖y‖ ≤ ‖y + v‖ + 1 := by
    have h := norm_sub_le (y + v) v
    rw [add_sub_cancel_right] at h
    linarith
  have hsq : ‖y‖ ^ 2 ≤ 2 * ‖y + v‖ ^ 2 + 2 := by
    nlinarith [norm_nonneg y, norm_nonneg (y + v), mul_self_le_mul_self (norm_nonneg y) hyz,
      sq_nonneg (‖y + v‖ - 1)]
  have hexp : Real.exp (-‖y + v‖ ^ 2 / (8 * θ)) ≤
      Real.exp (1 / (8 * θ)) * Real.exp (-(1 / (16 * θ)) * ‖y‖ ^ 2) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have key : -‖y + v‖ ^ 2 / (8 * θ) ≤ 1 / (8 * θ) + -(1 / (16 * θ)) * ‖y‖ ^ 2 := by
      have h8 : 0 < 8 * θ := by positivity
      have e : -‖y + v‖ ^ 2 / (8 * θ) = -(2 * ‖y + v‖ ^ 2) / (16 * θ) := by
        field_simp
        ring
      have e2 : 1 / (8 * θ) + -(1 / (16 * θ)) * ‖y‖ ^ 2 = (2 - ‖y‖ ^ 2) / (16 * θ) := by
        field_simp
        ring
      rw [e, e2]
      apply div_le_div_of_nonneg_right _ (by positivity)
      linarith
    exact key
  calc ‖fderiv ℝ (gaussKernel 2 θ) (y + v)‖
      ≤ C * θ ^ (-((((2 : ℕ) : ℝ) + ((1 : ℕ) : ℝ)) / 2)) *
          Real.exp (-‖y + v‖ ^ 2 / (8 * θ)) := h1
    _ ≤ C * θ ^ (-((((2 : ℕ) : ℝ) + ((1 : ℕ) : ℝ)) / 2)) *
          (Real.exp (1 / (8 * θ)) * Real.exp (-(1 / (16 * θ)) * ‖y‖ ^ 2)) := by
        gcongr
    _ = _ := by ring

/-- Differentiability of `e^{θΔ}u` at `x₀` for bounded continuous `u`, `θ > 0`. -/
theorem sfcHeat_differentiableAt {θ : ℝ} (hθ : 0 < θ) {u : ℝ × ℝ → ℂ} (hu : Continuous u)
    {M : ℝ} (hM : ∀ x, ‖u x‖ ≤ M) (x₀ : ℝ × ℝ) :
    DifferentiableAt ℝ (UnforcedLeray.B0224.planeHeat θ u) x₀ := by
  obtain ⟨A, hA0, hA⟩ := sfcGradEnvelope hθ
  have hKc : Continuous (gaussKernel 2 θ) := UnforcedLeray.Gaussian.continuous_gaussKernel θ
  have hKd : ContDiff ℝ 1 (gaussKernel 2 θ) := UnforcedLeray.Gaussian.contDiff_gaussKernel θ
  have hKint : Integrable (gaussKernel 2 θ) := UnforcedLeray.Gaussian.integrable_gaussKernel hθ
  have hι : Continuous (UnforcedLeray.B0224.planeι : Euc 2 → ℝ × ℝ) :=
    UnforcedLeray.B0224.continuous_planeι
  have huι : Continuous fun y : Euc 2 => u (x₀ - UnforcedLeray.B0224.planeι y) :=
    hu.comp (continuous_const.sub hι)
  -- the translated representation `Φ`
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : Euc 2 → ℂ, Φ = fun v =>
      ∫ y : Euc 2, gaussKernel 2 θ (y + v) • u (x₀ - UnforcedLeray.B0224.planeι y) :=
    ⟨_, rfl⟩
  have hrep : ∀ w : ℝ × ℝ,
      UnforcedLeray.B0224.planeHeat θ u w = Φ (sfcPsi (w - x₀)) := by
    intro w
    rw [UnforcedLeray.B0224.planeHeat_of_pos hθ, hΦ]
    set v := sfcPsi (w - x₀) with hv
    have hιv : UnforcedLeray.B0224.planeι v = w - x₀ := planeι_sfcPsi _
    -- translate the integration variable by `v`
    rw [← integral_add_right_eq_self
      (fun y : Euc 2 => gaussKernel 2 θ y • u (w - UnforcedLeray.B0224.planeι y)) v]
    congr 1
    funext y
    congr 2
    rw [map_add, hιv]
    abel
  -- differentiability of `Φ` at `0`
  have hΦd : DifferentiableAt ℝ Φ 0 := by
    rw [hΦ]
    have hball : Metric.ball (0 : Euc 2) 1 ∈ 𝓝 (0 : Euc 2) :=
      Metric.ball_mem_nhds _ one_pos
    have hmeas : ∀ v : Euc 2, AEStronglyMeasurable
        (fun y : Euc 2 => gaussKernel 2 θ (y + v) • u (x₀ - UnforcedLeray.B0224.planeι y))
        volume := by
      intro v
      have hc1 : Continuous fun y : Euc 2 => gaussKernel 2 θ (y + v) :=
        hKc.comp (continuous_id.add continuous_const)
      exact (hc1.smul huι).aestronglyMeasurable
    have hint0 : Integrable
        (fun y : Euc 2 => gaussKernel 2 θ (y + 0) • u (x₀ - UnforcedLeray.B0224.planeι y)) := by
      simp only [add_zero]
      refine (hKint.mul_const M).mono' ?_ (Eventually.of_forall fun y => ?_)
      · exact (hKc.smul huι).aestronglyMeasurable
      · rw [norm_smul, Real.norm_of_nonneg (UnforcedLeray.Gaussian.gaussKernel_nonneg hθ y)]
        exact mul_le_mul_of_nonneg_left (hM _) (UnforcedLeray.Gaussian.gaussKernel_nonneg hθ y)
    have hfd : Continuous fun y : Euc 2 => fderiv ℝ (gaussKernel 2 θ) (y + 0) := by
      have h0 : Continuous fun y : Euc 2 => fderiv ℝ (gaussKernel 2 θ) y :=
        hKd.continuous_fderiv (by norm_num)
      exact h0.comp (continuous_id.add continuous_const)
    have hc2 : Continuous fun y : Euc 2 =>
        (fderiv ℝ (gaussKernel 2 θ) (y + 0), u (x₀ - UnforcedLeray.B0224.planeι y)) :=
      hfd.prodMk huι
    have hF'meas : AEStronglyMeasurable
        (fun y : Euc 2 => (fderiv ℝ (gaussKernel 2 θ) (y + 0)).smulRight
          (u (x₀ - UnforcedLeray.B0224.planeι y))) volume := by
      have hcont := (ContinuousLinearMap.smulRightL ℝ (Euc 2) ℂ).continuous₂.comp hc2
      exact hcont.aestronglyMeasurable
    have hbd : ∀ᵐ y ∂(volume : Measure (Euc 2)), ∀ v ∈ Metric.ball (0 : Euc 2) 1,
        ‖(fderiv ℝ (gaussKernel 2 θ) (y + v)).smulRight
          (u (x₀ - UnforcedLeray.B0224.planeι y))‖ ≤
          A * Real.exp (-(1 / (16 * θ)) * ‖y‖ ^ 2) * M := by
      refine Eventually.of_forall fun y v hv => ?_
      rw [ContinuousLinearMap.norm_smulRight_apply]
      exact mul_le_mul (hA v y (mem_ball_zero_iff.mp hv)) (hM _) (norm_nonneg _)
        (by positivity)
    have hbint : Integrable (fun y : Euc 2 => A * Real.exp (-(1 / (16 * θ)) * ‖y‖ ^ 2) * M) :=
      ((UnforcedLeray.Gaussian.integrable_exp_neg_mul_sq_norm (b := 1 / (16 * θ))
        (by positivity)).const_mul A).mul_const M
    have hdiff : ∀ᵐ y ∂(volume : Measure (Euc 2)), ∀ v ∈ Metric.ball (0 : Euc 2) 1,
        HasFDerivAt (fun v : Euc 2 => gaussKernel 2 θ (y + v) •
            u (x₀ - UnforcedLeray.B0224.planeι y))
          ((fderiv ℝ (gaussKernel 2 θ) (y + v)).smulRight
            (u (x₀ - UnforcedLeray.B0224.planeι y))) v := by
      refine Eventually.of_forall fun y v _ => ?_
      have h1 : HasFDerivAt (fun v : Euc 2 => gaussKernel 2 θ (y + v))
          (fderiv ℝ (gaussKernel 2 θ) (y + v)) v := by
        have h2 := ((hKd.differentiable (by norm_num)) (y + v)).hasFDerivAt.comp v
          ((hasFDerivAt_id v).const_add y)
        rw [ContinuousLinearMap.comp_id] at h2
        exact h2
      exact h1.smul_const _
    have key := hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := (volume : Measure (Euc 2)))
      (F := fun v y => gaussKernel 2 θ (y + v) • u (x₀ - UnforcedLeray.B0224.planeι y))
      (F' := fun v y => (fderiv ℝ (gaussKernel 2 θ) (y + v)).smulRight
        (u (x₀ - UnforcedLeray.B0224.planeι y)))
      (bound := fun y => A * Real.exp (-(1 / (16 * θ)) * ‖y‖ ^ 2) * M)
      (x₀ := 0) (s := Metric.ball (0 : Euc 2) 1) hball
      (Eventually.of_forall fun v => hmeas v) hint0 hF'meas hbd hbint hdiff
    exact key.differentiableAt
  have hcomp : DifferentiableAt ℝ (fun w : ℝ × ℝ => Φ (sfcPsi (w - x₀))) x₀ := by
    have hψ : DifferentiableAt ℝ (fun w : ℝ × ℝ => sfcPsi (w - x₀)) x₀ :=
      (sfcPsi.differentiableAt).comp x₀ ((differentiableAt_id).sub_const x₀)
    have hΦ0 : DifferentiableAt ℝ Φ (sfcPsi (x₀ - x₀)) := by
      rw [sub_self, map_zero]; exact hΦd
    exact hΦ0.comp x₀ hψ
  have hfun : UnforcedLeray.B0224.planeHeat θ u = fun w => Φ (sfcPsi (w - x₀)) := funext hrep
  rw [hfun]
  exact hcomp

/-- **SFCHeatDifferentiable** (source 3426-3430): `e^{θΔ} f` is differentiable under the
`SFCCommuteHyp` hypotheses (only continuity and boundedness of `f` are used). -/
theorem sfcHeatDifferentiable : SFCHeatDifferentiable := by
  intro c θ _hc hθ f hyp z
  obtain ⟨hf, _, ⟨M, hM⟩, _⟩ := hyp
  exact sfcHeat_differentiableAt hθ hf.continuous hM z

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
