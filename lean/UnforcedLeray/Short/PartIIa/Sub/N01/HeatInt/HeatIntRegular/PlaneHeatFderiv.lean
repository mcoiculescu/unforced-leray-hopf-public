import UnforcedLeray.Units.B0224.PlaneHeat
import UnforcedLeray.Units.B0223.Lift
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# `PartII-a:N01/9/1/2/4/3` (helper): differentiability of the planar heat

For `θ > 0` and a `C¹` field `u` with bounded value and bounded derivative, the planar heat
`planeHeat θ u` is differentiable and its derivative commutes with the heat flow.
Differentiation under the Gaussian integral with the dominating function `G_θ · M`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.PartIIa.N01

theorem planeHeat_fderiv_apply (θ : ℝ) (hθ : 0 < θ) (u : ℝ × ℝ → UnforcedLeray.B0223.MeridC) (hu : ContDiff ℝ 1 u) (hb : ∃ M : ℝ, ∀ x, ‖u x‖ ≤ M ∧ ‖fderiv ℝ u x‖ ≤ M) : Differentiable ℝ (UnforcedLeray.B0224.planeHeat θ u) ∧ ∀ x v : ℝ × ℝ, fderiv ℝ (UnforcedLeray.B0224.planeHeat θ u) x v = UnforcedLeray.B0224.planeHeat θ (fun y => fderiv ℝ u y v) x := by
  obtain ⟨M, hM⟩ := hb
  have hMu : ∀ x, ‖u x‖ ≤ M := fun x => (hM x).1
  have hMd : ∀ x, ‖fderiv ℝ u x‖ ≤ M := fun x => (hM x).2
  have huc : Continuous u := hu.continuous
  have hdc : Continuous (fderiv ℝ u) := hu.continuous_fderiv (by norm_num)
  have hud : ∀ x, DifferentiableAt ℝ u x := fun x => (hu.differentiable (by norm_num)) x
  have hG : MeasureTheory.Integrable (fun y : UnforcedLeray.Gaussian.Euc 2 =>
      UnforcedLeray.Gaussian.gaussKernel 2 θ y * M) :=
    (UnforcedLeray.Gaussian.integrable_gaussKernel (d := 2) hθ).mul_const M
  have hG0 : ∀ y : UnforcedLeray.Gaussian.Euc 2, 0 ≤ UnforcedLeray.Gaussian.gaussKernel 2 θ y :=
    fun y => UnforcedLeray.Gaussian.gaussKernel_nonneg hθ y
  have hGc : Continuous (UnforcedLeray.Gaussian.gaussKernel 2 θ) :=
    UnforcedLeray.Gaussian.continuous_gaussKernel (d := 2) θ
  have hrep : UnforcedLeray.B0224.planeHeat θ u = fun x => ∫ y : UnforcedLeray.Gaussian.Euc 2,
      UnforcedLeray.Gaussian.gaussKernel 2 θ y • u (x - UnforcedLeray.B0224.planeι y) :=
    funext fun x => UnforcedLeray.B0224.planeHeat_of_pos hθ u x
  -- continuity in the integration variable of the integrands
  have hFc : ∀ x : ℝ × ℝ, Continuous fun y : UnforcedLeray.Gaussian.Euc 2 =>
      UnforcedLeray.Gaussian.gaussKernel 2 θ y • u (x - UnforcedLeray.B0224.planeι y) :=
    fun x => hGc.smul (huc.comp (continuous_const.sub UnforcedLeray.B0224.continuous_planeι))
  have hF'c : ∀ x : ℝ × ℝ, Continuous fun y : UnforcedLeray.Gaussian.Euc 2 =>
      UnforcedLeray.Gaussian.gaussKernel 2 θ y • fderiv ℝ u (x - UnforcedLeray.B0224.planeι y) :=
    fun x => hGc.smul (hdc.comp (continuous_const.sub UnforcedLeray.B0224.continuous_planeι))
  have hbnd : ∀ (y : UnforcedLeray.Gaussian.Euc 2) (A : ℝ × ℝ →L[ℝ] UnforcedLeray.B0223.MeridC),
      ‖A‖ ≤ M → ‖UnforcedLeray.Gaussian.gaussKernel 2 θ y • A‖ ≤
        UnforcedLeray.Gaussian.gaussKernel 2 θ y * M := by
    intro y A hA
    rw [norm_smul, Real.norm_of_nonneg (hG0 y)]
    exact mul_le_mul_of_nonneg_left hA (hG0 y)
  have hint : ∀ x0 : ℝ × ℝ, MeasureTheory.Integrable (fun y : UnforcedLeray.Gaussian.Euc 2 =>
      UnforcedLeray.Gaussian.gaussKernel 2 θ y • fderiv ℝ u (x0 - UnforcedLeray.B0224.planeι y)) := by
    intro x0
    exact hG.mono' (hF'c x0).aestronglyMeasurable
      (ae_of_all _ fun y => hbnd y _ (hMd _))
  have key : ∀ x0 : ℝ × ℝ, HasFDerivAt
      (fun x => ∫ y : UnforcedLeray.Gaussian.Euc 2,
        UnforcedLeray.Gaussian.gaussKernel 2 θ y • u (x - UnforcedLeray.B0224.planeι y))
      (∫ y : UnforcedLeray.Gaussian.Euc 2,
        UnforcedLeray.Gaussian.gaussKernel 2 θ y • fderiv ℝ u (x0 - UnforcedLeray.B0224.planeι y))
      x0 := by
    intro x0
    refine hasFDerivAt_integral_of_dominated_of_fderiv_le
      (μ := (volume : Measure (UnforcedLeray.Gaussian.Euc 2)))
      (F := fun x y => UnforcedLeray.Gaussian.gaussKernel 2 θ y • u (x - UnforcedLeray.B0224.planeι y))
      (F' := fun x y => UnforcedLeray.Gaussian.gaussKernel 2 θ y •
        fderiv ℝ u (x - UnforcedLeray.B0224.planeι y))
      (bound := fun y => UnforcedLeray.Gaussian.gaussKernel 2 θ y * M)
      (s := univ) (x₀ := x0) univ_mem ?_ ?_ ?_ ?_ hG ?_
    · exact Eventually.of_forall fun x => (hFc x).aestronglyMeasurable
    · exact hG.mono' (hFc x0).aestronglyMeasurable
        (ae_of_all _ fun y => by
          rw [norm_smul, Real.norm_of_nonneg (hG0 y)]
          exact mul_le_mul_of_nonneg_left (hMu _) (hG0 y))
    · exact (hF'c x0).aestronglyMeasurable
    · exact ae_of_all _ fun y x _ => hbnd y _ (hMd _)
    · refine ae_of_all _ fun y x _ => ?_
      have h1 : HasFDerivAt (fun x : ℝ × ℝ => u (x - UnforcedLeray.B0224.planeι y))
          ((fderiv ℝ u (x - UnforcedLeray.B0224.planeι y)).comp (ContinuousLinearMap.id ℝ (ℝ × ℝ))) x :=
        HasFDerivAt.comp x (hud _).hasFDerivAt ((hasFDerivAt_id x).sub_const _)
      rw [ContinuousLinearMap.comp_id] at h1
      have h2 := h1.const_smul (UnforcedLeray.Gaussian.gaussKernel 2 θ y)
      exact h2
  have hD : ∀ x0 : ℝ × ℝ, HasFDerivAt (UnforcedLeray.B0224.planeHeat θ u)
      (∫ y : UnforcedLeray.Gaussian.Euc 2,
        UnforcedLeray.Gaussian.gaussKernel 2 θ y • fderiv ℝ u (x0 - UnforcedLeray.B0224.planeι y)) x0 := by
    intro x0
    rw [hrep]
    exact key x0
  refine ⟨fun x => (hD x).differentiableAt, fun x v => ?_⟩
  rw [(hD x).fderiv, ContinuousLinearMap.integral_apply (hint x) v,
    UnforcedLeray.B0224.planeHeat_of_pos hθ]
  simp only [smul_apply]

end UnforcedLeray.Short.PartIIa.N01
