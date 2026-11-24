import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GEQuadSub.Sub.PartIIIb_C_ward_12_3_1_2_7_1

/-!
# `DySSpatMolAe` decomposed: slice identity for a.e. `τ`

Source `the November 2 reference manuscript`
lines 2562-2564 (local Friedrichs argument in `y`), phase tests 2525-2531.

`SliceIdAll` is the true source fact: if `∂_{y_j} f = Df` weakly on the cell, then for a.e. `τ` the
slice `f(τ,·)` is locally integrable and `∫ ∂_jρ(t) f(τ,y-t) dt = ∫ ρ(t) Df(τ,y-t) dt` for all `y`
(test the weak identity against `θ(τ) ρ(y-·)` for rational `y`, fundamental lemma in `τ`, then
continuity in `y`).  `dyS_spatMol_ae_of` derives `DySSpatMolAe` by differentiating the convolution.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Directional derivative of a mollified locally integrable slice (source 2562-2564). -/
theorem spatMol_slice_dir_deriv (ρ : UnforcedLeray.Space → ℝ) (hρs : ContDiff ℝ ∞ ρ)
    (hρc : HasCompactSupport ρ) (j : Fin 3) (g : UnforcedLeray.Space → ℂ)
    (hg : LocallyIntegrable g volume) (y : UnforcedLeray.Space) :
    fderiv ℝ (convolution (fun t : UnforcedLeray.Space => (ρ t : ℂ)) g
        (ContinuousLinearMap.mul ℝ ℂ) volume) y (UnforcedLeray.coordinateVector j) =
      ∫ t : UnforcedLeray.Space,
        fderiv ℝ (fun t : UnforcedLeray.Space => (ρ t : ℂ)) t
          (UnforcedLeray.coordinateVector j) * g (y - t) := by
  have hρC : ContDiff ℝ 1 (fun t : UnforcedLeray.Space => (ρ t : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (hρs.of_le (by simp))
  have hρK : HasCompactSupport (fun t : UnforcedLeray.Space => (ρ t : ℂ)) :=
    hρc.comp_left Complex.ofReal_zero
  have hK' : HasCompactSupport (fderiv ℝ (fun t : UnforcedLeray.Space => (ρ t : ℂ))) :=
    hρK.fderiv (𝕜 := ℝ)
  have hcont : Continuous (fderiv ℝ (fun t : UnforcedLeray.Space => (ρ t : ℂ))) :=
    hρC.continuous_fderiv (by simp)
  have hd := hρK.hasFDerivAt_convolution_left (ContinuousLinearMap.mul ℝ ℂ) hρC hg y
  rw [hd.fderiv]
  have hex := hK'.convolutionExists_left
    (ContinuousLinearMap.precompL UnforcedLeray.Space (ContinuousLinearMap.mul ℝ ℂ)) hcont hg
  have hint : Integrable (fun t : UnforcedLeray.Space =>
      (ContinuousLinearMap.precompL UnforcedLeray.Space (ContinuousLinearMap.mul ℝ ℂ))
        (fderiv ℝ (fun t : UnforcedLeray.Space => (ρ t : ℂ)) t) (g (y - t))) volume :=
    hex y
  rw [convolution_def, ContinuousLinearMap.integral_apply hint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only [ContinuousLinearMap.precompL_apply, ContinuousLinearMap.mul_apply']

/-- Slice weak identity for a.e. `τ` with locally integrable slices (source 2562-2564). -/
def SliceIdAll : Prop :=
  ∀ (P : ℝ) [Fact (0 < P)] (j : Fin 3) (ρ : UnforcedLeray.Space → ℝ), ContDiff ℝ ∞ ρ →
    HasCompactSupport ρ → ∀ f Df : ℝ × UnforcedLeray.Space → ℂ, MemLpLoc P f 1 → MemLpLoc P Df 1 →
      WeakDyS P j f Df →
      ∀ᵐ τ ∂(volume.restrict (Ioc (0 : ℝ) P)),
        LocallyIntegrable (fun y : UnforcedLeray.Space => f (τ, y)) volume ∧
        ∀ y : UnforcedLeray.Space,
          ∫ t : UnforcedLeray.Space, fderiv ℝ (fun t : UnforcedLeray.Space => (ρ t : ℂ)) t
              (UnforcedLeray.coordinateVector j) * f (τ, y - t) =
            ∫ t : UnforcedLeray.Space, (ρ t : ℂ) * Df (τ, y - t)

theorem dyS_spatMol_ae_of (h : SliceIdAll) : DySSpatMolAe := by
  intro P _ j ρ hρs hρc f Df hf hDf hW
  filter_upwards [h P j ρ hρs hρc f Df hf hDf hW] with τ hτ y
  obtain ⟨hloc, hid⟩ := hτ
  have key : (fun y : UnforcedLeray.Space => spatMol ρ f (τ, y)) =
      convolution (fun t : UnforcedLeray.Space => (ρ t : ℂ))
        (fun y : UnforcedLeray.Space => f (τ, y)) (ContinuousLinearMap.mul ℝ ℂ) volume := by
    funext y
    simp [spatMol, convolution_def]
  have := spatMol_slice_dir_deriv ρ hρs hρc j _ hloc y
  unfold dyS
  rw [key, this, hid y]
  rfl

end UnforcedLeray.Short.PartIIIb.Concrete
