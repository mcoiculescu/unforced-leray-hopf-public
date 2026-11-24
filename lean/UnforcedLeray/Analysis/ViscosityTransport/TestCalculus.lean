import UnforcedLeray.Analysis.ViscosityTransport.Defs
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Topology.Algebra.ConstMulAction

/-!
# Smooth compact spacetime tests under spatial normalization

The inverse spatial dilation preserves the actual test class, including its
strict upper time-support condition. Fréchet chain rules give the exact first
and second spatial factors; time differentiation is unchanged. These statements
concern the concrete test functions and do not presume PDE transport.
-/

noncomputable section
open Set
open scoped ContDiff
namespace UnforcedLeray.ViscosityTransport

/-- Spatial dilation as a homeomorphism leaving time unchanged. -/
def spaceHomeomorph (b : ℝ) (hb : b ≠ 0) : SpaceTime ≃ₜ SpaceTime :=
  (Homeomorph.refl ℝ).prodCongr (Homeomorph.smulOfNeZero b hb)

@[simp] theorem spaceHomeomorph_apply (b : ℝ) (hb : b ≠ 0) (z : SpaceTime) :
    spaceHomeomorph b hb z = spaceMap b z := rfl

/-- Inverse spatial dilation preserves smoothness, compactness, and time support. -/
theorem isSpacetimeTest_pullback {T : ℝ} {φ : SpaceTime → Space}
    (hφ : IsSpacetimeTest T φ) {b : ℝ} (hb : b ≠ 0) :
    IsSpacetimeTest T (pullbackTest b φ) := by
  constructor
  · exact hφ.smooth.comp (contDiff_fst.prodMk (contDiff_snd.const_smul b⁻¹))
  · exact hφ.compact.comp_homeomorph (spaceHomeomorph b⁻¹ (inv_ne_zero hb))
  · intro z hz
    have hz' : spaceMap b⁻¹ z ∈ tsupport φ :=
      (tsupport_comp_subset_preimage φ
        (continuous_fst.prodMk (continuous_snd.const_smul b⁻¹))) hz
    exact ⟨(hφ.timeSupport hz').1, Set.mem_univ _⟩

theorem timeDerivative_pullback (b : ℝ) (φ : SpaceTime → Space) (t : ℝ) (x : Space) :
    timeDerivative (pullbackTest b φ) t x = timeDerivative φ t (b⁻¹ • x) := rfl

theorem timeDerivative_pullback_at_dilation (b : ℝ) (hb : b ≠ 0)
    (φ : SpaceTime → Space) (t : ℝ) (x : Space) :
    timeDerivative (pullbackTest b φ) t (b • x) = timeDerivative φ t x := by
  simp only [timeDerivative_pullback, inv_smul_smul₀ hb]

theorem spatialDerivative_pullback (b : ℝ) (φ : SpaceTime → Space)
    (t : ℝ) (x : Space) :
    spatialDerivative (pullbackTest b φ) t x =
      b⁻¹ • spatialDerivative φ t (b⁻¹ • x) := by
  exact fderiv_comp_smul (f := fun y : Space => φ (t, y)) (x := x) b⁻¹

theorem spatialDerivative_pullback_at_dilation (b : ℝ) (hb : b ≠ 0)
    (φ : SpaceTime → Space) (t : ℝ) (x : Space) :
    spatialDerivative (pullbackTest b φ) t (b • x) =
      b⁻¹ • spatialDerivative φ t x := by
  simp only [spatialDerivative_pullback, inv_smul_smul₀ hb]

theorem spatialDivergence_pullback (b : ℝ) (φ : SpaceTime → Space)
    (t : ℝ) (x : Space) :
    spatialDivergence (pullbackTest b φ) t x =
      b⁻¹ * spatialDivergence φ t (b⁻¹ • x) := by
  simp only [spatialDivergence, spatialDerivative_pullback,
    smul_apply, PiLp.smul_apply, smul_eq_mul, Finset.mul_sum]

theorem spatialDivergence_pullback_at_dilation (b : ℝ) (hb : b ≠ 0)
    (φ : SpaceTime → Space) (t : ℝ) (x : Space) :
    spatialDivergence (pullbackTest b φ) t (b • x) =
      b⁻¹ * spatialDivergence φ t x := by
  simp only [spatialDivergence_pullback, inv_smul_smul₀ hb]

/-- Every mixed second spatial directional derivative gains two inverse factors. -/
theorem secondSpatialDerivative_pullback (b : ℝ) (φ : SpaceTime → Space)
    (t : ℝ) (x v w : Space) :
    fderiv ℝ (fun y => spatialDerivative (pullbackTest b φ) t y v) x w =
      (b⁻¹)^2 • fderiv ℝ (fun y => spatialDerivative φ t y v) (b⁻¹ • x) w := by
  simp_rw [spatialDerivative_pullback, smul_apply]
  change fderiv ℝ (b⁻¹ • (fun y => spatialDerivative φ t (b⁻¹ • y) v)) x w = _
  rw [fderiv_const_smul_field]
  simp only [Pi.smul_apply, smul_apply]
  rw [fderiv_comp_smul (f := fun y : Space => spatialDerivative φ t y v)]
  simp only [smul_apply, smul_smul, pow_two]

theorem spatialLaplacian_pullback (b : ℝ) (φ : SpaceTime → Space)
    (t : ℝ) (x : Space) :
    spatialLaplacian (pullbackTest b φ) t x =
      (b⁻¹)^2 • spatialLaplacian φ t (b⁻¹ • x) := by
  simp only [spatialLaplacian, secondSpatialDerivative_pullback, Finset.smul_sum]

theorem spatialLaplacian_pullback_at_dilation (b : ℝ) (hb : b ≠ 0)
    (φ : SpaceTime → Space) (t : ℝ) (x : Space) :
    spatialLaplacian (pullbackTest b φ) t (b • x) =
      (b⁻¹)^2 • spatialLaplacian φ t x := by
  simp only [spatialLaplacian_pullback, inv_smul_smul₀ hb]

end UnforcedLeray.ViscosityTransport
