import UnforcedLeray.Cons.L2.BackgroundConcrete
import UnforcedLeray.Blueprint.Construction.Steps
import UnforcedLeray.Lib.SobolevB.Mollify
import Mathlib.Analysis.Calculus.LineDeriv.Basic

/-! A jointly a.e.-measurable field with spatial derivatives at every point has jointly
    a.e.-measurable applied spatial derivatives. -/

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter
open scoped Topology
open UnforcedLeray.Blueprint

namespace UnforcedLeray.Cons.C03.Concrete

private abbrev Sp := EuclideanSpace ℝ (Fin 3)

/-- Spatial differentiation preserves joint a.e. strong measurability under pointwise spatial
    differentiability. No time regularity is required. -/
theorem aeStronglyMeasurable_spatialFderiv
    (U : ℝ → Sp → Sp)
    (hU : AEStronglyMeasurable (fun z : ℝ × Sp => U z.1 z.2) volume)
    (hderiv : ∀ τ y, DifferentiableAt ℝ (U τ) y)
    (v : Sp) :
    AEStronglyMeasurable (fun z : ℝ × Sp => fderiv ℝ (U z.1) z.2 v) volume := by
  let δ : ℕ → ℝ := fun n => ((n : ℝ) + 1)⁻¹
  let D : ℕ → ℝ × Sp → Sp := fun n z =>
    (δ n)⁻¹ • (U z.1 (z.2 + δ n • v) - U z.1 z.2)
  have hshift (n : ℕ) :
      AEStronglyMeasurable (fun z : ℝ × Sp => U z.1 (z.2 + δ n • v)) volume := by
    have hq : Measure.QuasiMeasurePreserving
        (Prod.map (id : ℝ → ℝ) (fun y : Sp => y + δ n • v)) volume volume :=
      QuasiMeasurePreserving.prodMap
        (Measure.QuasiMeasurePreserving.id volume)
        (measurePreserving_add_right volume (δ n • v)).quasiMeasurePreserving
    exact hU.comp_quasiMeasurePreserving hq
  have hD (n : ℕ) : AEStronglyMeasurable (D n) volume := by
    have h := ((hshift n).sub hU).const_smul ((δ n)⁻¹)
    have heq : (δ n)⁻¹ • ((fun z : ℝ × Sp => U z.1 (z.2 + δ n • v)) -
        fun z : ℝ × Sp => U z.1 z.2) = D n := by
      funext z
      simp [D]
    rw [heq] at h
    exact h
  have hδ : Tendsto δ atTop (𝓝[>] (0 : ℝ)) := by
    have ht : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
    exact tendsto_inv_atTop_nhdsGT_zero.comp ht
  have hlim (z : ℝ × Sp) :
      Tendsto (fun n => D n z) atTop (𝓝 (fderiv ℝ (U z.1) z.2 v)) := by
    have hline := (hderiv z.1 z.2).hasFDerivAt.hasLineDerivAt v
    simpa only [D, Function.comp_def] using hline.tendsto_slope_zero_right.comp hδ
  exact aestronglyMeasurable_of_tendsto_ae atTop hD (ae_of_all _ hlim)

/-- The spatial gradient of an actual bounded background is jointly a.e. strongly measurable.
This follows from its specified joint measurability and pointwise spatial differentiability. -/
theorem aeStronglyMeasurable_backgroundFderiv (U : ℝ → SpatialField)
    (hU : IsBoundedBackground U) (v : Space) :
    AEStronglyMeasurable (fun z : SpaceTime => fderiv ℝ (U z.1) z.2 v) volume :=
  aeStronglyMeasurable_spatialFderiv U hU.measurable
    (fun τ y => hU.differentiable τ y) v

#print axioms aeStronglyMeasurable_spatialFderiv
#print axioms aeStronglyMeasurable_backgroundFderiv

end UnforcedLeray.Cons.C03.Concrete
