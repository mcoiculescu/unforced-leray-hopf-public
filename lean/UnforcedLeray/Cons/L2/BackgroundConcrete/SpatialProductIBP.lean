import UnforcedLeray.Cons.L2.BackgroundConcrete.SpatialProductST
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-! Integration by parts against a compact spacetime test using only spatial line derivatives. -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ContDiff

namespace UnforcedLeray.Cons.C03.Concrete

open UnforcedLeray.Blueprint
open UnforcedLeray.PhaseSpace

/-- Compact-test integration by parts for the actual scalar product `Φ·U`. The three displayed
integrability premises are the exact hypotheses of Mathlib's line-IBP theorem; the next leaf will
supply them from boundedness and compact support. -/
theorem integral_smul_fderiv_scalarTestBackground_eq_neg
    {P : ℝ} {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ)
    {U : ℝ → SpatialField} (hU : IsBoundedBackground U)
    {η : SpaceTime → ℝ} (hη : ContDiff ℝ ∞ η)
    (v : Space)
    (h1 : Integrable (fun z : SpaceTime =>
      (fderiv ℝ η z (0, v) : ℝ) • scalarTestBackground Φ U z) volume)
    (h2 : Integrable (fun z : SpaceTime =>
      η z • fderiv ℝ (fun x : Space => scalarTestBackground Φ U (z.1, x)) z.2 v) volume)
    (h3 : Integrable (fun z : SpaceTime => η z • scalarTestBackground Φ U z) volume) :
    ∫ z : SpaceTime, η z •
        fderiv ℝ (fun x : Space => scalarTestBackground Φ U (z.1, x)) z.2 v ∂volume =
      -∫ z : SpaceTime, fderiv ℝ η z (0, v) • scalarTestBackground Φ U z ∂volume := by
  have hhaar : (volume : Measure SpaceTime).IsAddHaarMeasure := by
    rw [Measure.volume_eq_prod]
    infer_instance
  letI := hhaar
  let d : SpaceTime := (0, v)
  let g' : SpaceTime → ℂ := fun z =>
    fderiv ℝ (fun x : Space => scalarTestBackground Φ U (z.1, x)) z.2 v
  have hηline : ∀ z, HasLineDerivAt ℝ η (fderiv ℝ η z d) z d := by
    intro z
    exact (hη.differentiable (by simp) z).hasFDerivAt.hasLineDerivAt d
  have hgline : ∀ z ∈ tsupport η,
      HasLineDerivAt ℝ (scalarTestBackground Φ U) (g' z) z d := by
    intro z hz
    rcases z with ⟨τ, y⟩
    simpa [d, g', HasLineDerivAt, scalarTestBackground] using
      hasLineDerivAt_scalarTestBackground_spaceTime hΦ hU τ y v
  have h := integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
    (B := (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℂ →L[ℝ] ℂ))
    (f := η) (f' := fun z => fderiv ℝ η z d)
    (g := scalarTestBackground Φ U) (g' := g') (v := d)
    (by simpa [d, g'] using h1) (by simpa [g'] using h2)
    (by simpa using h3) (fun z _ => hηline z) hgline
  simpa [g', d] using h

#print axioms integral_smul_fderiv_scalarTestBackground_eq_neg

end UnforcedLeray.Cons.C03.Concrete
