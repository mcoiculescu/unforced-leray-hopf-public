import UnforcedLeray.Cons.L2.BackgroundConcrete.SpatialDerivativeMeas
import UnforcedLeray.Units.B0412.Action
import UnforcedLeray.Units.B0411.Operators

/-!
# Spatial differentiability of a compact test paired with a bounded background

This is the pointwise calculus input for spatial integration by parts. It asks for no time
regularity of the background.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Cons.C03.Concrete

open UnforcedLeray.Blueprint
open UnforcedLeray.PhaseSpace
open UnforcedLeray.B0411
open UnforcedLeray.B0412
open scoped ContDiff

private theorem contDiff_realC : ContDiff ℝ ∞ (fun x : Space => realC x) := by
  apply (contDiff_piLp 2).2
  intro i
  have hcoord : (fun x : Space => (realC x).ofLp i) =
      fun x : Space => ((x i : ℝ) : ℂ) := by
    funext x
    exact realC_apply x i
  rw [hcoord]
  exact Complex.ofRealCLM.contDiff.comp
    (contDiff_piLp_apply (p := 2) (i := i))

/-- The scalar bilinear pairing of a complex test field with a real background. -/
def scalarTestBackground (Φ : ℝ × Space → CVec3) (U : ℝ → SpatialField)
    (z : SpaceTime) : ℂ := dotL (Φ z) (realC (U z.1 z.2))

/-- At every fixed phase, the scalar test/background product is differentiable in space. -/
theorem differentiableAt_scalarTestBackground {P : ℝ} {Φ : ℝ × Space → CVec3}
    (hΦ : IsPhaseTest P Φ) {U : ℝ → SpatialField} (hU : IsBoundedBackground U)
    (τ : ℝ) (y : Space) :
    DifferentiableAt ℝ (fun x : Space => scalarTestBackground Φ U (τ, x)) y := by
  have hΦall : Differentiable ℝ Φ := hΦ.smooth.differentiable (by simp)
  have hΦslice : DifferentiableAt ℝ (fun x : Space => Φ (τ, x)) y := by
    have hmap : DifferentiableAt ℝ (fun x : Space => (τ, x)) y := by fun_prop
    exact (hΦall (τ, y)).comp y hmap
  have hUslice : DifferentiableAt ℝ (fun x : Space => U τ x) y := hU.differentiable τ y
  have hRealC : DifferentiableAt ℝ realC (U τ y) :=
    (contDiff_realC.differentiable (by simp)) (U τ y)
  have hUcomplex : DifferentiableAt ℝ (fun x : Space => realC (U τ x)) y :=
    hRealC.comp y hUslice
  have hpair := dotLR.hasFDerivAt_of_bilinear hΦslice.hasFDerivAt hUcomplex.hasFDerivAt
  simpa only [scalarTestBackground, dotLR_apply] using hpair.differentiableAt

/-- Product rule for the actual scalar test/background pairing at a fixed phase. -/
theorem fderiv_scalarTestBackground {P : ℝ} {Φ : ℝ × Space → CVec3}
    (hΦ : IsPhaseTest P Φ) {U : ℝ → SpatialField} (hU : IsBoundedBackground U)
    (τ : ℝ) (y v : Space) :
    fderiv ℝ (fun x : Space => scalarTestBackground Φ U (τ, x)) y v =
      (dotLR.precompR Space (Φ (τ, y))
          (fderiv ℝ (fun x : Space => realC (U τ x)) y) +
        dotLR.precompL Space
          (fderiv ℝ (fun x : Space => Φ (τ, x)) y) (realC (U τ y))) v := by
  have hΦall : Differentiable ℝ Φ := hΦ.smooth.differentiable (by simp)
  have hΦslice : DifferentiableAt ℝ (fun x : Space => Φ (τ, x)) y := by
    have hmap : DifferentiableAt ℝ (fun x : Space => (τ, x)) y := by fun_prop
    exact (hΦall (τ, y)).comp y hmap
  have hUslice : DifferentiableAt ℝ (fun x : Space => U τ x) y := hU.differentiable τ y
  have hRealC : DifferentiableAt ℝ realC (U τ y) :=
    (contDiff_realC.differentiable (by simp)) (U τ y)
  have hUcomplex : DifferentiableAt ℝ (fun x : Space => realC (U τ x)) y :=
    hRealC.comp y hUslice
  have hpair := dotLR.hasFDerivAt_of_bilinear hΦslice.hasFDerivAt hUcomplex.hasFDerivAt
  change fderiv ℝ (fun x : Space => dotLR (Φ (τ, x)) (realC (U τ x))) y v = _
  rw [hpair.fderiv]

/-- The scalar product has a spatial line derivative in every direction. -/
theorem hasLineDerivAt_scalarTestBackground {P : ℝ} {Φ : ℝ × Space → CVec3}
    (hΦ : IsPhaseTest P Φ) {U : ℝ → SpatialField} (hU : IsBoundedBackground U)
    (τ : ℝ) (y v : Space) :
    HasLineDerivAt ℝ (fun x : Space => scalarTestBackground Φ U (τ, x))
      (fderiv ℝ (fun x : Space => scalarTestBackground Φ U (τ, x)) y v) y v :=
  (differentiableAt_scalarTestBackground hΦ hU τ y).hasFDerivAt.hasLineDerivAt v

/-- A phase-only cutoff is constant along spatial lines, so it preserves the product's
line-derivative formula. -/
theorem hasLineDerivAt_cutoff_scalarTestBackground {P : ℝ} {Φ : ℝ × Space → CVec3}
    (hΦ : IsPhaseTest P Φ) {U : ℝ → SpatialField} (hU : IsBoundedBackground U)
    (χ : ℝ → ℝ) (τ : ℝ) (y v : Space) :
    HasLineDerivAt ℝ
      (fun x : Space => ((χ τ : ℝ) : ℂ) * scalarTestBackground Φ U (τ, x))
      (((χ τ : ℝ) : ℂ) *
        fderiv ℝ (fun x : Space => scalarTestBackground Φ U (τ, x)) y v) y v := by
  have h := hasLineDerivAt_scalarTestBackground hΦ hU τ y v
  change HasDerivAt (fun t : ℝ =>
      ((χ τ : ℝ) : ℂ) * scalarTestBackground Φ U (τ, y + t • v)) _ 0
  have h' := h.const_mul (((χ τ : ℝ) : ℂ))
  convert h' using 1

#print axioms differentiableAt_scalarTestBackground
#print axioms fderiv_scalarTestBackground
#print axioms hasLineDerivAt_scalarTestBackground
#print axioms hasLineDerivAt_cutoff_scalarTestBackground

end UnforcedLeray.Cons.C03.Concrete
