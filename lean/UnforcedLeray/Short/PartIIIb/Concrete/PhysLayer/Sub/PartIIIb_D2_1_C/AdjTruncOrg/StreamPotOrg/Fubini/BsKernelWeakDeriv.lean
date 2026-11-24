import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Fubini.Defs
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Fubini.BsKernelNewton
import UnforcedLeray.Analysis.Pressure.NewtonIdentity
import UnforcedLeray.Statement
import UnforcedLeray.TestFunctions

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The real-valued Newton identity, in the `EuclideanSpace.single` form. -/
private theorem wd_real (j : Fin 3) {φ : Space → ℝ} (hφ : UnforcedLeray.IsSpatialTest φ) :
    ∫ x : Space, UnforcedLeray.PressureAnalysis.newtonPotential x *
        fderiv ℝ φ x (EuclideanSpace.single j (1 : ℝ))
      = -∫ x : Space, UnforcedLeray.PressureAnalysis.newtonGradientKernel j x * φ x := by
  have h := UnforcedLeray.PressureAnalysis.newtonGradientKernel_test j hφ
  simp only [UnforcedLeray.spatialTestDerivative, UnforcedLeray.coordinateVector] at h
  rw [h, neg_neg]

/-- Fréchet derivative of a complex function splits into real and imaginary parts. -/
private theorem fderiv_re_im (g : Space → ℂ) (hg : Differentiable ℝ g) (y v : Space) :
    fderiv ℝ g y v = ((fderiv ℝ (fun x => (g x).re) y v : ℝ) : ℂ)
      + ((fderiv ℝ (fun x => (g x).im) y v : ℝ) : ℂ) * Complex.I := by
  have key : ∀ L : ℂ →L[ℝ] ℝ, fderiv ℝ (fun x => L (g x)) y v = L (fderiv ℝ g y v) := by
    intro L
    show fderiv ℝ (L ∘ g) y v = _
    rw [((L.hasFDerivAt (x := g y)).comp y (hg y).hasFDerivAt).fderiv]
    rfl
  have h1 := key Complex.reCLM
  have h2 := key Complex.imCLM
  simp only [Complex.reCLM_apply, Complex.imCLM_apply] at h1 h2
  rw [h1, h2]
  exact (Complex.re_add_im _).symm

/-- Integral of a real/imaginary split. -/
private theorem integral_split (a b : Space → ℝ) (ha : Integrable a) (hb : Integrable b) :
    ∫ x, ((a x : ℝ) : ℂ) + ((b x : ℝ) : ℂ) * Complex.I
      = ((∫ x, a x : ℝ) : ℂ) + ((∫ x, b x : ℝ) : ℂ) * Complex.I := by
  refine (integral_add ha.ofReal (hb.ofReal.mul_const Complex.I)).trans ?_
  rw [integral_mul_const]
  exact congrArg₂ (· + ·) integral_complex_ofReal
    (congrArg (· * Complex.I) integral_complex_ofReal)

private theorem re_test {g : Space → ℂ} (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) :
    UnforcedLeray.IsSpatialTest (fun x => (g x).re) :=
  ⟨Complex.reCLM.contDiff.comp hg, hc.comp_left (g := fun z : ℂ => z.re) Complex.zero_re⟩

private theorem im_test {g : Space → ℂ} (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) :
    UnforcedLeray.IsSpatialTest (fun x => (g x).im) :=
  ⟨Complex.imCLM.contDiff.comp hg, hc.comp_left (g := fun z : ℂ => z.im) Complex.zero_im⟩

/-- The complex Newton identity for smooth compactly supported `g`. -/
private theorem wd_complex (j : Fin 3) {g : Space → ℂ} (hg : ContDiff ℝ ∞ g)
    (hc : HasCompactSupport g) :
    ∫ x : Space, ((UnforcedLeray.PressureAnalysis.newtonPotential x : ℝ) : ℂ) *
        fderiv ℝ g x (EuclideanSpace.single j (1 : ℝ))
      = -∫ x : Space, ((UnforcedLeray.PressureAnalysis.newtonGradientKernel j x : ℝ) : ℂ) * g x := by
  have hdiff : Differentiable ℝ g := hg.differentiable (by simp)
  have hr := re_test hg hc
  have hi := im_test hg hc
  have hI1 : Integrable (fun x : Space =>
      UnforcedLeray.PressureAnalysis.newtonPotential x * fderiv ℝ (fun x => (g x).re) x
        (EuclideanSpace.single j (1 : ℝ))) :=
    UnforcedLeray.PressureAnalysis.integrable_newtonPotential_mul
      (φ := fun x => fderiv ℝ (fun x => (g x).re) x (EuclideanSpace.single j (1 : ℝ)))
      (hr.derivative j).continuous
      (hr.derivative j).compact
  have hI2 : Integrable (fun x : Space =>
      UnforcedLeray.PressureAnalysis.newtonPotential x * fderiv ℝ (fun x => (g x).im) x
        (EuclideanSpace.single j (1 : ℝ))) :=
    UnforcedLeray.PressureAnalysis.integrable_newtonPotential_mul
      (φ := fun x => fderiv ℝ (fun x => (g x).im) x (EuclideanSpace.single j (1 : ℝ)))
      (hi.derivative j).continuous
      (hi.derivative j).compact
  have hJ1 : Integrable (fun x : Space =>
      UnforcedLeray.PressureAnalysis.newtonGradientKernel j x * (g x).re) :=
    UnforcedLeray.PressureAnalysis.newtonGradientKernel_integrable_mul_test j
      (φ := fun x => (g x).re) (hr.continuous) hr.compact
  have hJ2 : Integrable (fun x : Space =>
      UnforcedLeray.PressureAnalysis.newtonGradientKernel j x * (g x).im) :=
    UnforcedLeray.PressureAnalysis.newtonGradientKernel_integrable_mul_test j
      (φ := fun x => (g x).im) (hi.continuous) hi.compact
  have hL : ∫ x : Space, ((UnforcedLeray.PressureAnalysis.newtonPotential x : ℝ) : ℂ) *
        fderiv ℝ g x (EuclideanSpace.single j (1 : ℝ))
      = ∫ x : Space, ((UnforcedLeray.PressureAnalysis.newtonPotential x *
            fderiv ℝ (fun x => (g x).re) x (EuclideanSpace.single j (1 : ℝ)) : ℝ) : ℂ)
          + ((UnforcedLeray.PressureAnalysis.newtonPotential x *
            fderiv ℝ (fun x => (g x).im) x (EuclideanSpace.single j (1 : ℝ)) : ℝ) : ℂ)
              * Complex.I := by
    congr 1
    funext x
    rw [fderiv_re_im g hdiff x]
    push_cast
    ring
  have hR : ∫ x : Space, ((UnforcedLeray.PressureAnalysis.newtonGradientKernel j x : ℝ) : ℂ) * g x
      = ∫ x : Space, ((UnforcedLeray.PressureAnalysis.newtonGradientKernel j x * (g x).re : ℝ) : ℂ)
          + ((UnforcedLeray.PressureAnalysis.newtonGradientKernel j x * (g x).im : ℝ) : ℂ)
              * Complex.I := by
    congr 1
    funext x
    conv_lhs => rw [← Complex.re_add_im (g x)]
    push_cast
    ring
  rw [hL, hR, integral_split _ _ hI1 hI2, integral_split _ _ hJ1 hJ2,
    wd_real j hr, wd_real j hi]
  push_cast
  ring

/-- **Weak derivative of the Newton potential** (source lines 1351-1362 via `curl ψ = Φ`). -/
theorem bsKernelWeakDeriv : BSKernelWeakDeriv := by
  intro h hh hc z j
  have hK : ∀ (w : Space) (i : Fin 3), bsKernel w i =
      ((-(UnforcedLeray.PressureAnalysis.newtonGradientKernel i w) : ℝ) : ℂ) := bsKernelNewton
  have hh' : ContDiff ℝ ∞ h := hh
  have hgs : ContDiff ℝ ∞ (fun x : Space => h (x + z)) :=
    hh'.comp (contDiff_id.add contDiff_const)
  have hgc : HasCompactSupport (fun x : Space => h (x + z)) :=
    hc.comp_homeomorph (Homeomorph.addRight z)
  have hL : ∫ y : Space, ((UnforcedLeray.PressureAnalysis.newtonPotential (y - z) : ℝ) : ℂ) *
        fderiv ℝ h y (EuclideanSpace.single j (1 : ℝ))
      = ∫ x : Space, ((UnforcedLeray.PressureAnalysis.newtonPotential x : ℝ) : ℂ) *
        fderiv ℝ (fun x : Space => h (x + z)) x (EuclideanSpace.single j (1 : ℝ)) := by
    refine Eq.trans (integral_add_right_eq_self (fun y : Space =>
      ((UnforcedLeray.PressureAnalysis.newtonPotential (y - z) : ℝ) : ℂ) *
        fderiv ℝ h y (EuclideanSpace.single j (1 : ℝ))) z).symm ?_
    congr 1
    funext x
    simp only [add_sub_cancel_right, fderiv_comp_add_right]
  have hR : ∫ y : Space, bsKernel (y - z) j * h y
      = -∫ x : Space, ((UnforcedLeray.PressureAnalysis.newtonGradientKernel j x : ℝ) : ℂ) *
        h (x + z) := by
    refine Eq.trans (integral_add_right_eq_self (fun y : Space => bsKernel (y - z) j * h y) z).symm ?_
    have key : ∀ x : Space, bsKernel (x + z - z) j * h (x + z) =
        -(((UnforcedLeray.PressureAnalysis.newtonGradientKernel j x : ℝ) : ℂ) * h (x + z)) := by
      intro x
      rw [add_sub_cancel_right, hK]
      push_cast
      ring
    simp only [key]
    rw [integral_neg]
  rw [hL, hR]
  exact wd_complex j hgs hgc

end UnforcedLeray.Short.PartIIIb.Concrete
