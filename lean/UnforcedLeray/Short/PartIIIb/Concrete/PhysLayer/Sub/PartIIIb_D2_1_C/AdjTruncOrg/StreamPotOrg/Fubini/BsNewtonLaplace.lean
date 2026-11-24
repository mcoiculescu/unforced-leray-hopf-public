import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Fubini.Defs
import UnforcedLeray.Analysis.Pressure.ConvolutionIdentity
import UnforcedLeray.Analysis.Pressure.NewtonIdentity
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Coordinate Laplacian of a vector-valued function, in the form used by `bsLapS`. -/
theorem bsNL_lap_comp {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) (f : Space → E) (hf : ContDiff ℝ ∞ f) (y : Space) :
    ∑ j : Fin 3, fderiv ℝ (fun x => fderiv ℝ (fun x => L (f x)) x (EuclideanSpace.single j (1 : ℝ)))
        y (EuclideanSpace.single j (1 : ℝ))
      = L (∑ j : Fin 3, fderiv ℝ (fun x => fderiv ℝ f x (EuclideanSpace.single j (1 : ℝ))) y
        (EuclideanSpace.single j (1 : ℝ))) := by
  have hdiff : Differentiable ℝ f := hf.differentiable (by simp)
  have hfd : ContDiff ℝ ∞ (fderiv ℝ f) := (contDiff_infty_iff_fderiv.mp hf).2
  have hgd : ∀ j : Fin 3,
      Differentiable ℝ (fun x => fderiv ℝ f x (EuclideanSpace.single j (1 : ℝ))) := fun j =>
    (hfd.clm_apply (contDiff_const (c := EuclideanSpace.single j (1 : ℝ)))).differentiable (by simp)
  have hLf : ∀ x, fderiv ℝ (fun x => L (f x)) x = L.comp (fderiv ℝ f x) := fun x =>
    ((L.hasFDerivAt : HasFDerivAt L L (f x)).comp x (hdiff x).hasFDerivAt).fderiv
  have hLd : ∀ (j : Fin 3) (y : Space),
      fderiv ℝ (fun x => L (fderiv ℝ f x (EuclideanSpace.single j (1 : ℝ)))) y
        (EuclideanSpace.single j (1 : ℝ))
        = L (fderiv ℝ (fun x => fderiv ℝ f x (EuclideanSpace.single j (1 : ℝ))) y
          (EuclideanSpace.single j (1 : ℝ))) := by
    intro j y
    have h : fderiv ℝ (fun x => L (fderiv ℝ f x (EuclideanSpace.single j (1 : ℝ)))) y
        = L.comp (fderiv ℝ (fun x => fderiv ℝ f x (EuclideanSpace.single j (1 : ℝ))) y) :=
      ((L.hasFDerivAt : HasFDerivAt L L (fderiv ℝ f y (EuclideanSpace.single j (1 : ℝ)))).comp y
        (hgd j y).hasFDerivAt).fderiv
    rw [h]
    rfl
  simp only [hLf, ContinuousLinearMap.comp_apply, hLd, map_sum]

/-- Coordinate Laplacian is additive. -/
theorem bsNL_lap_add {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f g : Space → E) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (y : Space) :
    ∑ j : Fin 3, fderiv ℝ (fun x => fderiv ℝ (fun x => f x + g x) x (EuclideanSpace.single j (1 : ℝ)))
        y (EuclideanSpace.single j (1 : ℝ))
      = (∑ j : Fin 3, fderiv ℝ (fun x => fderiv ℝ f x (EuclideanSpace.single j (1 : ℝ))) y
          (EuclideanSpace.single j (1 : ℝ)))
        + ∑ j : Fin 3, fderiv ℝ (fun x => fderiv ℝ g x (EuclideanSpace.single j (1 : ℝ))) y
          (EuclideanSpace.single j (1 : ℝ)) := by
  have hdf : Differentiable ℝ f := hf.differentiable (by simp)
  have hdg : Differentiable ℝ g := hg.differentiable (by simp)
  have hgf : ∀ j : Fin 3, Differentiable ℝ (fun x => fderiv ℝ f x (EuclideanSpace.single j (1 : ℝ))) :=
    fun j => ((contDiff_infty_iff_fderiv.mp hf).2.clm_apply
      (contDiff_const (c := EuclideanSpace.single j (1 : ℝ)))).differentiable (by simp)
  have hgg : ∀ j : Fin 3, Differentiable ℝ (fun x => fderiv ℝ g x (EuclideanSpace.single j (1 : ℝ))) :=
    fun j => ((contDiff_infty_iff_fderiv.mp hg).2.clm_apply
      (contDiff_const (c := EuclideanSpace.single j (1 : ℝ)))).differentiable (by simp)
  have hsum : ∀ (A B : Space → E) (z : Space), DifferentiableAt ℝ A z → DifferentiableAt ℝ B z →
      fderiv ℝ (fun x => A x + B x) z = fderiv ℝ A z + fderiv ℝ B z :=
    fun A B z hA hB => fderiv_add hA hB
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have h1 : (fun x => fderiv ℝ (fun x => f x + g x) x (EuclideanSpace.single j (1 : ℝ)))
      = fun x => fderiv ℝ f x (EuclideanSpace.single j (1 : ℝ))
          + fderiv ℝ g x (EuclideanSpace.single j (1 : ℝ)) := by
    funext x
    rw [hsum f g x (hdf x) (hdg x)]
    rfl
  rw [h1, hsum _ _ y (hgf j y) (hgg j y)]
  rfl

/-- Real-valued smooth functions: the complex coordinate Laplacian of `(u : ℂ)` is `(Δu : ℂ)`. -/
theorem bsNL_ofReal (u : Space → ℝ) (hu : ContDiff ℝ ∞ u) (y : Space) :
    bsLapS (fun x => ((u x : ℝ) : ℂ)) y = ((UnforcedLeray.Heat.laplacian u y : ℝ) : ℂ) := by
  have h := bsNL_lap_comp Complex.ofRealCLM u hu y
  simp only [Complex.ofRealCLM_apply] at h
  have h2 : UnforcedLeray.Heat.laplacian u y
      = ∑ j : Fin 3, fderiv ℝ (fun x => fderiv ℝ u x (EuclideanSpace.single j (1 : ℝ))) y
          (EuclideanSpace.single j (1 : ℝ)) := rfl
  rw [h2]
  exact h

/-- Multiplication by `I` commutes with the coordinate Laplacian. -/
theorem bsNL_const_mul (u : Space → ℝ) (hu : ContDiff ℝ ∞ u) (y : Space) :
    bsLapS (fun x => Complex.I * ((u x : ℝ) : ℂ)) y = Complex.I * bsLapS (fun x => ((u x : ℝ) : ℂ)) y := by
  have hc : ContDiff ℝ ∞ (fun x => ((u x : ℝ) : ℂ)) := Complex.ofRealCLM.contDiff.comp hu
  have h := bsNL_lap_comp (ContinuousLinearMap.mul ℝ ℂ Complex.I) (fun x => ((u x : ℝ) : ℂ)) hc y
  simp only [ContinuousLinearMap.mul_apply'] at h
  exact h

/-- Complex coordinate Laplacian splits into the Laplacians of the real and imaginary parts. -/
theorem bsNL_split (φ : Space → ℂ) (hφ : ContDiff ℝ ∞ φ) (y : Space) :
    bsLapS φ y = ((UnforcedLeray.Heat.laplacian (fun x => (φ x).re) y : ℝ) : ℂ)
      + Complex.I * ((UnforcedLeray.Heat.laplacian (fun x => (φ x).im) y : ℝ) : ℂ) := by
  have hre : ContDiff ℝ ∞ (fun x => (φ x).re) := Complex.reCLM.contDiff.comp hφ
  have him : ContDiff ℝ ∞ (fun x => (φ x).im) := Complex.imCLM.contDiff.comp hφ
  have hfun : φ = fun x => ((φ x).re : ℂ) + Complex.I * ((φ x).im : ℂ) :=
    funext fun x => by apply Complex.ext <;> simp
  have hA : ContDiff ℝ ∞ (fun x => ((φ x).re : ℂ)) := Complex.ofRealCLM.contDiff.comp hre
  have hB : ContDiff ℝ ∞ (fun x => Complex.I * ((φ x).im : ℂ)) :=
    contDiff_const.mul (Complex.ofRealCLM.contDiff.comp him)
  have e1 : bsLapS (fun x => Complex.I * ((φ x).im : ℂ)) y
      = Complex.I * bsLapS (fun x => ((φ x).im : ℂ)) y :=
    bsNL_const_mul (fun x => (φ x).im) him y
  have e2 : bsLapS (fun x => ((φ x).re : ℂ)) y
      = ((UnforcedLeray.Heat.laplacian (fun x => (φ x).re) y : ℝ) : ℂ) :=
    bsNL_ofReal (fun x => (φ x).re) hre y
  have e3 : bsLapS (fun x => ((φ x).im : ℂ)) y
      = ((UnforcedLeray.Heat.laplacian (fun x => (φ x).im) y : ℝ) : ℂ) :=
    bsNL_ofReal (fun x => (φ x).im) him y
  calc bsLapS φ y = bsLapS (fun x => ((φ x).re : ℂ) + Complex.I * ((φ x).im : ℂ)) y := by
        rw [← hfun]
    _ = bsLapS (fun x => ((φ x).re : ℂ)) y + bsLapS (fun x => Complex.I * ((φ x).im : ℂ)) y :=
        bsNL_lap_add _ _ hA hB y
    _ = _ := by rw [e1, e2, e3]

/-- Translated Newton integral: `∫ P(y - z) Δu(y) dy = -u(z)` for a real spatial test `u`. -/
theorem bsNL_real_int (z : Space) (u : Space → ℝ) (hu : IsSpatialTest u) :
    ∫ y : Space, UnforcedLeray.PressureAnalysis.newtonPotential (y - z)
        * UnforcedLeray.Heat.laplacian u y = -u z := by
  have hT : IsSpatialTest (fun y => u (y + z)) :=
    ⟨hu.smooth.comp (contDiff_id.add contDiff_const),
      hu.compact.comp_homeomorph (Homeomorph.addRight z)⟩
  have h1 := UnforcedLeray.PressureAnalysis.newtonPotential_laplacian_test hT
  have h2 : ∀ x : Space, UnforcedLeray.Heat.laplacian (fun y => u (y + z)) x
      = UnforcedLeray.Heat.laplacian u (x + z) := fun x =>
    UnforcedLeray.PressureAnalysis.scalar_laplacian_translate z u x
  simp only [h2, zero_add] at h1
  have h3 : ∫ y : Space, UnforcedLeray.PressureAnalysis.newtonPotential (y - z)
        * UnforcedLeray.Heat.laplacian u y
      = ∫ x : Space, UnforcedLeray.PressureAnalysis.newtonPotential x
          * UnforcedLeray.Heat.laplacian u (x + z) := by
    rw [← integral_sub_right_eq_self (fun x : Space =>
      UnforcedLeray.PressureAnalysis.newtonPotential x * UnforcedLeray.Heat.laplacian u (x + z)) z]
    congr 1
    funext y
    simp only [sub_add_cancel]
  rw [h3]
  exact h1

/-- Integrability of `y ↦ P(y - z) Δu(y)` for a real spatial test `u`. -/
theorem bsNL_integrable (z : Space) (u : Space → ℝ) (hu : IsSpatialTest u) :
    Integrable (fun y : Space => UnforcedLeray.PressureAnalysis.newtonPotential (y - z)
        * UnforcedLeray.Heat.laplacian u y) := by
  have hΔ := UnforcedLeray.PressureAnalysis.scalarTest_laplacian hu
  have H := UnforcedLeray.PressureAnalysis.integrable_newtonPotential_mul
    (φ := fun x => UnforcedLeray.Heat.laplacian u (x + z))
    (hΔ.smooth.continuous.comp (continuous_add_const z))
    (hΔ.compact.comp_homeomorph (Homeomorph.addRight z))
  have H2 := H.comp_sub_right z
  simpa using H2

/-- The complex Newton identity for complex spatial tests. -/
theorem bsNewtonLaplace : BSNewtonLaplace := by
  intro φ hφ hc z
  have hφ' : ContDiff ℝ ∞ φ := hφ
  have hre : ContDiff ℝ ∞ (fun x => (φ x).re) := Complex.reCLM.contDiff.comp hφ'
  have him : ContDiff ℝ ∞ (fun x => (φ x).im) := Complex.imCLM.contDiff.comp hφ'
  have hUa : IsSpatialTest (fun x => (φ x).re) :=
    ⟨hre, hc.comp_left Complex.zero_re⟩
  have hUb : IsSpatialTest (fun x => (φ x).im) :=
    ⟨him, hc.comp_left Complex.zero_im⟩
  have hpt : ∀ y : Space, ((UnforcedLeray.PressureAnalysis.newtonPotential (y - z) : ℝ) : ℂ)
      * bsLapS φ y
      = (((UnforcedLeray.PressureAnalysis.newtonPotential (y - z)
            * UnforcedLeray.Heat.laplacian (fun x => (φ x).re) y : ℝ)) : ℂ)
        + Complex.I * (((UnforcedLeray.PressureAnalysis.newtonPotential (y - z)
            * UnforcedLeray.Heat.laplacian (fun x => (φ x).im) y : ℝ)) : ℂ) := by
    intro y
    rw [bsNL_split φ hφ' y]
    push_cast
    ring
  simp only [hpt]
  have hIa := bsNL_integrable z _ hUa
  have hIb := bsNL_integrable z _ hUb
  have hRa := bsNL_real_int z _ hUa
  have hRb := bsNL_real_int z _ hUb
  have hIa' : Integrable (fun y : Space => (((UnforcedLeray.PressureAnalysis.newtonPotential (y - z)
      * UnforcedLeray.Heat.laplacian (fun x => (φ x).re) y : ℝ)) : ℂ)) volume := hIa.ofReal
  have hIb' : Integrable (fun y : Space => Complex.I * (((UnforcedLeray.PressureAnalysis.newtonPotential (y - z)
      * UnforcedLeray.Heat.laplacian (fun x => (φ x).im) y : ℝ)) : ℂ)) volume :=
    hIb.ofReal.const_mul Complex.I
  have eA : ∫ y : Space, (((UnforcedLeray.PressureAnalysis.newtonPotential (y - z)
      * UnforcedLeray.Heat.laplacian (fun x => (φ x).re) y : ℝ)) : ℂ)
      = ((∫ y : Space, UnforcedLeray.PressureAnalysis.newtonPotential (y - z)
      * UnforcedLeray.Heat.laplacian (fun x => (φ x).re) y : ℝ) : ℂ) := integral_ofReal
  have eB : ∫ y : Space, (((UnforcedLeray.PressureAnalysis.newtonPotential (y - z)
      * UnforcedLeray.Heat.laplacian (fun x => (φ x).im) y : ℝ)) : ℂ)
      = ((∫ y : Space, UnforcedLeray.PressureAnalysis.newtonPotential (y - z)
      * UnforcedLeray.Heat.laplacian (fun x => (φ x).im) y : ℝ) : ℂ) := integral_ofReal
  rw [integral_add hIa' hIb', integral_const_mul, eA, eB, hRa, hRb]
  apply Complex.ext <;> simp

end UnforcedLeray.Short.PartIIIb.Concrete
