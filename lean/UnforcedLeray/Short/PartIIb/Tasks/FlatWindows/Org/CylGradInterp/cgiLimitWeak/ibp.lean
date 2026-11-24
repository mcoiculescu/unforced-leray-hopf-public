import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T13_1_5_6_2

/-!
# Integration by parts for smooth `w` against a compactly supported test (`CgiIBP`)

Source of record: `the November 2 reference manuscript` lines 1933-1934
("integrate by parts against `φ`"). For smooth `w : Coord → ℂ` and a space-time test `φ`
(smooth with compact support), `∫ w ∂_{i+1} φ = -∫ ∂_{i+1} w φ`, by Mathlib's integration by
parts for the Fréchet derivative in the direction `cdir (i.succ)`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

open MeasureTheory Set Filter
open scoped ENNReal ContDiff Topology

/-- Integration by parts against a space-time test (SP 1933-1934). Proof of `CgiIBP`. -/
theorem cgiIBP_proof : CgiIBP := by
  intro w hw i φ hφ
  have hK : IsCompact (tsupport φ) := hφ.compact
  have hwd : ∀ x, DifferentiableAt ℝ w x := fun x => hw.differentiable (by simp) x
  have hφd : ∀ x, DifferentiableAt ℝ φ x := fun x => hφ.smooth.differentiable (by simp) x
  set ψ : Coord → ℂ := fun x => (φ x : ℂ) with hψdef
  have hψd : ∀ x, DifferentiableAt ℝ ψ x := fun x =>
    Complex.ofRealCLM.differentiableAt.comp x (hφd x)
  -- the derivative of `ψ` in a direction is the (complexified) derivative of `φ`
  have hfd : ∀ x (v : Coord), fderiv ℝ ψ x v = ((fderiv ℝ φ x v : ℝ) : ℂ) := by
    intro x v
    have h1 : HasFDerivAt (fun y => Complex.ofRealCLM (φ y))
        (Complex.ofRealCLM.comp (fderiv ℝ φ x)) x :=
      Complex.ofRealCLM.hasFDerivAt.comp x (hφd x).hasFDerivAt
    rw [show ψ = fun y => Complex.ofRealCLM (φ y) from rfl, h1.fderiv]
    simp
  -- vanishing outside the support of `φ`
  have hzero : ∀ x, x ∉ tsupport φ → ∀ v : Coord, fderiv ℝ φ x v = 0 := by
    intro x hx v
    rw [fderiv_of_notMem_tsupport ℝ hx]
    simp
  have hψz : ∀ x, x ∉ tsupport φ → ψ x = 0 := fun x hx => by
    simp [hψdef, image_eq_zero_of_notMem_tsupport hx]
  have hcont_ψ : Continuous ψ := Complex.continuous_ofReal.comp hφ.smooth.continuous
  have hcont_dψ : ∀ v : Coord, Continuous (fun x => fderiv ℝ ψ x v) := by
    intro v
    simp only [hfd]
    exact Complex.continuous_ofReal.comp
      ((hφ.smooth.continuous_fderiv (by simp)).clm_apply continuous_const)
  have hcont_dw : ∀ v : Coord, Continuous (fun x => fderiv ℝ w x v) := fun v =>
    (hw.continuous_fderiv (by simp)).clm_apply continuous_const
  -- integrability
  have hint1 : Integrable (fun x => fderiv ℝ w x (cdir i.succ) * ψ x) := by
    refine Continuous.integrable_of_hasCompactSupport
      ((hcont_dw _).mul hcont_ψ) (HasCompactSupport.intro hK fun x hx => ?_)
    simp [hψz x hx]
  have hint2 : Integrable (fun x => w x * fderiv ℝ ψ x (cdir i.succ)) := by
    refine Continuous.integrable_of_hasCompactSupport
      (hw.continuous.mul (hcont_dψ _)) (HasCompactSupport.intro hK fun x hx => ?_)
    simp [hfd, hzero x hx]
  have hint3 : Integrable (fun x => w x * ψ x) := by
    refine Continuous.integrable_of_hasCompactSupport
      (hw.continuous.mul hcont_ψ) (HasCompactSupport.intro hK fun x hx => ?_)
    simp [hψz x hx]
  have key := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume) (f := w)
    (g := ψ) (v := cdir i.succ) hint1 hint2 hint3 (fun x _ => hwd x) (fun x _ => hψd x)
  have e1 : ∀ x, (cpd i.succ φ x : ℂ) = fderiv ℝ ψ x (cdir i.succ) := fun x => by
    rw [cpd, hfd]
  simp only [e1]
  rw [key]
  congr 1

end UnforcedLeray.Short.IIb
