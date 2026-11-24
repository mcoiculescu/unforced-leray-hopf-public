import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Lemmas

/-!
# `smul_divEps_im`: `div_ε` of a real tensor has real coefficients (source 1660-1665)

Route. For `g : Profile → ℂ` with real values, every real-direction Fréchet derivative is real:
`Complex.imCLM ∘ g` is constant zero, so its derivative vanishes, and the derivative of `g`
composed with `imCLM` is that derivative (`HasFDerivAt.unique`); if `g` is not differentiable the
derivative is `0`. Then `divEps` is built from real-linear combinations of such derivatives and of
the real coefficients `p.1`, `p.2.2`, `ε`, so its components have zero imaginary part.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked

open UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Short.PartIIIb.NearInst UnforcedLeray.Short.PartIIIb.NearInst.Delta
  UnforcedLeray.Cons.C03.Concrete UnforcedLeray.Blueprint.Planar

/-- A real-valued complex function has real Fréchet derivatives. -/
theorem fderiv_im_eq_zero_of_real {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : E → ℂ) (hg : ∀ x, (g x).im = 0) (p v : E) : (fderiv ℝ g p v).im = 0 := by
  by_cases hd : DifferentiableAt ℝ g p
  · have h1 : HasFDerivAt (fun x => Complex.imCLM (g x))
        (Complex.imCLM.comp (fderiv ℝ g p)) p :=
      Complex.imCLM.hasFDerivAt.comp p hd.hasFDerivAt
    have hfun : (fun x => Complex.imCLM (g x)) = fun _ => (0 : ℝ) := by
      funext x
      simp [hg x]
    have h2 : HasFDerivAt (fun x => Complex.imCLM (g x)) (0 : E →L[ℝ] ℝ) p := by
      rw [hfun]
      exact hasFDerivAt_const _ _
    have h3 := h1.unique h2
    have h4 := congrArg (fun L : E →L[ℝ] ℝ => L v) h3
    simpa using h4
  · rw [fderiv_zero_of_not_differentiableAt hd]
    simp

/-- The operator `Q_ε` preserves real-valued functions. -/
theorem opQ_im_zero (ε : ℝ) (f : UnforcedLeray.B0220.Profile → ℂ) (hf : ∀ x, (f x).im = 0)
    (x : UnforcedLeray.B0220.Profile) :
    (UnforcedLeray.Short.PartIIa.opQ ε f x).im = 0 := by
  have a := fderiv_im_eq_zero_of_real f hf x (0, 1, 0)
  have b := fderiv_im_eq_zero_of_real f hf x (1, 0, 0)
  have c := fderiv_im_eq_zero_of_real f hf x (0, 0, 1)
  have d := hf x
  simp [UnforcedLeray.Short.PartIIa.opQ, UnforcedLeray.Short.PartIIa.opK,
    UnforcedLeray.Short.PartIIa.opS, UnforcedLeray.Short.PartIIa.pdQ,
    UnforcedLeray.Short.PartIIa.pdS, UnforcedLeray.Short.PartIIa.pdEta, a, b, c, d]

/-- The derivative `∂_η` preserves real-valued functions. -/
theorem pdEta_im_zero (f : UnforcedLeray.B0220.Profile → ℂ) (hf : ∀ x, (f x).im = 0)
    (x : UnforcedLeray.B0220.Profile) :
    (UnforcedLeray.Short.PartIIa.pdEta f x).im = 0 :=
  fderiv_im_eq_zero_of_real f hf x _

/-- `div_ε` of a real tensor has real coefficients (source 1660-1665). -/
theorem smul_divEps_im (ε : ℝ) (M : UnforcedLeray.B0220.Profile → UnforcedLeray.Short.PartIIa.TensorVal) (hM : ∀ p i, (M p i).im = 0) (p : UnforcedLeray.B0220.Profile) (i : Fin 2) : (((p.1 : ℂ) • UnforcedLeray.Short.PartIIa.divEps ε M p) i).im = 0 := by
  have h0 : (UnforcedLeray.Short.PartIIa.divEps ε M p 0).im = 0 := by
    have e := opQ_im_zero ε (fun x => M x 0) (fun x => hM x 0) p
    have e2 := pdEta_im_zero (fun x => M x 1) (fun x => hM x 1) p
    have e3 : ((ε : ℂ) * M p 3).im = 0 := by simp [hM p 3]
    change (UnforcedLeray.Short.PartIIa.opQ ε (fun x => M x 0) p
      + UnforcedLeray.Short.PartIIa.pdEta (fun x => M x 1) p - (ε : ℂ) * M p 3).im = 0
    simp [Complex.sub_im, Complex.add_im, e, e2, e3]
  have h1 : (UnforcedLeray.Short.PartIIa.divEps ε M p 1).im = 0 := by
    have e := opQ_im_zero ε (fun x => M x 1) (fun x => hM x 1) p
    have e2 := pdEta_im_zero (fun x => M x 2) (fun x => hM x 2) p
    change (UnforcedLeray.Short.PartIIa.opQ ε (fun x => M x 1) p
      + UnforcedLeray.Short.PartIIa.pdEta (fun x => M x 2) p).im = 0
    simp [Complex.add_im, e, e2]
  have hX : (UnforcedLeray.Short.PartIIa.divEps ε M p i).im = 0 := by
    fin_cases i
    · exact h0
    · exact h1
  simp [PiLp.smul_apply, Complex.mul_im, hX]

end UnforcedLeray.Short.PartIIIb.NearInst.Masked
