import UnforcedLeray.Short.PartIIa.Sub.N02_4_4
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Part II-a, task `PartII-a:N02/4/4`, helper for `NzModeBounds`: the operator `S = s ∂_s`

Helper file for `NonzeroMode/ModeBounds.lean` (target `NzModeBounds`, source lines 1722-1727).
Contents: smoothness of `nzS2`, the commutation `∂_η (S g) = S (∂_η g)` (from the symmetry of second
derivatives), linearity of `nzS2` on sums and products, and the propagation of the one-mode system
`NzModeEq` under `S^[n]`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

/-- The `w`-derivative `∂_w g` of a smooth function, as a function of the point. -/
theorem nzmb_contDiff_snd (g : ℝ × ℝ → ℂ) (hg : ContDiff ℝ ∞ g) (w : ℝ × ℝ) :
    ContDiff ℝ ∞ (fun y => fderiv ℝ g y w) :=
  (contDiff_infty_iff_fderiv.mp hg).2.clm_apply contDiff_const

theorem nzmb_contDiff_nzS2 (g : ℝ × ℝ → ℂ) (hg : ContDiff ℝ ∞ g) : ContDiff ℝ ∞ (nzS2 g) := by
  show ContDiff ℝ ∞ (fun x : ℝ × ℝ => x.1 • fderiv ℝ g x (1, 0))
  exact contDiff_fst.smul (nzmb_contDiff_snd g hg (1, 0))

theorem nzmb_symm (g : ℝ × ℝ → ℂ) (hg : ContDiff ℝ ∞ g) (x v w : ℝ × ℝ) :
    fderiv ℝ (fderiv ℝ g) x v w = fderiv ℝ (fderiv ℝ g) x w v :=
  (hg.contDiffAt.isSymmSndFDerivAt (by simp)) v w

theorem nzmb_fderiv_eval (g : ℝ × ℝ → ℂ) (hg : ContDiff ℝ ∞ g) (w x v : ℝ × ℝ) :
    fderiv ℝ (fun y => fderiv ℝ g y w) x v = fderiv ℝ (fderiv ℝ g) x v w := by
  have hc : DifferentiableAt ℝ (fderiv ℝ g) x :=
    ((contDiff_infty_iff_fderiv.mp hg).2.differentiable (by simp)) x
  rw [fderiv_clm_apply hc (differentiableAt_const w)]
  simp

/-- `S` commutes with `∂_η`: `∂_η (S g) = S (∂_η g)`, by the symmetry of second derivatives. -/
theorem nzmb_fderiv_nzS2 (g : ℝ × ℝ → ℂ) (hg : ContDiff ℝ ∞ g) (x : ℝ × ℝ) :
    fderiv ℝ (nzS2 g) x (0, 1) = nzS2 (fun y => fderiv ℝ g y (0, 1)) x := by
  have hh : DifferentiableAt ℝ (fun y => fderiv ℝ g y (1, 0)) x :=
    ((nzmb_contDiff_snd g hg (1, 0)).differentiable (by simp)) x
  have hd : HasFDerivAt (fun y : ℝ × ℝ => y.1 • fderiv ℝ g y (1, 0))
      (x.1 • fderiv ℝ (fun y => fderiv ℝ g y (1, 0)) x
        + (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (fderiv ℝ g x (1, 0))) x :=
    hasFDerivAt_fst.smul hh.hasFDerivAt
  rw [show nzS2 g = (fun y : ℝ × ℝ => y.1 • fderiv ℝ g y (1, 0)) from rfl]
  simp only [nzS2]
  rw [hd.fderiv]
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply]
  rw [nzmb_fderiv_eval g hg (1, 0) x (0, 1), nzmb_fderiv_eval g hg (0, 1) x (1, 0),
    nzmb_symm g hg x (0, 1) (1, 0)]
  simp

theorem nzmb_nzS2_sub (f g : ℝ × ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (x : ℝ × ℝ) : nzS2 (fun y => f y - g y) x = nzS2 f x - nzS2 g x := by
  simp only [nzS2]
  rw [fderiv_fun_sub ((hf.differentiable (by simp)) x) ((hg.differentiable (by simp)) x)]
  simp [smul_sub]

theorem nzmb_nzS2_add (f g : ℝ × ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (x : ℝ × ℝ) : nzS2 (fun y => f y + g y) x = nzS2 f x + nzS2 g x := by
  simp only [nzS2]
  rw [fderiv_fun_add ((hf.differentiable (by simp)) x) ((hg.differentiable (by simp)) x)]
  simp [smul_add]

theorem nzmb_nzS2_const_mul (c : ℂ) (f : ℝ × ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (x : ℝ × ℝ) :
    nzS2 (fun y => c * f y) x = c * nzS2 f x := by
  simp only [nzS2]
  rw [((hf.differentiable (by simp)) x).hasFDerivAt.const_mul c |>.fderiv]
  simp only [smul_apply, smul_eq_mul, Complex.real_smul]
  ring

/-- Iterates of `S` are smooth. -/
theorem nzmb_iter_contDiff (n : ℕ) :
    ∀ g : ℝ × ℝ → ℂ, ContDiff ℝ ∞ g → ContDiff ℝ ∞ (nzS2^[n] g) := by
  induction n with
  | zero => intro g hg; simpa using hg
  | succ n ih =>
    intro g hg
    rw [Function.iterate_succ_apply']
    exact nzmb_contDiff_nzS2 _ (ih g hg)

/-- `∂_η` commutes with `S^[n]`. -/
theorem nzmb_iter_fderiv (n : ℕ) : ∀ g : ℝ × ℝ → ℂ, ContDiff ℝ ∞ g → ∀ x : ℝ × ℝ,
    fderiv ℝ (nzS2^[n] g) x (0, 1) = nzS2^[n] (fun y => fderiv ℝ g y (0, 1)) x := by
  induction n with
  | zero => intro g hg x; simp
  | succ n ih =>
    intro g hg x
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      nzmb_fderiv_nzS2 _ (nzmb_iter_contDiff n g hg) x]
    have hfun : (fun y => fderiv ℝ (nzS2^[n] g) y (0, 1))
        = nzS2^[n] (fun y => fderiv ℝ g y (0, 1)) :=
      funext fun y => ih g hg y
    rw [hfun]

/-- One step: `S` maps solutions of the one-mode system to solutions with data `S a, S b`. -/
theorem nzmb_modeEq_nzS2 (k : ℝ) (a b φ ψ : ℝ × ℝ → ℂ)
    (hφ : ContDiff ℝ ∞ φ) (hψ : ContDiff ℝ ∞ ψ)
    (h : NzModeEq k a b φ ψ) : NzModeEq k (nzS2 a) (nzS2 b) (nzS2 φ) (nzS2 ψ) := by
  unfold NzModeEq at h ⊢
  have hA : a = fun y => Complex.I * (k : ℂ) * φ y - fderiv ℝ ψ y (0, 1) :=
    funext fun y => ((h y).1).symm
  have hB : b = fun y => fderiv ℝ φ y (0, 1) + Complex.I * (k : ℂ) * ψ y :=
    funext fun y => ((h y).2).symm
  have hf1 : ContDiff ℝ ∞ (fun y => Complex.I * (k : ℂ) * φ y) := contDiff_const.mul hφ
  have hf2 : ContDiff ℝ ∞ (fun y => Complex.I * (k : ℂ) * ψ y) := contDiff_const.mul hψ
  intro x
  constructor
  · rw [nzmb_fderiv_nzS2 ψ hψ x, hA,
      nzmb_nzS2_sub _ _ hf1 (nzmb_contDiff_snd ψ hψ (0, 1)) x,
      nzmb_nzS2_const_mul _ φ hφ x]
  · rw [nzmb_fderiv_nzS2 φ hφ x, hB,
      nzmb_nzS2_add _ _ (nzmb_contDiff_snd φ hφ (0, 1)) hf2 x,
      nzmb_nzS2_const_mul _ ψ hψ x]

/-- Iterated: `(S^[n] a, S^[n] b, S^[n] φ, S^[n] ψ)` solves the one-mode system. -/
theorem nzmb_modeEq_iter (k : ℝ) (n : ℕ) :
    ∀ (a b φ ψ : ℝ × ℝ → ℂ), ContDiff ℝ ∞ a → ContDiff ℝ ∞ b → ContDiff ℝ ∞ φ →
      ContDiff ℝ ∞ ψ → NzModeEq k a b φ ψ →
      NzModeEq k (nzS2^[n] a) (nzS2^[n] b) (nzS2^[n] φ) (nzS2^[n] ψ) := by
  induction n with
  | zero => intro a b φ ψ _ _ _ _ h; simpa using h
  | succ n ih =>
    intro a b φ ψ ha hb hφ hψ h
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', Function.iterate_succ_apply',
      Function.iterate_succ_apply']
    exact nzmb_modeEq_nzS2 k _ _ _ _ (nzmb_iter_contDiff n φ hφ) (nzmb_iter_contDiff n ψ hψ)
      (ih a b φ ψ ha hb hφ hψ h)

end UnforcedLeray.Short.PartIIa
