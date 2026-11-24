import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Add
import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N02_4_4

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0226

/-- Derivative of the `q`-exponential of mode `n`. -/
theorem nzfpExpDeriv (c : ℝ) (n : ℤ) (t : ℝ) :
    HasDerivAt
      (fun s : ℝ => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (s : ℂ) / (c : ℂ)))
      (Complex.I * ((nzk c n : ℝ) : ℂ) *
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (t : ℂ) / (c : ℂ))) t := by
  have h := (((hasDerivAt_id' t).ofReal_comp).const_mul
    (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) / (c : ℂ))).cexp
  have hfun : (fun s : ℝ => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (s : ℂ) / (c : ℂ)))
      = fun s : ℝ => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) / (c : ℂ) * (s : ℂ)) := by
    funext s
    congr 1
    ring
  have hexp : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (t : ℂ) / (c : ℂ))
      = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) / (c : ℂ) * (t : ℂ)) := by
    congr 1
    ring
  rw [hfun, hexp]
  convert h using 1
  unfold nzk
  push_cast
  ring

/-- Sums of `ℂ²`-valued vectors, evaluated at a coordinate. -/
theorem nzfpSumApply {ι : Type*} (s : Finset ι) (v : ι → MeridC) (i : Fin 2) :
    (∑ n ∈ s, v n) i = ∑ n ∈ s, v n i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, PiLp.add_apply, ih]

/-- Differentiability of one mode term, `q`-exponential times `g(s, η)`. -/
theorem nzfpDiffTerm (c : ℝ) (n : ℤ) (g : ℝ × ℝ → ℂ) (hg : ContDiff ℝ ∞ g) :
    Differentiable ℝ (fun p : Profile =>
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (p.2.1 : ℂ) / (c : ℂ)) * g (p.1, p.2.2)) := by
  have hgd : Differentiable ℝ g := hg.differentiable (by simp)
  have hq : Differentiable ℝ (fun p : Profile =>
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (p.2.1 : ℂ) / (c : ℂ))) := by
    fun_prop
  have hG : Differentiable ℝ (fun p : Profile => g (p.1, p.2.2)) :=
    hgd.comp (differentiable_fst.prodMk (differentiable_snd.comp differentiable_snd))
  exact hq.mul hG

/-- Differentiability of a finite mode sum. -/
theorem nzfpDiffSum (c : ℝ) (M : Finset ℤ) (g : ℤ → ℝ × ℝ → ℂ) (hg : ∀ n ∈ M, ContDiff ℝ ∞ (g n)) :
    Differentiable ℝ (nzModeSum c M g) := by
  have hterm : ∀ n ∈ M, Differentiable ℝ (fun p : Profile =>
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (p.2.1 : ℂ) / (c : ℂ)) • g n (p.1, p.2.2)) := by
    intro n hn
    have h := nzfpDiffTerm c n (g n) (hg n hn)
    simpa only [smul_eq_mul] using h
  unfold nzModeSum
  exact Differentiable.fun_sum hterm

/-- The `q`-derivative of a finite mode sum. -/
theorem nzfpPdQ (c : ℝ) (M : Finset ℤ) (g : ℤ → ℝ × ℝ → ℂ) (hg : ∀ n ∈ M, ContDiff ℝ ∞ (g n))
    (p : Profile) :
    pdQ (nzModeSum c M g) p = ∑ n ∈ M,
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (p.2.1 : ℂ) / (c : ℂ)) *
        (Complex.I * ((nzk c n : ℝ) : ℂ) * g n (p.1, p.2.2)) := by
  have hΦ : HasFDerivAt (nzModeSum c M g) (fderiv ℝ (nzModeSum c M g) (p.1, p.2.1, p.2.2))
      (p.1, p.2.1, p.2.2) :=
    (nzfpDiffSum c M g hg _).hasFDerivAt
  have hline : HasDerivAt (fun t : ℝ => ((p.1, t, p.2.2) : Profile)) ((0:ℝ), (1:ℝ), (0:ℝ)) p.2.1 :=
    (hasDerivAt_const p.2.1 p.1).prodMk ((hasDerivAt_id' p.2.1).prodMk (hasDerivAt_const p.2.1 p.2.2))
  have hc1 := hΦ.comp_hasDerivAt p.2.1 hline
  have hsum : HasDerivAt (fun t : ℝ => ∑ n ∈ M,
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (t : ℂ) / (c : ℂ)) * g n (p.1, p.2.2))
      (∑ n ∈ M, (Complex.I * ((nzk c n : ℝ) : ℂ) *
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (p.2.1 : ℂ) / (c : ℂ))) * g n (p.1, p.2.2))
      p.2.1 :=
    HasDerivAt.fun_sum (fun n _ => (nzfpExpDeriv c n p.2.1).mul_const (g n (p.1, p.2.2)))
  have hfun : (nzModeSum c M g ∘ fun t : ℝ => ((p.1, t, p.2.2) : Profile)) =
      fun t : ℝ => ∑ n ∈ M,
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (t : ℂ) / (c : ℂ)) * g n (p.1, p.2.2) := by
    funext t
    simp only [Function.comp, nzModeSum, smul_eq_mul]
  rw [hfun] at hc1
  have key := hc1.unique hsum
  unfold pdQ
  exact key.trans (Finset.sum_congr rfl (fun n _ => by ring))

/-- The `η`-derivative of a finite mode sum. -/
theorem nzfpPdEta (c : ℝ) (M : Finset ℤ) (g : ℤ → ℝ × ℝ → ℂ) (hg : ∀ n ∈ M, ContDiff ℝ ∞ (g n))
    (p : Profile) :
    pdEta (nzModeSum c M g) p = ∑ n ∈ M,
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (p.2.1 : ℂ) / (c : ℂ)) *
        fderiv ℝ (g n) (p.1, p.2.2) (0, 1) := by
  have hΦ : HasFDerivAt (nzModeSum c M g) (fderiv ℝ (nzModeSum c M g) (p.1, p.2.1, p.2.2))
      (p.1, p.2.1, p.2.2) :=
    (nzfpDiffSum c M g hg _).hasFDerivAt
  have hline : HasDerivAt (fun t : ℝ => ((p.1, p.2.1, t) : Profile)) ((0:ℝ), (0:ℝ), (1:ℝ)) p.2.2 :=
    (hasDerivAt_const p.2.2 p.1).prodMk ((hasDerivAt_const p.2.2 p.2.1).prodMk (hasDerivAt_id' p.2.2))
  have hc1 := hΦ.comp_hasDerivAt p.2.2 hline
  have hterm : ∀ n ∈ M, HasDerivAt (fun t : ℝ => g n (p.1, t))
      (fderiv ℝ (g n) (p.1, p.2.2) (0, 1)) p.2.2 := by
    intro n hn
    have hgd : DifferentiableAt ℝ (g n) (p.1, p.2.2) := (hg n hn).differentiable (by simp) _
    have hl : HasDerivAt (fun t : ℝ => ((p.1, t) : ℝ × ℝ)) ((0:ℝ), (1:ℝ)) p.2.2 :=
      (hasDerivAt_const p.2.2 p.1).prodMk (hasDerivAt_id' p.2.2)
    exact hgd.hasFDerivAt.comp_hasDerivAt p.2.2 hl
  have hsum : HasDerivAt (fun t : ℝ => ∑ n ∈ M,
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (p.2.1 : ℂ) / (c : ℂ)) * g n (p.1, t))
      (∑ n ∈ M, Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (p.2.1 : ℂ) / (c : ℂ)) *
        fderiv ℝ (g n) (p.1, p.2.2) (0, 1)) p.2.2 :=
    HasDerivAt.fun_sum (fun n hn => (hterm n hn).const_mul _)
  have hfun : (nzModeSum c M g ∘ fun t : ℝ => ((p.1, p.2.1, t) : Profile)) =
      fun t : ℝ => ∑ n ∈ M,
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (p.2.1 : ℂ) / (c : ℂ)) * g n (p.1, t) := by
    funext t
    simp only [Function.comp, nzModeSum, smul_eq_mul]
  rw [hfun] at hc1
  unfold pdEta
  exact hc1.unique hsum

theorem nzFpIdentity : UnforcedLeray.Short.PartIIa.NzFpIdentity := by
  intro c hc M a φ ψ hsm heq p
  have hφd : ∀ n ∈ M, ContDiff ℝ ∞ (φ n) := fun n hn => (hsm n hn).1
  have hψd : ∀ n ∈ M, ContDiff ℝ ∞ (ψ n) := fun n hn => (hsm n hn).2
  have hQφ := nzfpPdQ c M φ hφd p
  have hEφ := nzfpPdEta c M φ hφd p
  have hQψ := nzfpPdQ c M ψ hψd p
  have hEψ := nzfpPdEta c M ψ hψd p
  have e0 : ∑ n ∈ M, Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (p.2.1 : ℂ) / (c : ℂ)) *
        a n (p.1, p.2.2) 0 =
      pdQ (nzModeSum c M φ) p + -pdEta (nzModeSum c M ψ) p := by
    rw [hQφ, hEψ, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    have h := (heq n hn (p.1, p.2.2)).1
    dsimp only at h
    rw [← h]
    ring
  have e1 : ∑ n ∈ M, Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (p.2.1 : ℂ) / (c : ℂ)) *
        a n (p.1, p.2.2) 1 =
      pdEta (nzModeSum c M φ) p + pdQ (nzModeSum c M ψ) p := by
    rw [hEφ, hQψ, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    have h := (heq n hn (p.1, p.2.2)).2
    dsimp only at h
    rw [← h]
    ring
  ext i
  fin_cases i
  · show (∑ n ∈ M, Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (p.2.1 : ℂ) / (c : ℂ)) •
        a n (p.1, p.2.2)) 0 = _
    rw [nzfpSumApply]
    simp only [PiLp.smul_apply, smul_eq_mul, cgradC, streamC, PiLp.add_apply,
      Matrix.cons_val_zero, Complex.ofReal_zero, zero_mul, sub_zero,
      add_zero, Fin.zero_eta, Fin.isValue]
    exact e0
  · show (∑ n ∈ M, Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (p.2.1 : ℂ) / (c : ℂ)) •
        a n (p.1, p.2.2)) 1 = _
    rw [nzfpSumApply]
    simp only [PiLp.smul_apply, smul_eq_mul, cgradC, streamC, PiLp.add_apply,
      Matrix.cons_val_one, Complex.ofReal_zero, zero_mul, sub_zero,
      add_zero, Fin.mk_one, Fin.isValue]
    exact e1

end UnforcedLeray.Short.PartIIa
