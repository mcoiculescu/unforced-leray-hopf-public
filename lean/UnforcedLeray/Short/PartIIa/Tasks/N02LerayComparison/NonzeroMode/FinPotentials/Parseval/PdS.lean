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

/-- Differentiability of one mode term (helper for the `s`-derivative of mode sums). -/
theorem nzfpPdSDiffTerm (c : ℝ) (n : ℤ) (g : ℝ × ℝ → ℂ) (hg : ContDiff ℝ ∞ g) :
    Differentiable ℝ (fun p : Profile =>
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (p.2.1 : ℂ) / (c : ℂ)) * g (p.1, p.2.2)) := by
  have hgd : Differentiable ℝ g := hg.differentiable (by simp)
  have hq : Differentiable ℝ (fun p : Profile =>
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (p.2.1 : ℂ) / (c : ℂ))) := by
    fun_prop
  have hG : Differentiable ℝ (fun p : Profile => g (p.1, p.2.2)) :=
    hgd.comp (differentiable_fst.prodMk (differentiable_snd.comp differentiable_snd))
  exact hq.mul hG

/-- Differentiability of a finite mode sum (helper). -/
theorem nzfpPdSDiffSum (c : ℝ) (M : Finset ℤ) (g : ℤ → ℝ × ℝ → ℂ) (hg : ∀ n ∈ M, ContDiff ℝ ∞ (g n)) :
    Differentiable ℝ (nzModeSum c M g) := by
  have hterm : ∀ n ∈ M, Differentiable ℝ (fun p : Profile =>
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (p.2.1 : ℂ) / (c : ℂ)) • g n (p.1, p.2.2)) := by
    intro n hn
    have h := nzfpPdSDiffTerm c n (g n) (hg n hn)
    simpa only [smul_eq_mul] using h
  unfold nzModeSum
  exact Differentiable.fun_sum hterm

/-- The `s`-derivative of a finite mode sum: `∂_s Σ e_n g_n = Σ e_n ∂_s g_n`. -/
theorem nzfpPdS (c : ℝ) (M : Finset ℤ) (g : ℤ → ℝ × ℝ → ℂ) (hg : ∀ n ∈ M, ContDiff ℝ ∞ (g n))
    (p : Profile) :
    pdS (nzModeSum c M g) p = ∑ n ∈ M,
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (p.2.1 : ℂ) / (c : ℂ)) *
        fderiv ℝ (g n) (p.1, p.2.2) (1, 0) := by
  have hΦ : HasFDerivAt (nzModeSum c M g) (fderiv ℝ (nzModeSum c M g) (p.1, p.2.1, p.2.2))
      (p.1, p.2.1, p.2.2) :=
    (nzfpPdSDiffSum c M g hg _).hasFDerivAt
  have hline : HasDerivAt (fun t : ℝ => ((t, p.2.1, p.2.2) : Profile)) ((1:ℝ), (0:ℝ), (0:ℝ)) p.1 :=
    (hasDerivAt_id' p.1).prodMk ((hasDerivAt_const p.1 p.2.1).prodMk (hasDerivAt_const p.1 p.2.2))
  have hc1 := hΦ.comp_hasDerivAt p.1 hline
  have hterm : ∀ n ∈ M, HasDerivAt (fun t : ℝ => g n (t, p.2.2))
      (fderiv ℝ (g n) (p.1, p.2.2) (1, 0)) p.1 := by
    intro n hn
    have hgd : DifferentiableAt ℝ (g n) (p.1, p.2.2) := (hg n hn).differentiable (by simp) _
    have hl : HasDerivAt (fun t : ℝ => ((t, p.2.2) : ℝ × ℝ)) ((1:ℝ), (0:ℝ)) p.1 :=
      (hasDerivAt_id' p.1).prodMk (hasDerivAt_const p.1 p.2.2)
    exact hgd.hasFDerivAt.comp_hasDerivAt p.1 hl
  have hsum : HasDerivAt (fun t : ℝ => ∑ n ∈ M,
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (p.2.1 : ℂ) / (c : ℂ)) * g n (t, p.2.2))
      (∑ n ∈ M, Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (p.2.1 : ℂ) / (c : ℂ)) *
        fderiv ℝ (g n) (p.1, p.2.2) (1, 0)) p.1 :=
    HasDerivAt.fun_sum (fun n hn => (hterm n hn).const_mul _)
  have hfun : (nzModeSum c M g ∘ fun t : ℝ => ((t, p.2.1, p.2.2) : Profile)) =
      fun t : ℝ => ∑ n ∈ M,
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (p.2.1 : ℂ) / (c : ℂ)) * g n (t, p.2.2) := by
    funext t
    simp only [Function.comp, nzModeSum, smul_eq_mul]
  rw [hfun] at hc1
  unfold pdS
  exact hc1.unique hsum

/-- `opS` of a finite mode sum is the mode sum of `nzS2` (with `S = s ∂_s`). -/
theorem nzfpOpSModeSum (c : ℝ) (M : Finset ℤ) (g : ℤ → ℝ × ℝ → ℂ) (hg : ∀ n ∈ M, ContDiff ℝ ∞ (g n))
    (p : Profile) :
    opS (nzModeSum c M g) p = ∑ n ∈ M,
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (p.2.1 : ℂ) / (c : ℂ)) *
        nzS2 (g n) (p.1, p.2.2) := by
  unfold opS
  rw [nzfpPdS c M g hg p, Finset.smul_sum]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  simp only [nzS2, Complex.real_smul]
  ring

end UnforcedLeray.Short.PartIIa
