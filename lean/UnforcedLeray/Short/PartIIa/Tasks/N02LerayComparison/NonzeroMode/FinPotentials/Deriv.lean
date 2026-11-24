import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N02_4_4

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0226

/-- Smoothness of one summand-wise mode sum. -/
theorem nzfp_mode_contDiff (c : ℝ) (M : Finset ℤ) (g : ℤ → ℝ × ℝ → ℂ)
    (hg : ∀ n ∈ M, ContDiff ℝ ∞ (g n)) : ContDiff ℝ ∞ (nzModeSum c M g) := by
  unfold nzModeSum
  apply ContDiff.sum
  intro n hn
  have hgn := hg n hn
  have hq : ContDiff ℝ ∞ (fun x : Profile => ((x.2.1 : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_fst.comp contDiff_snd)
  have hgq : ContDiff ℝ ∞ (fun x : Profile => g n (x.1, x.2.2)) :=
    hgn.comp (contDiff_fst.prodMk (contDiff_snd.comp contDiff_snd))
  have hE : ContDiff ℝ ∞ (fun x : Profile =>
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * ((x.2.1 : ℝ) : ℂ) / (c : ℂ))) := by
    fun_prop
  simp only [smul_eq_mul]
  exact ContDiff.mul hE hgq

/-- Derivative in `q` of the mode sum along the line `t ↦ (s, q + t, η)`. -/
theorem nzfp_hasDerivAt_q (c : ℝ) (M : Finset ℤ) (g : ℤ → ℝ × ℝ → ℂ) (p : Profile) :
    HasDerivAt (fun t : ℝ => ∑ n ∈ M,
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * ((p.2.1 + t : ℝ) : ℂ) / (c : ℂ)) *
          g n (p.1, p.2.2))
      (∑ n ∈ M, Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (p.2.1 : ℂ) / (c : ℂ)) *
        (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * 1 / (c : ℂ)) * g n (p.1, p.2.2)) 0 := by
  apply HasDerivAt.fun_sum
  intro n hn
  have hq1 : HasDerivAt (fun t : ℝ => ((p.2.1 + t : ℝ) : ℂ)) 1 0 := by
    have h := ((hasDerivAt_id' (0:ℝ)).const_add p.2.1).ofReal_comp
    simpa using h
  have h2 := ((hq1.const_mul (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ))).div_const (c : ℂ)).cexp
  have h3 := h2.mul_const (g n (p.1, p.2.2))
  rw [add_zero] at h3
  exact h3

/-- Derivative in `η` of the mode sum along the line `t ↦ (s, q, η + t)`. -/
theorem nzfp_hasDerivAt_eta (c : ℝ) (M : Finset ℤ) (g : ℤ → ℝ × ℝ → ℂ)
    (hg : ∀ n ∈ M, ContDiff ℝ ∞ (g n)) (p : Profile) :
    HasDerivAt (fun t : ℝ => ∑ n ∈ M,
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (p.2.1 : ℂ) / (c : ℂ)) *
          g n (p.1, p.2.2 + t))
      (∑ n ∈ M, Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (p.2.1 : ℂ) / (c : ℂ)) *
        fderiv ℝ (g n) (p.1, p.2.2) (0, 1)) 0 := by
  apply HasDerivAt.fun_sum
  intro n hn
  have hm : HasDerivAt (fun t : ℝ => ((p.1, p.2.2 + t) : ℝ × ℝ)) ((0 : ℝ), (1 : ℝ)) 0 :=
    (hasDerivAt_const (0:ℝ) p.1).prodMk ((hasDerivAt_id' (0:ℝ)).const_add p.2.2)
  have hy : (p.1, p.2.2) = (fun t : ℝ => ((p.1, p.2.2 + t) : ℝ × ℝ)) 0 := by simp
  have hgc : HasDerivAt (fun t : ℝ => g n (p.1, p.2.2 + t))
      (fderiv ℝ (g n) (p.1, p.2.2) (0, 1)) 0 :=
    ((((hg n hn).differentiable (by simp)) (p.1, p.2.2)).hasFDerivAt).comp_hasDerivAt_of_eq 0 hm hy
  exact hgc.const_mul _

theorem nzfp_pdQ_mode (c : ℝ) (M : Finset ℤ) (g : ℤ → ℝ × ℝ → ℂ)
    (hg : ∀ n ∈ M, ContDiff ℝ ∞ (g n)) (p : Profile) :
    pdQ (nzModeSum c M g) p =
      nzModeSum c M (fun n x => Complex.I * ((nzk c n : ℂ) * g n x)) p := by
  have hF : DifferentiableAt ℝ (nzModeSum c M g) p :=
    ((nzfp_mode_contDiff c M g hg).differentiable (by simp)).differentiableAt
  have hl : HasDerivAt (fun t : ℝ => ((p.1, p.2.1 + t, p.2.2) : Profile))
      ((0 : ℝ), ((1 : ℝ), (0 : ℝ))) 0 :=
    (hasDerivAt_const (0:ℝ) p.1).prodMk
      (((hasDerivAt_id' (0:ℝ)).const_add p.2.1).prodMk (hasDerivAt_const (0:ℝ) p.2.2))
  have hy : p = (fun t : ℝ => ((p.1, p.2.1 + t, p.2.2) : Profile)) 0 := by
    simp
  have hcomp := hF.hasFDerivAt.comp_hasDerivAt_of_eq 0 hl hy
  have hfun : (nzModeSum c M g ∘ fun t : ℝ => ((p.1, p.2.1 + t, p.2.2) : Profile)) =
      fun t : ℝ => ∑ n ∈ M,
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * ((p.2.1 + t : ℝ) : ℂ) / (c : ℂ)) *
          g n (p.1, p.2.2) := rfl
  rw [hfun] at hcomp
  have huniq := hcomp.unique (nzfp_hasDerivAt_q c M g p)
  unfold pdQ
  rw [huniq]
  unfold nzModeSum
  refine Finset.sum_congr rfl (fun n _ => ?_)
  simp only [nzk, smul_eq_mul]
  push_cast
  ring

theorem nzfp_pdEta_mode (c : ℝ) (M : Finset ℤ) (g : ℤ → ℝ × ℝ → ℂ)
    (hg : ∀ n ∈ M, ContDiff ℝ ∞ (g n)) (p : Profile) :
    pdEta (nzModeSum c M g) p =
      nzModeSum c M (fun n x => fderiv ℝ (g n) x (0, 1)) p := by
  have hF : DifferentiableAt ℝ (nzModeSum c M g) p :=
    ((nzfp_mode_contDiff c M g hg).differentiable (by simp)).differentiableAt
  have hl : HasDerivAt (fun t : ℝ => ((p.1, p.2.1, p.2.2 + t) : Profile))
      ((0 : ℝ), ((0 : ℝ), (1 : ℝ))) 0 :=
    (hasDerivAt_const (0:ℝ) p.1).prodMk
      ((hasDerivAt_const (0:ℝ) p.2.1).prodMk ((hasDerivAt_id' (0:ℝ)).const_add p.2.2))
  have hy : p = (fun t : ℝ => ((p.1, p.2.1, p.2.2 + t) : Profile)) 0 := by
    simp
  have hcomp := hF.hasFDerivAt.comp_hasDerivAt_of_eq 0 hl hy
  have hfun : (nzModeSum c M g ∘ fun t : ℝ => ((p.1, p.2.1, p.2.2 + t) : Profile)) =
      fun t : ℝ => ∑ n ∈ M,
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (p.2.1 : ℂ) / (c : ℂ)) *
          g n (p.1, p.2.2 + t) := rfl
  rw [hfun] at hcomp
  have huniq := hcomp.unique (nzfp_hasDerivAt_eta c M g hg p)
  unfold pdEta
  rw [huniq]
  unfold nzModeSum
  refine Finset.sum_congr rfl (fun n _ => ?_)
  simp only [smul_eq_mul]

theorem nzFpDeriv : NzFpDeriv := by
  intro c _ M g hg
  constructor
  · funext p
    exact nzfp_pdQ_mode c M g hg p
  · funext p
    exact nzfp_pdEta_mode c M g hg p

end UnforcedLeray.Short.PartIIa
