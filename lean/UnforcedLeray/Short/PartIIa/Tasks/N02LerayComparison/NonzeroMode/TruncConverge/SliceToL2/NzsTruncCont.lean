import UnforcedLeray.Short.PartIIa.Sub.N02_4_11_2

/-!
# Part II-a, `Sub1` of `PartII-a:N02/4/11/2`: continuity of the Fourier truncations

Target: `nzsTruncCont : NzsTruncCont` (`Sub/N02_4_11_2.lean`). Source of record:
`the November 2 reference manuscript`, lines 1744-1749.

The coefficient `nzCoeff c n f` is a parametric interval integral over `[0, c]` of a continuous
integrand in `(s, η, q)`, hence continuous in `(s, η)`. The truncation is a finite sum of
continuous exponentials times such coefficients.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0226

theorem nzCoeff_continuous_aux (c : ℝ) (n : ℤ) (f : Profile → MeridC) (hf : Continuous f) :
    Continuous (nzCoeff c n f) := by
  have hcomp : Continuous (fun z : (ℝ × ℝ) × ℝ => f (z.1.1, z.2, z.1.2)) :=
    hf.comp (by fun_prop)
  have hexp : Continuous (fun z : (ℝ × ℝ) × ℝ =>
      Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (z.2 : ℂ) / (c : ℂ)))) := by
    fun_prop
  have hint : Continuous (fun x : ℝ × ℝ => ∫ t in (0 : ℝ)..c,
      Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (t : ℂ) / (c : ℂ))) •
        f (x.1, t, x.2)) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (μ := volume)
      (hexp.smul hcomp) 0 c
  unfold nzCoeff
  exact Continuous.smul (continuous_const : Continuous fun _ : ℝ × ℝ => ((1 / c : ℝ) : ℂ)) hint

theorem nzsTruncCont : NzsTruncCont := by
  intro c _hc f hf N
  have hfc : Continuous f := hf.smooth.continuous
  unfold nzTrunc
  apply continuous_finsetSum
  intro n _
  have hco : Continuous (nzCoeff c n f) := nzCoeff_continuous_aux c n f hfc
  have hcomp : Continuous (fun p : Profile => nzCoeff c n f (p.1, p.2.2)) :=
    hco.comp (by fun_prop)
  have hexp : Continuous (fun p : Profile =>
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (p.2.1 : ℂ) / (c : ℂ))) := by
    fun_prop
  exact hexp.smul hcomp

end UnforcedLeray.Short.PartIIa
