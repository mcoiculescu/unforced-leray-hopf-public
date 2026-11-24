import UnforcedLeray.Short.PartIIa.Sub.N02_4_10
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.NonzeroMode.TruncTest
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.ModeSplit.IntervalParamSmooth

/-!
# Part II-a, task `PartII-a:N02/4/10/3` (`NtmComm`): `S` commutes with the `q`-truncation

Target: `ntmComm : NtmComm` (`Sub/N02_4_10.lean`). Source of record:
`the November 2 reference manuscript`, lines 1744-1749.

Route.
* `ntmc_line`: the derivative of `G` along a line `x + t • v` at `t = 0` is `fderiv G x v`.
* `ntmc_coeff_fderiv`: `∂_s` of the Fourier coefficient is the coefficient of `∂_s f`
  (differentiation under the `q`-integral, `IntervalParamSmooth`).
* `ntmc_trunc_fderiv`: `∂_s` of the finite sum is the sum of `∂_s` of the coefficients.
* `ntmc_step`: `opS (nzTrunc f) = nzTrunc (opS f)` (since `s · ∂_s a_n = a_n(s ∂_s f)`).
* `ntmc_iter`: induction on the power `a` of `opS`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0226

/-- Derivative of `t ↦ G (x + t • v)` at `t = 0`. -/
theorem ntmc_line {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (G : X → E) (x v : X)
    (hG : DifferentiableAt ℝ G x) :
    HasDerivAt (fun t : ℝ => G (x + t • v)) (fderiv ℝ G x v) 0 := by
  have hl : HasFDerivAt G (fderiv ℝ G x) (x + (0 : ℝ) • v) := by
    rw [zero_smul, add_zero]
    exact hG.hasFDerivAt
  have hf : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
    have h := ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
    simpa using h
  exact HasFDerivAt.comp_hasDerivAt (0 : ℝ) hl hf

/-- Smoothness of `opS`. -/
theorem ntmc_opS_smooth {f : Profile → MeridC} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (opS f) := by
  have hD : ContDiff ℝ ∞ (fun p : Profile => fderiv ℝ f p) :=
    (contDiff_infty_iff_fderiv.mp hf).2
  have h1 : ContDiff ℝ ∞ (fun p : Profile => fderiv ℝ f p (1, 0, 0)) :=
    hD.clm_apply contDiff_const
  exact contDiff_fst.smul h1

/-- The smooth map `(x, q) ↦ e^{-2π i n q / c} f(x.1, q, x.2)` whose `q`-integral is the
Fourier coefficient. -/
def ntmcH (c : ℝ) (n : ℤ) (f : Profile → MeridC) : (ℝ × ℝ) × ℝ → MeridC := fun z =>
  Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (z.2 : ℂ) / (c : ℂ))) •
    f (z.1.1, z.2, z.1.2)

theorem ntmcH_smooth {f : Profile → MeridC} (hf : ContDiff ℝ ∞ f) (c : ℝ) (n : ℤ) :
    ContDiff ℝ ∞ (ntmcH c n f) := by
  have hofR : ContDiff ℝ ∞ (fun z : (ℝ × ℝ) × ℝ => (z.2 : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp contDiff_snd
  have hE : ContDiff ℝ ∞ (fun z : (ℝ × ℝ) × ℝ =>
      Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (z.2 : ℂ) / (c : ℂ)))) :=
    ((ContDiff.mul contDiff_const hofR).div_const (c : ℂ)).neg.cexp
  have hF : ContDiff ℝ ∞ (fun z : (ℝ × ℝ) × ℝ => f (z.1.1, z.2, z.1.2)) :=
    hf.comp (by fun_prop)
  unfold ntmcH
  exact hE.smul hF

/-- Pointwise derivative of `ntmcH` in the direction `((1,0),0)`. -/
theorem ntmc_pointwise {f : Profile → MeridC} (hf : ContDiff ℝ ∞ f) (c : ℝ) (n : ℤ)
    (x : ℝ × ℝ) (q : ℝ) :
    fderiv ℝ (ntmcH c n f) (x, q) (((1 : ℝ), (0 : ℝ)), (0 : ℝ)) =
      Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (q : ℂ) / (c : ℂ))) •
        fderiv ℝ f (x.1, q, x.2) (1, 0, 0) := by
  have hHd : DifferentiableAt ℝ (ntmcH c n f) (x, q) :=
    (ntmcH_smooth hf c n).differentiable (by simp) _
  have h1 := ntmc_line (ntmcH c n f) (x, q) (((1 : ℝ), (0 : ℝ)), (0 : ℝ)) hHd
  have hfd : DifferentiableAt ℝ f (x.1, q, x.2) := hf.differentiable (by simp) _
  have h2 := (ntmc_line f (x.1, q, x.2) (1, 0, 0) hfd).const_smul
    (Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (q : ℂ) / (c : ℂ))))
  have hfun : (fun t : ℝ => ntmcH c n f ((x, q) + t • (((1 : ℝ), (0 : ℝ)), (0 : ℝ)))) =
      (fun t : ℝ => Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (q : ℂ) / (c : ℂ))) •
        f ((x.1, q, x.2) + t • ((1 : ℝ), (0 : ℝ), (0 : ℝ)))) := by
    funext t
    have e1 : (x, q) + t • (((1 : ℝ), (0 : ℝ)), (0 : ℝ)) = ((x.1 + t, x.2), q) := by
      ext <;> simp
    have e2 : (x.1, q, x.2) + t • ((1 : ℝ), (0 : ℝ), (0 : ℝ)) = (x.1 + t, q, x.2) := by
      ext <;> simp
    rw [e1, e2]
    rfl
  rw [hfun] at h1
  exact h1.unique h2

/-- `∂_s` of the Fourier coefficient `nzCoeff c n f` is the coefficient of `∂_s f`. -/
theorem ntmc_coeff_fderiv {f : Profile → MeridC} (hf : ContDiff ℝ ∞ f) (c : ℝ) (n : ℤ)
    (x : ℝ × ℝ) :
    fderiv ℝ (nzCoeff c n f) x (1, 0) =
      ((1 / c : ℝ) : ℂ) • ∫ q in (0 : ℝ)..c,
        Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (q : ℂ) / (c : ℂ))) •
          fderiv ℝ f (x.1, q, x.2) (1, 0, 0) := by
  have hI := intervalParamSmooth_proof (ℝ × ℝ) MeridC 0 c (ntmcH c n f) (ntmcH_smooth hf c n)
  have hdiff : DifferentiableAt ℝ (fun y : ℝ × ℝ => ∫ q in (0 : ℝ)..c, ntmcH c n f (y, q)) x :=
    hI.1.differentiable (by simp) x
  have hcf : nzCoeff c n f = fun y : ℝ × ℝ => ((1 / c : ℝ) : ℂ) • ∫ q in (0 : ℝ)..c,
      ntmcH c n f (y, q) := rfl
  rw [hcf, fderiv_fun_const_smul hdiff, smul_apply, hI.2 x (1, 0)]
  congr 1
  refine intervalIntegral.integral_congr fun q _ => ?_
  exact ntmc_pointwise hf c n x q

/-- The finite Fourier sum is differentiated termwise along `∂_s`. -/
theorem ntmc_trunc_fderiv {f : Profile → MeridC} (hf : ContDiff ℝ ∞ f) (c : ℝ) (N : ℕ)
    (p : Profile) :
    fderiv ℝ (nzTrunc c N f) p (1, 0, 0) =
      ∑ n ∈ (Finset.Icc (-(N : ℤ)) N).erase 0,
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (p.2.1 : ℂ) / (c : ℂ)) •
          fderiv ℝ (nzCoeff c n f) (p.1, p.2.2) (1, 0) := by
  have hsm : ∀ n : ℤ, ContDiff ℝ ∞ (nzCoeff c n f) :=
    fun n => nztt_coeff_smooth intervalParamSmooth_proof c n f hf
  have hsmooth : ContDiff ℝ ∞ (nzTrunc c N f) := by
    unfold nzTrunc
    apply ContDiff.sum
    intro n _
    exact (nztt_exp_cd c n).smul ((hsm n).comp nztt_proj_cd)
  have hG : DifferentiableAt ℝ (nzTrunc c N f) p := hsmooth.differentiable (by simp) p
  have h1 := ntmc_line (nzTrunc c N f) p (1, 0, 0) hG
  have h2 : HasDerivAt (fun t : ℝ => ∑ n ∈ (Finset.Icc (-(N : ℤ)) N).erase 0,
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (p.2.1 : ℂ) / (c : ℂ)) •
          nzCoeff c n f ((p.1, p.2.2) + t • ((1 : ℝ), (0 : ℝ))))
      (∑ n ∈ (Finset.Icc (-(N : ℤ)) N).erase 0,
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (p.2.1 : ℂ) / (c : ℂ)) •
          fderiv ℝ (nzCoeff c n f) (p.1, p.2.2) (1, 0)) 0 := by
    apply HasDerivAt.fun_sum
    intro n _
    exact (ntmc_line (nzCoeff c n f) (p.1, p.2.2) ((1 : ℝ), (0 : ℝ))
      ((hsm n).differentiable (by simp) _)).const_smul
      (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (p.2.1 : ℂ) / (c : ℂ)))
  have hfun : (fun t : ℝ => nzTrunc c N f (p + t • ((1 : ℝ), (0 : ℝ), (0 : ℝ)))) =
      (fun t : ℝ => ∑ n ∈ (Finset.Icc (-(N : ℤ)) N).erase 0,
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (p.2.1 : ℂ) / (c : ℂ)) •
          nzCoeff c n f ((p.1, p.2.2) + t • ((1 : ℝ), (0 : ℝ)))) := by
    funext t
    have e1 : p + t • ((1 : ℝ), (0 : ℝ), (0 : ℝ)) = (p.1 + t, p.2.1, p.2.2) := by
      ext <;> simp
    have e2 : (p.1, p.2.2) + t • ((1 : ℝ), (0 : ℝ)) = (p.1 + t, p.2.2) := by
      ext <;> simp
    rw [e1, e2]
    rfl
  rw [hfun] at h1
  exact h1.unique h2

/-- Scalar commutation used in the one-step identity. -/
theorem ntmc_comm_aux (r : ℝ) (E w : ℂ) (X : MeridC) :
    r • (E • (w • X)) = E • (w • (r • X)) := by
  rw [smul_comm r E, smul_comm r w]

/-- **One-step commutation:** `opS (nzTrunc c N f) = nzTrunc c N (opS f)` for smooth `f`. -/
theorem ntmc_step {f : Profile → MeridC} (hf : ContDiff ℝ ∞ f) (c : ℝ) (N : ℕ) :
    opS (nzTrunc c N f) = nzTrunc c N (opS f) := by
  funext p
  show p.1 • fderiv ℝ (nzTrunc c N f) p (1, 0, 0) =
    ∑ n ∈ (Finset.Icc (-(N : ℤ)) N).erase 0,
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (p.2.1 : ℂ) / (c : ℂ)) •
        nzCoeff c n (opS f) (p.1, p.2.2)
  rw [ntmc_trunc_fderiv hf c N p, Finset.smul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  have hR : nzCoeff c n (opS f) (p.1, p.2.2) =
      ((1 / c : ℝ) : ℂ) • ∫ q in (0 : ℝ)..c,
        Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (q : ℂ) / (c : ℂ))) •
          (p.1 • fderiv ℝ f (p.1, q, p.2.2) (1, 0, 0)) := rfl
  have hint : ∫ q in (0 : ℝ)..c,
      Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (q : ℂ) / (c : ℂ))) •
        (p.1 • fderiv ℝ f (p.1, q, p.2.2) (1, 0, 0)) =
      p.1 • ∫ q in (0 : ℝ)..c,
        Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (q : ℂ) / (c : ℂ))) •
          fderiv ℝ f (p.1, q, p.2.2) (1, 0, 0) := by
    rw [← intervalIntegral.integral_smul]
    refine intervalIntegral.integral_congr fun q _ => ?_
    exact smul_comm _ _ _
  rw [ntmc_coeff_fderiv hf c n (p.1, p.2.2), hR, hint]
  exact ntmc_comm_aux _ _ _ _

/-- Iterated one-step identity. -/
theorem ntmc_iter (c : ℝ) (N : ℕ) : ∀ (a : ℕ) (f : Profile → MeridC), ContDiff ℝ ∞ f →
    opS^[a] (nzTrunc c N f) = nzTrunc c N (opS^[a] f) := by
  intro a
  induction a with
  | zero => intro f _; simp
  | succ k ih =>
    intro f hf
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ntmc_step hf c N]
    exact ih (opS f) (ntmc_opS_smooth hf)

/-- **`NtmComm` (target).** -/
theorem ntmComm : NtmComm := by
  intro c _hc f hf N a
  exact ntmc_iter c N a f hf.smooth

end UnforcedLeray.Short.PartIIa
