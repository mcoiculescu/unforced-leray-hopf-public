import UnforcedLeray.Short.PartIIa.Sub.F14_1_org.Defs
import UnforcedLeray.Short.PartIIa.Sub.F05_1
import UnforcedLeray.Short.PartIIa.Tasks.F05aAdjResolventSolution.HeatGaussSmooth
import UnforcedLeray.Short.PartIIa.Tasks.F05aAdjResolventSolution.HeatGaussEquation
import UnforcedLeray.Short.PartIIa.Tasks.F05aAdjResolventSolution.AdjIntegrandDeriv

/-!
# Part II-a, task `PartII-a:F14/1/1/2`: the `t`-derivative of the forward integrand

Target: `FwdIntegrandDeriv` (defined in `Sub/F14_1_org/Defs.lean`).

Source of record: `the November 2 reference manuscript`, lines 1370-1373.

Proof. Write `G = heatGauss f w` with `w = fwdW ν t`, `e = exp(t/2)`, `c = exp(-((μ - 1/2) t))`,
so `fwdIntegrand ν μ f s p = exp(-((μ-1/2)s)) • heatGauss f (fwdW ν s) (p.1 - s, exp(s/2) • p.2)`.
The chain rule along `s ↦ (fwdW ν s, (p.1 - s, exp(s/2) • p.2))` gives the derivative
`c' • H + c • (w' • (2w • lapT G x) + ∇G x (-1, (e/2) • p.2))` at `x = (p.1 - t, e • p.2)`, where
`w' = ν e^t / (2w)`, so `w' · 2w = ν e^t = ν e²`. Since `∇G x (-1, (e/2) p.2) = -∂_τG x + ½ radialT G x`
(`x.2 = e • p.2`), this is `-(μ - 1/2) F - ∂_τ F + ½ radialT F + ν lapT F` by the affine lemmas of
`AdjIntegrandDeriv.lean` (`dτ_F`, `radialT_F`, `lapT_F`, `fderiv_heat_joint`, `fderiv_zero_vec`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff
open UnforcedLeray.PhaseSpace

namespace UnforcedLeray.Short.PartIIa

namespace FwdIntegrandDerivAux

theorem fw_fderiv_neg_one (G : ℝ × Space → CVec3) (x : ℝ × Space) (u : Space) :
    fderiv ℝ G x ((-1 : ℝ), u) = (-1 : ℝ) • dτ G x + ∑ j : Fin 3, u j • dy j G x := by
  have h : ((-1 : ℝ), u) = (-1 : ℝ) • ((1 : ℝ), (0 : Space)) + ((0 : ℝ), u) := by
    refine Prod.ext ?_ ?_ <;> simp
  rw [h, map_add, map_smul, AdjIntegrandDerivAux.fderiv_zero_vec]
  rfl

theorem fw_sum_half (G : ℝ × Space → CVec3) (e : ℝ) (p2 : Space) (x : ℝ × Space)
    (hx : x.2 = e • p2) :
    ∑ j : Fin 3, ((e * (1 / 2)) • p2) j • dy j G x = (1 / 2 : ℝ) • radialT G x := by
  unfold radialT
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hx]
  simp only [PiLp.smul_apply, smul_eq_mul]
  rw [smul_smul]
  congr 1
  ring

theorem fw_algebra (c k : ℂ) (ν a w e : ℝ) (haw : a * (2 * w) = ν * (e * e))
    (gx dx rx lx : CVec3) :
    c • (a • ((2 * w) • lx) + ((-1 : ℝ) • dx + (1 / 2 : ℝ) • rx)) + (c * k) • gx
      = k • (c • gx) - c • dx + (1 / 2 : ℝ) • (c • rx) + ν • (c • (e • e • lx)) := by
  have h1 : a • ((2 * w) • lx) = ν • (e • e • lx) := by
    rw [smul_smul, haw]
    simp only [smul_smul]
  have e1 : (c * k) • gx = k • (c • gx) := by
    rw [mul_comm c k, mul_smul]
  have e2 : c • ((-1 : ℝ) • dx) = -(c • dx) := by
    rw [smul_comm c (-1 : ℝ) dx, neg_one_smul ℝ]
  have e3 : c • ((1 / 2 : ℝ) • rx) = (1 / 2 : ℝ) • (c • rx) := smul_comm c _ _
  have e4 : c • (ν • (e • e • lx)) = ν • (c • (e • e • lx)) := smul_comm c ν _
  rw [h1, e1, smul_add, smul_add, e2, e3, e4]
  abel

end FwdIntegrandDerivAux

open FwdIntegrandDerivAux in
theorem fwdIntegrandDeriv : FwdIntegrandDeriv := by
  intro P ν hP hν μ f hf t ht p
  obtain ⟨hJc, hHc, -⟩ := heatGaussSmooth_proof P hP f hf
  have hE := heatGaussEquation_proof P hP f hf
  have hJd : Differentiable ℝ (fun q : ℝ × (ℝ × Space) => heatGauss f q.1 q.2) :=
    hJc.differentiable (by simp)
  have hGc : ContDiff ℝ ∞ (heatGauss f (fwdW ν t)) := hHc (fwdW ν t)
  have hGd : Differentiable ℝ (heatGauss f (fwdW ν t)) := hGc.differentiable (by simp)
  have hexp1 : 1 < Real.exp t := by
    have := Real.exp_lt_exp.2 ht
    rwa [Real.exp_zero] at this
  have hpos : 0 < ν * (Real.exp t - 1) := mul_pos hν (by linarith)
  have hwpos : 0 < fwdW ν t := Real.sqrt_pos.mpr hpos
  -- the derivative of the heat parameter `w(s) = √(ν(e^s - 1))`
  have hw' : HasDerivAt (fun s : ℝ => fwdW ν s) (ν * Real.exp t / (2 * fwdW ν t)) t := by
    have h1 : HasDerivAt (fun s : ℝ => ν * (Real.exp s - 1)) (ν * Real.exp t) t :=
      (((hasDerivAt_id' t).exp.sub_const 1).const_mul ν).congr_deriv (by ring)
    exact h1.sqrt hpos.ne'
  -- the derivative of the spatial affine map `s ↦ (p.1 - s, e^{s/2} p.2)`
  have hκ : HasDerivAt (fun s : ℝ => Real.exp (s / 2)) (Real.exp (t / 2) * (1 / 2)) t :=
    ((hasDerivAt_id' t).div_const 2).exp
  have hq : HasDerivAt (fun s : ℝ => ((p.1 - s, Real.exp (s / 2) • p.2) : ℝ × Space))
      ((-1 : ℝ), (Real.exp (t / 2) * (1 / 2)) • p.2) t :=
    ((hasDerivAt_id' t).const_sub p.1).prodMk (hκ.smul_const p.2)
  have hΓ : HasDerivAt
      (fun s : ℝ => ((fwdW ν s, (p.1 - s, Real.exp (s / 2) • p.2)) : ℝ × (ℝ × Space)))
      ((ν * Real.exp t / (2 * fwdW ν t)), ((-1 : ℝ), (Real.exp (t / 2) * (1 / 2)) • p.2)) t :=
    hw'.prodMk hq
  have hJΓ := HasFDerivAt.comp_hasDerivAt t
    (hJd (fwdW ν t, (p.1 - t, Real.exp (t / 2) • p.2))).hasFDerivAt hΓ
  -- the derivative of the phase `c(s) = exp(-(μ - 1/2) s)`
  have hcf : HasDerivAt (fun s : ℝ => Complex.exp (-((μ - 1 / 2) * (s : ℂ))))
      (Complex.exp (-((μ - 1 / 2) * (t : ℂ))) * (-(μ - 1 / 2))) t := by
    have h1 : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := by
      simpa using HasDerivAt.ofReal_comp (hasDerivAt_id' t)
    have h2 := ((h1.const_mul (μ - 1 / 2)).neg).cexp
    exact h2.congr_deriv (by simp only [Pi.neg_apply]; ring)
  have hsm := hcf.smul hJΓ
  refine ((hsm : HasDerivAt (fun s : ℝ => fwdIntegrand ν μ f s p) _ t)).congr_deriv ?_
  -- rewrite the integrand as the affine composite
  have hF : fwdIntegrand ν μ f t = fun q : ℝ × Space =>
      Complex.exp (-((μ - 1 / 2) * (t : ℂ))) •
        heatGauss f (fwdW ν t) (q.1 + -t, Real.exp (t / 2) • q.2) := by
    funext q
    simp only [fwdIntegrand, sub_eq_add_neg]
  have haw : (ν * Real.exp t / (2 * fwdW ν t)) * (2 * fwdW ν t)
      = ν * (Real.exp (t / 2) * Real.exp (t / 2)) := by
    have he2 : Real.exp (t / 2) * Real.exp (t / 2) = Real.exp t := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [div_mul_cancel₀ _ (mul_pos two_pos hwpos).ne', he2]
  rw [hF, AdjIntegrandDerivAux.dτ_F hGd _ (-t) (Real.exp (t / 2)) p,
    AdjIntegrandDerivAux.radialT_F hGd _ (-t) (Real.exp (t / 2)) p,
    AdjIntegrandDerivAux.lapT_F hGc _ (-t) (Real.exp (t / 2)) p]
  simp only [Function.comp_apply]
  try dsimp only
  rw [← sub_eq_add_neg p.1 t]
  rw [AdjIntegrandDerivAux.fderiv_heat_joint f hJd hE hwpos (p.1 - t, Real.exp (t / 2) • p.2)
    (ν * Real.exp t / (2 * fwdW ν t)) ((-1 : ℝ), (Real.exp (t / 2) * (1 / 2)) • p.2)]
  rw [fw_fderiv_neg_one, fw_sum_half (heatGauss f (fwdW ν t)) (Real.exp (t / 2)) p.2
    (p.1 - t, Real.exp (t / 2) • p.2) rfl]
  exact fw_algebra _ _ _ _ _ _ haw _ _ _ _

end UnforcedLeray.Short.PartIIa
