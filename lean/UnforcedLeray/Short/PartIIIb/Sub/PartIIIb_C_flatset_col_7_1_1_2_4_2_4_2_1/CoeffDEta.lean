import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_4_2_1.FlatLerayDefs
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.ModeSplit.IntervalParamSmooth

/-!


Source of record `the November 2 reference manuscript` lines 1713-1716.
`∂_η` commutes with the `q`-Fourier coefficient: differentiate under the `q`-integral over `[0, c]`
(`IntervalParamSmooth`, the parametric-integral leaf), then the chain rule for `(s,q,η) ↦ (s,η)`
at fixed `q`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.FlatLeray

open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.Short.PartIIa

/-- The `q`-character `e^{-2π i n t / c}` of `nzCoeff`, as a function of `t`. -/
def cdetaExp (c : ℝ) (n : ℤ) (t : ℝ) : ℂ :=
  Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (t : ℂ) / (c : ℂ)))

theorem cdetaExp_cd (c : ℝ) (n : ℤ) : ContDiff ℝ ∞ (cdetaExp c n) := by
  have hofR : ContDiff ℝ ∞ (fun t : ℝ => (t : ℂ)) := Complex.ofRealCLM.contDiff
  unfold cdetaExp
  exact (((ContDiff.mul contDiff_const hofR).div_const (c : ℂ)).neg).cexp

/-- The linear reordering `((s, η'), q) ↦ (s, q, η')` of `(ℝ × ℝ) × ℝ` into the profile. -/
def cdetaReorderLin : ((ℝ × ℝ) × ℝ) →ₗ[ℝ] (ℝ × ℝ × ℝ) where
  toFun z := (z.1.1, z.2, z.1.2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The continuous linear map underlying `cdetaReorderLin`. -/
def cdetaReorderCLM : ((ℝ × ℝ) × ℝ) →L[ℝ] (ℝ × ℝ × ℝ) :=
  LinearMap.toContinuousLinearMap cdetaReorderLin

/-- Pointwise identity: the derivative of the integrand in the direction `((0,1),0)` (the `η`
direction at fixed `q`) is `e^{-2π i n q / c}` times `∂_η g`. -/
theorem cdetaPt (c : ℝ) (g : Profile → MeridC) (hg : ContDiff ℝ ∞ g) (n : ℤ) (x : ℝ × ℝ) (q : ℝ) :
    fderiv ℝ (fun z : (ℝ × ℝ) × ℝ => cdetaExp c n z.2 • g (z.1.1, z.2, z.1.2)) (x, q) ((0, 1), 0)
      = cdetaExp c n q • fderiv ℝ g (x.1, q, x.2) (0, 0, 1) := by
  have hg1 : ContDiff ℝ 1 g := by exact_mod_cast contDiff_infty.1 hg 1
  have hEc1 : ContDiff ℝ 1 (cdetaExp c n) := by
    exact_mod_cast contDiff_infty.1 (cdetaExp_cd c n) 1
  have hEd : DifferentiableAt ℝ (cdetaExp c n) q := hEc1.differentiable one_ne_zero q
  have hEz' : DifferentiableAt ℝ (cdetaExp c n ∘ Prod.snd) (x, q) :=
    DifferentiableAt.comp (g := cdetaExp c n) (f := Prod.snd) (x, q) hEd differentiableAt_snd
  have hEz : DifferentiableAt ℝ (fun z : (ℝ × ℝ) × ℝ => cdetaExp c n z.2) (x, q) := hEz'
  have hGz : DifferentiableAt ℝ (fun z : (ℝ × ℝ) × ℝ => g (z.1.1, z.2, z.1.2)) (x, q) := by
    have hΦ : DifferentiableAt ℝ (fun z : (ℝ × ℝ) × ℝ => (z.1.1, z.2, z.1.2)) (x, q) := by
      fun_prop
    exact (hg1.differentiable one_ne_zero (x.1, q, x.2)).comp (x, q) hΦ
  have hE0 : fderiv ℝ (fun z : (ℝ × ℝ) × ℝ => cdetaExp c n z.2) (x, q) ((0, 1), 0) = 0 := by
    have hcomp : (fun z : (ℝ × ℝ) × ℝ => cdetaExp c n z.2) = cdetaExp c n ∘ Prod.snd := rfl
    rw [hcomp, fderiv_comp (x, q) hEd differentiableAt_snd, ContinuousLinearMap.comp_apply,
      fderiv_snd]
    exact map_zero _
  have hGd : fderiv ℝ (fun z : (ℝ × ℝ) × ℝ => g (z.1.1, z.2, z.1.2)) (x, q) ((0, 1), 0)
      = fderiv ℝ g (x.1, q, x.2) (0, 0, 1) := by
    have hΦ : HasFDerivAt (fun z : (ℝ × ℝ) × ℝ => (z.1.1, z.2, z.1.2)) cdetaReorderCLM (x, q) :=
      cdetaReorderCLM.hasFDerivAt
    have hgd : HasFDerivAt g (fderiv ℝ g (x.1, q, x.2)) (x.1, q, x.2) :=
      (hg1.differentiable one_ne_zero (x.1, q, x.2)).hasFDerivAt
    have hcomp : HasFDerivAt (fun z : (ℝ × ℝ) × ℝ => g (z.1.1, z.2, z.1.2))
        ((fderiv ℝ g (x.1, q, x.2)).comp cdetaReorderCLM) (x, q) := hgd.comp (x, q) hΦ
    rw [hcomp.fderiv]
    rfl
  have hsm : (fun z : (ℝ × ℝ) × ℝ => cdetaExp c n z.2 • g (z.1.1, z.2, z.1.2))
      = (fun z : (ℝ × ℝ) × ℝ => cdetaExp c n z.2) • (fun z : (ℝ × ℝ) × ℝ => g (z.1.1, z.2, z.1.2)) :=
    rfl
  rw [hsm, fderiv_smul hEz hGz, add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, hE0, hGd, zero_smul, add_zero]

/-- **Task target: `∂_η` commutes with the `q`-coefficient** (source 1713-1716). -/
theorem coeffDEta : UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.FlatLeray.CoeffDEta := by
  intro c g hg n x
  have hGc : ContDiff ℝ ∞ (fun z : (ℝ × ℝ) × ℝ => g (z.1.1, z.2, z.1.2)) :=
    hg.comp (by fun_prop)
  have hHc : ContDiff ℝ ∞ (fun z : (ℝ × ℝ) × ℝ => cdetaExp c n z.2 • g (z.1.1, z.2, z.1.2)) :=
    ((cdetaExp_cd c n).comp contDiff_snd).smul hGc
  have hI := intervalParamSmooth_proof (ℝ × ℝ) MeridC 0 c _ hHc
  have hI1 : ContDiff ℝ 1 (fun y : ℝ × ℝ => ∫ q in (0 : ℝ)..c, cdetaExp c n q • g (y.1, q, y.2)) := by
    have h := contDiff_infty.1 hI.1 1
    exact_mod_cast h
  have hDiff : DifferentiableAt ℝ
      (fun y : ℝ × ℝ => ∫ q in (0 : ℝ)..c, cdetaExp c n q • g (y.1, q, y.2)) x :=
    hI1.differentiable one_ne_zero x
  have hD : fderiv ℝ (fun y : ℝ × ℝ => ∫ q in (0 : ℝ)..c, cdetaExp c n q • g (y.1, q, y.2)) x (0, 1)
      = ∫ q in (0 : ℝ)..c, cdetaExp c n q • fderiv ℝ g (x.1, q, x.2) (0, 0, 1) := by
    refine Eq.trans (hI.2 x (0, 1)) ?_
    apply intervalIntegral.integral_congr
    intro q _
    exact cdetaPt c g hg n x q
  have hfn : nzCoeff c n g
      = fun y : ℝ × ℝ => ((1 / c : ℝ) : ℂ) • ∫ q in (0 : ℝ)..c, cdetaExp c n q • g (y.1, q, y.2) :=
    rfl
  have hLHS : fderiv ℝ (nzCoeff c n g) x (0, 1)
      = ((1 / c : ℝ) : ℂ) • ∫ q in (0 : ℝ)..c, cdetaExp c n q • fderiv ℝ g (x.1, q, x.2) (0, 0, 1) := by
    rw [hfn, fderiv_fun_const_smul hDiff ((1 / c : ℝ) : ℂ), smul_apply, hD]
  have hRHS : nzCoeff c n (pdEta g) x
      = ((1 / c : ℝ) : ℂ) • ∫ q in (0 : ℝ)..c, cdetaExp c n q • fderiv ℝ g (x.1, q, x.2) (0, 0, 1) :=
    rfl
  rw [hLHS, hRHS]

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.FlatLeray
