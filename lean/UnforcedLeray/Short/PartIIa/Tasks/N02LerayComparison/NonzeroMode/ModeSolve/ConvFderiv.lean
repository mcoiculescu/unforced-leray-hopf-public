import UnforcedLeray.Short.PartIIa.Sub.N02_4_5.Gen

/-!
# Part II-a, task `PartII-a:N02/4/5` (`NzModeSolve`): `NzConvFderiv` from `NzConvGenHyp`

Source of record: `the November 2 reference manuscript`, lines 1713-1722.

Conditional theorem `nzConvFderiv_of`: from the domination hypotheses `NzConvGenHyp` (the Green
family satisfies `GenHyp`), the `(0,1)`-derivative of the Green convolution is the Green convolution
of the `(0,1)`-derivative of the data. The proof moves `fderiv` under the integral sign
(`ParamIntegralSmoothAux.pm_hasFDerivAt_gen`), evaluates the integral of a continuous linear map
(`ContinuousLinearMap.integral_apply`), and differentiates the translated term pointwise.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

/-- Pointwise `(0,1)`-derivative of one translated Green term `y ↦ G_k(t) h(y.1, y.2 - t)`. -/
theorem nzcf_fderiv_term (k t : ℝ) (h : ℝ × ℝ → ℂ) (hh : ContDiff ℝ ∞ h) (x : ℝ × ℝ) :
    fderiv ℝ (fun y : ℝ × ℝ => (nzGreen k t : ℂ) * h (y.1, y.2 - t)) x (0, 1)
      = (nzGreen k t : ℂ) * fderiv ℝ h (x.1, x.2 - t) (0, 1) := by
  have hφ : HasFDerivAt (fun y : ℝ × ℝ => (y.1, y.2 - t))
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).prod (ContinuousLinearMap.snd ℝ ℝ ℝ)) x :=
    hasFDerivAt_fst.prodMk (hasFDerivAt_snd.sub_const t)
  have hh' : HasFDerivAt h (fderiv ℝ h (x.1, x.2 - t)) (x.1, x.2 - t) :=
    ((hh.differentiable (by simp)) (x.1, x.2 - t)).hasFDerivAt
  have hG : HasFDerivAt (fun y : ℝ × ℝ => (nzGreen k t : ℂ) * h (y.1, y.2 - t))
      ((nzGreen k t : ℂ) • ((fderiv ℝ h (x.1, x.2 - t)).comp
        ((ContinuousLinearMap.fst ℝ ℝ ℝ).prod (ContinuousLinearMap.snd ℝ ℝ ℝ)))) x :=
    (HasFDerivAt.comp x hh' hφ).const_mul (nzGreen k t : ℂ)
  rw [hG.fderiv]
  simp [smul_eq_mul]

/-- **`NzConvFderiv` from `NzConvGenHyp`: `∂_η` commutes with the Green convolution.** -/
theorem nzConvFderiv_of (hG : NzConvGenHyp) : NzConvFderiv := by
  intro k hk h hh hcs x
  have hGH := hG k hk h hh hcs
  have hD : HasFDerivAt (nzConv k h)
      (∫ t : ℝ, fderiv ℝ (fun y : ℝ × ℝ => (nzGreen k t : ℂ) * h (y.1, y.2 - t)) x ∂volume) x :=
    ParamIntegralSmoothAux.pm_hasFDerivAt_gen hGH x
  have hint : Integrable
      (fun t : ℝ => fderiv ℝ (fun y : ℝ × ℝ => (nzGreen k t : ℂ) * h (y.1, y.2 - t)) x) volume := by
    obtain ⟨b, hb, hbd⟩ := hGH.2.2 1
    refine Integrable.mono' hb (ParamIntegralSmoothAux.pm_aesm1 x (hGH.2.1 1 x)) ?_
    filter_upwards [hbd] with t ht
    rw [ParamIntegralSmoothAux.pm_norm_fderiv_one]
    exact ht x
  rw [hD.fderiv, ContinuousLinearMap.integral_apply hint (0, 1)]
  have hint2 : ∫ t : ℝ, fderiv ℝ (fun y : ℝ × ℝ => (nzGreen k t : ℂ) * h (y.1, y.2 - t)) x (0, 1) ∂volume
      = ∫ t : ℝ, (nzGreen k t : ℂ) * fderiv ℝ h (x.1, x.2 - t) (0, 1) ∂volume := by
    congr 1
    funext t
    exact nzcf_fderiv_term k t h hh x
  rw [hint2]
  rfl

end UnforcedLeray.Short.PartIIa
