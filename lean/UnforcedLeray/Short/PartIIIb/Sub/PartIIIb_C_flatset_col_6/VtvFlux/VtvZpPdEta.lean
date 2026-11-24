import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6.VtvFlux.VtvZpSmooth
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.WeightedEnergy.DivFreeCutoffDensity.QPrimDeriv

/-!
# Part III-b, task `PartIII-b:C/flatset/col/6/5/3`: `∂_η Z = -Φ_q` for the stream function `vtvZp`

Target (`VtvFluxLemmas.lean`): `VtvZpPdEta`. Source of record:
`the November 2 reference manuscript`, lines 3511-3514 and 3426-3440.

Write `a = -(R₀+1)`. By `VtvZpSmooth` the slice `vtvZp Φ R₀ s` is differentiable, so
`pd 1` is the derivative of `t ↦ vtvZp Φ R₀ s (q, t)` (`DfcQPrimDerivAux.pd1_eq`). Unfolding,
`t ↦ vtvZp Φ R₀ s (q, t) = -∫_a^t Φ s (q,u) 0 du`, whose derivative is `-Φ s (q,η) 0` by the
fundamental theorem of calculus for a continuous integrand
(`intervalIntegral.integral_hasDerivAt_right`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ComplexConjugate

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.Short.IIIa (IsFlatTest)

/-- Target: `VtvZpPdEta`. `∂_η Z = -Φ_q` (fundamental theorem of calculus). -/
theorem vtvZpPdEta : VtvZpPdEta := by
  intro c Φ s₁ s₂ R₀ hS s x
  rcases x with ⟨q, η⟩
  have hΦ : IsFlatTest c Φ := hS.1
  -- joint smoothness of the stream function, and differentiability of its slice
  have hZ := vtvZpSmooth c Φ hΦ R₀
  have hG : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (vtvZp Φ R₀ s) :=
    hZ.comp (contDiff_const.prodMk contDiff_id)
  have hdiff : DifferentiableAt ℝ (vtvZp Φ R₀ s) (q, η) :=
    (hG.differentiable (by simp)).differentiableAt
  rw [UnforcedLeray.Short.IIIa.DfcQPrimDerivAux.pd1_eq (vtvZp Φ R₀ s) q η hdiff]
  -- the integrand `t ↦ Φ s (q, t) 0` is continuous
  have hs0 : Continuous (fun t : ℝ => Φ s (q, t) 0) :=
    ((hΦ.smooth 0).comp (contDiff_const.prodMk (contDiff_const.prodMk contDiff_id))).continuous
  have hF : HasDerivAt (fun t : ℝ => ∫ u in (-(R₀ + 1))..t, Φ s (q, u) 0) (Φ s (q, η) 0) η :=
    intervalIntegral.integral_hasDerivAt_right (hs0.intervalIntegrable _ _)
      (hs0.stronglyMeasurableAtFilter volume (𝓝 η)) hs0.continuousAt
  have hfun : (fun t : ℝ => vtvZp Φ R₀ s (q, t)) =
      fun t : ℝ => -∫ u in (-(R₀ + 1))..t, Φ s (q, u) 0 := rfl
  rw [hfun]
  exact hF.neg.deriv

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
