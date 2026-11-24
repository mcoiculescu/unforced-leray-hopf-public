import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6.VtvFlux.VtvZpSmooth
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.WeightedEnergy.DivFreeCutoffDensity.QPrimDeriv

/-!
# Part III-b, task `PartIII-b:C/flatset/col/6/5/4`: `∂_q Z = Φ_η` for the stream function `vtvZp`

Target (`VtvFluxLemmas.lean`): `VtvZpPdQ`. Source of record:
`the November 2 reference manuscript`, lines 3511-3514 and 3426-3440.

Write `a = -(R₀+1)`. By `VtvZpSmooth` the slice `vtvZp Φ R₀ s` is differentiable, so `pd 0` is the
derivative in `q` of `q' ↦ -∫_a^η Φ s (q', t) 0 dt`. Differentiating under the integral
(`DfcQPrimDerivAux.hasDerivAt_param`, with `f (t, q') = Φ s (q', t) 0`) gives
`-∫_a^η ∂_qΦ_0(q,t) dt`. By `div Φ = 0`, `∂_qΦ_0 = -∂_tΦ_1`, so the integral is
`∫_a^η ∂_tΦ_1 dt = Φ_1(q,η) - Φ_1(q,a)` (fundamental theorem of calculus), and `Φ_1(q,a) = 0`
since `|a| = R₀ + 1 > R₀` lies outside the support.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ComplexConjugate

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.Short.IIIa (IsFlatTest)

/-- Target: `VtvZpPdQ`. `∂_q Z = Φ_η` (`div Φ = 0` and vanishing of `Φ` at `η = -(R₀+1)`). -/
theorem vtvZpPdQ : VtvZpPdQ := by
  intro c Φ s₁ s₂ R₀ hS s x
  rcases x with ⟨q, η⟩
  have hΦ : IsFlatTest c Φ := hS.1
  -- joint smoothness of the stream function, and differentiability of its slice
  have hZ := vtvZpSmooth c Φ hΦ R₀
  have hG : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (vtvZp Φ R₀ s) :=
    hZ.comp (contDiff_const.prodMk contDiff_id)
  have hdiff : DifferentiableAt ℝ (vtvZp Φ R₀ s) (q, η) :=
    (hG.differentiable (by simp)).differentiableAt
  rw [UnforcedLeray.Short.IIIa.DfcQPrimDerivAux.pd0_eq (vtvZp Φ R₀ s) q η hdiff]
  -- smoothness of the components
  have hΦ0 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : ℝ × ℝ => Φ s y 0) :=
    (hΦ.smooth 0).comp (contDiff_const.prodMk contDiff_id)
  have hΦ1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : ℝ × ℝ => Φ s y 1) :=
    (hΦ.smooth 1).comp (contDiff_const.prodMk contDiff_id)
  have hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => Φ s (p.2, p.1) 0) :=
    hΦ0.comp (contDiff_snd.prodMk contDiff_fst)
  -- differentiation of `q' ↦ -∫_a^η Φ s (q', t) 0 dt` under the integral sign
  have hD := UnforcedLeray.Short.IIIa.DfcQPrimDerivAux.hasDerivAt_param
    (fun p : ℝ × ℝ => Φ s (p.2, p.1) 0) hf (-(R₀ + 1)) η q
  have hpt : ∀ t : ℝ, B0579.pd 1 (fun p : ℝ × ℝ => Φ s (p.2, p.1) 0) (t, q) =
      B0579.pd 0 (fun y : ℝ × ℝ => Φ s y 0) (q, t) := by
    intro t
    have hfd : DifferentiableAt ℝ (fun p : ℝ × ℝ => Φ s (p.2, p.1) 0) (t, q) :=
      (hf.differentiable (by simp)) (t, q)
    have hgd : DifferentiableAt ℝ (fun y : ℝ × ℝ => Φ s y 0) (q, t) :=
      (hΦ0.differentiable (by simp)) (q, t)
    rw [UnforcedLeray.Short.IIIa.DfcQPrimDerivAux.pd1_eq _ t q hfd,
      UnforcedLeray.Short.IIIa.DfcQPrimDerivAux.pd0_eq _ q t hgd]
  have hint_eq : ∫ t in (-(R₀ + 1))..η, B0579.pd 1 (fun p : ℝ × ℝ => Φ s (p.2, p.1) 0) (t, q) =
      ∫ t in (-(R₀ + 1))..η, B0579.pd 0 (fun y : ℝ × ℝ => Φ s y 0) (q, t) :=
    intervalIntegral.integral_congr (fun t _ => hpt t)
  have hD2 : HasDerivAt (fun q' : ℝ => vtvZp Φ R₀ s (q', η))
      (-(∫ t in (-(R₀ + 1))..η, B0579.pd 0 (fun y : ℝ × ℝ => Φ s y 0) (q, t))) q := by
    have h := hD.neg
    rw [hint_eq] at h
    exact h
  -- div Φ = 0 converts `∂_q Φ_0` into `-∂_t Φ_1`
  have hfin : ∫ t in (-(R₀ + 1))..η, B0579.pd 0 (fun y : ℝ × ℝ => Φ s y 0) (q, t) =
      ∫ t in (-(R₀ + 1))..η, -(B0579.pd 1 (fun y : ℝ × ℝ => Φ s y 1) (q, t)) := by
    apply intervalIntegral.integral_congr
    intro t _
    have h := hΦ.divFree s (q, t)
    dsimp only
    linarith
  -- fundamental theorem of calculus in `η`
  have hΦ1d : Differentiable ℝ (fun y : ℝ × ℝ => Φ s y 1) := hΦ1.differentiable (by simp)
  have hsl : Differentiable ℝ (fun τ : ℝ => Φ s (q, τ) 1) :=
    hΦ1d.comp ((differentiable_const q).prodMk differentiable_id)
  have hFTC : ∫ t in (-(R₀ + 1))..η, B0579.pd 1 (fun y : ℝ × ℝ => Φ s y 1) (q, t) =
      Φ s (q, η) 1 - Φ s (q, -(R₀ + 1)) 1 := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t : ℝ => Φ s (q, t) 1)
    · intro t _
      show HasDerivAt (fun τ : ℝ => Φ s (q, τ) 1) (B0579.pd 1 (fun y : ℝ × ℝ => Φ s y 1) (q, t)) t
      rw [UnforcedLeray.Short.IIIa.DfcQPrimDerivAux.pd1_eq _ q t (hΦ1d (q, t))]
      exact (hsl t).hasDerivAt
    · show IntervalIntegrable (fun t : ℝ => B0579.pd 1 (fun y : ℝ × ℝ => Φ s y 1) (q, t))
        volume (-(R₀ + 1)) η
      refine Continuous.intervalIntegrable ?_ _ _
      have hc : Continuous (fun z : ℝ × ℝ => B0579.pd 1 (fun y : ℝ × ℝ => Φ s y 1) z) :=
        (hΦ1.continuous_fderiv (by simp)).clm_apply continuous_const
      exact hc.comp (continuous_const.prodMk continuous_id)
  -- `Φ` vanishes at `η = -(R₀+1)`, since `|-(R₀+1)| > R₀`
  have hab : R₀ < |-(R₀ + 1)| := by
    rw [abs_neg, abs_of_nonneg (by linarith [hS.2.2.1])]
    linarith
  have hz : Φ s (q, -(R₀ + 1)) 1 = 0 := hS.2.2.2 s (q, -(R₀ + 1)) 1 (Or.inr (Or.inr hab))
  rw [hD2.deriv, hfin, intervalIntegral.integral_neg, hFTC, hz]
  ring

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
