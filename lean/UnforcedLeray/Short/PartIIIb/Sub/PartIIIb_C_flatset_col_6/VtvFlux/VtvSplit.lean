import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6.VtvFluxLemmas
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6.VtvFlux.VtvZpSmooth
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6.VtvFlux.VtvZpPdEta
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6.VtvFlux.VtvZpPdQ
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6.VtvFlux.VtvZpFlux
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6.VtvFlux.VtvThetaFacts
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.WeightedEnergy.DivFreeCutoffDensity.CutPd
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Part III-b, task `PartIII-b:C/flatset/col/6/5/9`: the split `Φ = ∇^⊥ζ_R + E_R`

Target (`VtvFluxLemmas.lean`): `VtvSplit`. Source of record:
`the November 2 reference manuscript`, lines 3511-3514 and 3426-3440.

For fixed `s`, put `g = Z(s,·) = vtvZp Φ R₀ s` and `ψ(t) = θ(t/R)`, so that
`ζ_R(s,·) = (y ↦ ψ(y.2) g(y))` and `ψ'(t) = θ'(t/R)/R`.  The product rule (`pdSndMul`) gives
`∂_η ζ_R = ψ(η)(-Φ_0) + g(η)ψ'(η)` and `∂_q ζ_R = ψ(η)Φ_1`, using `VtvZpPdEta`, `VtvZpPdQ`.
For `η ≤ R`: `ψ = 1`, `ψ' = 0`, `E_R = 0`, so the identity is `Φ = Φ`.
For `R ≤ η`: `Φ = 0` (support, since `R₀ < R ≤ η`) and `g = F(s)` (`VtvZpFlux`), so
`streamField 0 = -(g ψ') = -E_R,0` and `streamField 1 = 0 = E_R,1`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ComplexConjugate

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.Short.IIIa (IsFlatTest)

/-- Target: `VtvSplit`. -/
theorem vtvSplit : VtvSplit := by
  intro c Φ s₁ s₂ R₀ hS R hR s x i
  have hΦ : IsFlatTest c Φ := hS.1
  have hR0 : 0 < R := lt_of_le_of_lt hS.2.2.1 hR
  have hRne : R ≠ 0 := hR0.ne'
  -- smoothness of the cutoff profile and of its derivative
  obtain ⟨hθc, hθ1, hθ2, hθ0, -⟩ := vtvThetaFacts
  have hθd : Differentiable ℝ vtvTheta := hθc.differentiable (by simp)
  -- the one-variable profile `ψ(t) = θ(t/R)`
  obtain ⟨ψ, hψdef⟩ : ∃ ψ : ℝ → ℝ, ψ = fun t => vtvTheta (t / R) := ⟨_, rfl⟩
  have hψder : ∀ t, HasDerivAt ψ (deriv vtvTheta (t / R) / R) t := by
    intro t
    rw [hψdef]
    have h1 : HasDerivAt (fun u : ℝ => u / R) (1 / R) t :=
      (hasDerivAt_id' (x := t)).div_const R
    have hθt : HasDerivAt vtvTheta (deriv vtvTheta (t / R)) (t / R) := (hθd (t / R)).hasDerivAt
    have h2 : HasDerivAt (vtvTheta ∘ fun u : ℝ => u / R) (deriv vtvTheta (t / R) * (1 / R)) t :=
      HasDerivAt.comp t hθt h1
    have e : deriv vtvTheta (t / R) / R = deriv vtvTheta (t / R) * (1 / R) := by ring
    rw [e]
    exact h2
  have hψd : Differentiable ℝ ψ := fun t => (hψder t).differentiableAt
  -- the stream function `g = Z(s,·)` is differentiable
  have hZ := vtvZpSmooth c Φ hΦ R₀
  have hgd : Differentiable ℝ (vtvZp Φ R₀ s) :=
    (hZ.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp)
  -- the stream field is the product `ψ(η) Z`
  have hzeta : vtvZeta Φ R₀ R s = fun y => ψ y.2 * vtvZp Φ R₀ s y := by
    funext y
    simp only [vtvZeta, hψdef]
    ring
  -- the two partial derivatives of `ζ_R`
  have hA : B0579.pd 1 (vtvZeta Φ R₀ R s) x =
      ψ x.2 * (-Φ s x 0) + vtvZp Φ R₀ s x * deriv ψ x.2 := by
    rw [hzeta, UnforcedLeray.Short.IIIa.DfcCutPdAux.pdSndMul 1 ψ _ hψd hgd x,
      UnforcedLeray.Short.IIIa.DfcCutPdAux.dir1_snd, vtvZpPdEta c Φ s₁ s₂ R₀ hS s x]
    ring
  have hB : B0579.pd 0 (vtvZeta Φ R₀ R s) x = ψ x.2 * Φ s x 1 := by
    rw [hzeta, UnforcedLeray.Short.IIIa.DfcCutPdAux.pdSndMul 0 ψ _ hψd hgd x,
      UnforcedLeray.Short.IIIa.DfcCutPdAux.dir0_snd, vtvZpPdQ c Φ s₁ s₂ R₀ hS s x]
    ring
  -- unfolding the stream field and the remainder
  have hsf0 : streamField (vtvZeta Φ R₀ R) s x 0 = -(B0579.pd 1 (vtvZeta Φ R₀ R s) x) := by
    simp [streamField]
  have hsf1 : streamField (vtvZeta Φ R₀ R) s x 1 = B0579.pd 0 (vtvZeta Φ R₀ R s) x := by
    simp [streamField]
  have he0 : vtvErr Φ R₀ R s x 0 = vtvFluxF Φ R₀ s * deriv vtvTheta (x.2 / R) / R := by
    unfold vtvErr
    rw [if_pos rfl]
  have he1 : vtvErr Φ R₀ R s x 1 = 0 := by
    unfold vtvErr
    rw [if_neg (by decide)]
  -- the derivative of `ψ`
  have hψ'eq : deriv ψ x.2 = deriv vtvTheta (x.2 / R) / R := (hψder x.2).deriv
  obtain rfl | rfl : i = 0 ∨ i = 1 := by fin_cases i <;> simp
  · rw [hsf0, hA, he0, hψ'eq]
    rcases le_total x.2 R with h | h
    · -- `η ≤ R`: `ψ = 1`, `ψ' = 0`, and the remainder vanishes
      have hq : x.2 / R ≤ 1 := (div_le_one hR0).2 h
      have hψ1 : ψ x.2 = 1 := by
        simp only [hψdef]
        exact hθ1 _ hq
      rw [hψ1, hθ0 _ (Or.inl hq)]
      ring
    · -- `R ≤ η`: `Φ = 0` there and `Z = F(s)`
      have hRx : R₀ < |x.2| := lt_of_lt_of_le hR (le_trans h (le_abs_self _))
      have hΦ0 : Φ s x 0 = 0 := hS.2.2.2 s x 0 (Or.inr (Or.inr hRx))
      rw [vtvZpFlux c Φ s₁ s₂ R₀ hS s x (lt_of_lt_of_le hR h), hΦ0]
      ring
  · rw [hsf1, hB, he1]
    rcases le_total x.2 R with h | h
    · have hq : x.2 / R ≤ 1 := (div_le_one hR0).2 h
      have hψ1 : ψ x.2 = 1 := by
        simp only [hψdef]
        exact hθ1 _ hq
      rw [hψ1]
      ring
    · have hRx : R₀ < |x.2| := lt_of_lt_of_le hR (le_trans h (le_abs_self _))
      have hΦ1 : Φ s x 1 = 0 := hS.2.2.2 s x 1 (Or.inr (Or.inr hRx))
      rw [hΦ1]
      ring

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
