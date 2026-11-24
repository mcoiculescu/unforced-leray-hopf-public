import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6.VtvFluxLemmas
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6.VtvFlux.VtvZpSmooth
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6.VtvFlux.VtvZpPdQ

/-!
# Part III-b, task `PartIII-b:C/flatset/col/6/5/6`: above the support the stream function is the flux

Target (`VtvFluxLemmas.lean`): `VtvZpFlux`. Source of record:
`the November 2 reference manuscript`, lines 3511-3514 and 3426-3440.

Let `a = -(R₀+1)`, `b = R₀+1`, and `x = (q, η)` with `η > R₀`.

* Step 1 (`η`-independence): `Z(s,q,η) = Z(s,q,b)`, since `∫_b^η Φ_0(s,q,t) dt = 0` (on the interval
  between `b` and `η` every point has `|t| > R₀`, so `Φ = 0` there by the support clause).
* Step 2 (`q`-independence at `η = b`): `∂_q Z(s,·,b) = Φ_η(s,·,b) = 0` (`VtvZpPdQ`, since `|b| > R₀`),
  so `q ↦ Z(s,q,b)` is constant.

Hence `Z(s,q,η) = Z(s,0,b) = F(s)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ComplexConjugate

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.Short.IIIa (IsFlatTest)

/-- Target: `VtvZpFlux`. For `η > R₀`, `Z(s, q, η) = F(s)`, the flux. -/
theorem vtvZpFlux : VtvZpFlux := by
  intro c Φ s₁ s₂ R₀ hS s x hx
  rcases x with ⟨q, η⟩
  have hx' : R₀ < η := hx
  have hΦ : IsFlatTest c Φ := hS.1
  have hR0 : 0 ≤ R₀ := hS.2.2.1
  have hZ := vtvZpSmooth c Φ hΦ R₀
  -- continuity of the integrand `t ↦ Φ s (q, t) 0`
  have hcont : Continuous (fun t : ℝ => Φ s (q, t) 0) :=
    ((hΦ.smooth 0).comp (contDiff_const.prodMk (contDiff_const.prodMk contDiff_id))).continuous
  -- Step 1: `η`-independence
  have hsplit : vtvZp Φ R₀ s (q, η) = vtvZp Φ R₀ s (q, R₀ + 1) := by
    have hI1 : IntervalIntegrable (fun t : ℝ => Φ s (q, t) 0) volume (-(R₀ + 1)) (R₀ + 1) :=
      hcont.intervalIntegrable _ _
    have hI2 : IntervalIntegrable (fun t : ℝ => Φ s (q, t) 0) volume (R₀ + 1) η :=
      hcont.intervalIntegrable _ _
    have hadd := intervalIntegral.integral_add_adjacent_intervals hI1 hI2
    have hzero : ∫ t in (R₀ + 1)..η, Φ s (q, t) 0 = 0 := by
      have h' : ∫ t in (R₀ + 1)..η, Φ s (q, t) 0 = ∫ t in (R₀ + 1)..η, (0:ℝ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        have hR : R₀ < t := by
          rcases Set.mem_uIcc.1 ht with ⟨h1, _⟩ | ⟨h1, _⟩
          · linarith
          · linarith
        exact hS.2.2.2 s (q, t) 0 (Or.inr (Or.inr (lt_of_lt_of_le hR (le_abs_self t))))
      rw [h', intervalIntegral.integral_zero]
    have key : ∫ t in (-(R₀ + 1))..η, Φ s (q, t) 0 =
        ∫ t in (-(R₀ + 1))..(R₀ + 1), Φ s (q, t) 0 := by
      rw [← hadd, hzero, add_zero]
    show -∫ t in (-(R₀ + 1))..η, Φ s (q, t) 0 = -∫ t in (-(R₀ + 1))..(R₀ + 1), Φ s (q, t) 0
    rw [key]
  -- Step 2: `q`-independence at `η = R₀ + 1`
  have hG : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (vtvZp Φ R₀ s) :=
    hZ.comp (contDiff_const.prodMk contDiff_id)
  have hGq : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q' : ℝ => vtvZp Φ R₀ s (q', R₀ + 1)) :=
    hZ.comp (contDiff_const.prodMk (contDiff_id.prodMk contDiff_const))
  have hderiv : ∀ q' : ℝ, deriv (fun q'' : ℝ => vtvZp Φ R₀ s (q'', R₀ + 1)) q' = 0 := by
    intro q'
    have hdA : DifferentiableAt ℝ (vtvZp Φ R₀ s) (q', R₀ + 1) :=
      (hG.differentiable (by simp)).differentiableAt
    have h := UnforcedLeray.Short.IIIa.DfcQPrimDerivAux.pd0_eq (vtvZp Φ R₀ s) q' (R₀ + 1) hdA
    rw [← h, vtvZpPdQ c Φ s₁ s₂ R₀ hS s (q', R₀ + 1)]
    have hb : R₀ < |(q', R₀ + 1).2| := by
      show R₀ < |R₀ + 1|
      rw [abs_of_pos (by linarith)]
      linarith
    exact hS.2.2.2 s (q', R₀ + 1) 1 (Or.inr (Or.inr hb))
  have hdiff : Differentiable ℝ (fun q'' : ℝ => vtvZp Φ R₀ s (q'', R₀ + 1)) :=
    fun q' => (hGq.differentiable (by simp)).differentiableAt
  have hconst := is_const_of_deriv_eq_zero hdiff hderiv q 0
  -- assemble
  rw [hsplit]
  show vtvZp Φ R₀ s (q, R₀ + 1) = vtvZp Φ R₀ s (0, R₀ + 1)
  exact hconst

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
