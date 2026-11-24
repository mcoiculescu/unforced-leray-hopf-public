import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6.VtvFluxLemmas
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.WeightedEnergy.DivFreeCutoffDensity.QPrimSmooth

/-!
# Part III-b, task `PartIII-b:C/flatset/col/6/5/2`: joint smoothness of the stream function `vtvZp`

Target (`VtvFluxLemmas.lean`): `VtvZpSmooth`. Source of record:
`the November 2 reference manuscript`, lines 3511-3514 and 3426-3440.

With `a = -(R₀+1)` the substitution `t = (η - a) u + a` gives
`vtvZp Φ R₀ s x = -((η - a) ∫_0^1 Φ_s(q, (η - a) u + a) du)`, a parametric integral over the fixed
interval `[0,1]` with smooth integrand, smooth in every finite order by
`DfcQPrimSmoothAux.ipsContDiff` (differentiation under the integral sign).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ComplexConjugate

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

/-- Substitution form of the stream function (`intervalIntegral.smul_integral_comp_mul_add`). -/
theorem vtvZp_eq_param_aux (Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ) (R₀ : ℝ) (p : ℝ × (ℝ × ℝ)) :
    vtvZp Φ R₀ p.1 p.2 = -((p.2.2 - (-(R₀ + 1))) *
      ∫ u in (0:ℝ)..1, Φ p.1 (p.2.1, (p.2.2 - (-(R₀ + 1))) * u + -(R₀ + 1)) 0) := by
  have h := intervalIntegral.smul_integral_comp_mul_add (a := (0:ℝ)) (b := (1:ℝ))
    (f := fun t => Φ p.1 (p.2.1, t) 0) (p.2.2 - (-(R₀ + 1))) (-(R₀ + 1))
  have e0 : (p.2.2 - (-(R₀ + 1))) * 0 + -(R₀ + 1) = -(R₀ + 1) := by ring
  have e1 : (p.2.2 - (-(R₀ + 1))) * 1 + -(R₀ + 1) = p.2.2 := by ring
  rw [e0, e1, smul_eq_mul] at h
  unfold vtvZp
  linear_combination h

/-- Target: `VtvZpSmooth`. Joint smoothness of `(s, x) ↦ Z(s, x)` for a flat test. -/
theorem vtvZpSmooth : VtvZpSmooth := by
  intro c Φ hΦ R₀
  have hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : (ℝ × (ℝ × ℝ)) × ℝ =>
        Φ z.1.1 (z.1.2.1, (z.1.2.2 - (-(R₀ + 1))) * z.2 + -(R₀ + 1)) 0) := by
    have hmap : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun z : (ℝ × (ℝ × ℝ)) × ℝ =>
          (z.1.1, (z.1.2.1, (z.1.2.2 - (-(R₀ + 1))) * z.2 + -(R₀ + 1)))) := by
      fun_prop
    exact (hΦ.smooth 0).comp hmap
  have hI : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × (ℝ × ℝ) => ∫ u in (0:ℝ)..1,
        Φ p.1 (p.2.1, (p.2.2 - (-(R₀ + 1))) * u + -(R₀ + 1)) 0) :=
    contDiff_infty.2 fun n =>
      UnforcedLeray.Short.IIIa.DfcQPrimSmoothAux.ipsContDiff (ℝ × (ℝ × ℝ)) 0 1 n ℝ
        (fun z : (ℝ × (ℝ × ℝ)) × ℝ =>
          Φ z.1.1 (z.1.2.1, (z.1.2.2 - (-(R₀ + 1))) * z.2 + -(R₀ + 1)) 0)
        (contDiff_infty.1 hg n)
  have hfun : (fun p : ℝ × (ℝ × ℝ) => vtvZp Φ R₀ p.1 p.2) = fun p =>
      -((p.2.2 - (-(R₀ + 1))) *
        ∫ u in (0:ℝ)..1, Φ p.1 (p.2.1, (p.2.2 - (-(R₀ + 1))) * u + -(R₀ + 1)) 0) :=
    funext fun p => vtvZp_eq_param_aux Φ R₀ p
  rw [hfun]
  have hlin : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × (ℝ × ℝ) => p.2.2 - (-(R₀ + 1))) := by
    fun_prop
  exact (hlin.mul hI).neg

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
