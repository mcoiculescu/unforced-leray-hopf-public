import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6.VtvFluxLemmas

/-!
# Part III-b, task `PartIII-b:C/flatset/col/6/5/5`: periodicity and vanishing of the stream function

Target (`VtvFluxLemmas.lean`): `VtvZpVanish`. Source of record:
`the November 2 reference manuscript`, lines 3511-3514 and 3426-3440.

`vtvZp Φ R₀ s x = -∫_{-(R₀+1)}^{x₂} Φ_s(x₁, t, 0) dt`. Periodicity in `q` comes from the periodicity of
`Φ`; vanishing off the age band from the support of `Φ`; and for `x₂ < -R₀` the whole interval of
integration lies in `{t < -R₀}`, where the integrand is zero.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ComplexConjugate

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

/-- Target: `VtvZpVanish`. Periodicity, vanishing off the age band, and vanishing below the
support of the stream function. -/
theorem vtvZpVanish : VtvZpVanish := by
  unfold VtvZpVanish
  intro c Φ s₁ s₂ R₀ hS
  unfold VtvFlatSupp at hS
  obtain ⟨hF, hs1, hR0, hsupp⟩ := hS
  refine ⟨?_, ?_, ?_⟩
  · -- (i) periodicity in `q`
    intro s x
    unfold vtvZp
    congr 1
    apply intervalIntegral.integral_congr
    intro t _
    exact hF.periodic s (x.1, t) 0
  · -- (ii) vanishing off the age band `[s₁, s₂]`
    intro s x hs
    have hz : ∀ t, Φ s (x.1, t) 0 = 0 := fun t =>
      hsupp s (x.1, t) 0 (by
        rcases hs with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h))
    have hzero : ∫ t in (-(R₀ + 1))..x.2, Φ s (x.1, t) 0
        = ∫ t in (-(R₀ + 1))..x.2, (0:ℝ) := by
      apply intervalIntegral.integral_congr
      intro t _
      exact hz t
    unfold vtvZp
    rw [hzero]
    simp
  · -- (iii) vanishing below the support, `x₂ < -R₀`
    intro s x hx
    have hz : ∀ t ∈ uIcc (-(R₀ + 1)) x.2, Φ s (x.1, t) 0 = 0 := by
      intro t ht
      apply hsupp s (x.1, t) 0
      refine Or.inr (Or.inr ?_)
      show R₀ < |t|
      have hlt : t < -R₀ := by
        rcases Set.mem_uIcc.1 ht with ⟨_, h2⟩ | ⟨_, h2⟩
        · linarith
        · linarith
      have hneg : t < 0 := by linarith
      rw [abs_of_neg hneg]
      linarith
    have hzero : ∫ t in (-(R₀ + 1))..x.2, Φ s (x.1, t) 0
        = ∫ t in (-(R₀ + 1))..x.2, (0:ℝ) := by
      apply intervalIntegral.integral_congr
      intro t ht
      exact hz t ht
    unfold vtvZp
    rw [hzero]
    simp

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
