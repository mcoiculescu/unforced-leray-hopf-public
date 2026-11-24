import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T13_1_7_2
import UnforcedLeray.Short.PartIIb.Tasks.FlatUnique.CellStream.HrBox

/-!
# `PartII-b:T13/1/7/2/1`: integrability of `b ∈ H_r` against tests in `s > 0`

Source: `the November 2 reference manuscript` lines 1928-1933.

Proof. Let `K = tsupport ψ`, a compact subset of `Ioi 0 ×ˢ univ`. Its coordinates are bounded:
`x0.1 ≤ s ≤ H0`, `|q| ≤ R0`, `|η| ≤ L0` on `K`, where `x0` minimizes `s` on `K` (so `x0.1 > 0`).
The box `B = [x0.1, H0] × [-R0, R0] × [-L0, L0]` contains `K`. The leaf `hrBoxIntegrable`
(`CellStream/HrBox.lean`) gives `b · i` integrable on `B` for every `H_r` profile, and `ψ` is
continuous on the compact box, so `b · i · ψ` is integrable on `B` (`IntegrableOn.mul_continuousOn`).
It vanishes off `K ⊆ B`, hence it is integrable on the whole chart (`integrableOn_iff_integrable_of_support_subset`).
If `K` is empty, `ψ = 0` and the claim is trivial.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

open MeasureTheory Set Filter
open scoped ENNReal ContDiff

theorem wbdIntH_proof : UnforcedLeray.Short.IIb.WbdIntH := by
  intro c r hc hr b hb i ψ hψc hψcs hψsupp
  have hrb : HrBoxIntegrable := hrBoxIntegrable
  by_cases hne : (tsupport ψ).Nonempty
  · have hK : IsCompact (tsupport ψ) := hψcs.isCompact
    have hs : ContinuousOn (fun x : Coord => x.1) (tsupport ψ) := continuous_fst.continuousOn
    have hq : ContinuousOn (fun x : Coord => x.2.1) (tsupport ψ) :=
      (continuous_fst.comp continuous_snd).continuousOn
    have he : ContinuousOn (fun x : Coord => x.2.2) (tsupport ψ) :=
      (continuous_snd.comp continuous_snd).continuousOn
    obtain ⟨x0, hx0K, hmin⟩ := hK.exists_isMinOn hne hs
    have hσ : 0 < x0.1 := (hψsupp hx0K).1
    obtain ⟨H0, hH0⟩ := hK.exists_bound_of_continuousOn hs
    obtain ⟨R0, hR0⟩ := hK.exists_bound_of_continuousOn hq
    obtain ⟨L0, hL0⟩ := hK.exists_bound_of_continuousOn he
    have hmem : ∀ x ∈ tsupport ψ,
        x ∈ Icc x0.1 H0 ×ˢ (Icc (-R0) R0 ×ˢ Icc (-L0) L0) := by
      intro x hx
      have h1 : x0.1 ≤ x.1 := isMinOn_iff.1 hmin x hx
      have h2 : |x.1| ≤ H0 := by simpa [Real.norm_eq_abs] using hH0 x hx
      have h3 : |x.2.1| ≤ R0 := by simpa [Real.norm_eq_abs] using hR0 x hx
      have h4 : |x.2.2| ≤ L0 := by simpa [Real.norm_eq_abs] using hL0 x hx
      simp only [Set.mem_prod, Set.mem_Icc]
      exact ⟨⟨h1, (abs_le.1 h2).2⟩, abs_le.1 h3, abs_le.1 h4⟩
    have hBint : IntegrableOn (fun x : Coord => b x i)
        (Icc x0.1 H0 ×ˢ (Icc (-R0) R0 ×ˢ Icc (-L0) L0)) volume :=
      hrb c r b hc hr hb x0.1 H0 R0 L0 hσ i
    have hcont : ContinuousOn (fun x : Coord => ((ψ x : ℝ) : ℂ))
        (Icc x0.1 H0 ×ˢ (Icc (-R0) R0 ×ˢ Icc (-L0) L0)) :=
      (Complex.continuous_ofReal.comp hψc).continuousOn
    have hcompact : IsCompact (Icc x0.1 H0 ×ˢ (Icc (-R0) R0 ×ˢ Icc (-L0) L0)) :=
      isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
    have hmul := hBint.mul_continuousOn hcont hcompact
    have hsupp : Function.support (fun x : Coord => b x i * ((ψ x : ℝ) : ℂ)) ⊆
        Icc x0.1 H0 ×ˢ (Icc (-R0) R0 ×ˢ Icc (-L0) L0) := by
      intro x hx
      apply hmem x
      apply subset_tsupport ψ
      rw [Function.mem_support]
      intro h0
      exact (Function.mem_support.1 hx) (by simp [h0])
    exact (integrableOn_iff_integrable_of_support_subset hsupp).1 hmul
  · have hψ0 : ∀ x, ψ x = 0 := by
      intro x
      by_contra h
      exact hne ⟨x, subset_tsupport ψ h⟩
    simp [hψ0]

end UnforcedLeray.Short.IIb

end
