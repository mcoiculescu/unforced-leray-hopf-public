import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N01_9_1_1
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.StreamMember

/-!


Source of record: `the November 2 reference manuscript`, lines 1684-1689.

A stream field `StreamField ψ = -streamC 0 ψ` for a stream function `ψ`. The exact stream
membership `nearStreamMember_proof` (proved in `Tasks/N02LerayComparison/StreamMember.lean`, without
unconditional) gives `streamC 0 ψ ∈ solenoidalHC 0 c` for every complex band test `ψ`, and a stream
function is a band test. The submodule is closed under negation.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIa.N01

open UnforcedLeray.B0220 (Profile HSpace measureH)
open UnforcedLeray.B0223 (MeridC)

/-- A stream function is a complex band test. -/
theorem sfd2_isCTest {c : ℝ} {ψ : Profile → ℂ} (h : IsStreamFn c ψ) :
    UnforcedLeray.Short.PartIIa.IsCTest c ψ := by
  obtain ⟨hs, hp, s1, s2, R, hs1, hz⟩ := h
  refine ⟨hs, hp, s1, s2, R, hs1, fun p hne => ?_⟩
  by_contra hcon
  by_cases h1 : p.1 < s1
  · exact hne (hz p (Or.inl h1))
  by_cases h2 : s2 < p.1
  · exact hne (hz p (Or.inr (Or.inl h2)))
  by_cases h3 : R < |p.2.2|
  · exact hne (hz p (Or.inr (Or.inr h3)))
  exact hcon ⟨⟨not_lt.1 h1, not_lt.1 h2⟩, not_lt.1 h3⟩

/-- **Target `PartII-a:N01/9/1/1/2`**: stream fields are solenoidal in `𝓗`. -/
theorem streamSolenoidal : UnforcedLeray.Short.PartIIa.N01.StreamSolenoidal := by
  intro c _ g hg
  obtain ⟨ψ, hψ, hgψ⟩ := hg
  obtain ⟨hm, hmem⟩ := nearStreamMember_proof 0 c ψ (sfd2_isCTest hψ)
  have hneg : -(hm.toLp (streamC 0 ψ)) ∈ solenoidalHC 0 c := Submodule.neg_mem _ hmem
  have hEq : g = -(hm.toLp (streamC 0 ψ)) := by
    apply Lp.ext
    filter_upwards [hgψ, Lp.coeFn_neg (hm.toLp (streamC 0 ψ)), MemLp.coeFn_toLp hm]
      with p h1 h2 h3
    rw [h1, h2, Pi.neg_apply, h3]
    ext i
    fin_cases i <;> simp [StreamField, streamC]
  rw [hEq]
  exact hneg

end UnforcedLeray.Short.PartIIa.N01
