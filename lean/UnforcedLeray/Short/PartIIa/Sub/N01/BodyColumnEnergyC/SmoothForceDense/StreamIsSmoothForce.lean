import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N01_9_1_1
import UnforcedLeray.Short.PartIIa.Sub.N02
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.StreamMember.CTestFderiv

/-!


Source of record: `the November 2 reference manuscript`, lines 1684-1689.

The stream field `(∂_η ψ, -∂_q ψ)` of a stream function `ψ` (`IsStreamFn`) is a smooth force
(`IsSmoothForceFn`): its components are the directional derivatives of the complex band test
`ψ` (`ctf_isCTest_fderiv`), so they are smooth, `c`-periodic and vanish outside a band.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIa.N01

open UnforcedLeray.B0220 (Profile HSpace measureH)
open UnforcedLeray.B0223 (MeridC)

/-- A stream function is a complex band test. -/
theorem sfd1_isCTest {c : ℝ} {ψ : Profile → ℂ} (h : IsStreamFn c ψ) :
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

theorem sfd1_contDiff_mk {a b : Profile → ℂ} (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) :
    ContDiff ℝ ∞ (fun p : Profile => (!₂[a p, b p] : MeridC)) := by
  rw [contDiff_piLp]
  intro i
  fin_cases i
  · simpa using ha
  · simpa using hb

/-- **Target `PartII-a:N01/9/1/1/1`**: the stream field of a stream function is a smooth force. -/
theorem streamIsSmoothForce : UnforcedLeray.Short.PartIIa.N01.StreamIsSmoothForce := by
  intro c ψ hψ
  have hC := sfd1_isCTest hψ
  have hE : UnforcedLeray.Short.PartIIa.IsCTest c (pdEta ψ) :=
    UnforcedLeray.Short.PartIIa.ctf_isCTest_fderiv hC (0, 0, 1)
  have hQ : UnforcedLeray.Short.PartIIa.IsCTest c (pdQ ψ) :=
    UnforcedLeray.Short.PartIIa.ctf_isCTest_fderiv hC (0, 1, 0)
  obtain ⟨s0, t1, L, hs0, hb1⟩ := hE.band
  obtain ⟨t0, u1, M, ht0, hb2⟩ := hQ.band
  have key : ∀ p : Profile, (p.1 < min s0 t0 ∨ max t1 u1 < p.1 ∨ max L M < |p.2.2|) →
      pdEta ψ p = 0 ∧ pdQ ψ p = 0 := by
    intro p hdisj
    constructor
    · by_contra h
      obtain ⟨ha, hb⟩ := hb1 p h
      obtain ⟨ha1, ha2⟩ := Set.mem_Icc.mp ha
      rcases hdisj with h' | h' | h'
      · linarith [min_le_left s0 t0]
      · linarith [le_max_left t1 u1]
      · linarith [le_max_left L M]
    · by_contra h
      obtain ⟨ha, hb⟩ := hb2 p h
      obtain ⟨ha1, ha2⟩ := Set.mem_Icc.mp ha
      rcases hdisj with h' | h' | h'
      · linarith [min_le_right s0 t0]
      · linarith [le_max_right t1 u1]
      · linarith [le_max_right L M]
  refine ⟨?_, ?_, min s0 t0, max t1 u1, max L M, lt_min hs0 ht0, fun p hdisj => ?_⟩
  · unfold StreamField
    exact sfd1_contDiff_mk hE.smooth hQ.smooth.neg
  · intro p
    unfold StreamField
    rw [hE.periodic p, hQ.periodic p]
  · obtain ⟨k1, k2⟩ := key p hdisj
    ext i
    fin_cases i <;> simp [StreamField, k1, k2]

end UnforcedLeray.Short.PartIIa.N01
