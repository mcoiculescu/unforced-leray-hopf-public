import UnforcedLeray.Short.PartIIa.Sub.N02_2
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.StreamMember.Identity

/-!


Source of record: `the November 2 reference manuscript`, lines 1730-1732.
Target: `CTestFderiv` (`Sub/N02_2.lean`): for every `c`, every complex band test `F` and every
direction `v`, the function `p ↦ fderiv ℝ F p v` is again a complex band test.

Helpers (prefix `ctf`): the `c`-periodicity of `fderiv` (copy of `B0226.fderiv_qPeriodic` for
`ℂ`-valued `F`) and the closed-band inclusion of `tsupport` (copy of `B0226.tsupport_subset_band`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff InnerProductSpace

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0226

/-- The `q`-shift invariance of the derivative: `fderiv` of a `c`-periodic `ℂ`-valued profile
is `c`-periodic. -/
theorem ctf_fderiv_periodic {c : ℝ} {F : Profile → ℂ}
    (h : ∀ x : Profile, F (x.1, x.2.1 + c, x.2.2) = F x) (p : Profile) :
    fderiv ℝ F (p.1, p.2.1 + c, p.2.2) = fderiv ℝ F p := by
  have ha : ((p.1, p.2.1 + c, p.2.2) : Profile) = p + ((0 : ℝ), c, (0 : ℝ)) := by
    obtain ⟨s, q, η⟩ := p
    simp [add_comm]
  have hf : (fun x : Profile => F (x + ((0 : ℝ), c, (0 : ℝ)))) = F := by
    funext x
    obtain ⟨s, q, η⟩ := x
    have := h (s, q, η)
    simpa using this
  rw [ha, ← fderiv_comp_add_right, hf]

/-- A complex band test vanishes outside its closed band, so its support lies in the band. -/
theorem ctf_tsupport_subset {F : Profile → ℂ} {s0 s1 L : ℝ}
    (h : ∀ p : Profile, F p ≠ 0 → p.1 ∈ Icc s0 s1 ∧ |p.2.2| ≤ L) :
    tsupport F ⊆ {p : Profile | p.1 ∈ Icc s0 s1 ∧ |p.2.2| ≤ L} :=
  closure_minimal (fun p hp => h p hp)
    ((isClosed_Icc.preimage continuous_fst).inter
      (isClosed_le (continuous_abs.comp (continuous_snd.comp continuous_snd)) continuous_const))

/-- The directional derivative `p ↦ fderiv ℝ F p v` of a complex band test is a complex band
test. -/
theorem ctf_isCTest_fderiv {c : ℝ} {F : Profile → ℂ} (hF : IsCTest c F) (v : Profile) :
    IsCTest c (fun p => fderiv ℝ F p v) where
  smooth := NearStreamMemberAux.contDiff_fderiv_apply hF.smooth v
  periodic := by
    intro p
    show fderiv ℝ F (p.1, p.2.1 + c, p.2.2) v = fderiv ℝ F p v
    rw [ctf_fderiv_periodic hF.periodic p]
  band := by
    obtain ⟨s0, s1, L, hs0, hband⟩ := hF.band
    refine ⟨s0, s1, L, hs0, fun p hp => ?_⟩
    by_contra hpB
    have hnot : p ∉ tsupport F := fun hmem => hpB (ctf_tsupport_subset hband hmem)
    have h0 : fderiv ℝ F p = 0 := fderiv_of_notMem_tsupport ℝ hnot
    exact hp (by simp [h0])

/-- **Target `PartII-a:N02/2/1`**: `CTestFderiv`, the directional derivatives of complex band tests
are complex band tests. -/
theorem cTestFderiv : UnforcedLeray.Short.PartIIa.CTestFderiv :=
  fun _ _ hF v => ctf_isCTest_fderiv hF v

end UnforcedLeray.Short.PartIIa
