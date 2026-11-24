import UnforcedLeray.Short.PartIIa.Sub.N02_2
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.StreamMember.CTestFderiv
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.StreamMember.CTestAlgebra
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.StreamMember.CTestOpK
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.GradMember

/-!
# `StreamMemLp`: the stream field is in `L²` (task `PartII-a:N02/2/18`)

Proves `StreamMemLp` (`Sub/N02_2.lean`) exactly as defined there: for every `ε, c` and every
complex band test `ψ`, `streamC ε ψ ∈ L²(measureH c)`.

Source of record: `the November 2 reference manuscript`, lines 1730-1732.

The two components of `streamC ε ψ` are `-∂_η ψ` (band test by `CTestFderiv`) and
`∂_q ψ - ε K ψ + ε ψ` (band test by `CTestFderiv`, `CTestOpK`, `CTestAlgebra`). Each is continuous,
and the union of their bands is a band for the whole field, so `NearGradMemberAux.memLp_of_band`
applies.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff InnerProductSpace

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0226

/-- **Target `PartII-a:N02/2/18`**: the stream field `streamC ε ψ` of a complex band test `ψ`
is in `L²(measureH c)`. -/
theorem streamMemLp : UnforcedLeray.Short.PartIIa.StreamMemLp := by
  intro ε c ψ hψ
  -- Band tests: `∂_η ψ`, `∂_q ψ`, `K ψ`, and the algebra for the second component.
  have hPdEta : IsCTest c (pdEta ψ) := cTestFderiv c ψ hψ (0, 0, 1)
  have hPdQ : IsCTest c (pdQ ψ) := cTestFderiv c ψ hψ (0, 1, 0)
  have hOpK : IsCTest c (opK ψ) := cTestOpK c ψ hψ
  have hεOpK : IsCTest c (fun p => (ε : ℂ) * opK ψ p) :=
    cTestAlgebra.2.2.2 c (opK ψ) (fun _ => (ε : ℂ)) hOpK contDiff_const (fun _ => rfl)
  have hεψ : IsCTest c (fun p => (ε : ℂ) * ψ p) :=
    cTestAlgebra.2.2.2 c ψ (fun _ => (ε : ℂ)) hψ contDiff_const (fun _ => rfl)
  have hA : IsCTest c (fun p => pdQ ψ p - (ε : ℂ) * opK ψ p) :=
    cTestAlgebra.2.2.1 c (pdQ ψ) (fun p => (ε : ℂ) * opK ψ p) hPdQ hεOpK
  have hF2 : IsCTest c (fun p => pdQ ψ p - (ε : ℂ) * opK ψ p + (ε : ℂ) * ψ p) :=
    cTestAlgebra.2.1 c (fun p => pdQ ψ p - (ε : ℂ) * opK ψ p) (fun p => (ε : ℂ) * ψ p) hA hεψ
  -- Continuity of the stream field.
  have hf : Continuous (streamC ε ψ) := by
    unfold streamC
    exact NearGradMemberAux.continuous_mk hPdEta.smooth.continuous.neg hF2.smooth.continuous
  -- Bands of the two components and their union.
  obtain ⟨s0, s1, L, hs0, hb1⟩ := hPdEta.band
  obtain ⟨t0, t1, M, ht0, hb2⟩ := hF2.band
  refine NearGradMemberAux.memLp_of_band (c := c) (s0 := min s0 t0) (s1 := max s1 t1)
    (L := max L M) hf (lt_min hs0 ht0) ?_
  intro p hp
  have h1 : pdEta ψ p = 0 := by
    by_contra h
    obtain ⟨ha, hb⟩ := hb1 p h
    obtain ⟨ha1, ha2⟩ := Set.mem_Icc.mp ha
    apply hp
    exact ⟨Set.mem_Icc.mpr ⟨le_trans (min_le_left s0 t0) ha1, le_trans ha2 (le_max_left s1 t1)⟩,
      le_trans hb (le_max_left L M)⟩
  have h2 : pdQ ψ p - (ε : ℂ) * opK ψ p + (ε : ℂ) * ψ p = 0 := by
    by_contra h
    obtain ⟨ha, hb⟩ := hb2 p h
    obtain ⟨ha1, ha2⟩ := Set.mem_Icc.mp ha
    apply hp
    exact ⟨Set.mem_Icc.mpr ⟨le_trans (min_le_right s0 t0) ha1, le_trans ha2 (le_max_right s1 t1)⟩,
      le_trans hb (le_max_right L M)⟩
  ext i
  fin_cases i <;> simp [streamC, h1, h2]

end UnforcedLeray.Short.PartIIa
