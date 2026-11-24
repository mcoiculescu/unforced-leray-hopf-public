import UnforcedLeray.Short.PartIIIa.Sub.T21_3_Strip

/-!
# Part III-a, `PartIII-a:T21/3/12`: passage from windows `[t, t + N + 1]` to `[t, ∞)`

Source of record: `the November 2 reference manuscript`, the flow-on-windows
concatenation step of the full forward train estimate (`T21/3/12`, statement `FlowGlobal` in
`Sub/T21_3.lean`).

Every `s ≥ t` lies in the interior of some window `[t, t + (N + 1)]`, so the fields of
`IsLinearisedFlow` are read off from the window flows.  For the strong continuity, the one-sided
neighbourhoods `𝓝[Ici t] s` and `𝓝[Icc t T] s` agree when `s < T`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology

namespace UnforcedLeray.Short.IIIa.Exist

open UnforcedLeray.Short.IIIa
open UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution

/-- **Passage to `[t, ∞)`** (`T21/3/12`). -/
theorem flowGlobal : UnforcedLeray.Short.IIIa.Exist.FlowGlobal := by
  intro ν c m tr t f ω u h
  have hwin : ∀ s : ℝ, t ≤ s → ∃ N : ℕ, s < t + ((N + 1 : ℕ) : ℝ) := by
    intro s _
    obtain ⟨N, hN⟩ := exists_nat_gt (s - t)
    exact ⟨N, by push_cast; linarith⟩
  have hnhds : ∀ s T : ℝ, s < T → 𝓝[Ici t] s = 𝓝[Icc t T] s := by
    intro s T hsT
    have hI : Iio T ∈ 𝓝 s := Iio_mem_nhds hsT
    rw [nhdsWithin_restrict' (Ici t) hI, nhdsWithin_restrict' (Icc t T) hI]
    congr 1
    ext x
    simp only [mem_inter_iff, mem_Ici, mem_Iio, mem_Icc]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h1, h2.le⟩, h2⟩
    · rintro ⟨⟨h1, _⟩, h2⟩
      exact ⟨h1, h2⟩
  refine ⟨(h 0).initial, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s hs
    obtain ⟨N, hN⟩ := hwin s hs
    exact (h N).memX s ⟨hs, hN.le⟩
  · intro s hs
    obtain ⟨N, hN⟩ := hwin s hs
    have hc := (h N).strongCont s ⟨hs, hN.le⟩
    rw [hnhds s _ hN]
    exact hc
  · intro s hs
    obtain ⟨N, hN⟩ := hwin s hs
    exact (h N).biotSavart s ⟨hs, hN.le⟩
  · intro φ hφ r hr
    obtain ⟨N, hN⟩ := hwin r hr
    exact (h N).integrable φ hφ r ⟨hr, hN.le⟩
  · intro φ hφ s hs
    obtain ⟨N, hN⟩ := hwin s hs
    exact (h N).timeIntegrable φ hφ s ⟨hs, hN.le⟩
  · intro φ hφ s hs
    obtain ⟨N, hN⟩ := hwin s hs
    exact (h N).weak φ hφ s ⟨hs, hN.le⟩

end UnforcedLeray.Short.IIIa.Exist
