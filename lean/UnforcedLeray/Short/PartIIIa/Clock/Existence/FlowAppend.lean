import UnforcedLeray.Short.PartIIIa.Sub.T21_3_Strip

/-!
# Part III-a, `PartIII-a:T21/3/10`: concatenation of flows on consecutive windows

Source of record: `the November 2 reference manuscript`, the full forward train
estimate (existence of `U(s,t)`). Statement `FlowAppend` is in `Sub/T21_3.lean`.
The time integral splits at the junction `T` (`intervalIntegral.integral_add_adjacent_intervals`),
and the one-sided neighbourhoods `𝓝[Icc t T']` split at `T` into `𝓝[Icc t T]` and `𝓝[Icc T T']`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa.Exist

open UnforcedLeray.Short.IIIa

theorem flowAppend : FlowAppend := by
  unfold FlowAppend
  intro ν c m tr t T T' f ω u htT hTT' h1 h2
  exact
    { initial := h1.initial
      memX := fun s hs => by
        rcases le_total s T with hsT | hsT
        · exact h1.memX s ⟨hs.1, hsT⟩
        · exact h2.memX s ⟨hsT, hs.2⟩
      strongCont := fun s hs => by
        rcases lt_trichotomy s T with hlt | heq | hgt
        · have hmem : Icc t T ∈ 𝓝[Icc t T'] s :=
            mem_nhdsWithin.2 ⟨Iio T, isOpen_Iio, Set.mem_Iio.2 hlt,
              fun x hx => ⟨hx.2.1, (Set.mem_Iio.1 hx.1).le⟩⟩
          exact (h1.strongCont s ⟨hs.1, hlt.le⟩).mono_left (nhdsWithin_le_of_mem hmem)
        · rw [heq]
          rw [← Icc_union_Icc_eq_Icc htT hTT', nhdsWithin_union]
          exact Filter.tendsto_sup.2 ⟨h1.strongCont T ⟨htT, le_rfl⟩, h2.strongCont T ⟨le_rfl, hTT'⟩⟩
        · have hmem : Icc T T' ∈ 𝓝[Icc t T'] s :=
            mem_nhdsWithin.2 ⟨Ioi T, isOpen_Ioi, Set.mem_Ioi.2 hgt,
              fun x hx => ⟨(Set.mem_Ioi.1 hx.1).le, hx.2.2⟩⟩
          exact (h2.strongCont s ⟨hgt.le, hs.2⟩).mono_left (nhdsWithin_le_of_mem hmem)
      biotSavart := fun s hs => by
        rcases le_total s T with hsT | hsT
        · exact h1.biotSavart s ⟨hs.1, hsT⟩
        · exact h2.biotSavart s ⟨hsT, hs.2⟩
      integrable := fun φ hφ r hr => by
        rcases le_total r T with hrT | hrT
        · exact h1.integrable φ hφ r ⟨hr.1, hrT⟩
        · exact h2.integrable φ hφ r ⟨hrT, hr.2⟩
      timeIntegrable := fun φ hφ s hs => by
        rcases le_total s T with hsT | hsT
        · exact h1.timeIntegrable φ hφ s ⟨hs.1, hsT⟩
        · exact (h1.timeIntegrable φ hφ T ⟨htT, le_rfl⟩).trans
            (h2.timeIntegrable φ hφ s ⟨hsT, hs.2⟩)
      weak := fun φ hφ s hs => by
        rcases le_total s T with hsT | hsT
        · exact h1.weak φ hφ s ⟨hs.1, hsT⟩
        · have hA := h1.weak φ hφ T ⟨htT, le_rfl⟩
          have hB := h2.weak φ hφ s ⟨hsT, hs.2⟩
          have hI1 := h1.timeIntegrable φ hφ T ⟨htT, le_rfl⟩
          have hI2 := h2.timeIntegrable φ hφ s ⟨hsT, hs.2⟩
          rw [hB, hA, add_assoc, intervalIntegral.integral_add_adjacent_intervals hI1 hI2] }

end UnforcedLeray.Short.IIIa.Exist
