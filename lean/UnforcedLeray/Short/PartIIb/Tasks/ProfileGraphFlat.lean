import UnforcedLeray.Short.PartIIb.StatementsFree
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T13
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Core
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Sub
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.ClassSub
import UnforcedLeray.Short.PartIIb.Tasks.FlatUnique

/-!
# Part II-b, task `PartII-b:T14` (`ProfileGraphFlat`): assembly

Source of record: `the November 2 reference manuscript` (SP) lines 1923-1938.
Existence with the graph bound (`flatGraphExists`, T12/T13) and uniqueness in the flat class
(`flat_unique` with the linearity leaves `flatResponseSub`, `flatClassSub`, T11).
The constant is `max C 1`, so that `0 < C`; `GraphBound` is monotone in `C`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

theorem profileGraphFlat_proof : UnforcedLeray.Short.IIb.ProfileGraphFlat := by
  intro r hr hr3 μ ha
  obtain ⟨C, hC⟩ := flatGraphExists r hr hr3 μ ha
  refine ⟨max C 1, lt_max_of_lt_right one_pos, fun ν c hν hc F hF => ?_⟩
  obtain ⟨b, hbF, hb, hg⟩ := hC ν c hν hc F hF
  refine ⟨b, hb, hbF, ?_, ?_⟩
  · obtain ⟨Sb, Qb, Eb, h1, h2, h3, hn⟩ := hg
    have hle : ENNReal.ofReal C ≤ ENNReal.ofReal (max C 1) :=
      ENNReal.ofReal_le_ofReal (le_max_left C 1)
    exact ⟨Sb, Qb, Eb, h1, h2, h3, hn.trans (by gcongr)⟩
  · intro b' hb' hbF'
    have h0 : b' - b =ᵐ[hMeas c r] 0 :=
      flat_unique hc hν hr hr3 ha (b' - b) (flatClassSub c r b' b hb' hb)
        (flatResponseSub ν μ F b' b hbF' hbF)
    filter_upwards [h0] with x hx
    exact sub_eq_zero.mp hx

end UnforcedLeray.Short.IIb

end
