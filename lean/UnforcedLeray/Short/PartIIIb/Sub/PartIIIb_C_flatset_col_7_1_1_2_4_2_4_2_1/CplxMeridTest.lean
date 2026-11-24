import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_4_2_1.FlatLerayDefs

/-!
# Part III-b, task `PartIII-b:C/flatset/col/7/1/1/2/4/2/4/2/1/1/2` (`cplxMeridTest`)

Source of record `the November 2 reference manuscript`, lines 1684-1689: the
complexification of a smooth `c`-periodic band field is a smooth band test.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.FlatLeray

open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.Short.PartIIa

theorem cplxMeridTest : CplxMeridTest := by
  intro c F hF hper hband
  refine ⟨?_, ?_, ?_⟩
  · unfold cplxField
    exact (contDiff_piLp 2).2 (fun i => Complex.ofRealCLM.contDiff.comp (hF i))
  · intro p
    simp only [cplxField, hper p.1 p.2.1 p.2.2]
  · obtain ⟨s0, s1, L, h0, hb⟩ := hband
    refine ⟨s0, s1, L, h0, fun p hp => hb p (fun hF0 => hp ?_)⟩
    ext i
    simp [cplxField, hF0]

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.FlatLeray
