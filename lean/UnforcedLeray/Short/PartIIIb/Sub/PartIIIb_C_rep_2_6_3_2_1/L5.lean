import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_6_3_2_1_5
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_6_3_2_1_5.L1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_6_3_2_1_5.L2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_6_3_2_1_5.L3
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_6_3_2_1_5.L4
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_6_3_2_1_5.L5
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_6_3_2_1_5.L6
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_6_3_2_1_5.L7
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_6_3_2_1_5.L8
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_6_3_2_1_5.L9

/-!
# `extIntKdLipschitz` (`PartIII-b:C/rep/2/6/3/2/1/5`)

Source `shorter-proof-2026-11-02.tex` lines 3603-3626, 3800-3807, 4171-4200.

Composition of the nine lemma files `L1`..`L9` of `Sub/PartIII-b_C_rep_2_6_3_2_1_5/` through the
reduction theorem `extIntKdLipschitz_of`. The hypotheses of `extIntKdLipschitz_of` are supplied in
its order: `sepGapPointwiseUnif` (L1), `kdHasDerivAt` (L2), `lkerSumEq` (L3), `lOpBound` (L4),
`sepMajorantMono` (L5), `gkerMajShiftLe` (L6), `gkerMajIntegrable` (L7),
`gkerMajShiftIntegrable` (L8), `lipOffPoint` (L9).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem extIntKdLipschitz : ExtIntKdLipschitz :=
  extIntKdLipschitz_of sepGapPointwiseUnif kdHasDerivAt lkerSumEq lOpBound sepMajorantMono
    gkerMajShiftLe gkerMajIntegrable gkerMajShiftIntegrable lipOffPoint

end UnforcedLeray.Short.PartIIIb.Concrete
