import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T20
import UnforcedLeray.Short.PartIIb.Tasks.LocalInteractionComparison.FlatKObsOpPackage
import UnforcedLeray.Short.PartIIb.Tasks.LocalInteractionComparison.RemainderBound

/-!
# Part II-b, Task `PartII-b:T20`: Local interaction comparison (`LocalInteractionComparison`)

Source of record: `the November 2 reference manuscript` (SP), lines 2006–2056
(`bg:local-interaction`).

All shared infrastructure, the refutation of the un-periodic statement
(`isKOut_zero_gε_nonper`, `localInteractionComparison_counterexample_at_zero`), the leaf
specifications `FlatKObsOpPackage` (`PartII-b:T20/1`) and `LocalInteractionRemainderBound`
(`PartII-b:T20/2`), the corrected target `LocalInteractionComparisonCorrected`, and the
conditional assembly `localInteractionComparisonCorrected_of` are proved in
`UnforcedLeray.Short.PartII-b.Sub.PartII-b_T20` with zero `sorry`.

Once `PartII-b:T20/org` updates `LocalInteractionComparison` in `Short/PartII-b/StatementsFree.lean`
to include `∃ ν₀ > 0, ... p.ν ≤ ν₀` and `InHr p.c bgp gε` (matching `LocalInteractionComparisonCorrected`),
and leaves `PartII-b:T20/1` (`flatKObsOpPackage_of`) and `PartII-b:T20/2`
(`localInteractionRemainderBound_of`) are proved, `localInteractionComparison_of` closes via
`localInteractionComparisonCorrected_of flatKObsOpPackage_of localInteractionRemainderBound_of h19`.
-/

set_option autoImplicit false
noncomputable section

namespace UnforcedLeray.Short.IIb

/-- Re-export of the conditional assembly of `LocalInteractionComparison` from
`FlatKObsOpPackage` (`PartII-b:T20/1`), `LocalInteractionRemainderBound` (`PartII-b:T20/2`),
and `LpFreeComparison` (`PartII-b:T19`). -/
theorem localInteractionComparison_of_leaves
    (hB : FlatKObsOpPackage) (hrem : LocalInteractionRemainderBound)
    (h19 : UnforcedLeray.Short.IIb.LpFreeComparison) :
    LocalInteractionComparison :=
  localInteractionComparisonCorrected_of hB hrem h19

theorem localInteractionComparison_of
    (h19 : UnforcedLeray.Short.IIb.LpFreeComparison) :
    UnforcedLeray.Short.IIb.LocalInteractionComparison :=
  localInteractionComparisonCorrected_of flatKObsOpPackage_of localInteractionRemainderBound_of h19

end UnforcedLeray.Short.IIb

end
