import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T10_7_1_2_2
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.GradWeak.CTPair.CTUnfold
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.GradWeak.CTPair.FrameDot
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.GradWeak.CTPair.PhaseChartBochner
import UnforcedLeray.Short.PartIIb.Tasks.FlatUnique.CellStream.HrBox

/-!
# `PartII-b:T10/7/1/2/2` (`CTPair`): assembly

Source of record: `the November 2 reference manuscript` lines 1639-1668, 1902-1921.
The statement `CTPair` is discharged by `ct_pair_of` from the four chart facts
`ct_frame_dot`, `phase_chart_bochner`, `ct_unfold` and `hrBoxIntegrable`.
-/

set_option autoImplicit false

theorem ct_pair : UnforcedLeray.Short.IIb.CTPair :=
  UnforcedLeray.Short.IIb.ct_pair_of ct_frame_dot UnforcedLeray.Short.IIb.phase_chart_bochner ct_unfold
    UnforcedLeray.Short.IIb.hrBoxIntegrable

#print axioms ct_pair
