import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_3_2_11_2_2_2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_3_2_11_2_2_2.ParamTop
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_3_2_11_2_2_2.HeatKTop
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_3_2_11_2_2_2.MeasTop
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_3_2_11_2_2_2.GapTop
import UnforcedLeray.Short.PartIIIa.T15_SepKernelBounds

/-!
# `SepWSmoothTop` (`PartIII-b:IIIb-D2/3/2/11/2/2/2`, source 3604-3621)

Source of record: `the November 2 reference manuscript`
lines 3604-3621.  Discharges the all-order smoothness source fact `SepWSmoothTop` by
`sepWSmoothTop_of` applied to the four proved lemma files (`paramContDiffTop`,
`heatLerayKSmoothTop`, `sepPhiMeasurableTop`, `sepGapPointwiseTop`) and the proved
`IIIa.sepKernelBounds`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- `SepWSmoothTop` holds: all four source facts are proved, and `IIIa.sepKernelBounds` supplies
the kernel bounds. -/
theorem sepWSmoothTop_proved : SepWSmoothTop :=
  sepWSmoothTop_of IIIa.sepKernelBounds paramContDiffTop heatLerayKSmoothTop sepPhiMeasurableTop
    sepGapPointwiseTop

end UnforcedLeray.Short.PartIIIb.Concrete
