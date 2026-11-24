import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_2_6
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_2_6.HLS
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_2_6.SliceL2
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_2_6.WeakGrad

/-!
# `BSSlice` from its three slice facts

Source `the November 2 reference manuscript` lines 1351-1362 (stream potential of
the solenoidal cutoff, `L² * |w|⁻² → L⁶`) and 1334-1337 (`Y_r`).

`bsSlice_of` reduces `BSSlice` to the three slice facts `BSHLSSlice` (`bsHLSSlice`),
`PhaseSliceL2` (`phaseSliceL2`) and `PhaseSliceWeakGrad` (`phaseSliceWeakGrad`), each proved in
its own module.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb

open Concrete in
/-- **BSSlice** (source 1351-1362): the slice facts of the Biot-Savart potential hold.
(Declared in `PartIIIb`, not `PartIIIb.Concrete`, because `Concrete.bsSlice` is already the
slice map of the Fubini development.) -/
theorem bsSlice : Concrete.BSSlice :=
  Concrete.bsSlice_of Concrete.bsHLSSlice Concrete.phaseSliceL2 Concrete.phaseSliceWeakGrad

end UnforcedLeray.Short.PartIIIb
