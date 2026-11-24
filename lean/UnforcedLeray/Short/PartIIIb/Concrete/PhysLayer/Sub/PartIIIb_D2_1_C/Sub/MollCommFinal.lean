import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.MollCommutatorLimitFullProof
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.MollCommLemmas.MollKernelAdj
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.MollCommLemmas.ShiftTestPhase
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.MollCommLemmas.ShiftPairUnfold
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.MollCommLemmas.ShiftTestOpEq
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.MollCommLemmas.TestKerSmooth
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.MollCommLemmas.MollIntegralSplit
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.MollCommLemmas.KernelIdentity
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.MollCommLemmas.NormedBumpSmooth
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.MollCommLemmas.FriedrichsBound
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.MollCommLemmas.CommTestLimit
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.MollCommLemmas.PhaseTestDense
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.MollCommLemmas.CommSub
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.MollCommLemmas.CommMeas

/-!
# `MollCommutatorLimitFull`: unconditional assembly

Source `the November 2 reference manuscript` lines 1556-1583.
The thirteen ingredient theorems (one per `Sub/MollCommLemmas/<Name>.lean`) are fed to the
assembly `mollCommutatorLimitFull_of` of `Sub/MollCommutatorLimitFullProof.lean`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The unconditional commutator limit under the full equation (source 1556-1583). -/
theorem mollCommutatorLimitFull : MollCommutatorLimitFull :=
  mollCommutatorLimitFull_of mollKernelAdj shiftTestPhase shiftPairUnfold shiftTestOpEq
    testKerSmooth mollIntegralSplit normedBumpSmooth friedrichsBound commTestLimit
    phaseTestDense commSub commMeas

end UnforcedLeray.Short.PartIIIb.Concrete
