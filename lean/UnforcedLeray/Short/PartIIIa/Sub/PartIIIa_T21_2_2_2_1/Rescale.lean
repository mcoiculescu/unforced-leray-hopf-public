import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_2_1_3
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_2_1_3.RescaleMemLp
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_2_1_3.RescaleTest
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_2_1_3.RescaleKernelL2
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_2_1_3.RescaleKernelDiv
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_2_1_3.RescaleKernelCurl
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_2_1_3.RescaleLHS
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_2_1_3.RescaleRHS

/-!
# Part III-a, `PartIII-a:T21/2/2/2/1`: `InteractionRescale` from the seven leaf theorems

`interactionRescale_of` (Sub/PartIII-a_T21_2_2_2_1_3.lean) applied to the seven proved leaves
(SP lines 2875-2896, 3052-3058).
-/

set_option autoImplicit false

noncomputable section

theorem interactionRescale : UnforcedLeray.Short.IIIa.E0.InteractionRescale :=
  UnforcedLeray.Short.IIIa.E0.interactionRescale_of
    rescaleMemLp rescaleTest rescaleKernelL2 rescaleKernelDiv
    UnforcedLeray.Short.IIIa.E0.rescaleKernelCurl
    UnforcedLeray.Short.IIIa.E0.rescaleLHS
    UnforcedLeray.Short.IIIa.E0.rescaleRHS
