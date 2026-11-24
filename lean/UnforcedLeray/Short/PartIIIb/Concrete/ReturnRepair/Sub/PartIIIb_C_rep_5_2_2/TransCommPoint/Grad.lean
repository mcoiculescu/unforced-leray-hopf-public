import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_2_2_11_4
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_2.TransCommPoint.GradX0Struct
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_2.TransCommPoint.GradX0Decay

/-!
# `tcGrad` (`PartIII-b:C/rep/5/2/2/11/4`)

Source of record: `the November 2 reference manuscript` 3603-3647, 4171-4192.
The commutator identity `TCGrad` follows from the structure of `X₀` (`tcGradX0Struct`) and its
decay (`tcGradX0Decay`) through the generic calculus lemma `tcGrad_of_parts`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem tcGrad : TCGrad :=
  tcGrad_of_parts tcGradX0Struct tcGradX0Decay

end UnforcedLeray.Short.PartIIIb.Concrete
