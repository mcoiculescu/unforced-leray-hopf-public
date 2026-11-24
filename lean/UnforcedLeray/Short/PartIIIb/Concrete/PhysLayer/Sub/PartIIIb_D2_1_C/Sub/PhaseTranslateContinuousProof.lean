import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_2_3_2
import UnforcedLeray.Short.PartIIIb.Sub.PhaseTrans.LocalL2
import UnforcedLeray.Short.PartIIIb.Sub.PhaseTrans.CcTranslate
import UnforcedLeray.Short.PartIIIb.Sub.PhaseTrans.CcDensity
import UnforcedLeray.Short.PartIIIb.Sub.PhaseTrans.CellShift

/-!
# `PhaseTranslateContinuous`: assembly

Source `the November 2 reference manuscript`
lines 1556-1583. The four hypotheses of `phaseTranslateContinuous_of` are discharged by the
lemmas `phaseLocalL2`, `ccTranslateL2`, `ccDensityBox`, `phaseCellShift`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem phaseTranslateContinuous : PhaseTranslateContinuous :=
  phaseTranslateContinuous_of phaseLocalL2 ccTranslateL2 ccDensityBox phaseCellShift

end UnforcedLeray.Short.PartIIIb.Concrete
