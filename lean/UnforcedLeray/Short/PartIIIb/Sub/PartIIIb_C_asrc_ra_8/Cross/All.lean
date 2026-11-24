import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_8.Cross.Of
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_8.Cross.Sum
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_8.Cross.CellL2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_8.Cross.Cont
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_8.Cross.Separated

/-!
# `PartIII-b:C/asrc/ra/8/2/org` : the assembled cross-center bound

Source `the November 2 reference manuscript`
5026-5031, 4371.  `rCrossBound_of` (`Cross/Of.lean`) with the double-sum bound
(`rcCrossPointwise_of rcPairSeparated`), the cell-norm step (`rcCellGaussL2`) and continuity
(`rcCrossContinuous_of rcPairSeparated`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem rcCrossBound_assembled (as : ℝ) (χf : ℝ → ℝ) : RCrossBound as χf :=
  rCrossBound_of as χf (rcCrossPointwise_of rcPairSeparated) rcCellGaussL2
    (rcCrossContinuous_of rcPairSeparated)

end UnforcedLeray.Short.PartIIIb.Concrete
