import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_kflat_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_kflat_1_1
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.FrakTInt

/-!
# `PartIII-b:C/asrc/kflat/1`: `frakTOldFinite`

Assembles `frakTOldFinite` from `frakTOldFinite_of`, `frakTMeas`, and `frakTInt`.
-/

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem frakTOldFinite (as : ℝ) (χf : ℝ → ℝ) (m : ℝ) [Fact (1 < m)] : FrakTOldFinite as χf m :=
  frakTOldFinite_of as χf m (frakTMeas as χf m) (frakTInt as χf m)

end UnforcedLeray.Short.PartIIIb.Concrete
