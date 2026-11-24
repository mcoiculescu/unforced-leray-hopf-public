import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_1_3
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Dense
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.PairCont
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Conj
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.SelfPair

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem fwuHomog : FWUHomog :=
  fwuHomog_of fwuDense fwuPairCont fwuConj fwuSelfPair

end UnforcedLeray.Short.PartIIIb.Concrete
