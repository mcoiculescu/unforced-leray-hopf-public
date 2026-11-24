import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_3_1_5
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.ProductRule.Test
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.ProductRule.Weak
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.ProductRule.GCont
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.ProductRule.KCont
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.ProductRule.PairCont
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.ProductRule.Deriv

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIIa

/-- **Leaf assembly** (SP 3074-3075): the product rule for the cut pairing, assembled from the
six proved leaves. -/
theorem ladProductRule : LadProductRule :=
  ladProductRule_of ladPRTest ladPRWeak ladPRG ladPRK ladPRPair ladPRDeriv

end UnforcedLeray.Short.IIIa
