import UnforcedLeray.Short.PartIIa.Sub.N02_5.Cond
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.ModeSplit.IntervalParamSmooth
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.ModeSplit.QCauchySchwarz
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.ModeSplit.SliceMono

set_option autoImplicit false

namespace UnforcedLeray.Short.PartIIa

theorem nearLerayModeSplit_proof : NearLerayModeSplit :=
  nearLerayModeSplit_of_leaves' intervalParamSmooth_proof avgQCauchySchwarz_proof avgSliceMono_proof

end UnforcedLeray.Short.PartIIa
