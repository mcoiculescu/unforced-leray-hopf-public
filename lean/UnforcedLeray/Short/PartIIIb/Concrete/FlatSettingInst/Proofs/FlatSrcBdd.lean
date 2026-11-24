import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_data_2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_data_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_data_1.GaussPointBound
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_data_1.GaussMeasurable
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_data_1.PeriodizePointBound
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_data_1.WeightedL2Gauss
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_data_1.PeriodizeMeas

/-!


Source `the November 2 reference manuscript` lines 4565-4574. Glue only: the compiled
`flatSrcBdd_of` applied to the leaves `gaussPointBound`, `gaussMeasurable` and the periodization
bound `periodizeL2Bound_of` assembled from `periodizePointBound`, `weightedL2Gauss`, `periodizeMeas`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

theorem flatSrcBdd : FlatSrcBdd :=
  flatSrcBdd_of gaussPointBound gaussMeasurable
    (periodizeL2Bound_of periodizePointBound weightedL2Gauss periodizeMeas)

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
