import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_data_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_data_1.GaussPointBound
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_data_1.GaussMeasurable
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_data_1.PeriodizePointBound
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_data_1.PeriodizeMeas
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_data_1.WeightedL2Gauss
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_data_1.PeriodizeIntegral
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_data_1.PlaneIntegrable
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_data_1.PlaneZero
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_data_1.GaussSrcContinuous_of

/-!


Source `the November 2 reference manuscript`
lines 4562-4570 and 4565. Glue only: the Gaussian profiles are bounded, measurable, integrable
with zero plane integral, their periodizations are weighted-`L²` on the cell with zero circulation,
and depend continuously on the age; `gaussSourcesExist_of` assembles these leaves.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ComplexConjugate

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

/-- **`GaussSourcesExist`** (source 4562-4570): the glue of the leaf theorems. -/
theorem gaussSourcesExist : GaussSourcesExist :=
  gaussSourcesExist_of gaussPointBound gaussMeasurable
    (periodizeL2Bound_of periodizePointBound weightedL2Gauss periodizeMeas)
    periodizeIntegral planeIntegrable planeZero gaussSrcContinuous_of

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
