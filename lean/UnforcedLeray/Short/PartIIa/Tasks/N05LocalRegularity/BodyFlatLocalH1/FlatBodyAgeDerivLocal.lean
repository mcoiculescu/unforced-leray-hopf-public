import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N05_2_2
import UnforcedLeray.Short.PartIIa.Tasks.N05LocalRegularity.BodyFlatLocalH1.FlatBodyAgeDerivLocal.FlatBodyCutLaplacianLocal

/-!
# `FlatBodyAgeDerivLocal` (`PartII-a:N05/2/2`)

Source of record: `the November 2 reference manuscript`,
lines 1794-1799.

All proved infrastructure (`cellMeasure_ac_measureH`, `sMul` / `dsFromS_sMul`,
`cellL2Norm_flatCutAgeExplicitPart_T0flat_le`, `flatCutAgeExplicitPart_ibp_s_eq`) and the
conditional assembly `flatBodyAgeDerivLocal_of` from `FlatBodyCutLaplacianLocal`
(`PartII-a:N05/2/2/1`) are in `UnforcedLeray.Short.«PartII-a».Sub.«PartII-a_N05_2_2»`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIa

theorem flatBodyAgeDerivLocal : UnforcedLeray.Short.PartIIa.FlatBodyAgeDerivLocal :=
  flatBodyAgeDerivLocal_of flatBodyCutLaplacianLocal

end UnforcedLeray.Short.PartIIa
