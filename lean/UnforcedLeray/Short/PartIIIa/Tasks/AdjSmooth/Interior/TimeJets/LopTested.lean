import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_7_2_1_1_6_7

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIIa

/-- **The classical adjoint equation, tested** (SP 3060-3061, 3052-3058), from
`LopTestedAux.adjLopTested_of`. -/
theorem adjLopTested (m : ℝ) : AdjLopTested m := LopTestedAux.adjLopTested_of m

end UnforcedLeray.Short.IIIa
