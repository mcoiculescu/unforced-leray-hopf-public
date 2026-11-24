import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream

set_option autoImplicit false

noncomputable section

open UnforcedLeray.Blueprint.Planar (PlanarData)

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The repair transition leaf (`margin 19γ/66`, source 5301-5372, 5607-5627). -/
theorem ageYRep (Pl : PlanarData) (σ₀ mZ dm dp : ℝ) : AgeTransRep Pl σ₀ mZ dm dp :=
  ageTransRep Pl σ₀ mZ dm dp

end UnforcedLeray.Short.PartIIIb.Concrete
end
