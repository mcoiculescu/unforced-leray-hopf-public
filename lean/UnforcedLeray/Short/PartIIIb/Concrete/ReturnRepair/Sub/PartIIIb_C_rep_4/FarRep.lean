import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.LateEarlyLeaf

set_option autoImplicit false

noncomputable section

open UnforcedLeray.Blueprint.Planar (PlanarData)

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The repair far leaf (`margin 19γ/66`, source 5301-5372, 5607-5627). -/
theorem ageFarRep (Pl : PlanarData) (σ₀ mZ dm dp : ℝ) : AgeLateEarlyRep Pl σ₀ mZ dm dp :=
  ageLateEarlyRep Pl σ₀ mZ dm dp

end UnforcedLeray.Short.PartIIIb.Concrete
end
