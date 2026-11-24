import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.FarThin
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YThin
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.FarRep
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRep

/-!
# `PartIII-b:C/rep/4`: `repair:age-error`

Source `the November 2 reference manuscript`
lines 5301-5372, 5607-5627, 5687-5689.
-/

set_option autoImplicit false

noncomputable section

open UnforcedLeray.Blueprint.Planar (PlanarData)

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem ageError (Pl : PlanarData) (σ₀ mZ dm dp : ℝ) : ∃ k₀ : ℕ, ∀ D : SeqData, D.Pl = Pl → D.σ₀ = σ₀ → D.K.mZ = mZ → D.RepairStanding dm dp → D.AgeError ((k₀ : ℝ) * D.K.b * (gRate D.Pl / 3)) :=
  ageError_of Pl σ₀ mZ dm dp (ageLateEarlyThin Pl σ₀ mZ dm dp) (ageYThin Pl σ₀ mZ dm dp)
    (ageFarRep Pl σ₀ mZ dm dp) (ageYRep Pl σ₀ mZ dm dp)

end UnforcedLeray.Short.PartIIIb.Concrete
