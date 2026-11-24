import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_dec
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2

/-!
# `PartIII-b:C/rep/5`: `ageVelocity`

Source `the November 2 reference manuscript` lines 5569-5605, 5618-5619.
-/

set_option autoImplicit false

noncomputable section

open UnforcedLeray.Blueprint.Planar (PlanarData)

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem ageVelocity (Pl : PlanarData) (σ₀ mZ dm dp : ℝ) : ∃ k₀ : ℕ, ∀ D : SeqData, D.Pl = Pl → D.σ₀ = σ₀ → D.K.mZ = mZ → D.RepairStanding dm dp → D.AgeVelocity ((k₀ : ℝ) * D.K.b * (gRate D.Pl / 3)) :=
  ageVelocity_of Pl σ₀ mZ dm dp (ageVelThin Pl σ₀ mZ dm dp) (ageVelRep Pl σ₀ mZ dm dp)

end UnforcedLeray.Short.PartIIIb.Concrete

end
