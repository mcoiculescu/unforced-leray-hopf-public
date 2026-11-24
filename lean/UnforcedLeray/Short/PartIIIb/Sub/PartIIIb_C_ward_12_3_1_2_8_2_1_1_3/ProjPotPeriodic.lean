import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_8_2_1_1_3

set_option autoImplicit false

noncomputable section

open UnforcedLeray.Cons.C03.Concrete

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem projPotPeriodic : ProjPotPeriodic := by
  intro P _ Φ hΦ τ y
  show ((projectedPotentialRePath Φ (τ + P, y) : ℂ) + Complex.I * (projectedPotentialImPath Φ (τ + P, y) : ℂ))
    = ((projectedPotentialRePath Φ (τ, y) : ℂ) + Complex.I * (projectedPotentialImPath Φ (τ, y) : ℂ))
  rw [projectedPotentialRePath_periodic hΦ τ y, projectedPotentialImPath_periodic hΦ τ y]

end UnforcedLeray.Short.PartIIIb.Concrete
