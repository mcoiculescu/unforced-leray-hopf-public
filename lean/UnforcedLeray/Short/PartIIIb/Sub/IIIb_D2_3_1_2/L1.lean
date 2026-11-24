import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_2

/-!
# `oldPhysPeriodic` (PartIII-b:IIIb-D2/3/1/2/1)

Source of record: `the November 2 reference manuscript` 2666-2683.
`chartOf R c z (τ + 2c/R)` shifts the cell variable `q` by one period `c`, so the
chart tensor, and hence `cartLift`, is unchanged.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem oldPhysPeriodic : OldPhysPeriodic := by
  intro R c g τ z
  by_cases hR : R = 0
  · subst hR; simp [oldPhys]
  by_cases hc : c = 0
  · subst hc; simp [oldPhys]
  have e1 : R * Real.log (NearInst.hRad z / R) + R * (τ + 2 * c / R) / 2 =
      (R * Real.log (NearInst.hRad z / R) + R * τ / 2) + c := by
    field_simp
    ring
  have hfl : ∀ x : ℝ, ⌊(x + c) / c + 1 / 2⌋ = ⌊x / c + 1 / 2⌋ + 1 := by
    intro x
    have h : (x + c) / c + 1 / 2 = x / c + 1 / 2 + 1 := by
      rw [add_div, div_self hc]; ring
    rw [h, Int.floor_add_one]
  have key : NearInst.chartOf R c z (τ + 2 * c / R) = NearInst.chartOf R c z τ := by
    unfold NearInst.chartOf
    rw [e1, hfl]
    refine Prod.ext rfl (Prod.ext ?_ rfl)
    push_cast
    ring
  simp only [oldPhys, NearInst.cartLift]
  rw [key]

end UnforcedLeray.Short.PartIIIb.Concrete
