import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N01_6

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa.N01

open UnforcedLeray.Short.PartIIIb.NearInst (tv4 cartLift nsSym symRZ cylFrame chartOf hRad)

/-- `PartII-a:N01/6/1` pointwise Frobenius identity of the lift (source 1644-1648, 2683). -/
theorem slabFrobPointwise : UnforcedLeray.Short.PartIIa.N01.SlabFrobPointwise := by
  intro R c m τ z
  unfold frob2
  by_cases hz : hRad z = 0
  · have h0 : (chartOf R c z τ).1 = 0 := by
      simp [chartOf, hz]
    simp [cartLift, h0]
  · have hh2 : hRad z ^ 2 = z 0 ^ 2 + z 1 ^ 2 := by
      unfold hRad
      exact Real.sq_sqrt (by positivity)
    have huv : (z 0 / hRad z) ^ 2 + (z 1 / hRad z) ^ 2 = 1 := by
      rw [div_pow, div_pow, ← add_div, ← hh2, div_self (pow_ne_zero 2 hz)]
    unfold cartLift
    simp [Fin.sum_univ_three, Matrix.mul_apply, cylFrame, nsSym]
    linear_combination ((chartOf R c z τ).1 ^ 2) * ((((z 0 / hRad z) ^ 2 + (z 1 / hRad z) ^ 2) + 1) *
      (m (chartOf R c z τ) (0, 0) ^ 2 + m (chartOf R c z τ) (1, 1) ^ 2) +
      2 * (symRZ (m (chartOf R c z τ))) ^ 2) * huv

end UnforcedLeray.Short.PartIIa.N01
