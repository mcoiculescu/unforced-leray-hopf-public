import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_masked_22_2

/-!
# `PartIII-b:C/near/masked/22/2/3`: rotation covariance of the Cartesian lift (source 4000-4003)

Source of record: `the November 2 reference manuscript`, lines 4000-4003.

`hRad` and `chartOf` are invariant under the vertical-axis rotation `rotM co si` (`co² + si² = 1`),
and `cylFrame (Rz) = rotM co si * cylFrame z` (entrywise, using `sub_div` and `mul_div_assoc`,
which hold for division by zero). Associativity then gives `cartLift (Rz) = R cartLift(z) Rᵀ`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked

open UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Short.PartIIIb.NearInst UnforcedLeray.Short.PartIIIb.NearInst.Delta
  UnforcedLeray.Cons.C03.Concrete UnforcedLeray.Blueprint.Planar

theorem cartLiftRotCov_holds : CartLiftRotCov := by
  intro co si hcs R c g τ z
  have h0 : (actM (rotM co si) z) 0 = co * z 0 - si * z 1 := by
    simp [actM, rotM, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    ring
  have h1 : (actM (rotM co si) z) 1 = si * z 0 + co * z 1 := by
    simp [actM, rotM, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  have h2 : (actM (rotM co si) z) 2 = z 2 := by
    simp [actM, rotM, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  have hR : hRad (actM (rotM co si) z) = hRad z := by
    unfold hRad
    rw [h0, h1]
    congr 1
    linear_combination (z 0 ^ 2 + z 1 ^ 2) * hcs
  have hchart : chartOf R c (actM (rotM co si) z) τ = chartOf R c z τ := by
    unfold chartOf
    rw [hR, h2]
  have hCF : cylFrame (actM (rotM co si) z) = rotM co si * cylFrame z := by
    unfold cylFrame
    rw [hR, h0, h1]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [rotM, Matrix.mul_apply, Fin.sum_univ_three] <;> ring
  unfold cartLift
  rw [hchart, hCF, Matrix.transpose_mul]
  simp only [mul_assoc]

end UnforcedLeray.Short.PartIIIb.NearInst.Masked
