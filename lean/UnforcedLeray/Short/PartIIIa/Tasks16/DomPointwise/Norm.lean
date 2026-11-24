import UnforcedLeray.Short.PartIIIa.Tasks16.DomPointwise.Kernel

/-!
# The `L^b` norm of the dilated, translated kernel majorant
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

theorem real_norm_identity (j : ℕ) (D b l : ℝ) (hD : 0 < D) (hb : 0 < b) (hl : 0 < l) :
    ((l ^ 3)⁻¹ * D ^ (3 - (4 + (j : ℝ)) * b)) ^ (1 / b) =
      l ^ (-(3 / b)) * D ^ (-4 - (j : ℝ) + 3 / b) := by
  rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast, ← Real.rpow_neg (by positivity),
    ← Real.rpow_mul hl.le, ← Real.rpow_mul hD.le]
  congr 2
  · push_cast; field_simp
  · field_simp; ring

theorem kernelNorm (j : ℕ) (D b : ℝ) (hD : 0 < D) (hb : 0 < b) (y : Space) (l : ℝ) (hl : 0 < l) :
    (∫⁻ z : Space, sepKd j D (y - l • z) ^ b) ^ (1 / b) =
      ENNReal.ofReal (l ^ (-(3 / b))) *
        (ENNReal.ofReal (D ^ (-4 - (j : ℝ) + 3 / b)) *
          (∫⁻ x : Space, sepKd j 1 x ^ b) ^ (1 / b)) := by
  rw [lintegral_sepKd_dilate j D b y l hl hb, lintegral_sepKd_rpow j D b hD hb,
    ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
    ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
    ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity),
    real_norm_identity j D b l hD hb hl, ENNReal.ofReal_mul (by positivity), mul_assoc]

end UnforcedLeray.Short.IIIa

end
