import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_inst_10
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_inst_9_2
import UnforcedLeray.Short.PartIIIb.Concrete.AffineEnvelope.SDerivIterDiffOn
import UnforcedLeray.Short.PartIIIb.Concrete.AffineEnvelope.SDerivIterLeibniz

/-!
# `PartIII-b:C/inst/10/2`: size of `A^y` by the conormal supremum `M(A)`

Source `the November 2 reference manuscript` 4955-4962 (`A^y = χ_f A`,
`M(A) = sup_{0<s≤1.1/ν} s^{-5/2} Σ_{j≤6}|(s∂_s)^j A^y|`) and 5063-5079.

The boundedness of the defining supremum is `aySumBdd_of` (`Sub/PartIII-b_C_inst_9_2.lean`,
from `sDerivIterDiffOn` and `sDerivIterLeibniz`).  The `j = 0` term of the sum is `|A^y(s)|`, and
the other terms are nonnegative, so `s^{-5/2} |A^y(s)| ≤ s^{-5/2} Σ_j ≤ M(A)`.
-/

set_option autoImplicit false

noncomputable section

open Set

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem ayBound (as : ℝ) (χf : ℝ → ℝ) : AyBound as χf := by
  intro hχ ν hν A hA s hs hsT
  have hbdd := aySumBdd_of sDerivIterDiffOn sDerivIterLeibniz as χf hχ ν hν A hA
  unfold affM
  have hs0 : (0 : ℝ) < s := hs
  have hp : 0 < s ^ (5 / 2 : ℝ) := Real.rpow_pos_of_pos hs0 _
  have hinv : s ^ (5 / 2 : ℝ) * s ^ (-(5 / 2 : ℝ)) = 1 := by
    rw [← Real.rpow_add hs0]
    norm_num
  have hj0 : frob (Ay ν χf A s) ≤ affSum 6 (Ay ν χf A) s := by
    unfold affSum
    have h := Finset.single_le_sum
      (f := fun j => frob (sDerivIter j (Ay ν χf A) s))
      (fun j _ => Real.sqrt_nonneg _) (Finset.mem_range.2 (by norm_num : 0 < 6 + 1))
    simpa [sDerivIter] using h
  have hpw : 0 ≤ s ^ (-(5 / 2 : ℝ)) := Real.rpow_nonneg hs0.le _
  have hle : s ^ (-(5 / 2 : ℝ)) * affSum 6 (Ay ν χf A) s ≤
      sSup ((fun s => s ^ (-(5 / 2 : ℝ)) * affSum 6 (Ay ν χf A) s) '' Ioc 0 ((11 / 10) / ν)) :=
    le_csSup hbdd (Set.mem_image_of_mem _ ⟨hs0, hsT⟩)
  have hmain : s ^ (-(5 / 2 : ℝ)) * frob (Ay ν χf A s) ≤
      sSup ((fun s => s ^ (-(5 / 2 : ℝ)) * affSum 6 (Ay ν χf A) s) '' Ioc 0 ((11 / 10) / ν)) :=
    (mul_le_mul_of_nonneg_left hj0 hpw).trans hle
  calc frob (Ay ν χf A s)
      = s ^ (5 / 2 : ℝ) * (s ^ (-(5 / 2 : ℝ)) * frob (Ay ν χf A s)) := by
        rw [← mul_assoc, hinv, one_mul]
    _ ≤ s ^ (5 / 2 : ℝ) * sSup ((fun s => s ^ (-(5 / 2 : ℝ)) * affSum 6 (Ay ν χf A) s) ''
          Ioc 0 ((11 / 10) / ν)) :=
        mul_le_mul_of_nonneg_left hmain hp.le

end UnforcedLeray.Short.PartIIIb.Concrete
