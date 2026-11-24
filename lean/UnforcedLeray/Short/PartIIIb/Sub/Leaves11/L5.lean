import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_inst_10
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_inst_9_2
import UnforcedLeray.Short.PartIIIb.Concrete.AffineEnvelope.SDerivIterDiffOn
import UnforcedLeray.Short.PartIIIb.Concrete.AffineEnvelope.SDerivIterLeibniz

/-!
# `PartIII-b:C/inst/11/5`: `ayBound`, the bound `|A^y(s)| ≤ s^{5/2} M(A)`

Source `the November 2 reference manuscript`
lines 4955-4962 (`M(A)` is the supremum), 5063-5079 (conormal size).

The boundedness of the defining supremum of `affM` is `aySumBdd_of` (Sub/PartIII-b_C_inst_9_2),
fed by the two unconditional leaves `sDerivIterDiffOn` and `sDerivIterLeibniz`
(Concrete/AffineEnvelope/*.lean).  The `j = 0` term of `affSum 6` gives `|A^y(s)|`, and
`le_csSup` gives the supremum bound.
-/

set_option autoImplicit false

noncomputable section

open Set

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem ayBound (as : ℝ) (χf : ℝ → ℝ) : AyBound as χf := by
  intro hχ ν hν A hA s hs hsT
  have hBdd : BddAbove ((fun s => s ^ (-(5 / 2 : ℝ)) * affSum 6 (Ay ν χf A) s) ''
      Ioc 0 ((11 / 10) / ν)) :=
    aySumBdd_of sDerivIterDiffOn sDerivIterLeibniz as χf hχ ν hν A hA
  have hle : s ^ (-(5 / 2 : ℝ)) * affSum 6 (Ay ν χf A) s ≤ affM ν χf A :=
    le_csSup hBdd ⟨s, ⟨hs, hsT⟩, rfl⟩
  have hge : frob (Ay ν χf A s) ≤ affSum 6 (Ay ν χf A) s := by
    unfold affSum
    have h0 : frob (sDerivIter 0 (Ay ν χf A) s) ≤
        ∑ k ∈ Finset.range (6 + 1), frob (sDerivIter k (Ay ν χf A) s) :=
      Finset.single_le_sum (f := fun k => frob (sDerivIter k (Ay ν χf A) s))
        (fun k _ => frob_nonneg _) (Finset.mem_range.2 (by norm_num))
    exact h0
  have hpos : 0 < s ^ (5 / 2 : ℝ) := Real.rpow_pos_of_pos hs _
  have hr : s ^ (-(5 / 2 : ℝ)) = (s ^ (5 / 2 : ℝ))⁻¹ := Real.rpow_neg hs.le _
  have key : s ^ (5 / 2 : ℝ) * (s ^ (-(5 / 2 : ℝ)) * affSum 6 (Ay ν χf A) s)
      = affSum 6 (Ay ν χf A) s := by
    rw [hr, ← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul]
  calc frob (Ay ν χf A s) ≤ affSum 6 (Ay ν χf A) s := hge
    _ = s ^ (5 / 2 : ℝ) * (s ^ (-(5 / 2 : ℝ)) * affSum 6 (Ay ν χf A) s) := key.symm
    _ ≤ s ^ (5 / 2 : ℝ) * affM ν χf A := mul_le_mul_of_nonneg_left hle hpos.le

end UnforcedLeray.Short.PartIIIb.Concrete
