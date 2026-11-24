import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_inst_11_3_3

/-!
# `PartIII-b:C/inst/11/3/3/4`: Cauchy-Schwarz for `ℤ`-indexed sums in `[0, ∞]`

Source `shorter-proof-2026-11-02.tex` lines 5063-5079 (Cauchy-Schwarz step over `n`).
Finite Cauchy-Schwarz (`Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul`) on each finset, transported to
`ℝ≥0∞` through `ENNReal.ofReal`, and then passed to the supremum over finsets
(`ENNReal.tsum_eq_iSup_sum`, `ENNReal.iSup_pow_of_ne_zero`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem tsumCS : TsumCS := by
  intro g h hg hh
  have key : ∀ s : Finset ℤ,
      (∑ n ∈ s, ENNReal.ofReal (g n)) ^ 2 ≤
        (∑' n, ENNReal.ofReal (h n)) * ∑' n, ENNReal.ofReal (g n ^ 2 / h n) := by
    intro s
    have hA : 0 ≤ ∑ n ∈ s, g n := Finset.sum_nonneg fun n _ => hg n
    have hB0 : 0 ≤ ∑ n ∈ s, h n := Finset.sum_nonneg fun n _ => (hh n).le
    have hC0 : 0 ≤ ∑ n ∈ s, g n ^ 2 / h n :=
      Finset.sum_nonneg fun n _ => div_nonneg (sq_nonneg _) (hh n).le
    have e1 : ∑ n ∈ s, ENNReal.ofReal (g n) = ENNReal.ofReal (∑ n ∈ s, g n) :=
      (ENNReal.ofReal_sum_of_nonneg fun n _ => hg n).symm
    have e2 : ∑ n ∈ s, ENNReal.ofReal (h n) = ENNReal.ofReal (∑ n ∈ s, h n) :=
      (ENNReal.ofReal_sum_of_nonneg fun n _ => (hh n).le).symm
    have e3 : ∑ n ∈ s, ENNReal.ofReal (g n ^ 2 / h n)
        = ENNReal.ofReal (∑ n ∈ s, g n ^ 2 / h n) :=
      (ENNReal.ofReal_sum_of_nonneg fun n _ => div_nonneg (sq_nonneg _) (hh n).le).symm
    have hcs : (∑ n ∈ s, g n) ^ 2 ≤ (∑ n ∈ s, h n) * ∑ n ∈ s, g n ^ 2 / h n :=
      Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s (fun n _ => (hh n).le)
        (fun n _ => div_nonneg (sq_nonneg _) (hh n).le)
        (fun n _ => le_of_eq (by
          have := (hh n).ne'
          field_simp))
    rw [e1, ← ENNReal.ofReal_pow hA]
    calc ENNReal.ofReal ((∑ n ∈ s, g n) ^ 2)
        ≤ ENNReal.ofReal ((∑ n ∈ s, h n) * ∑ n ∈ s, g n ^ 2 / h n) :=
          ENNReal.ofReal_le_ofReal hcs
      _ = ENNReal.ofReal (∑ n ∈ s, h n) * ENNReal.ofReal (∑ n ∈ s, g n ^ 2 / h n) :=
          ENNReal.ofReal_mul hB0
      _ ≤ (∑' n, ENNReal.ofReal (h n)) * ∑' n, ENNReal.ofReal (g n ^ 2 / h n) := by
          apply mul_le_mul'
          · rw [← e2]
            exact ENNReal.sum_le_tsum s
          · rw [← e3]
            exact ENNReal.sum_le_tsum s
  rw [ENNReal.tsum_eq_iSup_sum (f := fun n => ENNReal.ofReal (g n)),
    ENNReal.iSup_pow_of_ne_zero two_ne_zero]
  exact iSup_le key

end UnforcedLeray.Short.PartIIIb.Concrete
