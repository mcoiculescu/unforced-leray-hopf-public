import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_5_1_3
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.HpPsiTermSummable.Gauss
import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable

/-!
# `PartIII-b:C/grad/3/5/1/3` L1: uniform-in-`t` Gaussian majorant

Proves `HpAGaussUnif` (source 5063-5079): for `|t| ≤ T` the fifth-power-weighted shifted Gaussian
`hpAGauss α c j t` is dominated by a summable sequence in `j`, obtained from `gp_gauss_dom` with
`|t|` replaced by `|T|`.
-/

set_option autoImplicit false

noncomputable section

open Set Real

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Dominating `j`-sequence of the Gaussian exponential with `|t|` replaced by `|T|`. -/
def hpAGaussE (a B : ℝ) (j : ℤ) : ℝ :=
  Real.exp (-π * (a * (j : ℝ) ^ 2 - 2 * B * |(j : ℝ)|))

lemma hpAGaussE_pow_summable (a B : ℝ) (ha : 0 < a) (k : ℕ) :
    Summable (fun j : ℤ => |(j : ℝ)| ^ k * hpAGaussE a B j) := by
  have h := summable_pow_mul_jacobiTheta₂_term_bound B ha k
  simpa only [hpAGaussE, Int.cast_abs] using h

lemma hpAGaussE_cube_summable (a B : ℝ) (ha : 0 < a) :
    Summable (fun j : ℤ => (1 + |(j : ℝ)|) ^ 5 * hpAGaussE a B j) := by
  have e : (fun j : ℤ => (1 + |(j : ℝ)|) ^ 5 * hpAGaussE a B j) = fun j : ℤ =>
      (|(j : ℝ)| ^ 0 * hpAGaussE a B j + 5 * (|(j : ℝ)| ^ 1 * hpAGaussE a B j)
        + 10 * (|(j : ℝ)| ^ 2 * hpAGaussE a B j) + 10 * (|(j : ℝ)| ^ 3 * hpAGaussE a B j)
        + 5 * (|(j : ℝ)| ^ 4 * hpAGaussE a B j)) + |(j : ℝ)| ^ 5 * hpAGaussE a B j := by
    funext j
    ring
  rw [e]
  exact ((((((hpAGaussE_pow_summable a B ha 0).add
    ((hpAGaussE_pow_summable a B ha 1).mul_left 5)).add
    ((hpAGaussE_pow_summable a B ha 2).mul_left 10)).add
    ((hpAGaussE_pow_summable a B ha 3).mul_left 10)).add
    ((hpAGaussE_pow_summable a B ha 4).mul_left 5))).add (hpAGaussE_pow_summable a B ha 5)

lemma hpAGauss_exp_unif (t T α c : ℝ) (hα : 0 < α) (hc : 0 < c) (ht : |t| ≤ |T|) (j : ℤ) :
    Real.exp (-α * (t - (j : ℝ) * c) ^ 2) ≤ hpAGaussE (α * c ^ 2 / π) (α * |T| * c / π) j := by
  unfold hpAGaussE
  refine (gp_gauss_dom t α c hα hc.le j).trans (Real.exp_le_exp.mpr ?_)
  have hBT : α * |t| * c / π ≤ α * |T| * c / π := by
    refine div_le_div_of_nonneg_right ?_ Real.pi_pos.le
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ht hα.le) hc.le
  have h2 : 2 * (α * |t| * c / π) * |(j : ℝ)| ≤ 2 * (α * |T| * c / π) * |(j : ℝ)| :=
    mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
  nlinarith [mul_nonneg Real.pi_pos.le (sub_nonneg.mpr h2)]

lemma hpAGauss_poly_unif (t T c : ℝ) (hc : 0 < c) (ht : |t| ≤ |T|) (j : ℤ) :
    (1 + |t - (j : ℝ) * c|) ^ 5 ≤ (1 + |T| + c) ^ 5 * (1 + |(j : ℝ)|) ^ 5 := by
  have hT : 0 ≤ |T| := abs_nonneg T
  have h1 : |t - (j : ℝ) * c| ≤ |T| + |(j : ℝ)| * c := by
    have h2 := abs_sub t ((j : ℝ) * c)
    rw [abs_mul, abs_of_pos hc] at h2
    linarith
  have hu : 1 + |t - (j : ℝ) * c| ≤ (1 + |T| + c) * (1 + |(j : ℝ)|) := by
    nlinarith [abs_nonneg (j : ℝ), mul_nonneg hT (abs_nonneg (j : ℝ)), hc.le, h1]
  rw [← mul_pow]
  exact pow_le_pow_left₀ (by linarith [abs_nonneg (t - (j : ℝ) * c)]) hu 5

theorem hpAGaussUnif : HpAGaussUnif := by
  intro α c T hα hc
  have ha : 0 < α * c ^ 2 / π := div_pos (mul_pos hα (pow_pos hc 2)) Real.pi_pos
  refine ⟨fun j => (1 + |T| + c) ^ 5 * ((1 + |(j : ℝ)|) ^ 5 * hpAGaussE (α * c ^ 2 / π) (α * |T| * c / π) j), ?_, ?_⟩
  · exact (hpAGaussE_cube_summable _ _ ha).mul_left _
  · intro t ht j
    have htT : |t| ≤ |T| := ht.trans (le_abs_self T)
    unfold hpAGauss
    calc (1 + |t - (j : ℝ) * c|) ^ 5 * Real.exp (-α * (t - (j : ℝ) * c) ^ 2)
        ≤ ((1 + |T| + c) ^ 5 * (1 + |(j : ℝ)|) ^ 5) * hpAGaussE (α * c ^ 2 / π) (α * |T| * c / π) j :=
          mul_le_mul (hpAGauss_poly_unif t T c hc htT j) (hpAGauss_exp_unif t T α c hα hc htT j)
            (Real.exp_pos _).le
            (mul_nonneg (pow_nonneg (by linarith [abs_nonneg T]) 5) (pow_nonneg (by positivity) 5))
      _ = (1 + |T| + c) ^ 5 * ((1 + |(j : ℝ)|) ^ 5 * hpAGaussE (α * c ^ 2 / π) (α * |T| * c / π) j) := by
          ring

end UnforcedLeray.Short.PartIIIb.Concrete
