import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_masked_18_3_2_4
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.Proofs.DB.FullOutLip.Lin.Core

/-!
# Dilation margin `FmMargin` (source 4001, `μ > -1/4`)

For `l ∈ (0,1)` and `2μ + 1/2 > 0` one has `l^{2μ+1/2} ≤ 1`, so the integrand is dominated by
`(1-l²)^{-1/2}`, whose `l`-integral is finite (`LinAux.lint_inv_sqrt_lt_top`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization

theorem fmMargin : UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.FmMargin := by
  intro μ hμ
  have hpt : ∀ l ∈ Ioo (0 : ℝ) 1,
      ENNReal.ofReal (l ^ (2 * μ + 1 / 2)) * ENNReal.ofReal ((1 - l ^ 2) ^ (-(1 / 2 : ℝ))) ≤
        ENNReal.ofReal ((1 - l ^ 2) ^ (-(1 / 2 : ℝ))) := by
    intro l hl
    have hl0 : 0 < l := hl.1
    have hl1 : l < 1 := hl.2
    have hsq : 0 ≤ 1 - l ^ 2 := by nlinarith
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hl0.le _)]
    apply ENNReal.ofReal_le_ofReal
    have h1 : l ^ (2 * μ + 1 / 2) ≤ 1 :=
      Real.rpow_le_one hl0.le hl1.le (by linarith)
    have h2 : 0 ≤ (1 - l ^ 2) ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hsq _
    exact mul_le_of_le_one_left h2 h1
  calc ∫⁻ l in Ioo (0 : ℝ) 1, ENNReal.ofReal (l ^ (2 * μ + 1 / 2)) *
          ENNReal.ofReal ((1 - l ^ 2) ^ (-(1 / 2 : ℝ)))
      ≤ ∫⁻ l in Ioo (0 : ℝ) 1, ENNReal.ofReal ((1 - l ^ 2) ^ (-(1 / 2 : ℝ))) :=
        setLIntegral_mono' measurableSet_Ioo hpt
    _ < ⊤ := LinAux.lint_inv_sqrt_lt_top

end UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization
