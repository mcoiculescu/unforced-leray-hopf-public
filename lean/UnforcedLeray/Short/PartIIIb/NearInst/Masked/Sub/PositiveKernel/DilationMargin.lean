import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.PositiveKernel

/-!
# The dilation margin (source 4000-4001)

Proves `dilationMargin_holds : DilationMargin` (defined in `Sub/PositiveKernel.lean`).
Route: for `μ ∈ Kset ⊆ (0, 1/4)` the exponent `2μ + 1/2` is positive, so `l^{2μ+1/2} ≤ 1` on
`(0,1)`, and the integral is at most the volume `1` of `(0,1)`. Constant `C = 1`; compactness is
not needed.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked

theorem dilationMargin_holds : DilationMargin := by
  intro Kset _ hKs
  refine ⟨1, zero_le_one, fun μ hμ => ?_⟩
  have hμ0 : 0 < μ := (hKs hμ).1
  have hexp : (0 : ℝ) ≤ 2 * μ + 1 / 2 := by linarith
  calc ∫⁻ l in Ioo (0 : ℝ) 1, ENNReal.ofReal (l ^ (2 * μ + 1 / 2))
      ≤ ∫⁻ _ in Ioo (0 : ℝ) 1, (1 : ℝ≥0∞) := by
        apply setLIntegral_mono' measurableSet_Ioo
        intro l hl
        rw [← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal (Real.rpow_le_one hl.1.le hl.2.le hexp)
    _ = ENNReal.ofReal 1 := by
        rw [setLIntegral_const, Real.volume_Ioo]
        simp

end UnforcedLeray.Short.PartIIIb.NearInst.Masked
