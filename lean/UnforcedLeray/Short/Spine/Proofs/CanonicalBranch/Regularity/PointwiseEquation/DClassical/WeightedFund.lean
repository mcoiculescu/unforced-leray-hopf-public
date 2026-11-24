import UnforcedLeray.Units.B0012
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# Weighted fundamental lemma on `(0, ∞)` (helper for `DClassicalAe`)

Let `w r = 4π e^{r²/4} r` (the `X_G` density on `(0, ∞)`, `B0010.xGDensity_eq`). If
`h : ℝ → ℂ` makes `h · w` locally integrable on `(0, ∞)` and `∫ ψ · (h · w) = 0` for every real
`C^∞` function `ψ` with compact support inside `(0, ∞)`, then `h = 0` `xGMeasure`-a.e.

Proof: Mathlib's `IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero` gives `h · w = 0`
Lebesgue-a.e. on `(0, ∞)`; `B0012.xG_ac` transfers this to `xGMeasure`, and `w r ≠ 0` for `r > 0`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ContDiff

namespace UnforcedLeray.Short.Spine.DClassicalAux

/-- The `X_G` density on `(0, ∞)` as a real function (`B0010.xGDensity_eq`). -/
def wDens (r : ℝ) : ℝ := 4 * Real.pi * Real.exp (r ^ 2 / 4) * r

theorem wDens_pos {r : ℝ} (hr : 0 < r) : 0 < wDens r := by
  unfold wDens
  exact mul_pos (mul_pos (mul_pos (by norm_num) Real.pi_pos) (Real.exp_pos _)) hr

/-- **Weighted fundamental lemma on `(0, ∞)`.** -/
theorem weighted_fundamental (h : ℝ → ℂ)
    (hloc : LocallyIntegrableOn (fun r => h r * (wDens r : ℂ)) (Ioi 0))
    (hzero : ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ Ioi 0 →
      ∫ r, ψ r • (h r * (wDens r : ℂ)) = 0) :
    ∀ᵐ r ∂B0010.xGMeasure, h r = 0 := by
  have hae : ∀ᵐ r ∂(volume : Measure ℝ), r ∈ Ioi (0 : ℝ) → h r * (wDens r : ℂ) = 0 :=
    IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero isOpen_Ioi hloc hzero
  have hae' : ∀ᵐ r ∂(volume.restrict (Ioi (0 : ℝ))), h r * (wDens r : ℂ) = 0 := by
    rw [ae_restrict_iff' measurableSet_Ioi]
    exact hae
  filter_upwards [B0012.xG_ac.ae_le hae', B0012.ae_xG_pos] with r h1 h2
  have hw : (wDens r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (wDens_pos h2).ne'
  exact (mul_eq_zero.mp h1).resolve_right hw

end UnforcedLeray.Short.Spine.DClassicalAux
