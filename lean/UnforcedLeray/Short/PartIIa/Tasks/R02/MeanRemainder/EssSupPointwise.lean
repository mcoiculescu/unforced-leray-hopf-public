import UnforcedLeray.Short.PartIIa.Sub.R02_3

/-!
# Part II-a, task `PartII-a:R02/3/2`: a continuous function is bounded pointwise by its `L^∞` norm

Source of record: `the November 2 reference manuscript`, lines 447-459
(`sct:expansion`, the `p = ∞` case read pointwise).

Target: `essSupPointwise : EssSupPointwise` (`Sub/R02_3.lean`). For continuous `f : ℝ → ℝ`,
`B ≥ 0` and `eLpNorm f ∞ volume ≤ ofReal B`, we have `|f x| ≤ B` for every `x`.

Proof: `ae_le_eLpNormEssSup` gives `|f y| ≤ B` for almost every `y`. If `|f x| > B` at some point,
the set `{y | B < |f y|}` is open (continuity), contains `x`, and so has positive Lebesgue measure,
yet it is contained in the null exceptional set. Contradiction.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory

namespace UnforcedLeray.Short.PartIIa

theorem essSupPointwise : UnforcedLeray.Short.PartIIa.EssSupPointwise := by
  unfold UnforcedLeray.Short.PartIIa.EssSupPointwise
  intro f hf B hB hbound x
  have hess : eLpNormEssSup f volume ≤ ENNReal.ofReal B := by
    rw [← eLpNorm_exponent_top]
    exact hbound
  have hae : ∀ᵐ y ∂(volume : Measure ℝ), |f y| ≤ B := by
    filter_upwards [ae_le_eLpNormEssSup (μ := (volume : Measure ℝ)) (f := f)] with y hy
    have h2 : ‖f y‖ₑ ≤ ENNReal.ofReal B := hy.trans hess
    rwa [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_le_ofReal_iff hB] at h2
  by_contra hlt
  have hxU : x ∈ {y : ℝ | B < |f y|} := not_le.mp hlt
  have hUopen : IsOpen {y : ℝ | B < |f y|} := isOpen_lt continuous_const hf.abs
  have hpos : 0 < (volume : Measure ℝ) {y : ℝ | B < |f y|} :=
    hUopen.measure_pos volume ⟨x, hxU⟩
  have hnull : (volume : Measure ℝ) {y : ℝ | ¬ |f y| ≤ B} = 0 := ae_iff.mp hae
  have hsub : {y : ℝ | B < |f y|} ⊆ {y : ℝ | ¬ |f y| ≤ B} := fun y hy => not_le.mpr hy
  have hzero : (volume : Measure ℝ) {y : ℝ | B < |f y|} = 0 := measure_mono_null hsub hnull
  exact hpos.ne' hzero

end UnforcedLeray.Short.PartIIa
