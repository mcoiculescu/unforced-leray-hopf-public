import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Lower semicontinuity of `L^r` norms along `L²` limits (INF01 T18)


target T18 (the Fatou step of the §4.6 cylinder bypass).

If `A n → g` in `L²(μ)` and `‖A n‖_{L^r} ≤ C` for every `n`, then `‖g‖_{L^r} ≤ C`.
Proof: `L²` convergence gives convergence in measure
(`tendstoInMeasure_of_tendsto_eLpNorm_of_ne_top`), hence an a.e. convergent subsequence
(`TendstoInMeasure.exists_seq_tendsto_ae`), and Fatou for `eLpNorm`
(`eLpNorm_le_of_ae_tendsto`).
-/

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace UnforcedLeray.CZ

set_option autoImplicit false

variable {α E : Type*} [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup E]

/-- **T18 (INF01 §5, Level 3).** If `A n → g` in `L²(μ)` and `eLpNorm (A n) r μ ≤ C` for all
`n`, then `eLpNorm g r μ ≤ C`. Measurability of `A n` and `g` is assumed explicitly (the
manuscript's `A n`, `g` are `L²` functions). -/
theorem eLpNorm_le_of_tendsto_two {r C : ℝ≥0∞} {A : ℕ → α → E} {g : α → E}
    (hA : ∀ n, AEStronglyMeasurable (A n) μ) (hg : AEStronglyMeasurable g μ)
    (hconv : Tendsto (fun n => eLpNorm (A n - g) 2 μ) atTop (𝓝 0))
    (hb : ∀ n, eLpNorm (A n) r μ ≤ C) :
    eLpNorm g r μ ≤ C := by
  have hm : TendstoInMeasure μ A atTop g :=
    tendstoInMeasure_of_tendsto_eLpNorm_of_ne_top (by norm_num) (by norm_num) hA hg hconv
  obtain ⟨ns, hns, hae⟩ := hm.exists_seq_tendsto_ae
  exact Lp.eLpNorm_le_of_ae_tendsto (u := atTop) (Eventually.of_forall fun n => hb (ns n))
    (fun n => hA (ns n)) hae

end UnforcedLeray.CZ
