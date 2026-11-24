import UnforcedLeray.Analysis.Sturm.CompactL2
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Topology.Sequences

/-!
# Identifying concrete representatives of bounded L² extensions

An explicit pointwise formula that depends continuously on the L² datum and
agrees almost everywhere with a bounded operator on the dense compact-support
domain agrees almost everywhere on all L² data. The proof uses a genuine
almost-everywhere convergent subsequence of an L²-convergent sequence.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace UnforcedLeray.Sturm

/-- Dense-domain equality identifies an actual pointwise-continuous formula
with its bounded L² extension. No pointwise evaluation continuity of L² itself
is assumed: continuity is required only for the explicit formula `F`. -/
theorem ae_eq_pointwiseFormula_of_compact
    (T : ComplexL2 →L[ℂ] ComplexL2) (F : ComplexL2 → ℝ → ℂ)
    (hF : ∀ x : ℝ, Continuous (fun f : ComplexL2 => F f x))
    (hcompact : ∀ d : compactL2, T (d : ComplexL2) =ᵐ[volume] F (d : ComplexL2))
    (f : ComplexL2) : T f =ᵐ[volume] F f := by
  obtain ⟨d, hd, hdt⟩ := mem_closure_iff_seq_limit.mp (dense_compactL2 f)
  have hT : Tendsto (fun n : ℕ => T (d n)) atTop (𝓝 (T f)) :=
    T.continuous.continuousAt.tendsto.comp hdt
  obtain ⟨ns, hns, hae⟩ :=
    (tendstoInMeasure_of_tendsto_Lp hT).exists_seq_tendsto_ae
  have hmatches : ∀ᵐ x ∂volume, ∀ n : ℕ, T (d n) x = F (d n) x := by
    apply ae_all_iff.mpr
    intro n
    exact hcompact ⟨d n, hd n⟩
  filter_upwards [hae, hmatches] with x hx hmatch
  have hformula : Tendsto (fun n : ℕ => F (d (ns n)) x) atTop (𝓝 (F f x)) :=
    (hF x).continuousAt.tendsto.comp (hdt.comp hns.tendsto_atTop)
  have hactual : Tendsto (fun n : ℕ => F (d (ns n)) x) atTop (𝓝 (T f x)) := by
    apply hx.congr'
    exact Eventually.of_forall fun n => hmatch (ns n)
  exact tendsto_nhds_unique hactual hformula

end UnforcedLeray.Sturm
