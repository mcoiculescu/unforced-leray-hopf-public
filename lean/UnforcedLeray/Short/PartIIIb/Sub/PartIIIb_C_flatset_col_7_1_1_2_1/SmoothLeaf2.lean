import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_1.SmoothOf

/-!
# Leaf 2: smoothness of the cut-off kernel `rhoCut` on `s > 0`
(task `PartIII-b:C/flatset/col/7/1/1/2/1/org2/smooth/2`).

`rhoCut s0 μ s τ = θ(s-τ) * ((s-τ)/s)^μ` with `θ = smoothTransition((· - s0/2)/(s0/2))`.
At a point with `s - τ > s0/4` the base `(s-τ)/s` is positive, so the complex power is the
composition of the real power `r ↦ r^μ` (smooth on `r ≠ 0`) with `ofReal`; at a point with
`s - τ < s0/2` the cut-off vanishes on a neighbourhood.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

/-- **Leaf 2.** `rhoCut` is smooth on `s > 0`. -/
theorem rhoCutSmooth : RhoCutSmooth := by
  intro s0 μ hs0
  refine fun p hp => ContDiffAt.contDiffWithinAt ?_
  have hps : 0 < p.1 := hp.1
  by_cases h : s0 / 4 < p.1 - p.2
  · -- positive base: the real power is smooth near `p`
    have hq0 : 0 < (p.1 - p.2) / p.1 := div_pos (by linarith) hps
    have hqr : ContDiffAt ℝ ∞ (fun q : ℝ × ℝ => (q.1 - q.2) / q.1) p :=
      ((contDiff_fst.sub contDiff_snd).contDiffAt).div contDiff_fst.contDiffAt hps.ne'
    have hpow : ContDiffAt ℝ ∞ (fun q : ℝ × ℝ => (((q.1 - q.2) / q.1) ^ μ : ℝ)) p :=
      hqr.rpow_const_of_ne hq0.ne'
    have hpowC : ContDiffAt ℝ ∞ (fun q : ℝ × ℝ => ((((q.1 - q.2) / q.1) ^ μ : ℝ) : ℂ)) p :=
      Complex.ofRealCLM.contDiff.comp_contDiffAt p hpow
    have hθ : ContDiffAt ℝ ∞
        (fun q : ℝ × ℝ => ((Real.smoothTransition (((q.1 - q.2) - s0 / 2) / (s0 / 2)) : ℝ) : ℂ)) p :=
      Complex.ofRealCLM.contDiff.comp_contDiffAt p
        (Real.smoothTransition.contDiff.comp_contDiffAt p
          ((((contDiff_fst.sub contDiff_snd).sub contDiff_const).div_const (s0 / 2)).contDiffAt))
    have hprod := hθ.mul hpowC
    have e1 : ∀ᶠ q in 𝓝 p, s0 / 4 < q.1 - q.2 :=
      ContinuousAt.eventually_lt continuousAt_const
        ((continuous_fst.sub continuous_snd).continuousAt) h
    have e2 : ∀ᶠ q in 𝓝 p, (0 : ℝ) < q.1 :=
      ContinuousAt.eventually_lt continuousAt_const continuous_fst.continuousAt hps
    have hEq : (fun q : ℝ × ℝ => rhoCut s0 μ q.1 q.2) =ᶠ[𝓝 p]
        (fun q : ℝ × ℝ => ((Real.smoothTransition (((q.1 - q.2) - s0 / 2) / (s0 / 2)) : ℝ) : ℂ) *
          ((((q.1 - q.2) / q.1) ^ μ : ℝ) : ℂ)) := by
      filter_upwards [e1, e2] with q hq1 hq2
      have hqn : 0 ≤ (q.1 - q.2) / q.1 := div_nonneg (by linarith) hq2.le
      unfold rhoCut
      rw [Complex.ofReal_cpow hqn]
    exact hprod.congr_of_eventuallyEq hEq
  · -- the cut-off vanishes on a neighbourhood of `p`
    have hlt : p.1 - p.2 < s0 / 2 := by linarith [not_lt.1 h]
    have e : ∀ᶠ q in 𝓝 p, q.1 - q.2 < s0 / 2 :=
      ContinuousAt.eventually_lt ((continuous_fst.sub continuous_snd).continuousAt)
        continuousAt_const hlt
    have hEq : (fun q : ℝ × ℝ => rhoCut s0 μ q.1 q.2) =ᶠ[𝓝 p] (fun _ : ℝ × ℝ => (0 : ℂ)) := by
      filter_upwards [e] with q hq
      have hnp : ((q.1 - q.2) - s0 / 2) / (s0 / 2) ≤ 0 :=
        div_nonpos_iff.2 (Or.inr ⟨by linarith, by linarith⟩)
      unfold rhoCut
      rw [Real.smoothTransition.zero_of_nonpos hnp]
      simp
    exact (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq hEq

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
