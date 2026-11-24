import UnforcedLeray.Short.Spine.Sub.SP_CAN4_5_3

/-!
# Leaf 3 proof: a continuous function supported in `[a, b]` lies in `L²(xGMeasure)`

Proves `UnforcedLeray.Short.Spine.TestMemLp` (`Sub/SP_CAN4_5_3.lean`), the statement that
`X_G = L²(xGMeasure)` contains every continuous function vanishing off a bounded interval.

Source of record: `the November 2 reference manuscript` line 1086 (smooth for
positive `θ`) and lines 1134-1140 (`X_G = L²(xGMeasure)`).

Proof. `ψ` equals `(Icc a b).indicator ψ`, so by `memLp_indicator_iff_restrict` it suffices to show
`MemLp ψ 2 (xGMeasure.restrict (Icc a b))`. That restricted measure is finite, because
`xGMeasure (Icc a b)` is the lintegral of the density `4π e^{r²/4} r` over `Icc a b ∩ Ioi 0`
(`B0010.xGMeasure_apply`), and this density is bounded there by `4π e^{R²/4} R` with
`R = |a| + |b|`. A continuous `ψ` is bounded on `Icc a b`, so `MemLp.of_bound` applies.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ContDiff Topology InnerProductSpace

namespace UnforcedLeray.Short.Spine

open UnforcedLeray.B0010 Blueprint.Planar ComplexODEC UnforcedLeray.Cons.C01
open UnforcedLeray.Cons.G3b
open UnforcedLeray.Short.Spine.DClassicalAux

/-- **Leaf 3, proof.** A continuous `ψ` vanishing on `(-∞, a)` and `(b, ∞)` lies in
`L²(xGMeasure)`. -/
theorem testMemLp_proof : UnforcedLeray.Short.Spine.TestMemLp := by
  intro ψ hψ a b hψa hψb
  -- (a) `ψ` is the indicator of `Icc a b`
  have hsupp : (Icc a b).indicator ψ = ψ := by
    funext r
    by_cases hr : r ∈ Icc a b
    · exact Set.indicator_of_mem hr ψ
    · rw [Set.indicator_of_notMem hr]
      simp only [Set.mem_Icc, not_and_or, not_le] at hr
      rcases hr with h | h
      · exact (hψa r h).symm
      · exact (hψb r h).symm
  -- (b) the density is bounded on `Icc a b ∩ Ioi 0`
  have hC : ∀ r ∈ Icc a b ∩ Ioi 0,
      ENNReal.ofReal ((radialGaussianWeight r)⁻¹ * r) ≤
        ENNReal.ofReal (4 * Real.pi * Real.exp ((|a| + |b|) ^ 2 / 4) * (|a| + |b|)) := by
    intro r hr
    obtain ⟨hrI, hr0⟩ := hr
    have hr0' : (0 : ℝ) < r := hr0
    have hrb : r ≤ b := hrI.2
    have hrR : r ≤ |a| + |b| := by
      have h1 := le_abs_self b
      have h2 := abs_nonneg a
      linarith
    have hsq : r ^ 2 ≤ (|a| + |b|) ^ 2 := by nlinarith [hrR, hr0']
    have hexp : Real.exp (r ^ 2 / 4) ≤ Real.exp ((|a| + |b|) ^ 2 / 4) :=
      Real.exp_le_exp.2 (by linarith)
    have hpi : (0 : ℝ) ≤ 4 * Real.pi := by positivity
    rw [radialGaussianWeight_inv]
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul (mul_le_mul_of_nonneg_left hexp hpi) hrR hr0'.le (by positivity)
  -- (c) `xGMeasure (Icc a b)` is finite
  have hvol : volume (Icc a b ∩ Ioi 0) ≠ ⊤ :=
    ne_top_of_le_ne_top (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
      (measure_mono Set.inter_subset_left)
  have hfin : xGMeasure (Icc a b) ≠ ⊤ := by
    rw [xGMeasure_apply measurableSet_Icc]
    refine ne_top_of_le_ne_top ?_ (setLIntegral_mono measurable_const hC)
    rw [setLIntegral_const]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hvol
  -- (d) the restricted measure is finite
  have hfinM : IsFiniteMeasure (xGMeasure.restrict (Icc a b)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.2 hfin⟩
  -- (e) `ψ` is bounded on `Icc a b`
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ x ∈ Icc a b, ‖ψ x‖ ≤ M :=
    isCompact_Icc.exists_bound_of_continuousOn hψ.continuousOn
  have hres : MemLp ψ 2 (xGMeasure.restrict (Icc a b)) :=
    MemLp.of_bound hψ.aestronglyMeasurable M
      (ae_restrict_of_forall_mem measurableSet_Icc (fun r hr => hM r hr))
  -- (f) transfer back from the restriction to `ψ`
  have hind := (memLp_indicator_iff_restrict (μ := xGMeasure) measurableSet_Icc).2 hres
  rw [hsupp] at hind
  exact hind

end UnforcedLeray.Short.Spine
