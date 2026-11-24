import UnforcedLeray.Short.PartI.Sub.T01Class

/-!
# Part I, task `PartI:TC/2`: the mean stream decays

Source of record: `the November 2 reference manuscript`, lines 397-404 (the mean
stream `S = \bar ψ` of the train) and lines 261-288 (the train is the Gallay-Slijepcevic solution).
The Prop `MeanStreamDecay` is defined in `Short/PartI/Sub/T01Class.lean`.

Route, for `ν, c > 0`, a train `tr : B0140.TrainSol ν c` and an age `s ≥ 0`:

* `IsTrain.stream_decay` gives `ψ(s,·) → 0` along `comap (fun z => |z.2|) atTop`, so for `ε > 0`
  there is `R` with `‖ψ(s,q,η)‖ ≤ ε/2` for all `q` whenever `|η| ≥ R`;
* for such `η` the cell `(-c/2, c/2]` has length `c`, so
  `‖∫_{(-c/2,c/2]} ψ(s,q,η) dq‖ ≤ (ε/2) c` (`norm_setIntegral_le_of_norm_le_const`);
* hence `‖meanStream tr s η‖ = c⁻¹ ‖∫ ...‖ ≤ ε/2 < ε`.

No hypotheses are added; the statement is the Prop `MeanStreamDecay` unchanged.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)

/-- **`PartI:TC/2`. The mean stream decays** (lines 397-404): for every train and every age
`s ≥ 0`, `η ↦ S(s,η)` tends to `0` as `η → +∞`. -/
theorem meanStreamDecay : MeanStreamDecay := by
  intro ν c _hν hc tr s hs
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hdec := Metric.tendsto_nhds.1 (tr.isTrain.stream_decay s hs) (ε / 2) (half_pos hε)
  rw [Filter.eventually_comap] at hdec
  obtain ⟨R, hR⟩ := Filter.eventually_atTop.1 hdec
  refine Filter.eventually_atTop.2 ⟨R, fun η hη => ?_⟩
  have hbd : ∀ q : ℝ, ‖tr.ψ s (q, η)‖ ≤ ε / 2 := by
    intro q
    have h := hR |η| (le_trans hη (le_abs_self η)) (q, η) rfl
    rw [dist_zero_right] at h
    exact h.le
  have hint : ‖∫ q in Ioc (-c / 2) (c / 2), tr.ψ s (q, η)‖ ≤ ε / 2 * c := by
    have h := norm_setIntegral_le_of_norm_le_const (μ := volume)
      (s := Ioc (-c / 2) (c / 2)) (f := fun q : ℝ => tr.ψ s (q, η))
      (C := ε / 2) measure_Ioc_lt_top (fun q _ => hbd q)
    rw [Real.volume_real_Ioc_of_le (by linarith), show c / 2 - -c / 2 = c by ring] at h
    exact h
  show dist (c⁻¹ • ∫ q in Ioc (-c / 2) (c / 2), tr.ψ s (q, η)) 0 < ε
  rw [dist_zero_right, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hc]
  have hmain : c⁻¹ * ‖∫ q in Ioc (-c / 2) (c / 2), tr.ψ s (q, η)‖ ≤
      c⁻¹ * (ε / 2 * c) := mul_le_mul_of_nonneg_left hint (inv_nonneg.2 hc.le)
  have hcancel : c⁻¹ * (ε / 2 * c) = ε / 2 := by
    field_simp
  linarith

end UnforcedLeray.Short.PartI
