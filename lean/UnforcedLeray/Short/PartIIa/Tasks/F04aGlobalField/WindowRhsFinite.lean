import UnforcedLeray.Short.PartIIa.Sub.PartIIa_F04_1

/-!
# Part II-a, task `PartII-a:F04/1/3`: finiteness of the window right side

Source of record: `the November 2 reference manuscript`, lines 1451-1480.
Proves `WindowRhsFinite` (Sub C of `Sub/PartIIa_F04_1.lean`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

theorem windowRhsFinite : UnforcedLeray.Short.PartIIa.WindowRhsFinite := by
  intro r _ hr P _ μ f w τ₀
  have hf := UnforcedLeray.Short.PartIIa.Rep.lintegral_window_lt_top hr f 0 (τ₀ - 2) (τ₀ + 2)
  have hw := UnforcedLeray.Short.PartIIa.Rep.lintegral_window_lt_top hr w 0 (τ₀ - 2) (τ₀ + 2)
  simp only [zero_add] at hf hw
  have hfm : AEMeasurable (fun τ : ℝ => ‖f (τ : AddCircle P)‖ₑ ^ r.toReal) volume :=
    ((UnforcedLeray.PhaseTrace.aestronglyMeasurable_comp_mk f).enorm).pow_const _
  have hc : ENNReal.ofReal (1 + ‖μ‖) ^ r.toReal ≠ ⊤ :=
    (ENNReal.rpow_lt_top_of_nonneg ENNReal.toReal_nonneg ENNReal.ofReal_ne_top).ne
  have hIoo : Ioo (τ₀ - 2) (τ₀ + 2) ⊆ Icc (τ₀ - 2) (τ₀ + 2) := Ioo_subset_Icc_self
  rw [lintegral_add_left' (hfm.mono_measure Measure.restrict_le_self),
    lintegral_const_mul' _ _ hc]
  refine ENNReal.add_lt_top.2 ⟨?_, ENNReal.mul_lt_top ?_ ?_⟩
  · exact (lintegral_mono_set hIoo).trans_lt hf
  · exact ENNReal.rpow_lt_top_of_nonneg ENNReal.toReal_nonneg ENNReal.ofReal_ne_top
  · exact (lintegral_mono_set hIoo).trans_lt hw
