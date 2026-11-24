import UnforcedLeray.Short.PartIIb.Defs

/-!
# Helper for `PeriodicRepresentative` (task `PartII-b:T07/7`): `ageμ`-null sets

SIZE M. An arbitrary (not necessarily measurable) set `N` in the chart space `Coord` with
`ageμ c a N = 0` has Lebesgue-null trace on the half cell `(0, ∞) × qCell c`.

The weight `ENNReal.ofReal (c⁻¹ * s^a)` is strictly positive on `s > 0`, so the vanishing of
`∫⁻ _{(0,∞) × cell} w · 1_{N'}` forces `1_{N'} = 0` almost everywhere on the half cell, for a
measurable superset `N'` of `N` with `ageμ c a N' = 0` (Lean: `exists_measurable_superset_of_null`).

Source of record: `the November 2 reference manuscript` (no line located for

`Axi.lintegral_ageμ`, `Axi.qCell`, `lintegral_indicator_one` (pattern of `ageμ_null_of_volume_null`,
`Sub/T07.lean`, and `Axi.ae_ageμ_mem`, `Lib/AxisymmetricB/Jv.lean`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace UnforcedLeray.Short.IIb.NvCNorm

/-- An `ageμ`-null set (measurable or not) is Lebesgue-null on the half cell
`(0, ∞) × qCell c`. -/
theorem volume_null_of_ageμ_null {c a : ℝ} (hc : 0 < c) {N : Set Coord}
    (hN : UnforcedLeray.Axi.ageμ c a N = 0) :
    MeasureTheory.volume (N ∩ (Set.Ioi (0 : ℝ) ×ˢ UnforcedLeray.Axi.qCell c)) = 0 := by
  obtain ⟨N', hNN', hN'm, hN'0⟩ := exists_measurable_superset_of_null hN
  have hS : MeasurableSet (Ioi (0 : ℝ) ×ˢ UnforcedLeray.Axi.qCell c) := by
    unfold UnforcedLeray.Axi.qCell
    exact measurableSet_Ioi.prod (measurableSet_Ico.prod MeasurableSet.univ)
  have hw : Measurable fun p : Coord => ENNReal.ofReal (c⁻¹ * p.1 ^ a) :=
    ENNReal.measurable_ofReal.comp ((measurable_fst.pow_const a).const_mul c⁻¹)
  have hI : Measurable (N'.indicator (1 : Coord → ℝ≥0∞)) := measurable_one.indicator hN'm
  have h := UnforcedLeray.Axi.lintegral_ageμ hc a (f := N'.indicator (1 : Coord → ℝ≥0∞)) hI
  rw [lintegral_indicator_one hN'm, hN'0] at h
  have hf0 : ∫⁻ p in Ioi (0 : ℝ) ×ˢ UnforcedLeray.Axi.qCell c,
      ENNReal.ofReal (c⁻¹ * p.1 ^ a) * N'.indicator (1 : Coord → ℝ≥0∞) p = 0 := h.symm
  have hm : Measurable fun p : Coord =>
      ENNReal.ofReal (c⁻¹ * p.1 ^ a) * N'.indicator (1 : Coord → ℝ≥0∞) p := hw.mul hI
  have hf := (lintegral_eq_zero_iff hm).1 hf0
  have hmem : ∀ᵐ p ∂(volume.restrict (Ioi (0 : ℝ) ×ˢ UnforcedLeray.Axi.qCell c)),
      p ∈ Ioi (0 : ℝ) ×ˢ UnforcedLeray.Axi.qCell c := ae_restrict_mem hS
  have hae : ∀ᵐ p ∂(volume.restrict (Ioi (0 : ℝ) ×ˢ UnforcedLeray.Axi.qCell c)),
      p ∉ N' := by
    filter_upwards [hf, hmem] with p hp hpS
    intro hpN
    have hpos : 0 < p.1 := hpS.1
    have hval : ENNReal.ofReal (c⁻¹ * p.1 ^ a) * N'.indicator (1 : Coord → ℝ≥0∞) p = 0 := hp
    rw [Set.indicator_of_mem hpN, Pi.one_apply, mul_one] at hval
    have hwpos : 0 < c⁻¹ * p.1 ^ a :=
      mul_pos (inv_pos.2 hc) (Real.rpow_pos_of_pos hpos a)
    exact (ENNReal.ofReal_pos.2 hwpos).ne' hval
  have hzero : (volume.restrict (Ioi (0 : ℝ) ×ˢ UnforcedLeray.Axi.qCell c)) N' = 0 :=
    measure_eq_zero_iff_ae_notMem.2 hae
  rw [Measure.restrict_apply' hS] at hzero
  refine measure_mono_null ?_ hzero
  intro x hx
  exact ⟨hNN' hx.1, hx.2⟩

end UnforcedLeray.Short.IIb.NvCNorm
