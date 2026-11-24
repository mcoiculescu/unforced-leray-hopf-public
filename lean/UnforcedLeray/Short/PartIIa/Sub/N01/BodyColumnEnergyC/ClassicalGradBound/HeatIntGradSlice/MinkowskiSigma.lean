import UnforcedLeray.Short.PartIIa.Sub.N01.BodyColumnEnergyC.ClassicalGradBound.HeatIntGradSlice.MinkowskiL2Slice

/-!
# Minkowski's integral inequality (squared) for a σ-finite measure `ν` (helper for `heatIntGradSlice`)
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIa.N01.MinkowskiL2

theorem minkowski_sq_sigmaFinite {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite μ] [SigmaFinite ν]
    (H : α → β → ℝ≥0∞) (hH : Measurable (fun p : α × β => H p.1 p.2)) :
    ∫⁻ y, (∫⁻ x, H x y ∂μ) ^ 2 ∂ν ≤
      (∫⁻ x, (∫⁻ y, H x y ^ 2 ∂ν) ^ (1 / 2 : ℝ) ∂μ) ^ 2 := by
  have hGm : Measurable (fun y : β => (∫⁻ x, H x y ∂μ) ^ 2) :=
    (hH.lintegral_prod_left').pow_const 2
  set A : ℕ → Set β := spanningSets ν with hA
  have hAm : ∀ n, MeasurableSet (A n) := measurableSet_spanningSets ν
  have hAmono : Monotone A := monotone_spanningSets ν
  have hAU : ⋃ n, A n = univ := iUnion_spanningSets ν
  have key : ∀ n, ∫⁻ y in A n, (∫⁻ x, H x y ∂μ) ^ 2 ∂ν ≤
      (∫⁻ x, (∫⁻ y, H x y ^ 2 ∂ν) ^ (1 / 2 : ℝ) ∂μ) ^ 2 := by
    intro n
    have : IsFiniteMeasure (ν.restrict (A n)) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact measure_spanningSets_lt_top ν n⟩
    refine (minkowski_sq_lintegral (μ := μ) (ν := ν.restrict (A n)) H hH).trans ?_
    gcongr with x
    exact Measure.restrict_le_self
  have hind : ∀ y, (∫⁻ x, H x y ∂μ) ^ 2 = ⨆ n, (A n).indicator
      (fun y => (∫⁻ x, H x y ∂μ) ^ 2) y := by
    intro y
    obtain ⟨n, hn⟩ : ∃ n, y ∈ A n := by
      have : y ∈ ⋃ n, A n := by rw [hAU]; trivial
      simpa using this
    apply le_antisymm
    · exact le_iSup_of_le n (by rw [indicator_of_mem hn])
    · refine iSup_le fun m => ?_
      by_cases h : y ∈ A m
      · rw [indicator_of_mem h]
      · rw [indicator_of_notMem h]; exact bot_le
  calc ∫⁻ y, (∫⁻ x, H x y ∂μ) ^ 2 ∂ν
      = ∫⁻ y, ⨆ n, (A n).indicator (fun y => (∫⁻ x, H x y ∂μ) ^ 2) y ∂ν :=
        lintegral_congr hind
    _ = ⨆ n, ∫⁻ y, (A n).indicator (fun y => (∫⁻ x, H x y ∂μ) ^ 2) y ∂ν := by
        apply lintegral_iSup
        · intro n; exact hGm.indicator (hAm n)
        · intro a b hab y
          exact indicator_le_indicator_of_subset (hAmono hab) (fun _ => bot_le) y
    _ ≤ _ := iSup_le fun n => by
        rw [lintegral_indicator (hAm n)]
        exact key n

end UnforcedLeray.Short.PartIIa.N01.MinkowskiL2
