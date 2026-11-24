import UnforcedLeray.Short.PartIIa.Sub.F03_1

/-!
# Part II-a, task `PartII-a:F03/1/2`: unfolding the pairing with a periodized test

Target: `UnforcedLeray.Short.PartIIa.periodizedPairing : PeriodizedPairing` (the Prop is defined in
`Sub/F03_1.lean`, line 70).
Source of record: `the November 2 reference manuscript`, lines 1431-1434.

Route. If `A ≤ B`, the unfolding lemma `PhaseTrace.phasePair_perT`
(`Lib/PhaseTrace/Periodize.lean`) gives `⟪perT P G, w⟫ = P⁻¹ ∫_ℝ H(t) dt` with
`H(t) = ∫ G(t, y) · w(t)(y) dy` (`pairH`). If `A > B`, the set `Icc A B` is empty, so `G` vanishes
on all of `ℝ × ℝ³` and `TimeSupp 0 0 G` holds; then `A = B = 0` is used. In both cases Fubini
(`integral_prod`, from the integrability hypothesis) rewrites `∫_ℝ H` as `∫_{ℝ × ℝ³} G · W`,
using `IsRep.slice` (for a.e. `t`, `W(t, ·) = w(t)` a.e. on `ℝ³`) and `pairH_eq`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.PhaseSpace UnforcedLeray.PhaseTrace UnforcedLeray.Short.PartIIa.Rep

/-- **Periodized pairing** (task `PartII-a:F03/1/2`): for a smooth test `G` with bounded spatial
support, vanishing outside a bounded phase window, and integrable against a representative `W`
of `w`, the pairing of `perT P G` with `w` is `P⁻¹ ∫_{ℝ × ℝ³} G · W`. -/
theorem periodizedPairing : PeriodizedPairing := by
  intro r hr1 hr P hP w W hW G A B hG hG0 hint
  obtain ⟨A', B', hAB', hG'⟩ : ∃ A' B' : ℝ, A' ≤ B' ∧ TimeSupp A' B' G := by
    by_cases hAB : A ≤ B
    · exact ⟨A, B, hAB, hG⟩
    · refine ⟨0, 0, le_refl _, ?_⟩
      intro τ y _
      exact hG τ y (fun hτ => hAB (hτ.1.trans hτ.2))
  rw [UnforcedLeray.PhaseTrace.phasePair_perT hG0 hAB' hG' w]
  congr 1
  rw [Measure.volume_eq_prod ℝ Space] at hint ⊢
  rw [integral_prod _ hint]
  refine integral_congr_ae ?_
  filter_upwards [hW.slice] with t ht
  rw [UnforcedLeray.PhaseTrace.pairH_eq]
  refine integral_congr_ae ?_
  filter_upwards [ht] with y hy
  have hy' : W (t, y) = (w (t : AddCircle P) : Space → CVec3) y := hy
  simp only [hy']
