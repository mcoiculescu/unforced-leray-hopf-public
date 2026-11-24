import UnforcedLeray.Short.PartIIa.Sub.F03_1

/-!
# Part II-a, task `PartII-a:F03/1/1`: representatives are locally integrable

Target: `UnforcedLeray.Short.PartIIa.RepLocInt` (defined in `Sub/F03_1.lean`).
Source of record: `the November 2 reference manuscript`, lines 1431-1434.

Route. For a compact `K`, the time coordinate is bounded by some `R` on `K`. Then
`lintegral_rep` with `m = 1_{[-R,R]}` and `lintegral_window_lt_top` give
`∫⁻ p in K, ‖W p‖ₑ ^ r < ∞`. The inequality `x ≤ 1 + x ^ r` (valid for `1 ≤ r`) and
`volume K < ∞` then make `W` integrable on `K`, hence locally integrable. For the second
clause, `dotL` is a bounded bilinear map and `G` is bounded with compact support.

Helper prefix: `rli`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.PhaseSpace UnforcedLeray.Short.PartIIa.Rep

/-- For `1 ≤ s` and `x : ℝ≥0∞`, `x ≤ 1 + x ^ s`. -/
theorem rliEnorm_le (s : ℝ) (hs : 1 ≤ s) (x : ℝ≥0∞) : x ≤ 1 + x ^ s := by
  rcases le_total x 1 with h | h
  · exact h.trans le_self_add
  · calc x = x ^ (1 : ℝ) := (ENNReal.rpow_one x).symm
      _ ≤ x ^ s := ENNReal.rpow_le_rpow_of_exponent_le h hs
      _ ≤ 1 + x ^ s := le_add_self

/-- A representative is integrable on every compact set. -/
theorem rliIntegrableOn (r : ℝ≥0∞) [hr1 : Fact (1 ≤ r)] (hr : r ≠ ⊤) (P : ℝ) [Fact (0 < P)]
    (w : Yq P r) (W : ℝ × Space → CVec3) (hW : IsRep w W) (K : Set (ℝ × Space))
    (hK : IsCompact K) : IntegrableOn W K volume := by
  have h1r : (1 : ℝ≥0∞) ≤ r := hr1.out
  have hs1 : (1 : ℝ) ≤ r.toReal := by
    have := ENNReal.toReal_mono hr h1r
    rwa [ENNReal.toReal_one] at this
  -- the time coordinate is bounded on `K`
  obtain ⟨R, hR⟩ := hK.exists_bound_of_continuousOn continuous_fst.norm.continuousOn
  have hKsub : ∀ p ∈ K, p.1 ∈ Icc (-R) R := by
    intro p hp
    have h2 : |p.1| ≤ R := by simpa [Real.norm_eq_abs] using hR p hp
    exact Set.mem_Icc.2 (abs_le.1 h2)
  -- window bound on `[-R, R]`
  have hwin : ∫⁻ t in Icc (-R) R, ‖w ((0 + t : ℝ) : AddCircle P)‖ₑ ^ r.toReal < ⊤ :=
    lintegral_window_lt_top hr w 0 (-R) R
  simp only [zero_add] at hwin
  have hRHS : ∫⁻ t, (Icc (-R) R).indicator (fun _ : ℝ => (1 : ℝ≥0∞)) t *
      ‖w (t : AddCircle P)‖ₑ ^ r.toReal < ⊤ := by
    have hpt : ∀ t : ℝ, (Icc (-R) R).indicator (fun _ : ℝ => (1 : ℝ≥0∞)) t *
        ‖w (t : AddCircle P)‖ₑ ^ r.toReal =
        (Icc (-R) R).indicator (fun t : ℝ => ‖w (t : AddCircle P)‖ₑ ^ r.toReal) t := by
      intro t
      by_cases ht : t ∈ Icc (-R) R
      · simp [Set.indicator_of_mem ht]
      · simp [Set.indicator_of_notMem ht]
    simp_rw [hpt]
    rw [lintegral_indicator measurableSet_Icc]
    exact hwin
  -- the pulled-back identity from `lintegral_rep`
  have hkey := lintegral_rep hr hW 0 (m := (Icc (-R) R).indicator (fun _ : ℝ => (1 : ℝ≥0∞)))
    (measurable_const.indicator measurableSet_Icc)
  simp only [zero_add, Prod.mk.eta] at hkey
  have hKmeas : MeasurableSet K := hK.isClosed.measurableSet
  have hfin : ∫⁻ p in K, ‖W p‖ₑ ^ r.toReal < ⊤ := by
    calc ∫⁻ p in K, ‖W p‖ₑ ^ r.toReal
        = ∫⁻ p, K.indicator (fun p => ‖W p‖ₑ ^ r.toReal) p :=
          (lintegral_indicator hKmeas _).symm
      _ ≤ ∫⁻ p, (Icc (-R) R).indicator (fun _ : ℝ => (1 : ℝ≥0∞)) p.1 * ‖W p‖ₑ ^ r.toReal := by
          apply lintegral_mono
          intro p
          dsimp only
          by_cases hp : p ∈ K
          · rw [Set.indicator_of_mem hp, Set.indicator_of_mem (hKsub p hp)]
            simp
          · rw [Set.indicator_of_notMem hp]
            exact zero_le
      _ = ∫⁻ t, (Icc (-R) R).indicator (fun _ : ℝ => (1 : ℝ≥0∞)) t *
            ‖w (t : AddCircle P)‖ₑ ^ r.toReal := hkey
      _ < ⊤ := hRHS
  have hvol : volume K < ⊤ := hK.measure_lt_top
  have hone : ∫⁻ _p in K, (1 : ℝ≥0∞) < ⊤ := by
    rw [lintegral_one, Measure.restrict_apply_univ]
    exact hvol
  unfold IntegrableOn Integrable
  refine ⟨hW.meas.aestronglyMeasurable, hasFiniteIntegral_iff_enorm.2 ?_⟩
  calc ∫⁻ p in K, ‖W p‖ₑ ≤ ∫⁻ p in K, (1 + ‖W p‖ₑ ^ r.toReal) :=
        lintegral_mono (fun p => rliEnorm_le _ hs1 _)
    _ = (∫⁻ p in K, (1 : ℝ≥0∞)) + ∫⁻ p in K, ‖W p‖ₑ ^ r.toReal :=
        lintegral_add_left measurable_const _
    _ < ⊤ := ENNReal.add_lt_top.2 ⟨hone, hfin⟩

/-- For a representative `W` and a continuous compactly supported `G`, `p ↦ G p · W p` is
integrable. -/
theorem rliDotIntegrable (r : ℝ≥0∞) [hr1 : Fact (1 ≤ r)] (hr : r ≠ ⊤) (P : ℝ) [Fact (0 < P)]
    (w : Yq P r) (W : ℝ × Space → CVec3) (hW : IsRep w W) (G : ℝ × Space → CVec3)
    (hG : Continuous G) (hGc : HasCompactSupport G) :
    Integrable (fun p => dotL (G p) (W p)) volume := by
  have hKc : IsCompact (tsupport G) := hGc.isCompact
  have hWK : IntegrableOn W (tsupport G) volume :=
    rliIntegrableOn r hr P w W hW (tsupport G) hKc
  have hKm : MeasurableSet (tsupport G) := hKc.isClosed.measurableSet
  obtain ⟨M, hM⟩ := hG.bounded_above_of_compact_support hGc
  have hind : Integrable ((tsupport G).indicator fun p => ‖W p‖) volume :=
    (integrable_indicator_iff hKm).2 (Integrable.norm hWK)
  refine Integrable.mono' (hind.const_mul (‖dotL‖ * M)) ?_ ?_
  · exact dotL.aestronglyMeasurable_comp₂ hG.aestronglyMeasurable hW.meas.aestronglyMeasurable
  · refine Filter.Eventually.of_forall (fun p => ?_)
    by_cases hp : p ∈ tsupport G
    · rw [Set.indicator_of_mem hp]
      calc ‖dotL (G p) (W p)‖ ≤ ‖dotL‖ * ‖G p‖ * ‖W p‖ := dotL.le_opNorm₂ (G p) (W p)
        _ ≤ ‖dotL‖ * M * ‖W p‖ :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hM p) (norm_nonneg dotL))
              (norm_nonneg (W p))
    · rw [image_eq_zero_of_notMem_tsupport hp, Set.indicator_of_notMem hp]
      simp

/-- **Representatives are locally integrable** (task `PartII-a:F03/1/1`). -/
theorem repLocInt : UnforcedLeray.Short.PartIIa.RepLocInt := by
  unfold RepLocInt
  intro r hr hr_top P hP w W hW
  refine ⟨?_, fun G hG hGc => rliDotIntegrable r hr_top P w W hW G hG hGc⟩
  exact locallyIntegrable_iff.2 (fun K hK => rliIntegrableOn r hr_top P w W hW K hK)

end UnforcedLeray.Short.PartIIa
