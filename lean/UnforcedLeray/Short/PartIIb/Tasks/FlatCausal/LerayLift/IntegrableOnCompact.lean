import UnforcedLeray.Short.PartIIb.Sub.T12_2_5
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.LerayLift.WindowCellFinite
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.LerayLift.WindowStripFinite

/-!
# Part II-b, task `PartII-b:T12/2/5/5`: local integrability of `H_r` (`1 < r`)

Source of record: `the November 2 reference manuscript` (SP 1901-1903, 1923-1926). Proves
the Prop `IntegrableOnCompact` of `Sub/T12_2_5.lean`: a compact `K ⊆ {s > 0}` lies in a box
`B = [a, b] × [-Q, Q] × [-L, L]` with `a > 0`, on which `G ∈ L^r` (`WindowCellFinite`,
`WindowStripFinite`), hence `G ∈ L^1` on the finite-measure set `B`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb.LerayLiftSub

theorem integrableOnCompact_proof : UnforcedLeray.Short.IIb.LerayLiftSub.IntegrableOnCompact := by
  intro c r G hc hr hGs hper hN K hK hKsub
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · exact integrableOn_empty
  have hr0 : 0 < r := lt_trans zero_lt_one hr
  -- bounds of K in the age, q and eta directions
  obtain ⟨x0, hx0K, hmin⟩ := hK.exists_isMinOn hKne
    (continuous_fst : Continuous fun x : Coord => x.1).continuousOn
  obtain ⟨x1, hx1K, hmax⟩ := hK.exists_isMaxOn hKne
    (continuous_fst : Continuous fun x : Coord => x.1).continuousOn
  obtain ⟨y0, hy0K, hymax⟩ := hK.exists_isMaxOn hKne
    (f := fun x : Coord => |x.2.1|) (continuous_abs.comp (continuous_fst.comp continuous_snd)).continuousOn
  obtain ⟨z0, hz0K, hzmax⟩ := hK.exists_isMaxOn hKne
    (f := fun x : Coord => |x.2.2|) (continuous_abs.comp (continuous_snd.comp continuous_snd)).continuousOn
  have ha : 0 < x0.1 := (hKsub hx0K).1
  set a : ℝ := x0.1 with ha_def
  set b : ℝ := x1.1 with hb_def
  set Q : ℝ := |y0.2.1| with hQ_def
  set L : ℝ := |z0.2.2| with hL_def
  set B : Set Coord := Icc a b ×ˢ (Icc (-Q) Q ×ˢ Icc (-L) L) with hB_def
  have hKB : K ⊆ B := by
    intro x hx
    have h1 : a ≤ x.1 := isMinOn_iff.1 hmin x hx
    have h2 : x.1 ≤ b := isMaxOn_iff.1 hmax x hx
    have h3 : |x.2.1| ≤ Q := isMaxOn_iff.1 hymax x hx
    have h4 : |x.2.2| ≤ L := isMaxOn_iff.1 hzmax x hx
    exact ⟨⟨h1, h2⟩, abs_le.1 h3, abs_le.1 h4⟩
  have hBc : IsCompact B := isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hBfin : volume B < ⊤ := hBc.measure_lt_top
  -- finiteness of the L^r mass on the strip containing B
  have hcell := UnforcedLeray.Short.IIb.LerayLiftSub.windowCellFinite_proof c r G hc hr0 hGs
    (by simpa [UnforcedLeray.Short.IIb.hNorm] using hN) a b ha
  have hstrip := UnforcedLeray.Short.IIb.windowStripFinite_proof c r G hc hGs hper a b hcell Q
  have hBsub : B ⊆ Icc a b ×ˢ (Icc (-Q) Q ×ˢ (univ : Set ℝ)) := by
    intro x hx
    exact ⟨hx.1, hx.2.1, trivial⟩
  have hBint : ∫⁻ x in B, ‖G x‖ₑ ^ r < ⊤ :=
    lt_of_le_of_lt (lintegral_mono_set hBsub) hstrip
  -- G is in L^r on B
  have hp0 : ENNReal.ofReal r ≠ 0 := (ENNReal.ofReal_pos.2 hr0).ne'
  have hpt : ENNReal.ofReal r ≠ ⊤ := ENNReal.ofReal_ne_top
  have hmem : MemLp G (ENNReal.ofReal r) (volume.restrict B) := by
    refine ⟨hGs.aestronglyMeasurable, ?_⟩
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt, ENNReal.toReal_ofReal hr0.le]
    exact ENNReal.rpow_lt_top_of_nonneg (by positivity) hBint.ne
  have hfin : IsFiniteMeasure (volume.restrict B) := isFiniteMeasure_restrict.2 hBfin.ne
  have hI : IntegrableOn G B :=
    hmem.integrable (ENNReal.one_le_ofReal.2 hr.le)
  exact hI.mono_set hKB

end UnforcedLeray.Short.IIb.LerayLiftSub
