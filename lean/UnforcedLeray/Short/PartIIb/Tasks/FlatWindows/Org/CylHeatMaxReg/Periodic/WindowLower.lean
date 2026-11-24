import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T13_1_4_2
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.CylHeatMaxReg.Periodic.WindowUpper.Strip

/-!
# Part II-b, task `PartII-b:T13/1/4/2/4` (`ChmWindowLower`): lower window bound

Source `the November 2 reference manuscript` lines 1933-1935 and 1377-1424.
The core `q ∈ (0, N c)` differs from the `N`-cell strip `[0, N c)` by a null set; the strip identity
for a.e. periodic functions (`WinStrip.lintegral_coord_strip`) gives the cell norm.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

open MeasureTheory Set Filter Topology
open scoped ENNReal

theorem chmWindowLower : UnforcedLeray.Short.IIb.ChmWindowLower := by
  intro r hr c hc N g G hg hper hG hGg
  have hr0 : 0 < r := by linarith
  have hp0 : ENNReal.ofReal r ≠ 0 := (ENNReal.ofReal_pos.2 hr0).ne'
  have hpt : ENNReal.ofReal r ≠ ⊤ := ENNReal.ofReal_ne_top
  have hpr : (ENNReal.ofReal r).toReal = r := ENNReal.toReal_ofReal hr0.le
  set F : Coord → ℝ≥0∞ := fun x => ‖g x‖ₑ ^ r with hFdef
  have hFm : AEMeasurable F volume := hg.enorm.pow_const r
  have hFper : ∀ᵐ x : Coord ∂volume, F (qShift c x) = F x := by
    filter_upwards [hper] with x hx
    simp only [hFdef, hx]
  set E : Set Coord := {x : Coord | x.2.1 ∈ Ico (0 : ℝ) (0 + (N : ℝ) * c)} with hEdef
  have hstrip := WinStrip.lintegral_coord_strip hc N 0 hFm hFper
  have hcoreM : MeasurableSet (chmCore c N) :=
    (measurableSet_Ioo).preimage (measurable_fst.comp measurable_snd)
  have hZ : (volume : Measure Coord) {x : Coord | x.2.1 = 0} = 0 := by
    have : {x : Coord | x.2.1 = 0} =
        (univ : Set ℝ) ×ˢ (({0} : Set ℝ) ×ˢ (univ : Set ℝ)) := by
      ext x; simp
    rw [this, Measure.volume_eq_prod, Measure.prod_prod, Measure.volume_eq_prod, Measure.prod_prod]
    simp
  have hsub : E ⊆ chmCore c N ∪ {x : Coord | x.2.1 = 0} := by
    intro x hx
    simp only [hEdef, mem_setOf_eq, mem_Ico, zero_add] at hx
    by_cases h0 : x.2.1 = 0
    · exact Or.inr h0
    · exact Or.inl ⟨lt_of_le_of_ne hx.1 (Ne.symm h0), hx.2⟩
  have h1 : ∫⁻ x in E, F x ≤ ∫⁻ x in chmCore c N, F x := by
    calc ∫⁻ x in E, F x ≤ ∫⁻ x in chmCore c N ∪ {x : Coord | x.2.1 = 0}, F x :=
          lintegral_mono_set hsub
      _ ≤ (∫⁻ x in chmCore c N, F x) + ∫⁻ x in {x : Coord | x.2.1 = 0}, F x :=
          lintegral_union_le (μ := volume) F (chmCore c N) {x : Coord | x.2.1 = 0}
      _ = ∫⁻ x in chmCore c N, F x := by
          rw [Measure.restrict_eq_zero.2 hZ]; simp
  have h2 : ∫⁻ x in chmCore c N, F x = ∫⁻ x in chmCore c N, ‖G x‖ₑ ^ r := by
    refine lintegral_congr_ae ?_
    filter_upwards [hGg] with x hx
    simp only [hFdef, hx]
  have h3 : ∫⁻ x in chmCore c N, ‖G x‖ₑ ^ r ≤ ∫⁻ x, ‖G x‖ₑ ^ r :=
    setLIntegral_le_lintegral _ _
  have hmain : ((N : ℝ≥0∞) * ENNReal.ofReal c) * ∫⁻ x, F x ∂(cylMeas c) ≤
      ∫⁻ x, ‖G x‖ₑ ^ r := by
    rw [← hstrip]; exact h1.trans (h2.le.trans h3)
  have hnm : (N : ℝ≥0∞) * ENNReal.ofReal c = ENNReal.ofReal ((N : ℝ) * c) := by
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg N), ENNReal.ofReal_natCast]
  have hNc : 0 ≤ (N : ℝ) * c := mul_nonneg (Nat.cast_nonneg N) hc.le
  unfold cylNorm
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt, hpr,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt, hpr]
  have hroot := ENNReal.rpow_le_rpow hmain (show (0 : ℝ) ≤ 1 / r by positivity)
  refine le_trans (le_of_eq ?_) hroot
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), hnm,
    ENNReal.ofReal_rpow_of_nonneg hNc (by positivity)]

end UnforcedLeray.Short.IIb
