import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T13_1_4_2
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.CylHeatMaxReg.Periodic.WindowUpper.Strip

/-!
# Part II-b, task `PartII-b:T13/1/4/2/3` (`ChmWindowUpper`): upper window bound

Source `the November 2 reference manuscript` lines 1933-1935 and 1377-1424.
The `volume` integral over `m` cells of an a.e. `q`-periodic function is `m c` times the `cylMeas`
integral (`WinStrip.lintegral_coord_strip`); then `‖h g‖ ≤ b ‖g‖` and take `r`-th roots.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

open MeasureTheory Set Filter Topology
open scoped ENNReal

theorem chmWindowUpper : UnforcedLeray.Short.IIb.ChmWindowUpper := by
  intro r hr c hc g hg hper h b a m hh hb hsupp
  have hr0 : 0 < r := by linarith
  have hb0 : 0 ≤ b := (abs_nonneg _).trans (hb 0)
  have hp0 : ENNReal.ofReal r ≠ 0 := (ENNReal.ofReal_pos.2 hr0).ne'
  have hpt : ENNReal.ofReal r ≠ ⊤ := ENNReal.ofReal_ne_top
  have hpr : (ENNReal.ofReal r).toReal = r := ENNReal.toReal_ofReal hr0.le
  set F : Coord → ℝ≥0∞ := fun x => ‖g x‖ₑ ^ r with hFdef
  have hFm : AEMeasurable F volume := hg.enorm.pow_const r
  have hFper : ∀ᵐ x : Coord ∂volume, F (qShift c x) = F x := by
    filter_upwards [hper] with x hx
    simp only [hFdef, hx]
  set E : Set Coord := {x : Coord | x.2.1 ∈ Ico a (a + (m : ℝ) * c)} with hEdef
  have hE : MeasurableSet E := (measurableSet_Ico).preimage (measurable_fst.comp measurable_snd)
  have hstrip := WinStrip.lintegral_coord_strip hc m a hFm hFper
  have hnull : ∀ᵐ x : Coord ∂volume, x.2.1 ≠ a + (m : ℝ) * c := by
    rw [ae_iff]
    have : {x : Coord | ¬ x.2.1 ≠ a + (m : ℝ) * c} =
        (univ : Set ℝ) ×ˢ (({a + (m : ℝ) * c} : Set ℝ) ×ˢ (univ : Set ℝ)) := by
      ext x; simp
    rw [this, Measure.volume_eq_prod, Measure.prod_prod, Measure.volume_eq_prod, Measure.prod_prod]
    simp
  have hbd : ∀ᵐ x : Coord ∂volume, ‖(h x.2.1 : ℂ) * g x‖ₑ ^ r ≤
      E.indicator (fun x => ENNReal.ofReal b ^ r * F x) x := by
    filter_upwards [hnull] with x hx
    by_cases hxE : x ∈ E
    · rw [Set.indicator_of_mem hxE]
      have h1 : ‖(h x.2.1 : ℂ) * g x‖ₑ ≤ ENNReal.ofReal b * ‖g x‖ₑ := by
        rw [enorm_mul]
        gcongr
        rw [← ofReal_norm_eq_enorm, Complex.norm_real, Real.norm_eq_abs]
        exact ENNReal.ofReal_le_ofReal (hb x.2.1)
      calc ‖(h x.2.1 : ℂ) * g x‖ₑ ^ r ≤ (ENNReal.ofReal b * ‖g x‖ₑ) ^ r :=
            ENNReal.rpow_le_rpow h1 hr0.le
        _ = ENNReal.ofReal b ^ r * F x := ENNReal.mul_rpow_of_nonneg _ _ hr0.le
    · have hz : h x.2.1 = 0 := by
        apply hsupp
        simp only [hEdef, mem_setOf_eq, mem_Ico, not_and_or, not_le, not_lt] at hxE
        rcases hxE with h1 | h1
        · exact Or.inl h1
        · exact Or.inr (lt_of_le_of_ne h1 (Ne.symm hx))
      rw [hz]
      simp [ENNReal.zero_rpow_of_pos hr0]
  have hmain : ∫⁻ x, ‖(h x.2.1 : ℂ) * g x‖ₑ ^ r ≤
      ENNReal.ofReal b ^ r * (((m : ℝ≥0∞) * ENNReal.ofReal c) * ∫⁻ x, F x ∂(cylMeas c)) := by
    calc ∫⁻ x, ‖(h x.2.1 : ℂ) * g x‖ₑ ^ r
        ≤ ∫⁻ x, E.indicator (fun x => ENNReal.ofReal b ^ r * F x) x := lintegral_mono_ae hbd
      _ = ∫⁻ x in E, ENNReal.ofReal b ^ r * F x := lintegral_indicator hE _
      _ = ENNReal.ofReal b ^ r * ∫⁻ x in E, F x :=
          lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hr0.le ENNReal.ofReal_ne_top)
      _ = _ := by rw [hstrip]
  have hnm : (m : ℝ≥0∞) * ENNReal.ofReal c = ENNReal.ofReal ((m : ℝ) * c) := by
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg m), ENNReal.ofReal_natCast]
  unfold cylNorm
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt, hpr,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt, hpr]
  have hroot := ENNReal.rpow_le_rpow hmain (show (0 : ℝ) ≤ 1 / r by positivity)
  refine hroot.trans (le_of_eq ?_)
  have hmc : 0 ≤ (m : ℝ) * c := mul_nonneg (Nat.cast_nonneg m) hc.le
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
    ← ENNReal.rpow_mul, mul_one_div_cancel hr0.ne', ENNReal.rpow_one, hnm,
    ENNReal.ofReal_rpow_of_nonneg hmc (by positivity), ENNReal.ofReal_mul hb0, mul_assoc]

end UnforcedLeray.Short.IIb
