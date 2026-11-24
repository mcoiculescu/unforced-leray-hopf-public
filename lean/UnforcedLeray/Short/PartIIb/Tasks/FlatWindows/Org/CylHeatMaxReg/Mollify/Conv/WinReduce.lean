import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T13_1_4_3_3

/-!
# Part II-b, task `PartII-b:T13/1/4/3/3/3` (`chmWinReduce`): reduction to the whole space

Source: `the November 2 reference manuscript` (SP) lines 1933-1935. For `‖y‖ ≤ 1`
and `x` in the cell strip `{x.2.1 ∈ [-c/2, c/2)}`, the points `x` and `x - y` lie in the window
`|q| ≤ c/2 + 1`, so the translate differences of `g` and of its window truncation agree on the
cell. Since `cylMeas c = c⁻¹ • volume.restrict (univ ×ˢ cell c)`, the `cylMeas`-norm is bounded by
`c⁻¹^(1/r)` times the `volume`-norm of the restricted difference.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

open MeasureTheory Set Filter
open scoped ENNReal

/-- The cell strip `univ ×ˢ cell c` of `Coord`, as a measure restriction of `cylMeas c`. -/
theorem chmRed_cylMeas_eq (c : ℝ) :
    cylMeas c = ENNReal.ofReal c⁻¹ •
      (volume : Measure Coord).restrict ((Set.univ : Set ℝ) ×ˢ UnforcedLeray.Cyl.cell c) := by
  unfold cylMeas UnforcedLeray.Cyl.avgμ UnforcedLeray.Cyl.cellμ
  rw [Measure.prod_smul_right]
  congr 1
  have hcoord : (volume : Measure Coord) = (volume : Measure ℝ).prod (volume : Measure (ℝ × ℝ)) :=
    Measure.volume_eq_prod _ _
  rw [hcoord, ← Measure.prod_restrict, Measure.restrict_univ]

theorem chmWinReduce : UnforcedLeray.Short.IIb.ChmWinReduce := by
  intro r hr c hc g y hy
  have hr0 : 0 < r := by linarith
  have hpne : ENNReal.ofReal r ≠ ⊤ := ENNReal.ofReal_ne_top
  have hSm : MeasurableSet ((Set.univ : Set ℝ) ×ˢ UnforcedLeray.Cyl.cell c) := by
    unfold UnforcedLeray.Cyl.cell
    exact MeasurableSet.univ.prod (measurableSet_Ico.prod MeasurableSet.univ)
  have hyq : |y.2.1| ≤ 1 := by
    have h1 : ‖y.2.1‖ ≤ ‖y‖ := (norm_fst_le y.2).trans (norm_snd_le y)
    rw [Real.norm_eq_abs] at h1
    linarith
  -- pointwise agreement on the cell strip
  have hpt : ∀ x ∈ (Set.univ : Set ℝ) ×ˢ UnforcedLeray.Cyl.cell c,
      chmWinR (c / 2 + 1) g (x - y) - chmWinR (c / 2 + 1) g x = g (x - y) - g x := by
    intro x hx
    have h2 : x.2 ∈ Set.Ico (-c / 2) (c / 2) ×ˢ (Set.univ : Set ℝ) := (Set.mem_prod.mp hx).2
    have hx' : x.2.1 ∈ Set.Ico (-c / 2) (c / 2) := (Set.mem_prod.mp h2).1
    have hxq : |x.2.1| ≤ c / 2 := by
      rw [abs_le]
      exact ⟨by linarith [hx'.1], by linarith [hx'.2]⟩
    have e : (x - y).2.1 = x.2.1 - y.2.1 := rfl
    have hdq : |(x - y).2.1| ≤ c / 2 + 1 := by
      obtain ⟨h1, h2'⟩ := abs_le.mp hxq
      obtain ⟨h3, h4⟩ := abs_le.mp hyq
      rw [e, abs_le]
      constructor <;> linarith
    have hqx : |x.2.1| ≤ c / 2 + 1 := by linarith
    simp only [chmWinR, if_pos hdq, if_pos hqx]
  have hfeq : (fun x => g (x - y) - g x) =ᵐ[(volume : Measure Coord).restrict
      ((Set.univ : Set ℝ) ×ˢ UnforcedLeray.Cyl.cell c)]
      (fun x => chmWinR (c / 2 + 1) g (x - y) - chmWinR (c / 2 + 1) g x) :=
    ae_restrict_of_forall_mem hSm fun x hx => (hpt x hx).symm
  have hexp : (1 / ENNReal.ofReal r).toReal = 1 / r := by
    rw [ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofReal hr0.le]
  have hcyl : cylNorm c r (fun x => g (x - y) - g x) = ENNReal.ofReal c⁻¹ ^ (1 / r) *
      eLpNorm (fun x => g (x - y) - g x) (ENNReal.ofReal r)
        ((volume : Measure Coord).restrict ((Set.univ : Set ℝ) ×ˢ UnforcedLeray.Cyl.cell c)) := by
    show eLpNorm _ (ENNReal.ofReal r) (cylMeas c) = _
    rw [chmRed_cylMeas_eq c, eLpNorm_smul_measure_of_ne_top hpne, smul_eq_mul, hexp]
  rw [hcyl]
  apply mul_le_mul_of_nonneg_left _ zero_le
  rw [eLpNorm_congr_ae hfeq]
  exact eLpNorm_mono_measure _ Measure.restrict_le_self

#print axioms UnforcedLeray.Short.IIb.chmWinReduce

end UnforcedLeray.Short.IIb
