import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T12_1_4_2

/-!
# Part II-b, task `PartII-b:T12/1/4/2/5` (`pplAvg`): from the window bound to the cell average.

The window `W_1 = [-c, c) × ℝ` is the union of two period strips, so for a `c`-periodic `Gp` the
window `r`-th lower integral is twice the cell one, while `avgμ c` carries the factor `c⁻¹`; the
factor `(2c)^{1/r}` of the window bound cancels.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-- Lower integral over `n` consecutive period strips of a periodic function. -/
theorem lintegral_strips_eq {c : ℝ} (hc : 0 < c) {f : ℝ × ℝ → ℝ≥0∞}
    (hf : UnforcedLeray.Cyl.IsPeriodic c f) (n : ℕ) (a : ℝ) :
    ∫⁻ z in Ico a (a + (n : ℝ) * c) ×ˢ (univ : Set ℝ), f z =
      (n : ℝ≥0∞) * ∫⁻ z in UnforcedLeray.Cyl.cell c, f z := by
  induction n generalizing a with
  | zero => simp
  | succ n ih =>
    have hnc : (0 : ℝ) ≤ (n : ℝ) * c := mul_nonneg (Nat.cast_nonneg n) hc.le
    have h1 : a ≤ a + (n : ℝ) * c := by linarith
    have h2 : a + (n : ℝ) * c ≤ a + (n : ℝ) * c + c := by linarith
    have e : a + ((n + 1 : ℕ) : ℝ) * c = a + (n : ℝ) * c + c := by push_cast; ring
    have hdisj : Disjoint (Ico a (a + (n : ℝ) * c) ×ˢ (univ : Set ℝ))
        (Ico (a + (n : ℝ) * c) (a + (n : ℝ) * c + c) ×ˢ (univ : Set ℝ)) := by
      rw [Set.disjoint_left]
      intro z hz1 hz2
      simp only [Set.mem_prod, Set.mem_Ico, Set.mem_univ, and_true] at hz1 hz2
      linarith [hz1.2, hz2.1]
    rw [e, ← Set.Ico_union_Ico_eq_Ico h1 h2, Set.union_prod,
      MeasureTheory.lintegral_union (measurableSet_Ico.prod MeasurableSet.univ) hdisj,
      ih a, UnforcedLeray.Cyl.lintegral_strip_eq_cell hc hf]
    push_cast
    ring

/-- The window `W_1` as a strip of two periods. -/
theorem ppWindow_one_eq (c : ℝ) :
    ppWindow c 1 = Ico (-c) (-c + ((2 : ℕ) : ℝ) * c) ×ˢ (univ : Set ℝ) := by
  ext z
  simp only [ppWindow, Set.mem_setOf_eq, Set.mem_prod, Set.mem_Ico, Set.mem_univ, and_true,
    Nat.cast_one, Nat.cast_ofNat]
  constructor
  · intro h
    constructor <;> linarith [h.1, h.2]
  · intro h
    constructor <;> linarith [h.1, h.2]

theorem pplAvg : UnforcedLeray.Short.IIb.PPLAvg := by
  intro r C c F Gp hr hC hc hF hper hmeas hb
  have hr0 : 0 < r := by linarith
  have hpr : (ENNReal.ofReal r).toReal = r := ENNReal.toReal_ofReal hr0.le
  have hperF : UnforcedLeray.Cyl.IsPeriodic c (fun z : ℝ × ℝ => ‖Gp z‖ₑ ^ r) := fun z => by
    show ‖Gp (z.1 + c, z.2)‖ₑ ^ r = ‖Gp z‖ₑ ^ r
    rw [hper z]
  have hS := lintegral_strips_eq hc hperF 2 (-c)
  have hWin : ∫⁻ z in ppWindow c 1, ‖Gp z‖ₑ ^ r =
      2 * ∫⁻ z in UnforcedLeray.Cyl.cell c, ‖Gp z‖ₑ ^ r := by
    rw [ppWindow_one_eq, hS]
    norm_num
  have hA : ∫⁻ z, ‖Gp z‖ₑ ^ r ∂(UnforcedLeray.Cyl.avgμ c) =
      ENNReal.ofReal c⁻¹ * ∫⁻ z in UnforcedLeray.Cyl.cell c, ‖Gp z‖ₑ ^ r :=
    UnforcedLeray.Cyl.lintegral_avgμ _
  have hp0 : ENNReal.ofReal r ≠ 0 := (ENNReal.ofReal_pos.2 hr0).ne'
  have hpt : ENNReal.ofReal r ≠ ⊤ := ENNReal.ofReal_ne_top
  have eW : eLpNorm Gp (ENNReal.ofReal r) (volume.restrict (ppWindow c 1)) =
      (2 * ∫⁻ z in UnforcedLeray.Cyl.cell c, ‖Gp z‖ₑ ^ r) ^ (1 / r) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt, hpr, hWin]
  have eA : eLpNorm Gp (ENNReal.ofReal r) (UnforcedLeray.Cyl.avgμ c) =
      (ENNReal.ofReal c⁻¹ * ∫⁻ z in UnforcedLeray.Cyl.cell c, ‖Gp z‖ₑ ^ r) ^ (1 / r) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt, hpr, hA]
  have h2 : ENNReal.ofReal (2 * ((1 : ℕ) : ℝ) * c) * ENNReal.ofReal c⁻¹ = 2 := by
    rw [← ENNReal.ofReal_mul (mul_nonneg (by norm_num) hc.le)]
    rw [show 2 * ((1 : ℕ) : ℝ) * c * c⁻¹ = 2 by rw [Nat.cast_one]; field_simp]
    simp
  have hK : 2 * ∫⁻ z in UnforcedLeray.Cyl.cell c, ‖Gp z‖ₑ ^ r =
      ENNReal.ofReal (2 * ((1 : ℕ) : ℝ) * c) *
        (ENNReal.ofReal c⁻¹ * ∫⁻ z in UnforcedLeray.Cyl.cell c, ‖Gp z‖ₑ ^ r) := by
    rw [← mul_assoc, h2]
  have hsplit : (2 * ∫⁻ z in UnforcedLeray.Cyl.cell c, ‖Gp z‖ₑ ^ r) ^ (1 / r) =
      (ENNReal.ofReal (2 * ((1 : ℕ) : ℝ) * c)) ^ (1 / r) *
        (ENNReal.ofReal c⁻¹ * ∫⁻ z in UnforcedLeray.Cyl.cell c, ‖Gp z‖ₑ ^ r) ^ (1 / r) := by
    rw [hK, ENNReal.mul_rpow_of_nonneg _ _ (div_nonneg zero_le_one hr0.le)]
  have hX0 : (ENNReal.ofReal (2 * ((1 : ℕ) : ℝ) * c)) ^ (1 / r) ≠ 0 :=
    (ENNReal.rpow_pos (ENNReal.ofReal_pos.2 (mul_pos (by norm_num) hc))
      ENNReal.ofReal_ne_top).ne'
  have hXt : (ENNReal.ofReal (2 * ((1 : ℕ) : ℝ) * c)) ^ (1 / r) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (div_nonneg zero_le_one hr0.le) ENNReal.ofReal_ne_top
  have hb' := hb
  rw [eW, hsplit] at hb'
  have hYle : (ENNReal.ofReal c⁻¹ * ∫⁻ z in UnforcedLeray.Cyl.cell c, ‖Gp z‖ₑ ^ r) ^ (1 / r) ≤
      ENNReal.ofReal C * eLpNorm F (ENNReal.ofReal r) (UnforcedLeray.Cyl.avgμ c) := by
    refine (ENNReal.mul_le_mul_iff_right hX0 hXt).1 ?_
    calc (ENNReal.ofReal (2 * ((1 : ℕ) : ℝ) * c)) ^ (1 / r) *
          (ENNReal.ofReal c⁻¹ * ∫⁻ z in UnforcedLeray.Cyl.cell c, ‖Gp z‖ₑ ^ r) ^ (1 / r)
        ≤ ENNReal.ofReal C * (ENNReal.ofReal (2 * ((1 : ℕ) : ℝ) * c)) ^ (1 / r) *
            eLpNorm F (ENNReal.ofReal r) (UnforcedLeray.Cyl.avgμ c) := hb'
      _ = (ENNReal.ofReal (2 * ((1 : ℕ) : ℝ) * c)) ^ (1 / r) *
            (ENNReal.ofReal C * eLpNorm F (ENNReal.ofReal r) (UnforcedLeray.Cyl.avgμ c)) := by
          ring
  have hEA : eLpNorm Gp (ENNReal.ofReal r) (UnforcedLeray.Cyl.avgμ c) ≤
      ENNReal.ofReal C * eLpNorm F (ENNReal.ofReal r) (UnforcedLeray.Cyl.avgμ c) := by
    rw [eA]
    exact hYle
  have hsub : UnforcedLeray.Cyl.cell c ⊆ ppWindow c 1 := by
    intro z hz
    rw [UnforcedLeray.Cyl.mem_cell] at hz
    show -((1 : ℕ) : ℝ) * c ≤ z.1 ∧ z.1 < ((1 : ℕ) : ℝ) * c
    simp only [Nat.cast_one, one_mul, neg_mul]
    constructor <;> linarith [hz.1, hz.2]
  have hAsm : AEStronglyMeasurable Gp (UnforcedLeray.Cyl.avgμ c) := by
    rw [UnforcedLeray.Cyl.avgμ, UnforcedLeray.Cyl.cellμ]
    exact (hmeas.mono_set hsub).smul_measure _
  exact ⟨⟨hAsm, lt_of_le_of_lt hEA (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hF)⟩, hEA⟩

end UnforcedLeray.Short.IIb
