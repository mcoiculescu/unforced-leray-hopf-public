import UnforcedLeray.Short.PartIIb.Sub.T12_1_3_1
import UnforcedLeray.Lib.CylinderB.Periodize

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIb.CylLocIntCover

open UnforcedLeray.Cyl

/-- Translate of the centred cell by `m c` in `q`: `{w | (w.1 + m c, w.2) ∈ cell c}`. -/
def shiftCell (c : ℝ) (m : ℤ) : Set (ℝ × ℝ) := (fun w : ℝ × ℝ => w + ((m : ℝ) * c, 0)) ⁻¹' cell c

theorem lintegral_shiftCell {c : ℝ} (hc : 0 < c) {g : ℝ × ℝ → ℝ≥0∞} (hper : IsPeriodic c g)
    (m : ℤ) : ∫⁻ w in shiftCell c m, g w = ∫⁻ y in cell c, g y := by
  set v : ℝ × ℝ := ((m : ℝ) * c, 0) with hv
  have hmp : MeasurePreserving (fun w : ℝ × ℝ => w + v) (volume : Measure (ℝ × ℝ)) volume :=
    measurePreserving_add_right volume v
  have hemb : MeasurableEmbedding (fun w : ℝ × ℝ => w + v) :=
    (Homeomorph.addRight v).measurableEmbedding
  have key := hmp.setLIntegral_comp_preimage_emb hemb (fun y => g (y - v)) (cell c)
  simp only [add_sub_cancel_right] at key
  have hs : shiftCell c m = (fun w : ℝ × ℝ => w + v) ⁻¹' cell c := rfl
  rw [hs, key]
  simp only [sub_eq_add_neg]
  exact lintegral_cell_comp_add hc hper (-v)


theorem mem_shiftCell_iff {c : ℝ} (m : ℤ) (w : ℝ × ℝ) :
    w ∈ shiftCell c m ↔ -c / 2 ≤ w.1 + (m : ℝ) * c ∧ w.1 + (m : ℝ) * c < c / 2 := by
  simp [shiftCell, mem_cell]

/-- The shifted cells with index in a finite window of radius `N` cover a closed ball. -/
theorem closedBall_subset_iUnion_shiftCell {c : ℝ} (hc : 0 < c) (z0 : ℝ × ℝ) (R : ℝ) :
    ∃ N : ℕ, Metric.closedBall z0 R ⊆ ⋃ m ∈ Finset.Icc (-(N : ℤ)) N, shiftCell c m := by
  set A : ℝ := |z0.1| + |R| with hA
  obtain ⟨N, hN⟩ := exists_nat_gt (A / c + 1)
  have hNc : A + c < (N : ℝ) * c := by
    have h := mul_lt_mul_of_pos_right hN hc
    rw [add_mul, div_mul_cancel₀ _ hc.ne', one_mul] at h
    linarith
  refine ⟨N, fun w hw => ?_⟩
  have hw' : dist w z0 ≤ R := hw
  have hd : dist w z0 ≤ R := hw'
  have hd1 : dist w.1 z0.1 ≤ R := le_trans (le_max_left _ _) (by rw [← Prod.dist_eq]; exact hd)
  rw [Real.dist_eq] at hd1
  have hb := abs_le.mp (le_trans hd1 (le_abs_self R))
  have hz := abs_le.mp (le_refl |z0.1|)
  have hwA1 : w.1 ≤ A := by
    have := le_abs_self z0.1
    linarith [le_abs_self R, abs_nonneg z0.1]
  have hwA2 : -A ≤ w.1 := by
    have := neg_abs_le z0.1
    linarith [le_abs_self R, abs_nonneg z0.1, neg_abs_le R]
  -- the integer index `k = ⌊(w.1 + c/2)/c⌋`
  set k : ℤ := ⌊(w.1 + c / 2) / c⌋ with hk
  have hk1 : (k : ℝ) ≤ (w.1 + c / 2) / c := Int.floor_le _
  have hk2 : (w.1 + c / 2) / c < (k : ℝ) + 1 := Int.lt_floor_add_one _
  have hk1' : (k : ℝ) * c ≤ w.1 + c / 2 := (le_div_iff₀ hc).1 hk1
  have hk2' : w.1 + c / 2 < ((k : ℝ) + 1) * c := (div_lt_iff₀ hc).1 hk2
  have hmem : w ∈ shiftCell c (-k) := by
    rw [mem_shiftCell_iff]
    push_cast
    constructor <;> nlinarith
  refine Set.mem_iUnion₂.2 ⟨-k, ?_, hmem⟩
  rw [Finset.mem_Icc]
  constructor
  · by_contra hcon
    push Not at hcon
    -- -k < -N, so k ≥ N + 1
    have hk3 : (N : ℝ) + 1 ≤ (k : ℝ) := by
      have : (-(N : ℤ)) > -k := by linarith
      have h4 : (k : ℤ) ≥ (N : ℤ) + 1 := by omega
      exact_mod_cast h4
    nlinarith
  · by_contra hcon
    push Not at hcon
    have hk3 : (k : ℝ) + 1 ≤ -(N : ℝ) := by
      have h4 : (k : ℤ) + 1 ≤ -(N : ℤ) := by omega
      exact_mod_cast h4
    nlinarith



theorem lintegral_biUnion_le (F : Finset ℤ) (s : ℤ → Set (ℝ × ℝ)) (f : ℝ × ℝ → ℝ≥0∞) :
    ∫⁻ w in ⋃ m ∈ F, s m, f w ≤ ∑ m ∈ F, ∫⁻ w in s m, f w := by
  classical
  refine Finset.induction_on F (by simp) ?_
  intro a F ha ih
  rw [Finset.set_biUnion_insert, Finset.sum_insert ha]
  exact (lintegral_union_le _ _ _).trans (add_le_add_right ih _)

/-- A periodic nonnegative function has a finite-window bound on every closed ball. -/
theorem lintegral_closedBall_le {c : ℝ} (hc : 0 < c) {g : ℝ × ℝ → ℝ≥0∞} (hper : IsPeriodic c g)
    (z0 : ℝ × ℝ) (R : ℝ) :
    ∃ N : ℕ, ∫⁻ w in Metric.closedBall z0 R, g w ≤
      ((2 * N + 1 : ℕ) : ℝ≥0∞) * ∫⁻ w in cell c, g w := by
  obtain ⟨N, hsub⟩ := closedBall_subset_iUnion_shiftCell hc z0 R
  refine ⟨N, ?_⟩
  have hcard : (Finset.Icc (-(N : ℤ)) N).card = 2 * N + 1 := by
    rw [Int.card_Icc]; omega
  calc ∫⁻ w in Metric.closedBall z0 R, g w
      ≤ ∫⁻ w in ⋃ m ∈ Finset.Icc (-(N : ℤ)) N, shiftCell c m, g w := lintegral_mono_set hsub
    _ ≤ ∑ m ∈ Finset.Icc (-(N : ℤ)) N, ∫⁻ w in shiftCell c m, g w := lintegral_biUnion_le _ _ _
    _ = ∑ m ∈ Finset.Icc (-(N : ℤ)) N, ∫⁻ w in cell c, g w :=
        Finset.sum_congr rfl fun m _ => lintegral_shiftCell hc hper m
    _ = ((2 * N + 1 : ℕ) : ℝ≥0∞) * ∫⁻ w in cell c, g w := by
        rw [Finset.sum_const, hcard, nsmul_eq_mul]

theorem exists_shift_mem {c : ℝ} (hc : 0 < c) (x : ℝ) :
    ∃ m : ℤ, -c / 2 ≤ x + (m : ℝ) * c ∧ x + (m : ℝ) * c < c / 2 := by
  set k : ℤ := ⌊(x + c / 2) / c⌋ with hk
  have hk1' : (k : ℝ) * c ≤ x + c / 2 := (le_div_iff₀ hc).1 (Int.floor_le _)
  have hk2' : x + c / 2 < ((k : ℝ) + 1) * c := (div_lt_iff₀ hc).1 (Int.lt_floor_add_one _)
  refine ⟨-k, ?_, ?_⟩ <;> push_cast <;> nlinarith

/-- A `c`-periodic function that is a.e. strongly measurable on the cell is a.e. strongly
measurable on the plane. -/
theorem aestronglyMeasurable_of_cell {c : ℝ} (hc : 0 < c) {D : ℝ × ℝ → CMerid}
    (hper : IsPeriodic c D) (hD : AEStronglyMeasurable D (cellμ c)) :
    AEStronglyMeasurable D (volume : Measure (ℝ × ℝ)) := by
  have hcover : (⋃ m : ℤ, shiftCell c m) = univ := by
    refine eq_univ_of_forall fun w => mem_iUnion.2 ?_
    obtain ⟨m, hm⟩ := exists_shift_mem hc w.1
    exact ⟨m, (mem_shiftCell_iff m w).2 hm⟩
  rw [← Measure.restrict_univ (μ := (volume : Measure (ℝ × ℝ))), ← hcover,
    aestronglyMeasurable_iUnion_iff]
  intro m
  have hmp : MeasurePreserving (fun w : ℝ × ℝ => w + ((m : ℝ) * c, 0)) (volume : Measure (ℝ × ℝ))
      volume := measurePreserving_add_right volume _
  have hemb : MeasurableEmbedding (fun w : ℝ × ℝ => w + ((m : ℝ) * c, 0)) :=
    (Homeomorph.addRight _).measurableEmbedding
  have hmp' := hmp.restrict_preimage_emb hemb (cell c)
  have h := hD.comp_measurePreserving hmp'
  have hfun : (D ∘ fun w : ℝ × ℝ => w + ((m : ℝ) * c, 0)) = D := funext fun w => by
    have h2 : w + ((m : ℝ) * c, 0) = (w.1 + (m : ℝ) * c, w.2) := by ext <;> simp
    simp only [Function.comp_apply, h2]
    exact IsPeriodic.add_int_mul hper m w
  rw [hfun] at h
  exact h

theorem memLp_cell_of_avg {c r : ℝ} (hc : 0 < c) {D : ℝ × ℝ → CMerid}
    (hD : MemLp D (ENNReal.ofReal r) (avgμ c)) : MemLp D (ENNReal.ofReal r) (cellμ c) := by
  have h := hD.smul_measure (ENNReal.ofReal_ne_top (r := c))
  have h2 : ENNReal.ofReal c • avgμ c = cellμ c := by
    unfold avgμ
    rw [smul_smul, ← ENNReal.ofReal_mul hc.le, mul_inv_cancel₀ hc.ne', ENNReal.ofReal_one,
      one_smul]
  rwa [h2] at h

/-- The core estimate: a periodic `L^r` field (`1 ≤ r`) is integrable on every closed ball. -/
theorem integrableOn_closedBall_of_cell {c r : ℝ} (hc : 0 < c) (hr1 : 1 ≤ r)
    {D : ℝ × ℝ → CMerid} (hper : IsPeriodic c D)
    (hD : MemLp D (ENNReal.ofReal r) (cellμ c)) (z0 : ℝ × ℝ) (R : ℝ) :
    IntegrableOn D (Metric.closedBall z0 R) volume := by
  have hr0 : 0 < r := by linarith
  have hAE : AEStronglyMeasurable D (volume : Measure (ℝ × ℝ)) :=
    aestronglyMeasurable_of_cell hc hper hD.aestronglyMeasurable
  have h1 : ∫⁻ a, ‖D a‖ₑ ^ r ∂(cellμ c) < ∞ := by
    have := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top (μ := cellμ c)
      (ENNReal.ofReal_pos.2 hr0).ne' ENNReal.ofReal_ne_top hD.eLpNorm_lt_top
    rwa [ENNReal.toReal_ofReal hr0.le] at this
  have hgper : IsPeriodic c (fun w => ‖D w‖ₑ ^ r) := fun z => by
    show ‖D (z.1 + c, z.2)‖ₑ ^ r = ‖D z‖ₑ ^ r
    rw [hper z]
  obtain ⟨N, hN⟩ := lintegral_closedBall_le hc hgper z0 R
  have hball : ∫⁻ w in Metric.closedBall z0 R, ‖D w‖ₑ ^ r < ∞ :=
    lt_of_le_of_lt hN (ENNReal.mul_lt_top (ENNReal.natCast_ne_top _).lt_top h1)
  have : IsFiniteMeasure (volume.restrict (Metric.closedBall z0 R)) :=
    isFiniteMeasure_restrict.2 measure_closedBall_lt_top.ne
  have hmem : MemLp D (ENNReal.ofReal r) (volume.restrict (Metric.closedBall z0 R)) := by
    refine ⟨hAE.restrict, ?_⟩
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.2 hr0).ne'
      ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hr0.le]
    exact ENNReal.rpow_lt_top_of_nonneg (by positivity) hball.ne
  exact MemLp.integrable (ENNReal.one_le_ofReal.2 hr1) hmem

end UnforcedLeray.Short.IIb.CylLocIntCover
