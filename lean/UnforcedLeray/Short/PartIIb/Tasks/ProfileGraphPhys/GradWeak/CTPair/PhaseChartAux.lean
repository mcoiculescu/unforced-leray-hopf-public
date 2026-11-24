import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T10_7_1_2_2

/-!
# Helpers for `PartII-b:T10/7/1/2/2/2` and `/3`: `q`-shifts, reduction to the cell, `ageμ` null sets.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIb.PCAux

open UnforcedLeray UnforcedLeray.Axi

/-- Integer `q`-shift. -/
def sh (c : ℝ) (n : ℤ) (x : Coord) : Coord := (x.1, (x.2.1 + n * c, x.2.2))

lemma sh_zero (c : ℝ) (x : Coord) : sh c 0 x = x := by simp [sh]

lemma sh_one (c : ℝ) (x : Coord) : sh c 1 x = qShift c x := by simp [sh, qShift]

lemma sh_succ (c : ℝ) (n : ℤ) (x : Coord) : sh c (n + 1) x = qShift c (sh c n x) := by
  refine Prod.ext rfl (Prod.ext ?_ rfl)
  simp only [sh, qShift]
  push_cast; ring

lemma sh_sh (c : ℝ) (n m : ℤ) (x : Coord) : sh c n (sh c m x) = sh c (n + m) x := by
  refine Prod.ext rfl (Prod.ext ?_ rfl)
  simp only [sh]
  push_cast; ring

lemma sh_fst (c : ℝ) (n : ℤ) (x : Coord) : (sh c n x).1 = x.1 := rfl

lemma measurable_sh (c : ℝ) (n : ℤ) : Measurable (sh c n) := by
  unfold sh
  fun_prop

lemma measurable_qShift (c : ℝ) : Measurable (qShift c) := by
  unfold qShift
  fun_prop

lemma mp_sh (c : ℝ) (n : ℤ) : MeasurePreserving (sh c n) (volume : Measure Coord) volume := by
  have h1 : MeasurePreserving (fun q : ℝ => q + (n : ℝ) * c) volume volume :=
    measurePreserving_add_right _ _
  have : sh c n = Prod.map id (Prod.map (fun q : ℝ => q + (n : ℝ) * c) id) := rfl
  rw [this, Measure.volume_eq_prod, Measure.volume_eq_prod ℝ ℝ]
  exact (MeasurePreserving.id _).prod (h1.prod (MeasurePreserving.id _))

/-- The cell index of `q`. -/
def kk (c q : ℝ) : ℤ := ⌊(q + c / 2) / c⌋

/-- Reduction to the cell. -/
def red (c : ℝ) (x : Coord) : Coord := sh c (-(kk c x.2.1)) x

lemma measurable_red (c : ℝ) : Measurable (red c) := by
  unfold red sh kk
  fun_prop

lemma red_mem {c : ℝ} (hc : 0 < c) (x : Coord) : (red c x).2 ∈ Cyl.cell c := by
  have h1 := Int.floor_le ((x.2.1 + c / 2) / c)
  have h2 := Int.lt_floor_add_one ((x.2.1 + c / 2) / c)
  simp only [red, sh, kk, Cyl.cell, mem_prod, mem_Ico, mem_univ, and_true]
  rw [le_div_iff₀ hc] at h1
  rw [div_lt_iff₀ hc] at h2
  push_cast
  constructor <;> nlinarith

lemma red_qShift (c : ℝ) (hc : 0 < c) (x : Coord) : red c (qShift c x) = red c x := by
  have : kk c (x.2.1 + c) = kk c x.2.1 + 1 := by
    unfold kk
    have : (x.2.1 + c + c / 2) / c = (x.2.1 + c / 2) / c + 1 := by field_simp; ring
    rw [this, Int.floor_add_one]
  refine Prod.ext rfl (Prod.ext ?_ rfl)
  simp only [red, sh, qShift, this]
  push_cast; ring

lemma red_eq_sh (c : ℝ) (x : Coord) : red c x = sh c (-(kk c x.2.1)) x := rfl

lemma red_fst (c : ℝ) (x : Coord) : (red c x).1 = x.1 := rfl


lemma meas_Ioi_cell (c : ℝ) : MeasurableSet (Ioi (0 : ℝ) ×ˢ qCell c) :=
  measurableSet_Ioi.prod (measurableSet_Ico.prod MeasurableSet.univ)

lemma ageμ_null {c : ℝ} (hc : 0 < c) (a : ℝ) {N : Set Coord} (hN : MeasurableSet N)
    (h : volume (N ∩ {x : Coord | 0 < x.1}) = 0) : ageμ c a N = 0 := by
  rw [← lintegral_indicator_one hN, lintegral_ageμ hc a (measurable_one.indicator hN)]
  have : ∀ᵐ p ∂(volume.restrict (Ioi (0 : ℝ) ×ˢ qCell c)), p ∉ N := by
    rw [ae_restrict_iff' (meas_Ioi_cell c)]
    have h0 : ∀ᵐ p ∂(volume : Measure Coord), p ∉ N ∩ {x : Coord | 0 < x.1} := by
      rw [ae_iff]; simp only [not_not]; exact h
    filter_upwards [h0] with p hp hpS
    intro hpN
    exact hp ⟨hpN, hpS.1⟩
  rw [lintegral_congr_ae (g := fun _ => 0)]
  · simp
  · filter_upwards [this] with p hp
    simp [hp]

lemma vol_null_of_ageμ_null {c : ℝ} (hc : 0 < c) (a : ℝ) {M : Set Coord} (hM : MeasurableSet M)
    (h : ageμ c a M = 0) : volume (M ∩ (Ioi (0 : ℝ) ×ˢ qCell c)) = 0 := by
  rw [← lintegral_indicator_one hM, lintegral_ageμ hc a (measurable_one.indicator hM)] at h
  rw [lintegral_eq_zero_iff (by
    exact (ENNReal.measurable_ofReal.comp
      ((measurable_const.mul (measurable_fst.pow_const a)))).mul
      (measurable_one.indicator hM))] at h
  rw [EventuallyEq, ae_restrict_iff' (meas_Ioi_cell c)] at h
  have h2 : ∀ᵐ p ∂(volume : Measure Coord), p ∈ Ioi (0 : ℝ) ×ˢ qCell c → p ∉ M := by
    filter_upwards [h] with p hp hpS
    intro hpM
    have := hp hpS
    have hpos : 0 < p.1 := hpS.1
    simp only [Pi.zero_apply, Pi.mul_apply, Set.indicator_of_mem hpM, Pi.one_apply, mul_one,
      ENNReal.ofReal_eq_zero] at this
    have : 0 < c⁻¹ * p.1 ^ a := by positivity
    linarith
  rw [← le_zero_iff]
  calc volume (M ∩ (Ioi (0 : ℝ) ×ˢ qCell c)) ≤ volume {p : Coord | ¬ (p ∈ Ioi (0 : ℝ) ×ˢ qCell c → p ∉ M)} := by
        apply measure_mono
        intro p hp
        simp only [mem_setOf_eq, not_imp, not_not]
        exact ⟨hp.2, hp.1⟩
    _ = 0 := by rw [← ae_iff]; exact h2 |>.mono fun p hp => hp
    _ = 0 := rfl

lemma ageμ_pos_ae {c : ℝ} (hc : 0 < c) (a : ℝ) : ∀ᵐ x ∂(ageμ c a), 0 < x.1 := by
  rw [ae_iff]
  have : {x : Coord | ¬ 0 < x.1} = {x : Coord | x.1 ≤ 0} := by ext x; simp
  rw [this]
  refine ageμ_null hc a (measurableSet_le measurable_fst measurable_const) ?_
  have : {x : Coord | x.1 ≤ 0} ∩ {x : Coord | 0 < x.1} = ∅ := by
    ext x; simp
  rw [this]; simp

lemma ae_ageμ_of_ae_vol {c : ℝ} (hc : 0 < c) (a : ℝ) {P : Coord → Prop}
    (h : ∀ᵐ x ∂(volume : Measure Coord), 0 < x.1 → P x) : ∀ᵐ x ∂(ageμ c a), P x := by
  have hN : ageμ c a (toMeasurable volume {x : Coord | ¬ (0 < x.1 → P x)}) = 0 := by
    refine ageμ_null hc a (measurableSet_toMeasurable _ _) ?_
    refine measure_mono_null Set.inter_subset_left ?_
    rw [measure_toMeasurable]
    exact ae_iff.1 h
  have h1 : ∀ᵐ x ∂(ageμ c a), x ∉ toMeasurable volume {x : Coord | ¬ (0 < x.1 → P x)} := by
    rw [ae_iff]; simpa using hN
  filter_upwards [h1, ageμ_pos_ae hc a] with x hx hpos
  by_contra hP
  exact hx (subset_toMeasurable _ _ (by simpa using ⟨hpos, hP⟩))

end UnforcedLeray.Short.IIb.PCAux
