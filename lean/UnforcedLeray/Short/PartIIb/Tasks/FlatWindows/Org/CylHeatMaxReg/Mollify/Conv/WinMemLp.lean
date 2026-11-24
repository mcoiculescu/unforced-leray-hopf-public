import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T13_1_4_3_3

/-!
# Part II-b, task `PartII-b:T13/1/4/3/3/2` (`chmWinMemLp`): the truncated window is in `L^r`

Source: `the November 2 reference manuscript` (SP) lines 1933-1935. A `q`-periodic
`g` with `cylNorm c r g < ⊤` has finite `L^r(volume)` norm on each `q`-window of finite width:
the window `|q| ≤ R` is covered by finitely many translated strips `S_k = {|q - k c| ≤ c/2}`, each
of which carries the same `L^r` mass as the base strip `S_0` (periodicity), and the base strip has
`L^r` norm controlled by `cylMeas c = c⁻¹ • volume.restrict (univ ×ˢ cell c)`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

open MeasureTheory Set Filter
open scoped ENNReal

/-- The strip `{x | x.2.1 - a ∈ [-c/2, c/2)}` in `Coord`. -/
def chmWinStripA (c a : ℝ) : Set Coord := {x : Coord | x.2.1 - a ∈ Set.Ico (-c / 2) (c / 2)}

theorem chm_qShift_comp (a b : ℝ) (x : Coord) : qShift b (qShift a x) = qShift (a + b) x := by
  simp only [qShift, add_assoc]

theorem chm_qShift_mp (a : ℝ) :
    MeasurePreserving (qShift a) (volume : Measure Coord) (volume : Measure Coord) := by
  have hfun : qShift a = fun x : Coord => x + ((0 : ℝ), (a, (0 : ℝ))) := by
    funext x
    refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp [qShift]
  rw [hfun]
  exact measurePreserving_add_right (volume : Measure Coord) _

theorem chm_strip_meas (c a : ℝ) : MeasurableSet (chmWinStripA c a) :=
  measurableSet_Ico.preimage ((measurable_fst.comp measurable_snd).sub_const a)

/-- Periodicity along all integer multiples of the period, almost everywhere. -/
theorem chm_ae_periodic_int (c : ℝ) (g : Coord → ℂ) (hp : QPeriodicS c g) (n : ℤ) :
    ∀ᵐ x : Coord, g (qShift ((n : ℝ) * c) x) = g x := by
  have hstep : ∀ a : ℝ, ∀ᵐ x : Coord, g (qShift (a + c) x) = g (qShift a x) := by
    intro a
    filter_upwards [((chm_qShift_mp a).quasiMeasurePreserving).ae hp] with x hx
    rw [chm_qShift_comp] at hx
    exact hx
  refine Int.induction_on n ?_ ?_ ?_
  · filter_upwards with x
    simp [qShift]
  · intro i ih
    filter_upwards [ih, hstep (((i : ℤ) : ℝ) * c)] with x h1 h2
    have e : (((i : ℤ) + 1 : ℤ) : ℝ) * c = (((i : ℤ) : ℝ)) * c + c := by push_cast; ring
    rw [e, h2, h1]
  · intro i ih
    filter_upwards [ih, hstep (((-(i : ℤ) - 1 : ℤ) : ℝ) * c)] with x h1 h2
    have e : ((((-(i : ℤ) - 1 : ℤ)) : ℝ) * c + c) = (((-(i : ℤ) : ℤ)) : ℝ) * c := by
      push_cast; ring
    rw [e] at h2
    rw [← h2]
    exact h1

theorem chm_mem_shift (c a : ℝ) (x : Coord) :
    qShift (-a) x ∈ chmWinStripA c 0 ↔ x ∈ chmWinStripA c a := by
  simp only [chmWinStripA, Set.mem_setOf_eq, qShift, sub_eq_add_neg, neg_zero, add_zero]

theorem chm_ind_shift (c a : ℝ) (g : Coord → ℂ) (h : ∀ᵐ x : Coord, g (qShift (-a) x) = g x) :
    (chmWinStripA c a).indicator g =ᵐ[volume] ((chmWinStripA c 0).indicator g) ∘ qShift (-a) := by
  filter_upwards [h] with x hx'
  by_cases hm : x ∈ chmWinStripA c a
  · simp only [Function.comp_apply]
    rw [Set.indicator_of_mem hm, Set.indicator_of_mem ((chm_mem_shift c a x).mpr hm), hx']
  · simp only [Function.comp_apply]
    rw [Set.indicator_of_notMem hm,
      Set.indicator_of_notMem (fun h' => hm ((chm_mem_shift c a x).mp h'))]

/-- The covering of the window `|q| ≤ R` by finitely many strips `[kc - c/2, kc + c/2)`. -/
theorem chm_cover {c : ℝ} (hc : 0 < c) (R q : ℝ) (hq : |q| ≤ R) :
    ∃ k : ℤ, -(⌈R / c⌉ + 1) ≤ k ∧ k ≤ ⌈R / c⌉ + 1 ∧ q - (k : ℝ) * c ∈ Set.Ico (-c / 2) (c / 2) := by
  have hc0 : c ≠ 0 := hc.ne'
  set u := q / c with hu
  have hqu : q = c * u := by rw [hu]; field_simp
  have habs : |u| ≤ R / c := by
    rw [hu, abs_div, abs_of_pos hc]
    exact div_le_div_of_nonneg_right hq hc.le
  refine ⟨⌊u + 1 / 2⌋, ?_, ?_, ?_⟩
  · have h1 := Int.lt_floor_add_one (u + 1 / 2)
    have h2 := Int.le_ceil (R / c)
    have h3 := neg_abs_le u
    have h4 : (-(⌈R / c⌉ + 1 : ℤ) : ℝ) < ((⌊u + 1 / 2⌋ : ℤ) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast h4.le
  · have h1 := Int.floor_le (u + 1 / 2)
    have h2 := Int.le_ceil (R / c)
    have h4 : ((⌊u + 1 / 2⌋ : ℤ) : ℝ) < ((⌈R / c⌉ + 1 : ℤ) : ℝ) := by
      push_cast
      linarith [le_abs_self u]
    exact_mod_cast h4.le
  · have h1 := Int.floor_le (u + 1 / 2)
    have h2 := Int.lt_floor_add_one (u + 1 / 2)
    have e : c * (u - (⌊u + 1 / 2⌋ : ℝ)) = q - (⌊u + 1 / 2⌋ : ℝ) * c := by
      rw [hqu]; ring
    constructor
    · have h3 : c * (-1 / 2) ≤ c * (u - (⌊u + 1 / 2⌋ : ℝ)) :=
        mul_le_mul_of_nonneg_left (by linarith) hc.le
      linarith
    · have h3 : c * (u - (⌊u + 1 / 2⌋ : ℝ)) < c * (1 / 2) :=
        mul_lt_mul_of_pos_left (by linarith) hc
      linarith

theorem chm_cylMeas_eq (c : ℝ) :
    cylMeas c = ENNReal.ofReal c⁻¹ • (volume : Measure Coord).restrict (chmWinStripA c 0) := by
  have hset : chmWinStripA c 0 = Set.univ ×ˢ UnforcedLeray.Cyl.cell c := by
    ext x
    simp only [chmWinStripA, Set.mem_setOf_eq, UnforcedLeray.Cyl.cell, Set.mem_prod,
      Set.mem_univ, true_and, and_true, sub_zero]
  rw [hset]
  unfold cylMeas UnforcedLeray.Cyl.avgμ UnforcedLeray.Cyl.cellμ
  rw [Measure.prod_smul_right]
  congr 1
  have hcoord : (volume : Measure Coord) = (volume : Measure ℝ).prod (volume : Measure (ℝ × ℝ)) :=
    Measure.volume_eq_prod _ _
  rw [hcoord, ← Measure.prod_restrict, Measure.restrict_univ]

theorem chmWinMemLp : UnforcedLeray.Short.IIb.ChmWinMemLp := by
  intro r hr c hc g hp hm hn R
  have hpne : ENNReal.ofReal r ≠ ⊤ := ENNReal.ofReal_ne_top
  have hper := chm_ae_periodic_int c g hp
  have hpos : (0 : ℝ≥0∞) < ENNReal.ofReal c⁻¹ := ENNReal.ofReal_pos.mpr (inv_pos.mpr hc)
  -- the base strip is in `L^r(volume)`
  have hS0 : MemLp ((chmWinStripA c 0).indicator g) (ENNReal.ofReal r) volume := by
    rw [memLp_indicator_iff_restrict (chm_strip_meas c 0)]
    refine ⟨hm.restrict, ?_⟩
    have hcyl : eLpNorm g (ENNReal.ofReal r) (cylMeas c) < ⊤ := hn
    rw [chm_cylMeas_eq c, eLpNorm_smul_measure_of_ne_top hpne, smul_eq_mul] at hcyl
    exact ENNReal.lt_top_of_mul_ne_top_right hcyl.ne
      (ENNReal.rpow_pos hpos ENNReal.ofReal_ne_top).ne'
  -- each translated strip is in `L^r(volume)`
  have hkMemLp : ∀ k : ℤ, MemLp ((chmWinStripA c ((k : ℝ) * c)).indicator g) (ENNReal.ofReal r)
      volume := by
    intro k
    have hk : ∀ᵐ x : Coord, g (qShift (-((k : ℝ) * c)) x) = g x := by
      filter_upwards [hper (-k)] with x hx
      rw [show ((-k : ℤ) : ℝ) * c = -((k : ℝ) * c) by push_cast; ring] at hx
      exact hx
    exact (hS0.comp_measurePreserving (chm_qShift_mp (-((k : ℝ) * c)))).ae_eq
      (chm_ind_shift c _ g hk).symm
  have hG : MemLp (fun x : Coord => ∑ k ∈ Finset.Icc (-(⌈R / c⌉ + 1)) (⌈R / c⌉ + 1),
      ‖(chmWinStripA c ((k : ℝ) * c)).indicator g x‖) (ENNReal.ofReal r) volume :=
    memLp_finsetSum _ (fun k _ => (hkMemLp k).norm)
  have hWm : MeasurableSet {x : Coord | |x.2.1| ≤ R} :=
    measurableSet_le (continuous_abs.measurable.comp (measurable_fst.comp measurable_snd))
      measurable_const
  have hfe : chmWinR R g = {x : Coord | |x.2.1| ≤ R}.indicator g := by
    funext x
    simp only [chmWinR, Set.indicator_apply, Set.mem_setOf_eq]
  have hmeas : AEStronglyMeasurable (chmWinR R g) volume := by
    rw [hfe]
    exact hm.indicator hWm
  refine hG.mono hmeas (ae_of_all _ fun x => ?_)
  rw [Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _)]
  by_cases hx : |x.2.1| ≤ R
  · obtain ⟨k, hk1, hk2, hk3⟩ := chm_cover hc R x.2.1 hx
    have hxS : x ∈ chmWinStripA c ((k : ℝ) * c) := hk3
    have hle : ‖(chmWinStripA c ((k : ℝ) * c)).indicator g x‖ ≤
        ∑ k' ∈ Finset.Icc (-(⌈R / c⌉ + 1)) (⌈R / c⌉ + 1),
          ‖(chmWinStripA c ((k' : ℝ) * c)).indicator g x‖ :=
      Finset.single_le_sum (f := fun k' : ℤ => ‖(chmWinStripA c ((k' : ℝ) * c)).indicator g x‖)
        (fun _ _ => norm_nonneg _) (Finset.mem_Icc.mpr ⟨hk1, hk2⟩)
    have hW : ‖chmWinR R g x‖ = ‖g x‖ := by
      simp only [chmWinR, if_pos hx]
    have hI : ‖(chmWinStripA c ((k : ℝ) * c)).indicator g x‖ = ‖g x‖ := by
      rw [Set.indicator_of_mem hxS]
    rw [hW]
    linarith
  · rw [chmWinR, if_neg hx, norm_zero]
    exact Finset.sum_nonneg fun _ _ => norm_nonneg _

#print axioms UnforcedLeray.Short.IIb.chmWinMemLp

end UnforcedLeray.Short.IIb
