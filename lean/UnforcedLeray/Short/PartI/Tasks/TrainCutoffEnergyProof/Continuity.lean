import UnforcedLeray.Short.PartI.Sub.T05b_2

/-!


Target: `cutoffEnergyContinuous : CutoffEnergyContinuous` (`Short/PartI/Sub/T05b_2.lean`, line 168).

Source of record: `the November 2 reference manuscript`, lines 276-288.

Outline. For `R ≥ 1` the cutoff energy is `F_R(s) = ∫_cell φ_R(η) ‖v(s) - v'(s)‖²` with
`φ_R = etaCutoff R`. Only `0 < c` and `1 ≤ R` are used.

1. `0 ≤ etaCutoff R ≤ 1`, `etaCutoff R` is continuous, and `etaCutoff R η = 0` when `2R ≤ |η|`.
2. The squared difference of the two velocities is jointly continuous on `[0, ∞) × ℝ²`
   (`IsTrain.smooth_v`). On the compact set `Icc 0 S × box`, `box = [-c/2, c/2] × [-2R, 2R]`,
   it is bounded by some `C`.
3. On the cell the integrand is dominated by `max C 0 · 1_box`, which is integrable on the cell
   because `box` has finite measure. Continuity of parameter integrals
   (`MeasureTheory.continuousOn_of_dominated`) gives the claim.
-/

set_option autoImplicit false

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)

/-- The cutoff `etaCutoff R` is nonnegative. -/
lemma cutoffCont_eta_nonneg (R η : ℝ) : 0 ≤ etaCutoff R η := by
  show 0 ≤ Real.smoothTransition (2 - |η| / R) ^ 2
  positivity

/-- The cutoff `etaCutoff R` is at most `1`. -/
lemma cutoffCont_eta_le_one (R η : ℝ) : etaCutoff R η ≤ 1 := by
  show Real.smoothTransition (2 - |η| / R) ^ 2 ≤ 1
  exact pow_le_one₀ (Real.smoothTransition.nonneg _) (Real.smoothTransition.le_one _)

/-- The cutoff `etaCutoff R` vanishes for `2R ≤ |η|`. -/
lemma cutoffCont_eta_eq_zero {R : ℝ} (hR : 0 < R) {η : ℝ} (hη : 2 * R ≤ |η|) :
    etaCutoff R η = 0 := by
  have h2 : 2 ≤ |η| / R := (le_div_iff₀ hR).2 (by linarith)
  have hle : 2 - |η| / R ≤ 0 := by linarith
  show Real.smoothTransition (2 - |η| / R) ^ 2 = 0
  simp [Real.smoothTransition.zero_of_nonpos hle]

/-- The cutoff `etaCutoff R` is continuous. -/
lemma cutoffCont_eta_continuous (R : ℝ) : Continuous (etaCutoff R) := by
  show Continuous fun η : ℝ => Real.smoothTransition (2 - |η| / R) ^ 2
  exact (Real.smoothTransition.continuous.comp
    (continuous_const.sub (continuous_abs.div_const R))).pow 2

/-- **Leaf `CutoffEnergyContinuous`** (proof): `F_R` is continuous on `[0, S]`. -/
theorem cutoffEnergyContinuous : CutoffEnergyContinuous := by
  unfold CutoffEnergyContinuous
  intro ν c hν hc tr tr' R hR S
  have hR0 : 0 < R := by linarith
  -- the velocities are continuous on `[0, ∞) × ℝ²`
  have hv : ContinuousOn (fun x : ℝ × Plane => tr.v x.1 x.2) (Ici 0 ×ˢ univ) :=
    tr.isTrain.smooth_v.continuousOn
  have hv' : ContinuousOn (fun x : ℝ × Plane => tr'.v x.1 x.2) (Ici 0 ×ˢ univ) :=
    tr'.isTrain.smooth_v.continuousOn
  -- the squared difference is jointly continuous on `[0, ∞) × ℝ²`
  have hq : ContinuousOn (fun x : ℝ × Plane => ‖tr.v x.1 x.2 - tr'.v x.1 x.2‖ ^ 2)
      (Ici 0 ×ˢ univ) :=
    ((hv.sub hv').norm).pow 2
  -- the compact set `Icc 0 S × box`
  have hK : IsCompact (Icc (0 : ℝ) S ×ˢ (Icc (-c / 2) (c / 2) ×ˢ Icc (-(2 * R)) (2 * R))) :=
    isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hK_sub : Icc (0 : ℝ) S ×ˢ (Icc (-c / 2) (c / 2) ×ˢ Icc (-(2 * R)) (2 * R)) ⊆
      Ici 0 ×ˢ (univ : Set Plane) := by
    intro x hx
    exact Set.mem_prod.2 ⟨Set.mem_Ici.2 (Set.mem_Icc.1 (Set.mem_prod.1 hx).1).1, mem_univ _⟩
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hq.mono hK_sub)
  -- the box has finite measure, hence so does its trace on the cell
  have hbox_meas : MeasurableSet (Icc (-c / 2) (c / 2) ×ˢ Icc (-(2 * R)) (2 * R)) :=
    measurableSet_Icc.prod measurableSet_Icc
  have hbox_fin : volume (Icc (-c / 2) (c / 2) ×ˢ Icc (-(2 * R)) (2 * R)) < ⊤ :=
    (isCompact_Icc.prod isCompact_Icc).measure_lt_top
  have hcell_meas : MeasurableSet (Cyl.cell c) := by
    unfold Cyl.cell
    exact measurableSet_Ico.prod MeasurableSet.univ
  have hfin : (volume.restrict (Cyl.cell c)) (Icc (-c / 2) (c / 2) ×ˢ Icc (-(2 * R)) (2 * R)) ≠ ⊤ :=
    ne_top_of_le_ne_top hbox_fin.ne (Measure.restrict_apply_le _ _)
  -- the dominating function `max C 0 · 1_box` is integrable on the cell
  have hbound_int : Integrable
      ((Icc (-c / 2) (c / 2) ×ˢ Icc (-(2 * R)) (2 * R)).indicator (fun _ : Plane => max C 0))
      (volume.restrict (Cyl.cell c)) :=
    (integrable_indicator_iff hbox_meas).2 (integrableOn_const hfin)
  -- continuity in `z` for fixed `s ≥ 0`
  have hz : ∀ s : ℝ, 0 ≤ s →
      Continuous (fun z : Plane => etaCutoff R z.2 * ‖tr.v s z - tr'.v s z‖ ^ 2) := by
    intro s hs
    have hmap : ∀ z : Plane, (s, z) ∈ Ici (0 : ℝ) ×ˢ (univ : Set Plane) :=
      fun z => Set.mk_mem_prod (Set.mem_Ici.2 hs) (mem_univ z)
    have hcont : Continuous (fun z : Plane => ((s, z) : ℝ × Plane)) :=
      continuous_const.prodMk continuous_id
    have h1 : Continuous (fun z : Plane => tr.v s z) := hv.comp_continuous hcont hmap
    have h2 : Continuous (fun z : Plane => tr'.v s z) := hv'.comp_continuous hcont hmap
    exact ((cutoffCont_eta_continuous R).comp continuous_snd).mul (((h1.sub h2).norm).pow 2)
  -- continuity in `s ∈ [0, S]` for fixed `z`
  have hs_cont : ∀ a : Plane, ContinuousOn
      (fun s : ℝ => etaCutoff R a.2 * ‖tr.v s a - tr'.v s a‖ ^ 2) (Icc (0 : ℝ) S) := by
    intro a
    have hmap : MapsTo (fun s : ℝ => ((s, a) : ℝ × Plane)) (Icc (0 : ℝ) S)
        (Ici (0 : ℝ) ×ˢ (univ : Set Plane)) :=
      fun s hs => Set.mk_mem_prod (Set.mem_Ici.2 hs.1) (mem_univ a)
    have hcont : ContinuousOn (fun s : ℝ => ((s, a) : ℝ × Plane)) (Icc (0 : ℝ) S) :=
      (continuous_id.prodMk continuous_const).continuousOn
    have hc1 : ContinuousOn (fun s : ℝ => tr.v s a) (Icc (0 : ℝ) S) :=
      hv.comp hcont hmap
    have hc2 : ContinuousOn (fun s : ℝ => tr'.v s a) (Icc (0 : ℝ) S) :=
      hv'.comp hcont hmap
    exact continuousOn_const.mul (((hc1.sub hc2).norm).pow 2)
  -- the domination on the cell
  have hbound : ∀ s ∈ Icc (0 : ℝ) S, ∀ᵐ a ∂(volume.restrict (Cyl.cell c)),
      ‖etaCutoff R a.2 * ‖tr.v s a - tr'.v s a‖ ^ 2‖ ≤
        (Icc (-c / 2) (c / 2) ×ˢ Icc (-(2 * R)) (2 * R)).indicator (fun _ : Plane => max C 0) a := by
    intro s hs
    filter_upwards [ae_restrict_mem hcell_meas] with a ha
    have hq0 : 0 ≤ ‖tr.v s a - tr'.v s a‖ ^ 2 := sq_nonneg _
    by_cases hb : a ∈ Icc (-c / 2) (c / 2) ×ˢ Icc (-(2 * R)) (2 * R)
    · have hbC : ‖‖tr.v s a - tr'.v s a‖ ^ 2‖ ≤ C := hC (s, a) (Set.mk_mem_prod hs hb)
      rw [Real.norm_of_nonneg hq0] at hbC
      rw [Set.indicator_of_mem hb, Real.norm_of_nonneg (mul_nonneg (cutoffCont_eta_nonneg R a.2) hq0)]
      exact (mul_le_of_le_one_left hq0 (cutoffCont_eta_le_one R a.2)).trans
        (hbC.trans (le_max_left _ _))
    · have ha1 : a.1 ∈ Icc (-c / 2) (c / 2) := Ico_subset_Icc_self (Set.mem_prod.1 ha).1
      have hR2 : 2 * R ≤ |a.2| := by
        by_contra hlt
        rw [not_le] at hlt
        apply hb
        exact Set.mem_prod.2 ⟨ha1, Set.mem_Icc.2
          ⟨by linarith [neg_abs_le a.2], by linarith [le_abs_self a.2]⟩⟩
      rw [Set.indicator_of_notMem hb]
      simp [cutoffCont_eta_eq_zero hR0 hR2]
  -- dominated continuity of parameter integrals
  have hmain : ContinuousOn
      (fun s : ℝ => ∫ z, etaCutoff R z.2 * ‖tr.v s z - tr'.v s z‖ ^ 2 ∂(volume.restrict (Cyl.cell c)))
      (Icc (0 : ℝ) S) :=
    MeasureTheory.continuousOn_of_dominated
      (F := fun s z => etaCutoff R z.2 * ‖tr.v s z - tr'.v s z‖ ^ 2)
      (fun s hs => (hz s hs.1).aestronglyMeasurable) hbound hbound_int
      (ae_of_all _ (fun a => hs_cont a))
  unfold cutoffEnergy
  exact hmain

end UnforcedLeray.Short.PartI
