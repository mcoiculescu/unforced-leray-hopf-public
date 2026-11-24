import UnforcedLeray.Short.PartI.Sub.T02_3_10

/-!


Target: `ebContinuous : EtaCutoffFacts → EbContinuous` (`Short/PartI/Sub/T02_3_10.lean`, line 133,
`EbContinuous`). Source of record: `the November 2 reference manuscript`, lines 276-282.

Outline. For `R ≥ 1` the cutoff energy is `E_R(s) = ∫_cell φ_R(η) ‖v(s)‖²` with `φ_R = etaCutoff R`.
Only `1 ≤ R` and the regularity in `IsClassicalOn` are used. The hypothesis `EtaCutoffFacts` is not
needed: `etaCutoff R` is continuous by its own definition through `Real.smoothTransition`.

1. `0 ≤ etaCutoff R ≤ 1`, `etaCutoff R` is continuous, and `etaCutoff R η = 0` when `2R ≤ |η|`.
2. `v` is jointly continuous on `Icc 0 T × ℝ²` (`IsClassicalOn.smooth_v`). On the compact set
   `Icc 0 T × box`, `box = [-c/2, c/2] × [-2R, 2R]`, the function `‖v‖²` is bounded by some `C`.
3. On the cell the integrand is dominated by `max C 0 · 1_box`, which is integrable because `box` has
   finite measure. Continuity of parameter integrals (`MeasureTheory.continuousOn_of_dominated`) gives
   the claim.
-/

set_option autoImplicit false

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)

/-- The cutoff `etaCutoff R` is nonnegative. -/
lemma ebCont_eta_nonneg (R η : ℝ) : 0 ≤ etaCutoff R η := by
  show 0 ≤ Real.smoothTransition (2 - |η| / R) ^ 2
  positivity

/-- The cutoff `etaCutoff R` is at most `1`. -/
lemma ebCont_eta_le_one (R η : ℝ) : etaCutoff R η ≤ 1 := by
  show Real.smoothTransition (2 - |η| / R) ^ 2 ≤ 1
  exact pow_le_one₀ (Real.smoothTransition.nonneg _) (Real.smoothTransition.le_one _)

/-- The cutoff `etaCutoff R` vanishes for `2R ≤ |η|`. -/
lemma ebCont_eta_eq_zero {R : ℝ} (hR : 0 < R) {η : ℝ} (hη : 2 * R ≤ |η|) :
    etaCutoff R η = 0 := by
  have h2 : 2 ≤ |η| / R := (le_div_iff₀ hR).2 (by linarith)
  have hle : 2 - |η| / R ≤ 0 := by linarith
  show Real.smoothTransition (2 - |η| / R) ^ 2 = 0
  simp [Real.smoothTransition.zero_of_nonpos hle]

/-- The cutoff `etaCutoff R` is continuous. -/
lemma ebCont_eta_continuous (R : ℝ) : Continuous (etaCutoff R) := by
  show Continuous fun η : ℝ => Real.smoothTransition (2 - |η| / R) ^ 2
  exact (Real.smoothTransition.continuous.comp
    (continuous_const.sub (continuous_abs.div_const R))).pow 2

/-- **Leaf `EbContinuous`** (proof): the cutoff energy `E_R` is continuous on `[0, T]`. -/
theorem ebContinuous : EtaCutoffFacts → EbContinuous := by
  intro _hF
  unfold EbContinuous
  intro ν c T v p hc hcl R hR
  have hR0 : 0 < R := by linarith
  -- the velocity is continuous on `[0, T] × ℝ²`
  have hv : ContinuousOn (fun x : ℝ × Plane => v x.1 x.2) (Icc 0 T ×ˢ univ) :=
    hcl.smooth_v.continuousOn
  -- the squared norm is jointly continuous on `[0, T] × ℝ²`
  have hq : ContinuousOn (fun x : ℝ × Plane => ‖v x.1 x.2‖ ^ 2) (Icc 0 T ×ˢ univ) :=
    (hv.norm).pow 2
  -- the compact set `Icc 0 T × box`
  have hK : IsCompact (Icc (0 : ℝ) T ×ˢ (Icc (-c / 2) (c / 2) ×ˢ Icc (-(2 * R)) (2 * R))) :=
    isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hK_sub : Icc (0 : ℝ) T ×ˢ (Icc (-c / 2) (c / 2) ×ˢ Icc (-(2 * R)) (2 * R)) ⊆
      Icc (0 : ℝ) T ×ˢ (univ : Set Plane) :=
    Set.prod_mono subset_rfl (subset_univ _)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hq.mono hK_sub)
  -- the box has finite measure, hence so does its trace on the cell
  have hbox_meas : MeasurableSet (Icc (-c / 2) (c / 2) ×ˢ Icc (-(2 * R)) (2 * R)) :=
    measurableSet_Icc.prod measurableSet_Icc
  have hbox_fin : volume (Icc (-c / 2) (c / 2) ×ˢ Icc (-(2 * R)) (2 * R)) < ⊤ :=
    (isCompact_Icc.prod isCompact_Icc).measure_lt_top
  have hcell_meas : MeasurableSet (Cyl.cell c) := by
    unfold Cyl.cell
    exact measurableSet_Ico.prod MeasurableSet.univ
  have hfin : (volume.restrict (Cyl.cell c))
      (Icc (-c / 2) (c / 2) ×ˢ Icc (-(2 * R)) (2 * R)) ≠ ⊤ :=
    ne_top_of_le_ne_top hbox_fin.ne (Measure.restrict_apply_le _ _)
  -- the dominating function `max C 0 · 1_box` is integrable on the cell
  have hbound_int : Integrable
      ((Icc (-c / 2) (c / 2) ×ˢ Icc (-(2 * R)) (2 * R)).indicator (fun _ : Plane => max C 0))
      (volume.restrict (Cyl.cell c)) :=
    (integrable_indicator_iff hbox_meas).2 (integrableOn_const hfin)
  -- continuity in `z` for fixed `s ∈ [0, T]`
  have hz : ∀ s ∈ Icc (0 : ℝ) T,
      Continuous (fun z : Plane => etaCutoff R z.2 * ‖v s z‖ ^ 2) := by
    intro s hs
    have hmap : ∀ z : Plane, (s, z) ∈ Icc (0 : ℝ) T ×ˢ (univ : Set Plane) :=
      fun z => Set.mk_mem_prod hs (mem_univ z)
    have hcont : Continuous (fun z : Plane => ((s, z) : ℝ × Plane)) :=
      continuous_const.prodMk continuous_id
    have h1 : Continuous (fun z : Plane => v s z) := hv.comp_continuous hcont hmap
    exact ((ebCont_eta_continuous R).comp continuous_snd).mul ((h1.norm).pow 2)
  -- continuity in `s ∈ [0, T]` for fixed `z`
  have hs_cont : ∀ a : Plane, ContinuousOn
      (fun s : ℝ => etaCutoff R a.2 * ‖v s a‖ ^ 2) (Icc (0 : ℝ) T) := by
    intro a
    have hmap : MapsTo (fun s : ℝ => ((s, a) : ℝ × Plane)) (Icc (0 : ℝ) T)
        (Icc (0 : ℝ) T ×ˢ (univ : Set Plane)) :=
      fun s hs => Set.mk_mem_prod hs (mem_univ a)
    have hcont : ContinuousOn (fun s : ℝ => ((s, a) : ℝ × Plane)) (Icc (0 : ℝ) T) :=
      (continuous_id.prodMk continuous_const).continuousOn
    have hc1 : ContinuousOn (fun s : ℝ => v s a) (Icc (0 : ℝ) T) :=
      hv.comp hcont hmap
    exact continuousOn_const.mul ((hc1.norm).pow 2)
  -- the domination on the cell
  have hbound : ∀ s ∈ Icc (0 : ℝ) T, ∀ᵐ a ∂(volume.restrict (Cyl.cell c)),
      ‖etaCutoff R a.2 * ‖v s a‖ ^ 2‖ ≤
        (Icc (-c / 2) (c / 2) ×ˢ Icc (-(2 * R)) (2 * R)).indicator (fun _ : Plane => max C 0) a := by
    intro s hs
    filter_upwards [ae_restrict_mem hcell_meas] with a ha
    have hq0 : 0 ≤ ‖v s a‖ ^ 2 := sq_nonneg _
    by_cases hb : a ∈ Icc (-c / 2) (c / 2) ×ˢ Icc (-(2 * R)) (2 * R)
    · have hbC : ‖‖v s a‖ ^ 2‖ ≤ C := hC (s, a) (Set.mk_mem_prod hs hb)
      rw [Real.norm_of_nonneg hq0] at hbC
      rw [Set.indicator_of_mem hb, Real.norm_of_nonneg (mul_nonneg (ebCont_eta_nonneg R a.2) hq0)]
      exact (mul_le_of_le_one_left hq0 (ebCont_eta_le_one R a.2)).trans
        (hbC.trans (le_max_left _ _))
    · have ha1 : a.1 ∈ Icc (-c / 2) (c / 2) := Ico_subset_Icc_self (Set.mem_prod.1 ha).1
      have hR2 : 2 * R ≤ |a.2| := by
        by_contra hlt
        rw [not_le] at hlt
        apply hb
        exact Set.mem_prod.2 ⟨ha1, Set.mem_Icc.2
          ⟨by linarith [neg_abs_le a.2], by linarith [le_abs_self a.2]⟩⟩
      rw [Set.indicator_of_notMem hb]
      simp [ebCont_eta_eq_zero hR0 hR2]
  -- dominated continuity of parameter integrals
  have hmain : ContinuousOn
      (fun s : ℝ => ∫ z, etaCutoff R z.2 * ‖v s z‖ ^ 2 ∂(volume.restrict (Cyl.cell c)))
      (Icc (0 : ℝ) T) :=
    MeasureTheory.continuousOn_of_dominated
      (F := fun s z => etaCutoff R z.2 * ‖v s z‖ ^ 2)
      (fun s hs => (hz s hs).aestronglyMeasurable) hbound hbound_int
      (ae_of_all _ (fun a => hs_cont a))
  unfold ebEnergy
  exact hmain

end UnforcedLeray.Short.PartI
