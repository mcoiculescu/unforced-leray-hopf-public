import UnforcedLeray.Short.PartI.Sub.PartI_T08_2_2.EnergyIneq
import UnforcedLeray.Short.PartI.Tasks.TrainCutoffEnergyProof.Continuity

/-!
# Part I, task `PartI:T08/2/2/2/2`: continuity of the cutoff jet energy

Target: `cutoffJetContinuous_proof : CutoffJetContinuous` (`Sub/PartI_T08_2_2/EnergyIneq.lean`).

Source of record: `the November 2 reference manuscript`, lines 286-287.

Same argument as `cutoffEnergyContinuous`, with the squared-difference integrand replaced by the
finite sum of squares `∑ u ∈ ι, W u (s, z) ^ 2`, which is continuous on `[0, ∞) × ℝ²` as a finite
sum of continuous functions.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)

/-- **Leaf `CutoffJetContinuous`** (proof): the cutoff jet energy is continuous on `[0, S]`. -/
theorem cutoffJetContinuous_proof : CutoffJetContinuous := by
  unfold CutoffJetContinuous
  intro c R S ι W hc hR hW
  have hR0 : 0 < R := hR
  -- the integrand's sum of squares is continuous on `[0, ∞) × ℝ²`
  have hG : ContinuousOn (fun x : ℝ × Plane => ∑ u ∈ ι, W u x ^ 2) (Ici 0 ×ˢ univ) :=
    continuousOn_finsetSum ι (fun u hu => (hW u hu).pow 2)
  -- the compact set `Icc 0 S × box`
  have hK : IsCompact (Icc (0 : ℝ) S ×ˢ (Icc (-c / 2) (c / 2) ×ˢ Icc (-(2 * R)) (2 * R))) :=
    isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hK_sub : Icc (0 : ℝ) S ×ˢ (Icc (-c / 2) (c / 2) ×ˢ Icc (-(2 * R)) (2 * R)) ⊆
      Ici 0 ×ˢ (univ : Set Plane) := by
    intro x hx
    exact Set.mem_prod.2 ⟨Set.mem_Ici.2 (Set.mem_Icc.1 (Set.mem_prod.1 hx).1).1, mem_univ _⟩
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hG.mono hK_sub)
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
      Continuous (fun z : Plane => etaCutoff R z.2 * ∑ u ∈ ι, W u (s, z) ^ 2) := by
    intro s hs
    have hmap : ∀ z : Plane, (s, z) ∈ Ici (0 : ℝ) ×ˢ (univ : Set Plane) :=
      fun z => Set.mk_mem_prod (Set.mem_Ici.2 hs) (mem_univ z)
    have hcont : Continuous (fun z : Plane => ((s, z) : ℝ × Plane)) :=
      continuous_const.prodMk continuous_id
    have h1 : Continuous (fun z : Plane => ∑ u ∈ ι, W u (s, z) ^ 2) :=
      hG.comp_continuous hcont hmap
    exact ((cutoffCont_eta_continuous R).comp continuous_snd).mul h1
  -- continuity in `s ∈ [0, S]` for fixed `z`
  have hs_cont : ∀ a : Plane, ContinuousOn
      (fun s : ℝ => etaCutoff R a.2 * ∑ u ∈ ι, W u (s, a) ^ 2) (Icc (0 : ℝ) S) := by
    intro a
    have hmap : MapsTo (fun s : ℝ => ((s, a) : ℝ × Plane)) (Icc (0 : ℝ) S)
        (Ici (0 : ℝ) ×ˢ (univ : Set Plane)) :=
      fun s hs => Set.mk_mem_prod (Set.mem_Ici.2 hs.1) (mem_univ a)
    have hcont : ContinuousOn (fun s : ℝ => ((s, a) : ℝ × Plane)) (Icc (0 : ℝ) S) :=
      (continuous_id.prodMk continuous_const).continuousOn
    have hc1 : ContinuousOn (fun s : ℝ => ∑ u ∈ ι, W u (s, a) ^ 2) (Icc (0 : ℝ) S) :=
      hG.comp hcont hmap
    exact continuousOn_const.mul hc1
  -- the domination on the cell
  have hbound : ∀ s ∈ Icc (0 : ℝ) S, ∀ᵐ a ∂(volume.restrict (Cyl.cell c)),
      ‖etaCutoff R a.2 * ∑ u ∈ ι, W u (s, a) ^ 2‖ ≤
        (Icc (-c / 2) (c / 2) ×ˢ Icc (-(2 * R)) (2 * R)).indicator (fun _ : Plane => max C 0) a := by
    intro s hs
    filter_upwards [ae_restrict_mem hcell_meas] with a ha
    have hq0 : 0 ≤ ∑ u ∈ ι, W u (s, a) ^ 2 := Finset.sum_nonneg (fun u _ => sq_nonneg _)
    by_cases hb : a ∈ Icc (-c / 2) (c / 2) ×ˢ Icc (-(2 * R)) (2 * R)
    · have hbC : ‖∑ u ∈ ι, W u (s, a) ^ 2‖ ≤ C := hC (s, a) (Set.mk_mem_prod hs hb)
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
      (fun s : ℝ => ∫ z, etaCutoff R z.2 * ∑ u ∈ ι, W u (s, z) ^ 2 ∂(volume.restrict (Cyl.cell c)))
      (Icc (0 : ℝ) S) :=
    MeasureTheory.continuousOn_of_dominated
      (F := fun s z => etaCutoff R z.2 * ∑ u ∈ ι, W u (s, z) ^ 2)
      (fun s hs => (hz s hs.1).aestronglyMeasurable) hbound hbound_int
      (ae_of_all _ (fun a => hs_cont a))
  exact hmain

end UnforcedLeray.Short.PartI
