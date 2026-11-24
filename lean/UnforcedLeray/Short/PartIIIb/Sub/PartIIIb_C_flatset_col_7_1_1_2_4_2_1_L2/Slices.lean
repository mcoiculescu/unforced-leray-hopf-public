import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_1_L2.Congr

/-!
# Helpers for `SFCDuhamelLift`: a.e. slices of the periodic extension
(decomposition of `PartIII-b:C/flatset/col/7/1/1/2/4/2/1/2`)

* `reduceIoc_shift` : `reduceIoc` is invariant under integer shifts of its argument.
* `measurePreserving_shiftQ` : shifting the `q`-coordinate of a profile by `a` preserves Lebesgue.
* `ae_slices_of_measureH` : if `F = H` `measureH`-a.e., then for a.e. `σ > 0` the periodic
  extensions of `F` and `H` agree Lebesgue-a.e. on the slice `z ∈ ℝ²`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

theorem reduceIoc_shift {c : ℝ} (hc : 0 < c) (q : ℝ) (m : ℤ) :
    UnforcedLeray.B0220.reduceIoc c (q + m * c) = UnforcedLeray.B0220.reduceIoc c q := by
  have hc' : c ≠ 0 := hc.ne'
  unfold UnforcedLeray.B0220.reduceIoc
  have h : (q + m * c) / c = q / c + (m : ℝ) := by
    field_simp
  rw [h, Int.ceil_add_intCast]
  push_cast
  ring

theorem measurePreserving_shiftQ (a : ℝ) :
    MeasurePreserving (fun p : UnforcedLeray.B0220.Profile => (p.1, p.2.1 + a, p.2.2))
      volume volume := by
  have hA : MeasurePreserving (fun z : ℝ × ℝ => (z.1 + a, z.2)) volume volume := by
    have h := measurePreserving_add_right (volume : Measure (ℝ × ℝ)) ((a, 0) : ℝ × ℝ)
    convert h using 1
    funext z
    ext <;> simp
  have hP := (MeasurePreserving.id (volume : Measure ℝ)).prod hA
  rw [← Measure.volume_eq_prod] at hP
  exact hP

theorem ae_slices_of_measureH {c : ℝ} (hc : 0 < c)
    {F H : UnforcedLeray.B0220.Profile → UnforcedLeray.B0223.MeridC}
    (h : F =ᵐ[UnforcedLeray.B0220.measureH c] H) :
    ∀ᵐ σ : ℝ, 0 < σ → ∀ᵐ z : ℝ × ℝ,
      UnforcedLeray.B0220.periodize c F (σ, z) = UnforcedLeray.B0220.periodize c H (σ, z) := by
  set G : Set UnforcedLeray.B0220.Profile := {p | 0 < p.1 ∧
    UnforcedLeray.B0220.periodize c F p ≠ UnforcedLeray.B0220.periodize c H p} with hG
  have hcl : MeasurableSet (UnforcedLeray.B0220.cell c) :=
    measurableSet_Ioi.prod (measurableSet_Ioc.prod MeasurableSet.univ)
  have hnull : UnforcedLeray.B0220.measureH c {p | F p ≠ H p} = 0 := ae_iff.1 h
  have hw : AEMeasurable UnforcedLeray.B0220.weightH
      (volume.restrict (UnforcedLeray.B0220.cell c)) :=
    (ENNReal.measurable_ofReal.comp (measurable_fst.pow_const _)).aemeasurable
  -- the cell part of `G` is null
  have hcell : volume (G ∩ UnforcedLeray.B0220.cell c) = 0 := by
    have hm := hnull
    unfold UnforcedLeray.B0220.measureH UnforcedLeray.B0220.cellMeasure at hm
    rw [withDensity_apply_eq_zero' hw, Measure.restrict_apply' hcl] at hm
    refine measure_mono_null ?_ hm
    rintro p ⟨hpG, hpc⟩
    have hp1 : 0 < p.1 := hpc.1
    refine ⟨⟨?_, ?_⟩, hpc⟩
    · show UnforcedLeray.B0220.weightH p ≠ 0
      unfold UnforcedLeray.B0220.weightH
      exact (ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos hp1 _)).ne'
    · intro heq
      apply hpG.2
      unfold UnforcedLeray.B0220.periodize
      rw [UnforcedLeray.B0220.reduceIoc_of_mem hc hpc.2.1]
      exact heq
  -- the periodic part of `G` is null
  have hGcl : ∀ m : ℤ, volume ((fun p : UnforcedLeray.B0220.Profile =>
      (p.1, p.2.1 + (m : ℝ) * c, p.2.2)) ⁻¹' (G ∩ UnforcedLeray.B0220.cell c)) = 0 := by
    intro m
    exact (measurePreserving_shiftQ ((m : ℝ) * c)).quasiMeasurePreserving.preimage_null hcell
  have hsub : G ⊆ ⋃ m : ℤ, (fun p : UnforcedLeray.B0220.Profile =>
      (p.1, p.2.1 + (m : ℝ) * c, p.2.2)) ⁻¹' (G ∩ UnforcedLeray.B0220.cell c) := by
    intro p hp
    set m : ℤ := 1 - ⌈p.2.1 / c⌉ with hm
    have hval : p.2.1 + (m : ℝ) * c = UnforcedLeray.B0220.reduceIoc c p.2.1 := by
      unfold UnforcedLeray.B0220.reduceIoc
      rw [hm]
      push_cast
      ring
    have hmem : UnforcedLeray.B0220.reduceIoc c p.2.1 ∈ Ioc 0 c :=
      UnforcedLeray.B0220.reduceIoc_mem hc _
    have hfix : ∀ K : UnforcedLeray.B0220.Profile → UnforcedLeray.B0223.MeridC,
        UnforcedLeray.B0220.periodize c K (p.1, p.2.1 + (m : ℝ) * c, p.2.2) =
          UnforcedLeray.B0220.periodize c K p := by
      intro K
      unfold UnforcedLeray.B0220.periodize
      rw [hval, UnforcedLeray.B0220.reduceIoc_of_mem hc hmem]
    refine Set.mem_iUnion.2 ⟨m, ?_⟩
    show (p.1, p.2.1 + (m : ℝ) * c, p.2.2) ∈ G ∩ UnforcedLeray.B0220.cell c
    refine ⟨⟨hp.1, ?_⟩, ⟨hp.1, ?_, trivial⟩⟩
    · show UnforcedLeray.B0220.periodize c F (p.1, p.2.1 + (m : ℝ) * c, p.2.2) ≠
        UnforcedLeray.B0220.periodize c H (p.1, p.2.1 + (m : ℝ) * c, p.2.2)
      rw [hfix F, hfix H]
      exact hp.2
    · show p.2.1 + (m : ℝ) * c ∈ Ioc 0 c
      rw [hval]
      exact hmem
  have hG0 : volume G = 0 := measure_mono_null hsub (measure_iUnion_null hGcl)
  have hnot : ∀ᵐ p ∂(volume : Measure UnforcedLeray.B0220.Profile), p ∉ G :=
    measure_eq_zero_iff_ae_notMem.1 hG0
  have hnot' : ∀ᵐ p ∂((volume : Measure ℝ).prod (volume : Measure (ℝ × ℝ))), p ∉ G := by
    rw [← Measure.volume_eq_prod]
    exact hnot
  filter_upwards [Measure.ae_ae_of_ae_prod hnot'] with σ hσ
  intro hσpos
  filter_upwards [hσ] with z hz
  by_contra hne
  exact hz ⟨hσpos, hne⟩

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
