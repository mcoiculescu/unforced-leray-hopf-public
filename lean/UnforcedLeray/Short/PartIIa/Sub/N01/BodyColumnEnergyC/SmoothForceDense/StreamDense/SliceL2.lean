import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N01_9_1_1_3
import UnforcedLeray.Short.PartIIa.Sub.N01.BodyColumnEnergyC.SmoothForceDense.StreamDense.SliceVanish

/-!
# `SliceL2` (source lines 1684-1689): Fubini/Tonelli with the weight `s^{-3/2}`

`∫ s^{-3/2} ‖h(s,·)‖²_{L²(cell)} ds` is at most twice `‖h‖²_𝓗` (the periodized window
`[-c/2,c/2)` is covered twice by the profile cell `(0,c]`), hence the slice norm is finite for a.e. `s`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIa.N01.Sub

open UnforcedLeray.B0220 (Profile HSpace measureH reduceIoc)
open UnforcedLeray.B0223 (MeridC)

theorem sliceL2 : UnforcedLeray.Short.PartIIa.N01.Sub.SliceL2 := by
  intro c hc h
  set f : Profile → MeridC := (h : Profile → MeridC) with hf
  have hmeas : AEStronglyMeasurable f (measureH c) := Lp.aestronglyMeasurable h
  set g : Profile → MeridC := hmeas.mk f with hgdef
  have hg : Measurable g := hmeas.stronglyMeasurable_mk.measurable
  have hfg : f =ᵐ[measureH c] g := hmeas.ae_eq_mk
  haveI : (volume : Measure ℝ).IsAddRightInvariant := inferInstance
  haveI : (volume : Measure (ℝ × ℝ)).IsAddRightInvariant := by
    rw [Measure.volume_eq_prod]; infer_instance
  haveI : (volume : Measure Profile).IsAddRightInvariant := by
    rw [Measure.volume_eq_prod]; infer_instance
  haveI : SFinite (UnforcedLeray.Cyl.cellμ c) := by
    unfold UnforcedLeray.Cyl.cellμ; infer_instance
  set Φ : Profile → Profile := fun w => (w.1, reduceIoc c w.2.1, w.2.2) with hΦ
  have hΦm : Measurable Φ :=
    measurable_fst.prodMk (((UnforcedLeray.B0220.measurable_reduceIoc c).comp
      (measurable_fst.comp measurable_snd)).prodMk (measurable_snd.comp measurable_snd))
  set v : Profile := (0, c, 0) with hv
  set W : Set Profile := Ioi 0 ×ˢ (Ico (-c / 2) (c / 2) ×ˢ univ) with hW
  have hWm : MeasurableSet W :=
    measurableSet_Ioi.prod (measurableSet_Ico.prod MeasurableSet.univ)
  have hcellm := UnforcedLeray.B0220.measurableSet_cell c
  -- f = g a.e. on the cell, and the translate statement on W
  have hae : ∀ᵐ p ∂(volume : Measure Profile), p ∈ UnforcedLeray.B0220.cell c → f p = g p := by
    have h1 := hfg
    unfold UnforcedLeray.B0220.measureH at h1
    rw [Filter.EventuallyEq, ae_withDensity_iff UnforcedLeray.B0220.measurable_weightH] at h1
    unfold UnforcedLeray.B0220.cellMeasure at h1
    rw [ae_restrict_iff' hcellm] at h1
    filter_upwards [h1] with p hp hpc
    apply hp hpc
    have : 0 < p.1 := hpc.1
    unfold UnforcedLeray.B0220.weightH
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    positivity
  set T : Set Profile := {p | ¬ (p ∈ UnforcedLeray.B0220.cell c → f p = g p)} with hT
  have hT0 : volume T = 0 := by
    have := hae
    rw [ae_iff] at this
    exact this
  have hT1 : volume ((fun x : Profile => x + v) ⁻¹' T) = 0 := by
    rw [measure_preimage_add_right (volume : Measure Profile) v T]; exact hT0
  have hQ : ∀ᵐ w ∂(volume : Measure Profile), w ∈ W → f (Φ w) = g (Φ w) := by
    have a1 : ∀ᵐ w ∂(volume : Measure Profile), w ∉ T := measure_eq_zero_iff_ae_notMem.1 hT0
    have a2 : ∀ᵐ w ∂(volume : Measure Profile), w ∉ (fun x : Profile => x + v) ⁻¹' T :=
      measure_eq_zero_iff_ae_notMem.1 hT1
    filter_upwards [a1, a2] with w h1 h2 hw
    have hΦc : Φ w ∈ UnforcedLeray.B0220.cell c := by
      refine ⟨hw.1, UnforcedLeray.B0220.reduceIoc_mem hc _, trivial⟩
    by_contra hne
    rcases reduceIoc_window hc hw.2.1 with e | e
    · have : Φ w = w := by simp [hΦ, e]
      rw [this] at hne hΦc
      have h1' := h1
      simp only [hT, mem_ofPred_eq, not_not] at h1'
      exact hne (h1' hΦc)
    · have : Φ w = w + v := by
        simp only [hΦ, e, hv]
        ext <;> simp
      rw [this] at hne hΦc
      have h2' := h2
      simp only [mem_preimage, hT, mem_ofPred_eq, not_not] at h2'
      exact hne (h2' hΦc)
  -- global weighted L² bound for g
  have hMem : MemLp f 2 (measureH c) := Lp.memLp h
  have hEfin : ∫⁻ p in UnforcedLeray.B0220.cell c, ‖g p‖ₑ ^ (2 : ℝ) *
      UnforcedLeray.B0220.weightH p < ⊤ := by
    have h1 := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top (p := (2 : ℝ≥0∞))
      (by norm_num) (by norm_num) hMem.eLpNorm_lt_top
    have h2 : ∫⁻ p, ‖g p‖ₑ ^ (2 : ℝ) ∂(measureH c) < ⊤ := by
      have e : ∫⁻ p, ‖f p‖ₑ ^ (2 : ℝ) ∂(measureH c) = ∫⁻ p, ‖g p‖ₑ ^ (2 : ℝ) ∂(measureH c) :=
        lintegral_congr_ae (by filter_upwards [hfg] with p hp; rw [hp])
      rw [← e]; simpa using h1
    unfold measureH at h2
    rw [lintegral_withDensity_eq_lintegral_mul _ UnforcedLeray.B0220.measurable_weightH
      (hg.enorm.pow_const _)] at h2
    simpa [UnforcedLeray.B0220.cellMeasure, Pi.mul_apply, mul_comm] using h2
  set Kc : Profile → ℝ≥0∞ := (UnforcedLeray.B0220.cell c).indicator
    (fun p => ‖g p‖ₑ ^ (2 : ℝ) * UnforcedLeray.B0220.weightH p) with hKc
  have hKcm : Measurable Kc :=
    (hg.enorm.pow_const _ |>.mul UnforcedLeray.B0220.measurable_weightH).indicator hcellm
  have hKcint : (∫⁻ p, Kc p) < ⊤ := by
    rw [hKc, lintegral_indicator hcellm]; exact hEfin
  have hKcv : (∫⁻ p, Kc (p + v)) = ∫⁻ p, Kc p := lintegral_add_right_eq_self _ _
  -- slice function
  set Ks : Profile → ℝ≥0∞ := fun w => ‖g (Φ w)‖ₑ ^ (2 : ℝ) * UnforcedLeray.B0220.weightH w with hKs
  have hKsm : Measurable Ks :=
    ((hg.comp hΦm).enorm.pow_const _).mul UnforcedLeray.B0220.measurable_weightH
  have hpt : ∀ w, W.indicator Ks w ≤ Kc w + Kc (w + v) := by
    intro w
    by_cases hw : w ∈ W
    · rw [indicator_of_mem hw]
      rcases reduceIoc_window hc hw.2.1 with e | e
      · have hΦw : Φ w = w := by simp [hΦ, e]
        have hwc : w ∈ UnforcedLeray.B0220.cell c := by
          refine ⟨hw.1, ?_, trivial⟩
          have := UnforcedLeray.B0220.reduceIoc_mem hc w.2.1
          rwa [e] at this
        simp only [hKs, hKc, hΦw, indicator_of_mem hwc]
        exact le_self_add
      · have hΦw : Φ w = w + v := by
          simp only [hΦ, e, hv]
          ext <;> simp
        have hwc : w + v ∈ UnforcedLeray.B0220.cell c := by
          rw [← hΦw]
          exact ⟨hw.1, UnforcedLeray.B0220.reduceIoc_mem hc _, trivial⟩
        have hs : (w + v).1 = w.1 := by simp [hv]
        simp only [hKs, hKc, hΦw, indicator_of_mem hwc]
        rw [show UnforcedLeray.B0220.weightH w = UnforcedLeray.B0220.weightH (w + v) by
          unfold UnforcedLeray.B0220.weightH; rw [hs]]
        exact le_add_self
    · rw [indicator_of_notMem hw]; exact bot_le
  have hbound : (∫⁻ w in W, Ks w) ≤ (∫⁻ p, Kc p) + ∫⁻ p, Kc p := by
    rw [← lintegral_indicator hWm]
    calc (∫⁻ w, W.indicator Ks w) ≤ ∫⁻ w, (Kc w + Kc (w + v)) := lintegral_mono hpt
      _ = _ := by rw [lintegral_add_left hKcm, hKcv]
  have hprod : ((volume : Measure ℝ).restrict (Ioi 0)).prod (UnforcedLeray.Cyl.cellμ c) =
      (volume : Measure Profile).restrict W := by
    unfold UnforcedLeray.Cyl.cellμ
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    rfl
  have hFin : ∫⁻ s in Ioi (0 : ℝ), ∫⁻ z, Ks (s, z) ∂(UnforcedLeray.Cyl.cellμ c) < ⊤ := by
    rw [← lintegral_prod _ hKsm.aemeasurable, hprod]
    exact lt_of_le_of_lt hbound (ENNReal.add_lt_top.2 ⟨hKcint, hKcint⟩)
  have hFm : Measurable fun s : ℝ => ∫⁻ z, Ks (s, z) ∂(UnforcedLeray.Cyl.cellμ c) :=
    hKsm.lintegral_prod_right'
  have hfinS : ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))),
      ∫⁻ z, Ks (s, z) ∂(UnforcedLeray.Cyl.cellμ c) < ⊤ :=
    ae_lt_top hFm hFin.ne
  -- a.e. identification of the slice with g ∘ Φ
  have hQs : ∀ᵐ s ∂(volume : Measure ℝ), ∀ᵐ z ∂(volume : Measure (ℝ × ℝ)),
      (s, z) ∈ W → f (Φ (s, z)) = g (Φ (s, z)) := Measure.ae_ae_of_ae_prod hQ
  have hmem : ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))), s ∈ Ioi (0 : ℝ) :=
    ae_restrict_mem measurableSet_Ioi
  filter_upwards [ae_restrict_of_ae hQs, hfinS, hmem] with s h1 h2 h3 j
  have h1' : ∀ᵐ z ∂(UnforcedLeray.Cyl.cellμ c), (s, z) ∈ W → f (Φ (s, z)) = g (Φ (s, z)) :=
    ae_restrict_of_ae h1
  have hsl : (fun z => sliceFn h s z j) =ᵐ[UnforcedLeray.Cyl.cellμ c]
      fun z => g (Φ (s, z)) j := by
    filter_upwards [h1', ae_restrict_mem (UnforcedLeray.Cyl.measurableSet_cell c)] with z a hz
    have := a ⟨h3, hz⟩
    simp only [sliceFn, hΦ] at this ⊢
    rw [show (h : Profile → MeridC) = f from rfl, this]
  have hGs : Measurable fun z : ℝ × ℝ => g (Φ (s, z)) :=
    (hg.comp hΦm).comp measurable_prodMk_left
  have hGm : Measurable fun z : ℝ × ℝ => g (Φ (s, z)) j :=
    (EuclideanSpace.proj (𝕜 := ℂ) j).continuous.measurable.comp hGs
  have hw0 : UnforcedLeray.B0220.weightH (s, (0 : ℝ × ℝ)) ≠ 0 := by
    unfold UnforcedLeray.B0220.weightH
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    have : 0 < s := h3
    positivity
  have hAfin : ∫⁻ z, ‖g (Φ (s, z))‖ₑ ^ (2 : ℝ) ∂(UnforcedLeray.Cyl.cellμ c) < ⊤ := by
    by_contra hcon
    have htop : ∫⁻ z, ‖g (Φ (s, z))‖ₑ ^ (2 : ℝ) ∂(UnforcedLeray.Cyl.cellμ c) = ⊤ :=
      not_lt_top_iff.1 hcon
    have e : ∫⁻ z, Ks (s, z) ∂(UnforcedLeray.Cyl.cellμ c)
        = (∫⁻ z, ‖g (Φ (s, z))‖ₑ ^ (2 : ℝ) ∂(UnforcedLeray.Cyl.cellμ c)) *
          UnforcedLeray.B0220.weightH (s, (0 : ℝ × ℝ)) := by
      rw [← lintegral_mul_const _ (hGs.enorm.pow_const _)]
      rfl
    rw [e, htop, ENNReal.top_mul hw0] at h2
    exact lt_irrefl _ h2
  refine MemLp.ae_eq hsl.symm ?_
  refine ⟨hGm.aestronglyMeasurable, ?_⟩
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num)]
  refine lt_of_le_of_lt (lintegral_mono fun z => ?_) hAfin
  simp only [ENNReal.toReal_ofNat]
  refine ENNReal.rpow_le_rpow ?_ (by norm_num)
  rw [← ofReal_norm, ← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal (PiLp.norm_apply_le _ j)

end UnforcedLeray.Short.PartIIa.N01.Sub
