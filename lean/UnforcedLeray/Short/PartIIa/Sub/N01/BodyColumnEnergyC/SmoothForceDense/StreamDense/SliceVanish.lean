import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N01_9_1_1_3

/-!
# `SliceVanish` (source lines 1684-1689): Fubini on the profile cell

The periodized slices of `h ∈ 𝓗` on the cylinder cell `[-c/2,c/2)` vanish a.e. in `z` for a.e. `s`;
the map `Φ(s,q,η) = (s, reduceIoc c q, η)` is a translation by `0` or `(0,c,0)` on this window, so
`h = 0` a.e. for `measureH c`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIa.N01.Sub

open UnforcedLeray.B0220 (Profile HSpace measureH reduceIoc)
open UnforcedLeray.B0223 (MeridC)

theorem reduceIoc_window {c : ℝ} (hc : 0 < c) {q : ℝ} (hq : q ∈ Ico (-c / 2) (c / 2)) :
    reduceIoc c q = q ∨ reduceIoc c q = q + c := by
  unfold reduceIoc
  rcases lt_or_ge 0 q with h0 | h0
  · left
    have : ⌈q / c⌉ = 1 := by
      rw [Int.ceil_eq_iff]
      constructor
      · simp; positivity
      · simp; rw [div_le_one hc]; linarith [hq.2]
    rw [this]; simp
  · right
    have : ⌈q / c⌉ = 0 := by
      rw [Int.ceil_eq_iff]
      constructor
      · simp; rw [lt_div_iff₀ hc]; linarith [hq.1]
      · simp; exact div_nonpos_of_nonpos_of_nonneg h0 hc.le
    rw [this]; simp

theorem sliceVanish : UnforcedLeray.Short.PartIIa.N01.Sub.SliceVanish := by
  intro c hc h hs
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
  set Φ : Profile → Profile := fun w => (w.1, reduceIoc c w.2.1, w.2.2) with hΦ
  have hΦm : Measurable Φ :=
    measurable_fst.prodMk (((UnforcedLeray.B0220.measurable_reduceIoc c).comp
      (measurable_fst.comp measurable_snd)).prodMk (measurable_snd.comp measurable_snd))
  set v : Profile := (0, c, 0) with hv
  set W : Set Profile := Ioi 0 ×ˢ (Ico (-c / 2) (c / 2) ×ˢ univ) with hW
  have hWm : MeasurableSet W :=
    measurableSet_Ioi.prod (measurableSet_Ico.prod MeasurableSet.univ)
  have hcellm := UnforcedLeray.B0220.measurableSet_cell c
  -- f = g a.e. on the cell
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
  have hGm : Measurable fun w : Profile => g (Φ w) := hg.comp hΦm
  have hQs : ∀ᵐ s ∂(volume : Measure ℝ), ∀ᵐ z ∂(volume : Measure (ℝ × ℝ)),
      (s, z) ∈ W → f (Φ (s, z)) = g (Φ (s, z)) := Measure.ae_ae_of_ae_prod hQ
  have hR1 : ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))), ∀ᵐ z ∂(UnforcedLeray.Cyl.cellμ c),
      g (Φ (s, z)) = 0 := by
    have hmem : ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))), s ∈ Ioi (0 : ℝ) :=
      ae_restrict_mem measurableSet_Ioi
    filter_upwards [ae_restrict_of_ae hQs, hs, hmem] with s h1 h2 h3
    have h1' : ∀ᵐ z ∂(UnforcedLeray.Cyl.cellμ c), (s, z) ∈ W → f (Φ (s, z)) = g (Φ (s, z)) :=
      ae_restrict_of_ae h1
    filter_upwards [h1', h2, ae_restrict_mem (UnforcedLeray.Cyl.measurableSet_cell c)]
      with z a b hz
    have hzW : (s, z) ∈ W := ⟨h3, hz⟩
    have hf0 : f (Φ (s, z)) = 0 := by
      ext j
      simpa [sliceFn, hf, hΦ] using congrFun (congrArg (fun x => (x : Fin 2 → ℂ)) b) j
    rw [← a hzW, hf0]
  have hR2 : ∀ᵐ w ∂(volume : Measure Profile), w ∈ W → g (Φ w) = 0 := by
    have hprod : ((volume : Measure ℝ).restrict (Ioi 0)).prod (UnforcedLeray.Cyl.cellμ c) =
        (volume : Measure Profile).restrict W := by
      unfold UnforcedLeray.Cyl.cellμ
      rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
      rfl
    have hset : MeasurableSet {w : Profile | g (Φ w) = 0} := hGm (measurableSet_singleton 0)
    have := (Measure.ae_prod_iff_ae_ae (μ := (volume : Measure ℝ).restrict (Ioi 0))
      (ν := UnforcedLeray.Cyl.cellμ c) (p := fun w : Profile => g (Φ w) = 0) hset).2 hR1
    rw [hprod, ae_restrict_iff' hWm] at this
    exact this
  set S : Set Profile := {w | ¬ (w ∈ W → g (Φ w) = 0)} with hS
  have hS0 : volume S = 0 := by
    have := hR2
    rw [ae_iff] at this
    exact this
  have hS1 : volume ((fun x : Profile => x + -v) ⁻¹' S) = 0 := by
    rw [measure_preimage_add_right (volume : Measure Profile) (-v) S]; exact hS0
  have hgz : ∀ᵐ p ∂(volume : Measure Profile), p ∈ UnforcedLeray.B0220.cell c → g p = 0 := by
    have a1 : ∀ᵐ w ∂(volume : Measure Profile), w ∉ S := measure_eq_zero_iff_ae_notMem.1 hS0
    have a2 : ∀ᵐ w ∂(volume : Measure Profile), w ∉ (fun x : Profile => x + -v) ⁻¹' S :=
      measure_eq_zero_iff_ae_notMem.1 hS1
    filter_upwards [a1, a2] with p h1 h2 hpc
    obtain ⟨hp1, hp2, -⟩ := hpc
    rcases lt_or_ge p.2.1 (c / 2) with hlt | hge
    · have hpW : p ∈ W := ⟨hp1, ⟨by linarith [hp2.1], hlt⟩, trivial⟩
      have h1' := h1
      simp only [hS, mem_ofPred_eq, not_not] at h1'
      have := h1' hpW
      have e : Φ p = p := by
        simp only [hΦ, UnforcedLeray.B0220.reduceIoc_of_mem hc hp2]
      rwa [e] at this
    · have h2' := h2
      simp only [mem_preimage, hS, mem_ofPred_eq, not_not] at h2'
      have hpW : p + -v ∈ W := by
        refine ⟨by simpa [hv] using hp1, ⟨?_, ?_⟩, trivial⟩ <;> simp [hv] <;> linarith [hp2.2]
      have := h2' hpW
      have e : Φ (p + -v) = p := by
        simp only [hΦ, hv]
        have : reduceIoc c (p.2.1 + -c) = p.2.1 := by
          rw [← UnforcedLeray.B0220.reduceIoc_add hc, show p.2.1 + -c + c = p.2.1 by ring]
          exact UnforcedLeray.B0220.reduceIoc_of_mem hc hp2
        ext <;> simp [this]
      rwa [e] at this
  have hg0 : g =ᵐ[measureH c] 0 := by
    unfold measureH
    rw [Filter.EventuallyEq, ae_withDensity_iff UnforcedLeray.B0220.measurable_weightH]
    unfold UnforcedLeray.B0220.cellMeasure
    rw [ae_restrict_iff' (UnforcedLeray.B0220.measurableSet_cell c)]
    filter_upwards [hgz] with p hp hpc _
    exact hp hpc
  exact Lp.eq_zero_iff_ae_eq_zero.2 (hfg.trans hg0)

end UnforcedLeray.Short.PartIIa.N01.Sub
