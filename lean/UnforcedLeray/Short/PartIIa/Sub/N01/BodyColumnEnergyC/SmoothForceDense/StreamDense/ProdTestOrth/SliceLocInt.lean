import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N01_9_1_1_3_2
import UnforcedLeray.Short.PartIIa.Sub.N01.BodyColumnEnergyC.SmoothForceDense.StreamDense.SliceVanish

/-!
# `SliceLocInt` (source lines 1684-1689): local integrability of the weighted slice integrals

For `h ∈ 𝓗` and a cylinder test `ψ`, the weighted slice integrals `s ↦ s^{-3/2} divI(slice_s) ψ`
and `s ↦ s^{-3/2} curlI(slice_s) ψ` are locally integrable on `(0,∞)`.

* `sliceLocInt_rep`: the measurable representative `g` of `h`, the covering bound
  `∫⁻_{(0,∞)×[-c/2,c/2)×ℝ} ‖g(Φ w)‖² s^{-3/2} < ∞` (translation and periodicity, as in
  `SliceL2`), and the a.e. slice identity.
* `sliceLocInt_kernel`: for continuous kernels `A`, `B` vanishing for `|η|` large, the weighted
  integral `s ↦ s^{-3/2} ∫_cell (w_s₀ A + w_s₁ B)` is integrable on each `[a,b] ⊂ (0,∞)`
  (Cauchy-Schwarz-free: `ρ‖g∘Φ‖ ≤ a^{-3/2} + ρ‖g∘Φ‖²` on a box, Fubini).
* `sliceLocInt_locInt`: `IntegrableOn` on compact subintervals gives `LocallyIntegrableOn`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIa.N01.Sub

open UnforcedLeray.B0220 (Profile HSpace measureH reduceIoc)
open UnforcedLeray.B0223 (MeridC)

/-- The measurable representative `g` of `h`, its weighted `L²` bound on the covering window, and
the a.e. slice identity (as in `SliceL2`). -/
theorem sliceLocInt_rep {c : ℝ} (hc : 0 < c) (h : HSpace c MeridC) :
    ∃ g : Profile → MeridC, Measurable g ∧
      (∫⁻ w in Ioi (0 : ℝ) ×ˢ (Ico (-c / 2) (c / 2) ×ˢ (univ : Set ℝ)),
          ‖g (w.1, reduceIoc c w.2.1, w.2.2)‖ₑ ^ (2 : ℝ) * UnforcedLeray.B0220.weightH w) < ⊤ ∧
      ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))), ∀ᵐ z ∂(UnforcedLeray.Cyl.cellμ c),
        ∀ j, sliceFn h s z j = g (s, reduceIoc c z.1, z.2) j := by
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
  have hWfin : (∫⁻ w in W, Ks w) < ⊤ :=
    lt_of_le_of_lt hbound (ENNReal.add_lt_top.2 ⟨hKcint, hKcint⟩)
  refine ⟨g, hg, hWfin, ?_⟩
  -- a.e. identification of the slice with g ∘ Φ
  have hQs : ∀ᵐ s ∂(volume : Measure ℝ), ∀ᵐ z ∂(volume : Measure (ℝ × ℝ)),
      (s, z) ∈ W → f (Φ (s, z)) = g (Φ (s, z)) := Measure.ae_ae_of_ae_prod hQ
  have hmem : ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))), s ∈ Ioi (0 : ℝ) :=
    ae_restrict_mem measurableSet_Ioi
  filter_upwards [ae_restrict_of_ae hQs, hmem] with s h1 h3
  have h1' : ∀ᵐ z ∂(UnforcedLeray.Cyl.cellμ c), (s, z) ∈ W → f (Φ (s, z)) = g (Φ (s, z)) :=
    ae_restrict_of_ae h1
  filter_upwards [h1', ae_restrict_mem (UnforcedLeray.Cyl.measurableSet_cell c)] with z a hz j
  have e : f (s, reduceIoc c z.1, z.2) = g (s, reduceIoc c z.1, z.2) := a ⟨h3, hz⟩
  show (f (s, reduceIoc c z.1, z.2)) j = g (s, reduceIoc c z.1, z.2) j
  rw [e]

/-- Local integrability from integrability on compact subintervals `[a,b] ⊂ (0,∞)`. -/
theorem sliceLocInt_locInt (F : ℝ → ℂ)
    (hF : ∀ a b : ℝ, 0 < a → a ≤ b → IntegrableOn F (Icc a b) volume) :
    LocallyIntegrableOn F (Ioi 0) volume := by
  intro x hx
  have hx0 : 0 < x := hx
  exact ⟨Icc (x / 2) (2 * x),
    mem_nhdsWithin_of_mem_nhds (Icc_mem_nhds (by linarith) (by linarith)),
    hF _ _ (by linarith) (by linarith)⟩

/-- The core: integrability of the weighted slice integral for continuous kernels `A`, `B`
vanishing for `|η|` large. -/
theorem sliceLocInt_kernel {c : ℝ} (hc : 0 < c) (h : HSpace c MeridC)
    (A B : ℝ × ℝ → ℝ) (hA : Continuous A) (hB : Continuous B)
    (hR : ∃ R : ℝ, ∀ z : ℝ × ℝ, R < |z.2| → A z = 0 ∧ B z = 0) (a b : ℝ) (ha : 0 < a)
    (hab : a ≤ b) :
    IntegrableOn (fun s : ℝ => ((s ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) *
      ∫ z in UnforcedLeray.Cyl.cell c,
        (sliceFn h s z 0 * (A z : ℂ) + sliceFn h s z 1 * (B z : ℂ))) (Icc a b) volume := by
  obtain ⟨g, hg, hWfin, hslice⟩ := sliceLocInt_rep hc h
  obtain ⟨R, hR⟩ := hR
  set Bset : Set (ℝ × ℝ) := Ico (-c / 2) (c / 2) ×ˢ Icc (-R) R with hBset
  set K0 : Set (ℝ × ℝ) := Icc (-c / 2) (c / 2) ×ˢ Icc (-R) R with hK0
  set P : Set (ℝ × (ℝ × ℝ)) := Icc a b ×ˢ Bset with hP
  have hBm : MeasurableSet Bset := measurableSet_Ico.prod measurableSet_Icc
  have hPm : MeasurableSet P := measurableSet_Icc.prod hBm
  have hK0c : IsCompact K0 := isCompact_Icc.prod isCompact_Icc
  have hBK : Bset ⊆ K0 := Set.prod_mono Ico_subset_Icc_self subset_rfl
  have hBcell : Bset ⊆ UnforcedLeray.Cyl.cell c := Set.prod_mono subset_rfl (subset_univ _)
  have hKP : P ⊆ Icc a b ×ˢ K0 := Set.prod_mono subset_rfl hBK
  have hPfin : volume P < ⊤ :=
    lt_of_le_of_lt (measure_mono hKP) (isCompact_Icc.prod hK0c).measure_lt_top
  have hPW : P ⊆ Ioi (0 : ℝ) ×ˢ (Ico (-c / 2) (c / 2) ×ˢ (univ : Set ℝ)) :=
    fun p hp => ⟨lt_of_lt_of_le ha hp.1.1, hp.2.1, mem_univ _⟩
  -- bounds on the kernels
  obtain ⟨MA, hMA⟩ := hK0c.exists_bound_of_continuousOn hA.continuousOn
  obtain ⟨MB, hMB⟩ := hK0c.exists_bound_of_continuousOn hB.continuousOn
  set M : ℝ := max (max MA MB) 0 with hMdef
  have hM0 : 0 ≤ M := le_max_right _ _
  have hAM : ∀ z ∈ Bset, ‖(A z : ℂ)‖ ≤ M := fun z hz => by
    rw [Complex.norm_real]
    exact (hMA z (hBK hz)).trans (le_max_of_le_left (le_max_left _ _))
  have hBM : ∀ z ∈ Bset, ‖(B z : ℂ)‖ ≤ M := fun z hz => by
    rw [Complex.norm_real]
    exact (hMB z (hBK hz)).trans (le_max_of_le_left (le_max_right _ _))
  -- vanishing off the box
  have hout : ∀ z : ℝ × ℝ, z ∉ Bset → z ∈ UnforcedLeray.Cyl.cell c → A z = 0 ∧ B z = 0 := by
    intro z hz hzc
    apply hR z
    by_contra hcon
    push_neg at hcon
    exact hz (Set.mk_mem_prod hzc.1 (abs_le.1 hcon))
  -- pointwise bound for the cell integrand
  have hpt : ∀ (s : ℝ) (z : ℝ × ℝ), z ∈ UnforcedLeray.Cyl.cell c →
      (∀ j, sliceFn h s z j = g (s, reduceIoc c z.1, z.2) j) →
      (z ∈ Bset → ‖sliceFn h s z 0 * (A z : ℂ) + sliceFn h s z 1 * (B z : ℂ)‖ ≤
        2 * M * ‖g (s, reduceIoc c z.1, z.2)‖) ∧
      (z ∉ Bset → sliceFn h s z 0 * (A z : ℂ) + sliceFn h s z 1 * (B z : ℂ) = 0) := by
    intro s z hzc hj
    have hN : ∀ j, ‖sliceFn h s z j‖ ≤ ‖g (s, reduceIoc c z.1, z.2)‖ := fun j => by
      rw [hj j]; exact PiLp.norm_apply_le _ j
    constructor
    · intro hz
      calc ‖sliceFn h s z 0 * (A z : ℂ) + sliceFn h s z 1 * (B z : ℂ)‖
          ≤ ‖sliceFn h s z 0 * (A z : ℂ)‖ + ‖sliceFn h s z 1 * (B z : ℂ)‖ := norm_add_le _ _
        _ = ‖sliceFn h s z 0‖ * ‖(A z : ℂ)‖ + ‖sliceFn h s z 1‖ * ‖(B z : ℂ)‖ := by
          rw [norm_mul, norm_mul]
        _ ≤ ‖g (s, reduceIoc c z.1, z.2)‖ * M + ‖g (s, reduceIoc c z.1, z.2)‖ * M :=
          add_le_add (mul_le_mul (hN 0) (hAM z hz) (norm_nonneg _) (norm_nonneg _))
            (mul_le_mul (hN 1) (hBM z hz) (norm_nonneg _) (norm_nonneg _))
        _ = 2 * M * ‖g (s, reduceIoc c z.1, z.2)‖ := by ring
    · intro hz
      obtain ⟨h1, h2⟩ := hout z hz hzc
      simp [h1, h2]
  -- measurability of the product integrand
  have hΦm : Measurable (fun p : ℝ × (ℝ × ℝ) => (p.1, reduceIoc c p.2.1, p.2.2)) :=
    measurable_fst.prodMk (((UnforcedLeray.B0220.measurable_reduceIoc c).comp
      (measurable_fst.comp measurable_snd)).prodMk (measurable_snd.comp measurable_snd))
  have hNm : Measurable (fun p : ℝ × (ℝ × ℝ) => ‖g (p.1, reduceIoc c p.2.1, p.2.2)‖) :=
    (hg.comp hΦm).norm
  have hρm : Measurable (fun p : ℝ × (ℝ × ℝ) => p.1 ^ (-(3 / 2 : ℝ))) :=
    measurable_fst.pow_const _
  -- the weighted L² bound on P
  have hweight : ∀ p : ℝ × (ℝ × ℝ), 0 ≤ p.1 →
      ‖p.1 ^ (-(3 / 2 : ℝ)) * ‖g (p.1, reduceIoc c p.2.1, p.2.2)‖ ^ 2‖ₑ =
        ‖g (p.1, reduceIoc c p.2.1, p.2.2)‖ₑ ^ (2 : ℝ) *
          UnforcedLeray.B0220.weightH p := by
    intro p hp
    have hr : 0 ≤ p.1 ^ (-(3 / 2 : ℝ)) := Real.rpow_nonneg hp _
    rw [enorm_mul, enorm_pow, enorm_norm, Real.enorm_eq_ofReal hr, ENNReal.rpow_two]
    simp only [UnforcedLeray.B0220.weightH]
    ring
  have hL2 : Integrable (fun p : ℝ × (ℝ × ℝ) => p.1 ^ (-(3 / 2 : ℝ)) *
      ‖g (p.1, reduceIoc c p.2.1, p.2.2)‖ ^ 2) (volume.restrict P) := by
    refine ⟨((hρm.mul (hNm.pow_const 2))).aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    calc ∫⁻ p, ‖p.1 ^ (-(3 / 2 : ℝ)) * ‖g (p.1, reduceIoc c p.2.1, p.2.2)‖ ^ 2‖ₑ ∂(volume.restrict P)
        ≤ ∫⁻ p, (‖g (p.1, reduceIoc c p.2.1, p.2.2)‖ₑ ^ (2 : ℝ) *
            UnforcedLeray.B0220.weightH p) ∂(volume.restrict P) := by
          apply lintegral_mono_ae
          filter_upwards [ae_restrict_mem hPm] with p hp
          exact le_of_eq (hweight p (ha.trans_le hp.1.1).le)
      _ ≤ ∫⁻ p in (Ioi (0 : ℝ) ×ˢ (Ico (-c / 2) (c / 2) ×ˢ (univ : Set ℝ))),
            (‖g (p.1, reduceIoc c p.2.1, p.2.2)‖ₑ ^ (2 : ℝ) *
              UnforcedLeray.B0220.weightH p) := lintegral_mono_set hPW
      _ < ⊤ := hWfin
  -- integrability of the weighted norm on P
  have hHp : Integrable (fun p : ℝ × (ℝ × ℝ) =>
      p.1 ^ (-(3 / 2 : ℝ)) * ‖g (p.1, reduceIoc c p.2.1, p.2.2)‖) (volume.restrict P) := by
    refine Integrable.mono' (g := fun p : ℝ × (ℝ × ℝ) =>
      a ^ (-(3 / 2 : ℝ)) + p.1 ^ (-(3 / 2 : ℝ)) * ‖g (p.1, reduceIoc c p.2.1, p.2.2)‖ ^ 2)
      ?_ ?_ ?_
    · exact (integrableOn_const hPfin.ne).add hL2
    · exact (hρm.mul hNm).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem hPm] with p hp
      have h0 : 0 ≤ p.1 := (ha.trans_le hp.1.1).le
      have hr0 : 0 ≤ p.1 ^ (-(3 / 2 : ℝ)) := Real.rpow_nonneg h0 _
      have hrA : p.1 ^ (-(3 / 2 : ℝ)) ≤ a ^ (-(3 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos ha hp.1.1 (by norm_num)
      rw [Real.norm_of_nonneg (mul_nonneg hr0 (norm_nonneg _))]
      nlinarith [mul_nonneg hr0 (sq_nonneg (‖g (p.1, reduceIoc c p.2.1, p.2.2)‖ - 1 / 2))]
  -- Fubini on the product of the two restricted measures
  have hprod : (volume.restrict (Icc a b)).prod (volume.restrict Bset) = volume.restrict P := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
  have hHpP : Integrable (fun p : ℝ × (ℝ × ℝ) =>
      p.1 ^ (-(3 / 2 : ℝ)) * ‖g (p.1, reduceIoc c p.2.1, p.2.2)‖)
      ((volume.restrict (Icc a b)).prod (volume.restrict Bset)) := by
    rw [hprod]; exact hHp
  have hMaj : Integrable (fun s : ℝ => ∫ z in Bset,
      2 * M * (s ^ (-(3 / 2 : ℝ)) * ‖g (s, reduceIoc c z.1, z.2)‖)) (volume.restrict (Icc a b)) :=
    Integrable.integral_prod_left (hHpP.const_mul (2 * M))
  have hae1 : ∀ᵐ s ∂(volume.restrict (Icc a b)), Integrable (fun z : ℝ × ℝ =>
      s ^ (-(3 / 2 : ℝ)) * ‖g (s, reduceIoc c z.1, z.2)‖) (volume.restrict Bset) :=
    hHpP.prod_right_ae
  -- measurability of the integrand of `F`
  have hK : Measurable (fun p : ℝ × (ℝ × ℝ) =>
      g (p.1, reduceIoc c p.2.1, p.2.2) 0 * (A p.2 : ℂ) +
        g (p.1, reduceIoc c p.2.1, p.2.2) 1 * (B p.2 : ℂ)) := by
    have hc0 : Measurable (fun p : ℝ × (ℝ × ℝ) => g (p.1, reduceIoc c p.2.1, p.2.2) 0) :=
      (EuclideanSpace.proj (𝕜 := ℂ) 0).continuous.measurable.comp (hg.comp hΦm)
    have hc1 : Measurable (fun p : ℝ × (ℝ × ℝ) => g (p.1, reduceIoc c p.2.1, p.2.2) 1) :=
      (EuclideanSpace.proj (𝕜 := ℂ) 1).continuous.measurable.comp (hg.comp hΦm)
    exact (hc0.mul (Complex.measurable_ofReal.comp (hA.measurable.comp measurable_snd))).add
      (hc1.mul (Complex.measurable_ofReal.comp (hB.measurable.comp measurable_snd)))
  have hI := (hK.stronglyMeasurable).integral_prod_right'
    (ν := UnforcedLeray.Cyl.cellμ c)
  have hGm : AEStronglyMeasurable (fun s : ℝ => ((s ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) *
      ∫ z, (g (s, reduceIoc c z.1, z.2) 0 * (A z : ℂ) + g (s, reduceIoc c z.1, z.2) 1 * (B z : ℂ))
        ∂(UnforcedLeray.Cyl.cellμ c)) (volume.restrict (Icc a b)) := by
    exact ((Complex.measurable_ofReal.comp (measurable_id.pow_const (-(3 / 2 : ℝ)))).mul
      hI.measurable).aestronglyMeasurable
  have hFG : (fun s : ℝ => ((s ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) *
      ∫ z in UnforcedLeray.Cyl.cell c,
        (sliceFn h s z 0 * (A z : ℂ) + sliceFn h s z 1 * (B z : ℂ))) =ᵐ[volume.restrict (Icc a b)]
      (fun s : ℝ => ((s ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) *
        ∫ z, (g (s, reduceIoc c z.1, z.2) 0 * (A z : ℂ) + g (s, reduceIoc c z.1, z.2) 1 * (B z : ℂ))
          ∂(UnforcedLeray.Cyl.cellμ c)) := by
    have hIcc : Icc a b ⊆ Ioi (0 : ℝ) := fun x hx => lt_of_lt_of_le ha hx.1
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hIcc hslice] with s hs
    congr 1
    apply integral_congr_ae
    filter_upwards [hs] with z hz
    simp only [hz 0, hz 1]
  -- the pointwise majorant
  have hbd : ∀ᵐ s ∂(volume.restrict (Icc a b)),
      ‖((s ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) *
        ∫ z in UnforcedLeray.Cyl.cell c,
          (sliceFn h s z 0 * (A z : ℂ) + sliceFn h s z 1 * (B z : ℂ))‖ ≤
        ∫ z in Bset, 2 * M * (s ^ (-(3 / 2 : ℝ)) * ‖g (s, reduceIoc c z.1, z.2)‖) := by
    have hIcc : Icc a b ⊆ Ioi (0 : ℝ) := fun x hx => lt_of_lt_of_le ha hx.1
    filter_upwards [hae1, ae_restrict_of_ae_restrict_of_subset hIcc hslice,
      ae_restrict_mem measurableSet_Icc] with s hs1 hs2 hs3
    have hρs : 0 ≤ s ^ (-(3 / 2 : ℝ)) := Real.rpow_nonneg (ha.trans_le hs3.1).le _
    have hs1' : IntegrableOn (fun z : ℝ × ℝ =>
        2 * M * (s ^ (-(3 / 2 : ℝ)) * ‖g (s, reduceIoc c z.1, z.2)‖)) Bset volume :=
      hs1.const_mul (2 * M)
    have hint : Integrable (fun z : ℝ × ℝ => indicator Bset (fun z =>
        2 * M * (s ^ (-(3 / 2 : ℝ)) * ‖g (s, reduceIoc c z.1, z.2)‖)) z)
        (volume.restrict (UnforcedLeray.Cyl.cell c)) :=
      (hs1'.integrable_indicator hBm).integrableOn
    calc ‖((s ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) *
          ∫ z in UnforcedLeray.Cyl.cell c,
            (sliceFn h s z 0 * (A z : ℂ) + sliceFn h s z 1 * (B z : ℂ))‖
        = s ^ (-(3 / 2 : ℝ)) * ‖∫ z in UnforcedLeray.Cyl.cell c,
            (sliceFn h s z 0 * (A z : ℂ) + sliceFn h s z 1 * (B z : ℂ))‖ := by
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hρs]
      _ ≤ s ^ (-(3 / 2 : ℝ)) * ∫ z in UnforcedLeray.Cyl.cell c,
            ‖sliceFn h s z 0 * (A z : ℂ) + sliceFn h s z 1 * (B z : ℂ)‖ :=
          mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) hρs
      _ = ∫ z in UnforcedLeray.Cyl.cell c,
            s ^ (-(3 / 2 : ℝ)) * ‖sliceFn h s z 0 * (A z : ℂ) + sliceFn h s z 1 * (B z : ℂ)‖ :=
          (integral_const_mul _ _).symm
      _ ≤ ∫ z in UnforcedLeray.Cyl.cell c, Bset.indicator (fun z =>
            2 * M * (s ^ (-(3 / 2 : ℝ)) * ‖g (s, reduceIoc c z.1, z.2)‖)) z := by
          apply integral_mono_of_nonneg
          · exact Eventually.of_forall (fun z => by positivity)
          · exact hint
          · filter_upwards [hs2, ae_restrict_mem (UnforcedLeray.Cyl.measurableSet_cell c)]
              with z hz hzc
            by_cases hzB : z ∈ Bset
            · rw [indicator_of_mem hzB]
              have hb := (hpt s z hzc hz).1 hzB
              calc s ^ (-(3 / 2 : ℝ)) * ‖sliceFn h s z 0 * (A z : ℂ) + sliceFn h s z 1 * (B z : ℂ)‖
                  ≤ s ^ (-(3 / 2 : ℝ)) * (2 * M * ‖g (s, reduceIoc c z.1, z.2)‖) :=
                    mul_le_mul_of_nonneg_left hb hρs
                _ = 2 * M * (s ^ (-(3 / 2 : ℝ)) * ‖g (s, reduceIoc c z.1, z.2)‖) := by ring
            · rw [indicator_of_notMem hzB, (hpt s z hzc hz).2 hzB]
              simp
      _ = ∫ z in Bset, 2 * M * (s ^ (-(3 / 2 : ℝ)) * ‖g (s, reduceIoc c z.1, z.2)‖) := by
          rw [setIntegral_indicator hBm, Set.inter_eq_right.2 hBcell]
  refine Integrable.mono' hMaj ?_ hbd
  exact hGm.congr hFG.symm

theorem sliceLocInt : UnforcedLeray.Short.PartIIa.N01.Sub.SliceLocInt := by
  intro c hc h ψ hψ
  have hd1 := hψ.dirDeriv (1, 0)
  have hd2 := hψ.dirDeriv (0, 1)
  obtain ⟨R1, hR1⟩ := hd1.bounded
  obtain ⟨R2, hR2⟩ := hd2.bounded
  have hRd : ∃ R : ℝ, ∀ z : ℝ × ℝ, R < |z.2| →
      fderiv ℝ ψ z (1, 0) = 0 ∧ fderiv ℝ ψ z (0, 1) = 0 :=
    ⟨max R1 R2, fun z hz => ⟨hR1 z (lt_of_le_of_lt (le_max_left _ _) hz),
      hR2 z (lt_of_le_of_lt (le_max_right _ _) hz)⟩⟩
  have hRc : ∃ R : ℝ, ∀ z : ℝ × ℝ, R < |z.2| →
      fderiv ℝ ψ z (0, 1) = 0 ∧ -fderiv ℝ ψ z (1, 0) = 0 :=
    ⟨max R1 R2, fun z hz => ⟨hR2 z (lt_of_le_of_lt (le_max_right _ _) hz),
      by rw [hR1 z (lt_of_le_of_lt (le_max_left _ _) hz), neg_zero]⟩⟩
  constructor
  · apply sliceLocInt_locInt
    intro a b ha hab
    exact sliceLocInt_kernel hc h (fun z => fderiv ℝ ψ z (1, 0)) (fun z => fderiv ℝ ψ z (0, 1))
      hd1.smooth.continuous hd2.smooth.continuous hRd a b ha hab
  · apply sliceLocInt_locInt
    intro a b ha hab
    have hfun : (fun s : ℝ => ((s ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) * curlI c (sliceFn h s) ψ) =
        (fun s : ℝ => ((s ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) *
          ∫ z in UnforcedLeray.Cyl.cell c,
            (sliceFn h s z 0 * ((fderiv ℝ ψ z (0, 1) : ℝ) : ℂ) +
              sliceFn h s z 1 * ((-fderiv ℝ ψ z (1, 0) : ℝ) : ℂ))) := by
      funext s
      congr 1
      unfold curlI
      congr 1
      funext z
      push_cast
      ring
    rw [hfun]
    exact sliceLocInt_kernel hc h (fun z => fderiv ℝ ψ z (0, 1)) (fun z => -fderiv ℝ ψ z (1, 0))
      hd2.smooth.continuous hd1.smooth.continuous.neg hRc a b ha hab

end UnforcedLeray.Short.PartIIa.N01.Sub
