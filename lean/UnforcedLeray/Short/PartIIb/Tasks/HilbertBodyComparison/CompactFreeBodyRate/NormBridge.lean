import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T16
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.NvCInYr
import UnforcedLeray.Short.PartIIa.StatementsNear

/-!
# Measure and `H_2` norm dictionary between `B0220.HSpace c MeridC` and `IIb.InHr c 2`

Connects the profile space `IIb.InHr c 2` (with norm `IIb.hNorm c 2` over `IIb.hMeas c 2`) to the
Hilbert space `B0220.HSpace c B0223.MeridC` (with measure `B0220.measureH c`) for `PartII-b:T16/1`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.IIb.CompactFreeRateSub

open UnforcedLeray.B0220 UnforcedLeray.B0223

theorem eLpNorm_two_sq {α : Type*} [MeasurableSpace α] {E : Type*} [NormedAddCommGroup E]
    (f : α → E) (μ : Measure α) :
    eLpNorm f 2 μ ^ (2 : ℝ) = ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ := by
  simpa using eLpNorm_nnreal_pow_eq_lintegral (f := f) (μ := μ) (p := 2) (by norm_num)

theorem lintegral_Ico_eq_Ioc_periodic {c : ℝ} (hc : 0 < c) {h : ℝ → ℝ≥0∞}
    (hper : Function.Periodic h c) :
    ∫⁻ q in Ico (-c / 2) (c / 2), h q = ∫⁻ q in Ioc 0 c, h q := by
  have hlen : c / 2 = -c / 2 + c := by ring
  have hae : (Ico (-c / 2) (c / 2) : Set ℝ) =ᵐ[volume] Ioc (-c / 2) (-c / 2 + c) := by
    rw [hlen]
    exact Ico_ae_eq_Ioc
  rw [setLIntegral_congr hae]
  have : Fact (0 < c) := ⟨hc⟩
  have e1 := AddCircle.lintegral_preimage (T := c) (-c / 2) hper.lift
  have e2 := AddCircle.lintegral_preimage (T := c) 0 hper.lift
  simp only [Function.Periodic.lift_coe, zero_add] at e1 e2
  rw [e1, e2]

theorem lintegral_qCell_eq_cell_periodic {c : ℝ} (hc : 0 < c) {g : Profile → ℝ≥0∞}
    (hgm : Measurable g) (hper : B0220.QPeriodic c g) :
    ∫⁻ p in Ioi (0 : ℝ) ×ˢ UnforcedLeray.Axi.qCell c, g p = ∫⁻ p in B0220.cell c, g p := by
  unfold UnforcedLeray.Axi.qCell B0220.cell
  rw [Measure.volume_eq_prod (α := ℝ) (β := ℝ × ℝ), ← Measure.prod_restrict, ← Measure.prod_restrict,
    lintegral_prod _ hgm.aemeasurable, lintegral_prod _ hgm.aemeasurable]
  refine lintegral_congr fun s => ?_
  rw [Measure.volume_eq_prod (α := ℝ) (β := ℝ), ← Measure.prod_restrict, ← Measure.prod_restrict]
  have hgs : Measurable fun x : ℝ × ℝ => g (s, x) :=
    hgm.comp (measurable_const.prodMk measurable_id)
  rw [lintegral_prod _ hgs.aemeasurable, lintegral_prod _ hgs.aemeasurable]
  have hswap1 := lintegral_lintegral_swap
    (μ := (volume : Measure ℝ).restrict (Ico (-c / 2) (c / 2)))
    (ν := (volume : Measure ℝ).restrict univ)
    (f := fun q η => g (s, q, η)) hgs.aemeasurable
  have hswap2 := lintegral_lintegral_swap
    (μ := (volume : Measure ℝ).restrict (Ioc 0 c))
    (ν := (volume : Measure ℝ).restrict univ)
    (f := fun q η => g (s, q, η)) hgs.aemeasurable
  rw [hswap1, hswap2]
  refine lintegral_congr fun η => ?_
  exact lintegral_Ico_eq_Ioc_periodic hc (fun q => hper (s, q, η))

theorem lintegral_hMeas_two_eq {c : ℝ} (hc : 0 < c) {f : Profile → MeridC}
    (hfm : Measurable f) (hper : B0220.QPeriodic c f) :
    ∫⁻ p, ‖f p‖ₑ ^ (2 : ℝ) ∂(hMeas c 2) =
      ENNReal.ofReal c⁻¹ * ∫⁻ p, ‖f p‖ₑ ^ (2 : ℝ) ∂(measureH c) := by
  have hexp : (2 : ℝ) / 2 - 5 / 2 = -(3 / 2 : ℝ) := by norm_num
  unfold hMeas
  rw [hexp, UnforcedLeray.Axi.lintegral_ageμ hc (-(3 / 2 : ℝ)) (hfm.enorm.pow_const _)]
  have hfactor : ∀ p : Profile,
      ENNReal.ofReal (c⁻¹ * p.1 ^ (-(3 / 2 : ℝ))) * ‖f p‖ₑ ^ (2 : ℝ) =
        ENNReal.ofReal c⁻¹ * (weightH p * ‖f p‖ₑ ^ (2 : ℝ)) := fun p => by
    rw [ENNReal.ofReal_mul (inv_nonneg.2 hc.le), weightH, mul_assoc]
  simp_rw [hfactor]
  have hgm : Measurable fun p : Profile => weightH p * ‖f p‖ₑ ^ (2 : ℝ) :=
    measurable_weightH.mul (hfm.enorm.pow_const _)
  have hgper : B0220.QPeriodic c (fun p : Profile => weightH p * ‖f p‖ₑ ^ (2 : ℝ)) := fun p => by
    show weightH (p.1, p.2.1 + c, p.2.2) * ‖f (p.1, p.2.1 + c, p.2.2)‖ₑ ^ (2 : ℝ) = _
    rw [hper p]
    rfl
  have hwd : ∫⁻ p, ‖f p‖ₑ ^ (2 : ℝ) ∂(measureH c) =
      ∫⁻ p in B0220.cell c, weightH p * ‖f p‖ₑ ^ (2 : ℝ) :=
    lintegral_withDensity_eq_lintegral_mul _ measurable_weightH (hfm.enorm.pow_const _)
  rw [lintegral_const_mul _ hgm, lintegral_qCell_eq_cell_periodic hc hgm hgper, ← hwd]

theorem hNorm_two_eq {c : ℝ} (hc : 0 < c) {f : Profile → MeridC}
    (hfm : Measurable f) (hper : B0220.QPeriodic c f) :
    hNorm c 2 f = ENNReal.ofReal (Real.sqrt c⁻¹) * eLpNorm f 2 (measureH c) := by
  have h2 : ENNReal.ofReal (2 : ℝ) = 2 := by norm_num
  unfold hNorm
  rw [h2]
  have hc_sq : ENNReal.ofReal (Real.sqrt c⁻¹) ^ (2 : ℝ) = ENNReal.ofReal c⁻¹ := by
    rw [ENNReal.ofReal_rpow_of_nonneg (Real.sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 2),
      Real.rpow_two, Real.sq_sqrt (inv_nonneg.2 hc.le)]
  have hsq : eLpNorm f 2 (hMeas c 2) ^ (2 : ℝ) =
      (ENNReal.ofReal (Real.sqrt c⁻¹) * eLpNorm f 2 (measureH c)) ^ (2 : ℝ) := by
    rw [eLpNorm_two_sq, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2),
      eLpNorm_two_sq, hc_sq]
    exact lintegral_hMeas_two_eq hc hfm hper
  apply le_antisymm <;> rw [← ENNReal.rpow_le_rpow_iff (by norm_num : (0 : ℝ) < 2), hsq]

theorem measurable_periodize_merid (c : ℝ) {f : Profile → MeridC} (hf : Measurable f) :
    Measurable (periodize c f) :=
  hf.comp (measurable_fst.prodMk
    (((measurable_reduceIoc c).comp (measurable_fst.comp measurable_snd)).prodMk
      (measurable_snd.comp measurable_snd)))

theorem periodize_ae_measureH {c : ℝ} (hc : 0 < c) (W : HSpace c MeridC) :
    periodize c (W : Profile → MeridC) =ᵐ[measureH c] (W : Profile → MeridC) := by
  filter_upwards [ae_cell_measureH c] with p hp
  exact periodize_of_mem hc (W : Profile → MeridC) hp

theorem inHr_periodize {c : ℝ} (hc : 0 < c) (w : HSpace c MeridC) :
    InHr c 2 (periodize c (w : Profile → MeridC)) := by
  have hwm : Measurable (periodize c (w : Profile → MeridC)) :=
    measurable_periodize_merid c (Lp.stronglyMeasurable w).measurable
  have hwper : B0220.QPeriodic c (periodize c (w : Profile → MeridC)) :=
    qPeriodic_periodize hc (w : Profile → MeridC)
  refine ⟨Eventually.of_forall fun p => hwper p, hwm.aestronglyMeasurable, ?_⟩
  rw [hNorm_two_eq hc hwm hwper, eLpNorm_congr_ae (periodize_ae_measureH hc w)]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (Lp.eLpNorm_lt_top w)

theorem ageμ_nonpos_null {c a : ℝ} (hc : 0 < c) :
    UnforcedLeray.Axi.ageμ c a {x : Profile | ¬ 0 < x.1} = 0 := by
  have hm : MeasurableSet {x : Profile | ¬ 0 < x.1} :=
    (measurableSet_Ioi.preimage measurable_fst).compl
  have h := UnforcedLeray.Axi.lintegral_ageμ hc a
    (f := ({x : Profile | ¬ 0 < x.1} : Set Profile).indicator 1) (measurable_one.indicator hm)
  rw [lintegral_indicator_one hm] at h
  rw [h]
  have h0 : ∀ p ∈ Ioi (0 : ℝ) ×ˢ UnforcedLeray.Axi.qCell c,
      ENNReal.ofReal (c⁻¹ * p.1 ^ a) *
        ({x : Profile | ¬ 0 < x.1} : Set Profile).indicator (1 : Profile → ℝ≥0∞) p = 0 := by
    intro p hp
    have hnot : p ∉ ({x : Profile | ¬ 0 < x.1} : Set Profile) := not_not.2 hp.1
    rw [Set.indicator_of_notMem hnot, mul_zero]
  have hms : MeasurableSet (Ioi (0 : ℝ) ×ˢ UnforcedLeray.Axi.qCell c) :=
    measurableSet_Ioi.prod (measurableSet_Ico.prod MeasurableSet.univ)
  rw [setLIntegral_congr_fun hms h0]
  simp

theorem ae_hMeas_of_ae_pos {c r : ℝ} (hc : 0 < c) {f g : CProf}
    (h : ∀ᵐ x ∂(volume : Measure Coord), 0 < x.1 → f x = g x) :
    f =ᵐ[hMeas c r] g := by
  have hnull : volume {x : Coord | ¬(0 < x.1 → f x = g x)} = 0 := ae_iff.1 h
  obtain ⟨E, hsub, hEm, hE0⟩ := exists_measurable_superset_of_null hnull
  have h1 : ∀ᵐ x ∂(hMeas c r), x ∉ E :=
    measure_eq_zero_iff_ae_notMem.1 (ageμ_null_of_volume_null hc hEm hE0)
  have h2 : ∀ᵐ x ∂(hMeas c r), 0 < x.1 := by
    rw [ae_iff]
    exact ageμ_nonpos_null hc
  filter_upwards [h1, h2] with x hxE hxpos
  by_contra hne
  exact hxE (hsub fun hp => absurd (hp hxpos) hne)

theorem exists_hs_rep {c : ℝ} (hc : 0 < c) (F : CProf) (hF : InHr c 2 F) :
    ∃ (F' : CProf) (M : Set Coord) (FH : HSpace c MeridC),
      Measurable F' ∧
      (∀ s q η, F' (s, (q + c, η)) = F' (s, (q, η))) ∧
      MeasurableSet M ∧ volume M = 0 ∧
      (∀ s q η, (s, (q + c, η)) ∈ M ↔ (s, (q, η)) ∈ M) ∧
      (∀ x : Coord, 0 < x.1 → x ∉ M → F x = F' x) ∧
      F' =ᵐ[hMeas c 2] F ∧
      (FH : Profile → MeridC) =ᵐ[measureH c] F' ∧
      ENNReal.ofReal (Real.sqrt c⁻¹) * ENNReal.ofReal ‖FH‖ = hNorm c 2 F := by
  obtain ⟨F', M, hF'm, hF'per, hMm, hM0, hMper, hFF'⟩ :=
    periodicRepresentative c 2 hc F hF.periodic hF.meas
  have hF'per_B : B0220.QPeriodic c F' := fun p => hF'per p.1 p.2.1 p.2.2
  have hF'_ae : F' =ᵐ[hMeas c 2] F := by
    refine ae_hMeas_of_ae_pos hc ?_
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hM0] with x hxM hxpos
    exact (hFF' x hxpos hxM).symm
  have hF'_norm_eq : ENNReal.ofReal (Real.sqrt c⁻¹) * eLpNorm F' 2 (measureH c) = hNorm c 2 F := by
    rw [← hNorm_two_eq hc hF'm hF'per_B]
    exact eLpNorm_congr_ae hF'_ae
  have hF'_lt : eLpNorm F' 2 (measureH c) < ⊤ := by
    have hlt : ENNReal.ofReal (Real.sqrt c⁻¹) * eLpNorm F' 2 (measureH c) < ⊤ := by
      rw [hF'_norm_eq]
      exact hF.finite
    have hne : ENNReal.ofReal (Real.sqrt c⁻¹) ≠ 0 :=
      (ENNReal.ofReal_pos.2 (Real.sqrt_pos.2 (inv_pos.2 hc))).ne'
    exact ENNReal.lt_top_of_mul_ne_top_right hlt.ne hne
  have hF'_mem : MemLp F' 2 (measureH c) := ⟨hF'm.aestronglyMeasurable, hF'_lt⟩
  let FH : HSpace c MeridC := hF'_mem.toLp F'
  refine ⟨F', M, FH, hF'm, hF'per, hMm, hM0, hMper, hFF', hF'_ae, hF'_mem.coeFn_toLp, ?_⟩
  rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top FH),
    eLpNorm_congr_ae hF'_mem.coeFn_toLp, hF'_norm_eq]

theorem hNorm_indBox_periodize_le_mulChi {c s0 s1 L : ℝ} (hc : 0 < c)
    {χ : Profile → ℝ} (hm : Measurable χ) (hB : ∀ p, |χ p| ≤ 1)
    (h1 : ∀ p : Profile, s0 ≤ p.1 → p.1 ≤ s1 → |p.2.2| ≤ L → χ p = 1)
    (D : HSpace c MeridC) :
    hNorm c 2 (indBox s0 s1 L (periodize c (D : Profile → MeridC))) ≤
      ENNReal.ofReal (Real.sqrt c⁻¹) *
        ENNReal.ofReal ‖UnforcedLeray.Short.PartIIa.mulChi (measureH c) χ hm hB D‖ := by
  set dPer : Profile → MeridC := periodize c (D : Profile → MeridC)
  have hd_m : Measurable dPer := measurable_periodize_merid c (Lp.stronglyMeasurable D).measurable
  have hd_per : B0220.QPeriodic c dPer := qPeriodic_periodize hc (D : Profile → MeridC)
  have hind_m : Measurable (indBox s0 s1 L dPer) :=
    hd_m.indicator (measurableSet_obsBox s0 s1 L)
  have hind_per : B0220.QPeriodic c (indBox s0 s1 L dPer) := fun p => by
    unfold indBox
    have hiff : (p.1, p.2.1 + c, p.2.2) ∈ obsBox s0 s1 L ↔ p ∈ obsBox s0 s1 L := by
      simp [obsBox]
    by_cases hp : p ∈ obsBox s0 s1 L
    · rw [Set.indicator_of_mem (hiff.2 hp), Set.indicator_of_mem hp]
      exact hd_per p
    · rw [Set.indicator_of_notMem (mt hiff.1 hp), Set.indicator_of_notMem hp]
  rw [hNorm_two_eq hc hind_m hind_per]
  gcongr
  set M := UnforcedLeray.Short.PartIIa.mulChi (measureH c) χ hm hB D
  have hM_coe : (M : Profile → MeridC) =ᵐ[measureH c] fun p => χ p • (D : Profile → MeridC) p :=
    (UnforcedLeray.Short.PartIIa.memLp_chi_smul (measureH c) χ hm hB (Lp.memLp D)).coeFn_toLp
  have hle_ae : ∀ᵐ p ∂(measureH c), ‖indBox s0 s1 L dPer p‖ ≤ ‖(M : Profile → MeridC) p‖ := by
    filter_upwards [periodize_ae_measureH hc D, hM_coe] with p hp_per hp_chi
    rw [hp_chi, norm_smul, Real.norm_eq_abs, ← hp_per]
    unfold indBox
    by_cases hp : p ∈ obsBox s0 s1 L
    · rw [Set.indicator_of_mem hp, h1 p hp.1.1 hp.1.2 (abs_le.2 hp.2.2), abs_one, one_mul]
    · rw [Set.indicator_of_notMem hp, norm_zero]
      positivity
  calc eLpNorm (indBox s0 s1 L dPer) 2 (measureH c)
      ≤ eLpNorm (M : Profile → MeridC) 2 (measureH c) := eLpNorm_mono_ae hle_ae
    _ = ENNReal.ofReal ‖M‖ := by
        rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top M)]

end UnforcedLeray.Short.IIb.CompactFreeRateSub
