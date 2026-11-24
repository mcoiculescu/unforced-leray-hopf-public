import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2Org
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_1.ThinMass

/-!
# `PartIII-b:C/rep/5/1/2/1`: the thin mass bound `ThinMassBound`

Source `the November 2 reference manuscript` 5569-5584.

This file derives `ThinMassBound mZ` (for `3/2 < mZ`) from the accepted slice bound
`thinMassBoundSlice`. The steps are:

1. `ageμ c (-3/2)` is absolutely continuous with respect to `z1Measure c mZ`
   (`z1Measure` is `ageμ c (-1/2)` with density `W²`, and `ageμ c (-1/2)` is `ageμ c (-3/2)`
   with density `s`);
2. `∫_{a<s} ‖F‖ dageμ(-3/2) ≤ thinMass c F a` (transverse Hölder with the probability
   weight `c⁻¹ dq` on the cell `[-c/2, c/2)`);
3. `thinMassBoundSlice` and `‖f‖ₑ = z1Norm c mZ F` with `c^0 = 1`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-! ## 1. The age measure `ageμ c (-3/2)` lives on `s > 0` -/

private lemma tmb_ageμ_nonpos_zero {c : ℝ} (hc : 0 < c) (a : ℝ) :
    ageμ c a {p : Chart | p.1 ≤ 0} = 0 := by
  have hS : MeasurableSet {p : Chart | p.1 ≤ 0} :=
    measurableSet_le measurable_fst measurable_const
  rw [← lintegral_indicator_one hS, lintegral_ageμ hc a (measurable_one.indicator hS)]
  have hz : ∀ p ∈ Ioi (0 : ℝ) ×ˢ qCell c,
      ENNReal.ofReal (c⁻¹ * p.1 ^ a) * Set.indicator {p : Chart | p.1 ≤ 0} 1 p = 0 := by
    intro p hp
    have h0 : 0 < p.1 := hp.1
    have hn : ¬ (p.1 ≤ 0) := not_le.2 h0
    simp [Set.indicator, hn]
  rw [setLIntegral_congr_fun (measurableSet_halfCell c) hz, lintegral_zero]

private lemma tmb_ae_pos {c : ℝ} (hc : 0 < c) (a : ℝ) :
    ∀ᵐ p ∂(ageμ c a), 0 < p.1 := by
  rw [ae_iff]
  simpa only [not_lt] using tmb_ageμ_nonpos_zero hc a

/-- `ageμ c (-1/2) = ageμ c (-3/2)` with density `s` (the `s`-factor of the age weight). -/
private lemma tmb_half_eq {c : ℝ} (hc : 0 < c) :
    ageμ c (-1 / 2) = (ageμ c (-3 / 2)).withDensity fun p => ENNReal.ofReal p.1 := by
  refine Measure.ext fun A hA => ?_
  rw [withDensity_apply _ hA, ← lintegral_indicator hA, ← lintegral_indicator_one hA,
    lintegral_ageμ hc (-1 / 2) (measurable_one.indicator hA),
    lintegral_ageμ hc (-3 / 2)
      ((show Measurable fun p : Chart => ENNReal.ofReal p.1 from
        ENNReal.measurable_ofReal.comp measurable_fst).indicator hA)]
  refine setLIntegral_congr_fun (measurableSet_halfCell c) (fun p hp => ?_)
  have h0 : 0 < p.1 := hp.1
  have key : ENNReal.ofReal (c⁻¹ * p.1 ^ (-1 / 2 : ℝ))
      = ENNReal.ofReal (c⁻¹ * p.1 ^ (-3 / 2 : ℝ)) * ENNReal.ofReal p.1 := by
    rw [← ENNReal.ofReal_mul (mul_nonneg (inv_nonneg.2 hc.le) (Real.rpow_nonneg h0.le _))]
    congr 1
    have e : p.1 ^ (-3 / 2 : ℝ) * p.1 = p.1 ^ (-1 / 2 : ℝ) := by
      rw [← Real.rpow_add_one h0.ne']
      norm_num
    calc c⁻¹ * p.1 ^ (-1 / 2 : ℝ) = c⁻¹ * (p.1 ^ (-3 / 2 : ℝ) * p.1) := by rw [e]
      _ = c⁻¹ * p.1 ^ (-3 / 2 : ℝ) * p.1 := by ring
  by_cases hpA : p ∈ A
  · simp [Set.indicator, hpA, key]
  · simp [Set.indicator, hpA]

/-- The age measure `ageμ c (-3/2)` is absolutely continuous with respect to `z1Measure`. -/
private lemma tmb_ac {c mZ : ℝ} (hc : 0 < c) : ageμ c (-3 / 2) ≪ z1Measure c mZ := by
  have tw : ∀ p : Chart, 0 < UnforcedLeray.Short.IIIa.transWeight mZ p := fun p => by
    unfold UnforcedLeray.Short.IIIa.transWeight
    exact Real.rpow_pos_of_pos (by positivity) _
  have hw : Measurable fun p : Chart =>
      ENNReal.ofReal (UnforcedLeray.Short.IIIa.transWeight mZ p ^ 2) :=
    ENNReal.measurable_ofReal.comp (by unfold UnforcedLeray.Short.IIIa.transWeight; fun_prop)
  have hwne : ∀ p : Chart, ENNReal.ofReal (UnforcedLeray.Short.IIIa.transWeight mZ p ^ 2) ≠ 0 :=
    fun p => (ENNReal.ofReal_pos.2 (pow_pos (tw p) 2)).ne'
  intro N hN
  have h1 : ageμ c (-1 / 2) N = 0 := by
    unfold z1Measure at hN
    rw [withDensity_apply_eq_zero' hw.aemeasurable] at hN
    have hsub : N ⊆ {x : Chart | ENNReal.ofReal (UnforcedLeray.Short.IIIa.transWeight mZ x ^ 2) ≠ 0} ∩ N :=
      fun x hx => ⟨hwne x, hx⟩
    exact measure_mono_null hsub hN
  have hm1 : Measurable fun p : Chart => ENNReal.ofReal p.1 :=
    ENNReal.measurable_ofReal.comp measurable_fst
  rw [tmb_half_eq hc, withDensity_apply_eq_zero' hm1.aemeasurable] at h1
  refine measure_mono_null (fun x hx => ?_)
    (measure_union_null h1 (tmb_ageμ_nonpos_zero hc _))
  by_cases h0 : x.1 ≤ 0
  · exact Or.inr h0
  · exact Or.inl ⟨(ENNReal.ofReal_pos.2 (not_le.1 h0)).ne', hx⟩

/-! ## 2. The transverse Hölder bound on the cell -/

/-- Hölder on the cell `q ∈ [-c/2, c/2)` with the probability weight `c⁻¹ dq`. -/
private lemma tmb_holder {c : ℝ} (hc : 0 < c) {G : ℝ → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ q in Ico (-c / 2) (c / 2), ENNReal.ofReal c⁻¹ * G q
      ≤ (∫⁻ q in Ico (-c / 2) (c / 2), ENNReal.ofReal c⁻¹ * G q ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
  have hk : ENNReal.ofReal c⁻¹ ^ (1 / 2 : ℝ) * ENNReal.ofReal c⁻¹ ^ (1 / 2 : ℝ)
      = ENNReal.ofReal c⁻¹ := by
    rw [← pow_two, ← ENNReal.rpow_two, sq_rpow_half]
  have hpt : ∀ q : ℝ, ENNReal.ofReal c⁻¹ * G q
      = ENNReal.ofReal c⁻¹ ^ (1 / 2 : ℝ) * (ENNReal.ofReal c⁻¹ ^ (1 / 2 : ℝ) * G q) := by
    intro q
    rw [← mul_assoc, hk]
  have hf : AEMeasurable (fun _ : ℝ => ENNReal.ofReal c⁻¹ ^ (1 / 2 : ℝ))
      ((volume : Measure ℝ).restrict (Ico (-c / 2) (c / 2))) := aemeasurable_const
  have hg : AEMeasurable (fun q : ℝ => ENNReal.ofReal c⁻¹ ^ (1 / 2 : ℝ) * G q)
      ((volume : Measure ℝ).restrict (Ico (-c / 2) (c / 2))) :=
    (measurable_const.mul hG).aemeasurable
  have key := ENNReal.lintegral_mul_le_Lp_mul_Lq ((volume : Measure ℝ).restrict (Ico (-c / 2) (c / 2)))
    Real.HolderConjugate.two_two hf hg
  have h1 : ∫⁻ _q, (ENNReal.ofReal c⁻¹ ^ (1 / 2 : ℝ)) ^ (2 : ℝ)
      ∂((volume : Measure ℝ).restrict (Ico (-c / 2) (c / 2))) = 1 := by
    simp only [sq_rpow_half]
    rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ico,
      show c / 2 - -c / 2 = c by ring, ← ENNReal.ofReal_mul (inv_nonneg.2 hc.le),
      inv_mul_cancel₀ hc.ne', ENNReal.ofReal_one]
  have h2 : ∫⁻ q, (ENNReal.ofReal c⁻¹ ^ (1 / 2 : ℝ) * G q) ^ (2 : ℝ)
      ∂((volume : Measure ℝ).restrict (Ico (-c / 2) (c / 2)))
      = ∫⁻ q in Ico (-c / 2) (c / 2), ENNReal.ofReal c⁻¹ * G q ^ (2 : ℝ) := by
    refine lintegral_congr fun q => ?_
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2), sq_rpow_half]
  calc ∫⁻ q in Ico (-c / 2) (c / 2), ENNReal.ofReal c⁻¹ * G q
      = ∫⁻ q, ENNReal.ofReal c⁻¹ ^ (1 / 2 : ℝ) * (ENNReal.ofReal c⁻¹ ^ (1 / 2 : ℝ) * G q)
          ∂((volume : Measure ℝ).restrict (Ico (-c / 2) (c / 2))) :=
        lintegral_congr fun q => hpt q
    _ ≤ (∫⁻ _q, (ENNReal.ofReal c⁻¹ ^ (1 / 2 : ℝ)) ^ (2 : ℝ)
            ∂((volume : Measure ℝ).restrict (Ico (-c / 2) (c / 2)))) ^ (1 / 2 : ℝ)
          * (∫⁻ q, (ENNReal.ofReal c⁻¹ ^ (1 / 2 : ℝ) * G q) ^ (2 : ℝ)
            ∂((volume : Measure ℝ).restrict (Ico (-c / 2) (c / 2)))) ^ (1 / 2 : ℝ) := key
    _ = (∫⁻ q in Ico (-c / 2) (c / 2), ENNReal.ofReal c⁻¹ * G q ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
        rw [h1, h2, ENNReal.one_rpow, one_mul]

/-! ## 3. The pointwise slice bound -/

/-- At an output age `t > 0`, the `q`-integral of the cell-averaged stress over `a < s` is at
most `t^{-3/2}` times the `L²_q` slice norm. -/
private lemma tmb_pt {c : ℝ} (hc : 0 < c) {F : Chart → Ten3} (hF : Measurable F) {a : ℝ}
    (t : ℝ) :
    ∫⁻ η, ∫⁻ q in Ico (-c / 2) (c / 2),
        ENNReal.ofReal (c⁻¹ * t ^ (-3 / 2 : ℝ))
          * Set.indicator {p : Chart | a < p.1} (fun p => ‖F p‖ₑ) (t, (q, η))
      ≤ (Ioi a).indicator
          (fun t => ENNReal.ofReal (t ^ (-3 / 2 : ℝ)) * ∫⁻ η, sliceL2q c F t η) t := by
  by_cases ht : a < t
  · rw [Set.indicator_of_mem (show t ∈ Ioi a from ht)]
    have hind : ∀ q η, Set.indicator {p : Chart | a < p.1} (fun p => ‖F p‖ₑ) (t, (q, η))
        = ‖F (t, (q, η))‖ₑ := fun q η =>
      Set.indicator_of_mem (show (t, (q, η)) ∈ {p : Chart | a < p.1} from ht) _
    have hq : ∀ η, ∫⁻ q in Ico (-c / 2) (c / 2),
        ENNReal.ofReal (c⁻¹ * t ^ (-3 / 2 : ℝ))
          * Set.indicator {p : Chart | a < p.1} (fun p => ‖F p‖ₑ) (t, (q, η))
        ≤ ENNReal.ofReal (t ^ (-3 / 2 : ℝ)) * sliceL2q c F t η := by
      intro η
      have e1 : ∫⁻ q in Ico (-c / 2) (c / 2),
          ENNReal.ofReal (c⁻¹ * t ^ (-3 / 2 : ℝ))
            * Set.indicator {p : Chart | a < p.1} (fun p => ‖F p‖ₑ) (t, (q, η))
          = ENNReal.ofReal (t ^ (-3 / 2 : ℝ))
            * ∫⁻ q in Ico (-c / 2) (c / 2), ENNReal.ofReal c⁻¹ * ‖F (t, (q, η))‖ₑ := by
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine lintegral_congr fun q => ?_
        rw [hind q η, ENNReal.ofReal_mul (inv_nonneg.2 hc.le)]
        ring
      rw [e1]
      exact mul_le_mul_of_nonneg_left (tmb_holder hc (G := fun q => ‖F (t, (q, η))‖ₑ)
        ((hF.comp (measurable_const.prodMk (measurable_id.prodMk measurable_const))).enorm))
        (by positivity)
    calc ∫⁻ η, ∫⁻ q in Ico (-c / 2) (c / 2),
          ENNReal.ofReal (c⁻¹ * t ^ (-3 / 2 : ℝ))
            * Set.indicator {p : Chart | a < p.1} (fun p => ‖F p‖ₑ) (t, (q, η))
        ≤ ∫⁻ η, ENNReal.ofReal (t ^ (-3 / 2 : ℝ)) * sliceL2q c F t η := lintegral_mono hq
      _ = ENNReal.ofReal (t ^ (-3 / 2 : ℝ)) * ∫⁻ η, sliceL2q c F t η :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  · simp [Set.indicator, ht]

/-! ## 4. The age integral against the thin stress -/

private lemma tmb_ageμ_le_thinMass {c : ℝ} (hc : 0 < c) {F : Chart → Ten3} (hF : Measurable F)
    {a : ℝ} (ha : 0 < a) :
    ∫⁻ p in {p : Chart | a < p.1}, ‖F p‖ₑ ∂(ageμ c (-3 / 2)) ≤ thinMass c F a := by
  have hS : MeasurableSet {p : Chart | a < p.1} := measurableSet_lt measurable_const measurable_fst
  have hgm : Measurable fun p : Chart => ‖F p‖ₑ := hF.enorm
  have hSg : Measurable fun p : Chart => Set.indicator {p : Chart | a < p.1}
      (fun p => ‖F p‖ₑ) p := hgm.indicator hS
  have hH : Measurable fun p : ℝ × (ℝ × ℝ) => ENNReal.ofReal (c⁻¹ * p.1 ^ (-3 / 2 : ℝ))
      * Set.indicator {p : Chart | a < p.1} (fun p => ‖F p‖ₑ) p := by
    apply Measurable.mul
    · exact ENNReal.measurable_ofReal.comp (by fun_prop)
    · exact hSg
  rw [← lintegral_indicator hS, lintegral_ageμ hc (-3 / 2) hSg, lintegral_ioi_qCell _ hH]
  unfold thinMass
  refine le_trans (setLIntegral_mono' measurableSet_Ioi fun t _ => tmb_pt hc hF t) (le_of_eq ?_)
  rw [lintegral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
    Set.inter_eq_left.2 (Set.Ioi_subset_Ioi ha.le)]

/-! ## 5. The thin mass bound -/

/-- **Thin mass bound** (source 5571-5575): `ThinMassBound`, derived from `thinMassBoundSlice`. -/
theorem thinMassBound (mZ : ℝ) (h : 3 / 2 < mZ) : ThinMassBound mZ := by
  obtain ⟨C, hC⟩ := thinMassBoundSlice mZ h
  refine ⟨C, 0, fun c hc1 a ha f => ?_⟩
  have hc : 0 < c := lt_of_lt_of_le one_pos hc1
  have hfa : AEStronglyMeasurable (⇑f) (z1Measure c mZ) := Lp.aestronglyMeasurable f
  obtain ⟨F, hFm, hFae⟩ : ∃ F : Chart → Ten3, Measurable F ∧
      ∀ᵐ p ∂(z1Measure c mZ), (f : Chart → Ten3) p = F p :=
    ⟨hfa.mk _, hfa.stronglyMeasurable_mk.measurable, hfa.ae_eq_mk⟩
  have hz1 : ‖f‖ₑ = z1Norm c mZ F := by
    rw [Lp.enorm_def, eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num),
      ENNReal.toReal_ofNat]
    unfold z1Norm
    congr 1
    refine lintegral_congr_ae ?_
    filter_upwards [hFae] with p hp
    rw [hp]
  have hae : ∀ᵐ p ∂(ageμ c (-3 / 2)), (f : Chart → Ten3) p = F p :=
    ae_iff.2 (tmb_ac hc (ae_iff.1 hFae))
  have hmain := tmb_ageμ_le_thinMass hc hFm ha
  have hslice := hC c hc a ha F hFm
  have e1 : (-3 / 4 : ℝ) = -(3 / 4) := by norm_num
  have e2 : (-1 / 2 : ℝ) = -(1 / 2) := by norm_num
  calc ∫⁻ p in {p : Chart | a < p.1}, ‖(f : Chart → Ten3) p‖ₑ ∂(ageμ c (-3 / 2))
      = ∫⁻ p in {p : Chart | a < p.1}, ‖F p‖ₑ ∂(ageμ c (-3 / 2)) := by
        refine lintegral_congr_ae ?_
        filter_upwards [ae_restrict_of_ae hae] with p hp
        rw [hp]
    _ ≤ thinMass c F a := hmain
    _ ≤ ENNReal.ofReal (C * (a ^ (-3 / 4 : ℝ) + a ^ (-1 / 2 : ℝ))) * z1Norm c mZ F := hslice
    _ = ENNReal.ofReal (C * c ^ (0 : ℕ) * (a ^ (-(3 / 4 : ℝ)) + a ^ (-(1 / 2 : ℝ)))) * ‖f‖ₑ := by
        rw [hz1, pow_zero, mul_one, e1, e2]

end UnforcedLeray.Short.PartIIIb.Concrete
