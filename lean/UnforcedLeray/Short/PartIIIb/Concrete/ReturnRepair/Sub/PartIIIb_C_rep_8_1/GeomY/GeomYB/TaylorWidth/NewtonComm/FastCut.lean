import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomY.GeomYB.TaylorWidth.Of
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomX.TaylorWidth.Bridge.KernelDict
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomX.TaylorWidth.Bridge.SigmaCollapse
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomX.TaylorWidth.Bridge.Newton

/-!
# Cut-tensor representation and zero-width Newton bridge under `oldN1 ≠ ⊤`

For `T : LStr Pl K L` with `oldN1 Pl K L T ≠ ⊤` and `ThinAziZero Pl K L T` (without assuming
`OldThinFinite (cOf L.ν) L.ν (thinRep T)` or `3 / 2 < K.mZ`):

* `cutRep K L T p = K.χo (L.ν * p.1) • thinRep T p` satisfies `OldThinFinite (cOf L.ν) ν''` for
  every `ν'' > 0` (`oldThinFinite_cutRep`), by Cauchy–Schwarz on the periodic cell `Ico (-c/2) (c/2)`
  and `firstMoment_thinG`;
* with `χo_fast t = Real.smoothTransition (10 * t - 12)` and `ν' = 13 / 12 * L.ν`, one has
  `χo_fast (ν' * u) * K.χo (L.ν * u) = K.χo (L.ν * u)` for all `u : ℝ`, so `(ν', χo_fast, cutRep)`
  has the exact same `phaseMean`, `sigmaM`, `newtonV`, and `youngW` as `(L.ν, K.χo, thinRep T)`;
* hence the zero-width collapse (`sigmaCollapse_cut`) and the pointwise identification
  `zMt = newtonX0` on `{5ν/6 < (εy)₀² + (εy)₁²}` (`zMt_eq_newtonX0_of_gt`) hold under `oldN1 ≠ ⊤`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Blueprint.Planar (PlanarData)

namespace YBWidth

open YBComm PhasePrim
open TWBridge hiding meanSrc

/-! ## 1. Auxiliary fast outward cutoff and cut representative -/

/-- Auxiliary outward cutoff equal to `0` on `(-∞, 6/5]` and `1` on `[13/10, ∞)`. -/
def χo_fast (t : ℝ) : ℝ := Real.smoothTransition (10 * t - 12)

theorem isOutwardCutoff_fast : IsOutwardCutoff χo_fast where
  smooth := Real.smoothTransition.contDiff.comp
    ((contDiff_const.mul contDiff_id).sub contDiff_const)
  zero t ht := Real.smoothTransition.zero_of_nonpos (by linarith)
  one t ht := Real.smoothTransition.one_of_one_le (by linarith)
  range t := ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

theorem χo_fast_one_of_ge {t : ℝ} (ht : 13 / 10 ≤ t) : χo_fast t = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

theorem χo_fast_mul_eq {ν : ℝ} (_hν : 0 < ν) {χo : ℝ → ℝ} (hχ : IsOutwardCutoff χo) (u : ℝ) :
    χo_fast ((13 / 12 * ν) * u) * χo (ν * u) = χo (ν * u) := by
  by_cases hu : ν * u ≤ 6 / 5
  · rw [hχ.zero _ hu, mul_zero]
  · have hu' : 6 / 5 < ν * u := not_le.mp hu
    have hge : 13 / 10 ≤ (13 / 12 * ν) * u := by linarith
    rw [χo_fast_one_of_ge hge, one_mul]

/-- The outward-cut thin representative `p ↦ K.χo (L.ν * p.1) • thinRep T p`. -/
def cutRep (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (T : LStr Pl K L)
    (p : Chart) : Mat3 :=
  K.χo (L.ν * p.1) • thinRep T p

theorem cutRep_apply (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (T : LStr Pl K L)
    (p : Chart) (i j : Fin 3) :
    cutRep Pl K L T p i j = K.χo (L.ν * p.1) * thinRep T p i j := rfl

theorem phaseMean_cutRep (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (T : LStr Pl K L)
    (u : ℝ) :
    phaseMean (cOf L.ν) (13 / 12 * L.ν) χo_fast (cutRep Pl K L T) u =
      phaseMean (cOf L.ν) L.ν K.χo (thinRep T) u := by
  ext i j
  unfold phaseMean cutRep
  by_cases h : i = 1 ∨ j = 1
  · simp [h]
  · simp only [h, ↓reduceIte, Pi.smul_apply, smul_eq_mul]
    rw [integral_const_mul, ← mul_assoc, χo_fast_mul_eq L.ν_pos K.hχo u]

theorem sigmaM_cutRep (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (T : LStr Pl K L)
    (x' : ℝ × ℝ) :
    sigmaM (cOf L.ν) (13 / 12 * L.ν) χo_fast (cutRep Pl K L T) x' =
      sigmaM (cOf L.ν) L.ν K.χo (thinRep T) x' := by
  ext a b
  unfold sigmaM
  simp only [phaseMean_cutRep]

theorem newtonV_cutRep (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (p : ℝ)
    (T : LStr Pl K L) (x : Vec3) :
    newtonV (cOf L.ν) (13 / 12 * L.ν) p χo_fast (cutRep Pl K L T) x =
      newtonV (cOf L.ν) L.ν p K.χo (thinRep T) x := by
  funext i
  unfold newtonV
  simp only [sigmaM_cutRep]

theorem youngW_cutRep (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (p : ℝ)
    (T : LStr Pl K L) :
    youngW (cOf L.ν) (13 / 12 * L.ν) L.ε p χo_fast (cutRep Pl K L T) =
      youngW (cOf L.ν) L.ν L.ε p K.χo (thinRep T) := by
  funext y
  unfold youngW
  rw [newtonV_cutRep]

/-! ## 2. `OldThinFinite` for `cutRep` from `oldN1 ≠ ⊤` -/

/-- Cauchy–Schwarz on `Ico (-c/2) (c/2)` with normalized Lebesgue measure `c⁻¹ dq`. -/
theorem cell_q_cs {c : ℝ} (hc : 0 < c) {f : ℝ → ℝ} (hf0 : ∀ q, 0 ≤ f q)
    (hfm : Measurable f) :
    (∫⁻ q in Ico (-(c / 2)) (c / 2), ENNReal.ofReal c⁻¹ * ENNReal.ofReal (f q)) ≤
      (∫⁻ q in Ico (-(c / 2)) (c / 2), ENNReal.ofReal c⁻¹ * ENNReal.ofReal (f q ^ 2)) ^
        (1 / 2 : ℝ) := by
  set μ : Measure ℝ := volume.restrict (Ico (-(c / 2)) (c / 2))
  set a : ℝ≥0∞ := ENNReal.ofReal c⁻¹ ^ (1 / 2 : ℝ)
  have ha2 : a ^ (2 : ℝ) = ENNReal.ofReal c⁻¹ := by
    dsimp [a]
    rw [← ENNReal.rpow_mul, show (1 / 2 : ℝ) * 2 = 1 by norm_num, ENNReal.rpow_one]
  have hmul : a * a = ENNReal.ofReal c⁻¹ := by
    rw [← sq, ← ENNReal.rpow_two, ha2]
  have h1 : (∫⁻ q, ENNReal.ofReal c⁻¹ * ENNReal.ofReal (f q) ∂μ) =
      ∫⁻ q, a * (a * ENNReal.ofReal (f q)) ∂μ := by
    refine lintegral_congr fun q => ?_
    rw [← mul_assoc, hmul]
  rw [h1]
  have hcs := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two (f := fun _ => a)
    aemeasurable_const (hfm.ennreal_ofReal.const_mul a).aemeasurable
  have hfirst : (∫⁻ _ : ℝ, a ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) = 1 := by
    rw [lintegral_const, ha2, Measure.restrict_apply_univ, Real.volume_Ico,
      show c / 2 - -(c / 2) = c by ring, ← ENNReal.ofReal_mul (by positivity),
      inv_mul_cancel₀ hc.ne', ENNReal.ofReal_one, ENNReal.one_rpow]
  have hsec : (∫⁻ q, (a * ENNReal.ofReal (f q)) ^ (2 : ℝ) ∂μ) =
      ∫⁻ q, ENNReal.ofReal c⁻¹ * ENNReal.ofReal (f q ^ 2) ∂μ := by
    refine lintegral_congr fun q => ?_
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ha2, ENNReal.rpow_two, sq,
      ← ENNReal.ofReal_mul (hf0 q), ← sq]
  exact calc (∫⁻ q, a * (a * ENNReal.ofReal (f q)) ∂μ)
      ≤ (∫⁻ _ : ℝ, a ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) *
          (∫⁻ q, (a * ENNReal.ofReal (f q)) ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) := hcs
    _ = (∫⁻ q, ENNReal.ofReal c⁻¹ * ENNReal.ofReal (f q ^ 2) ∂μ) ^ (1 / 2 : ℝ) := by
        rw [hfirst, one_mul, hsec]

theorem oldMeasure_ac_ageμ {c ν'' : ℝ} (hν'' : 0 < ν'') :
    oldMeasure c ν'' ≪ ageμ c (-1 / 2) := by
  have hA : (volume.restrict (Ioi (6 / 5 / ν''))) ≪
      (volume.restrict (Ioi (0 : ℝ))).withDensity (fun s : ℝ => ENNReal.ofReal (s ^ (-1 / 2 : ℝ))) := by
    have hsub : Ioi (6 / 5 / ν'') ⊆ Ioi (0 : ℝ) :=
      Set.Ioi_subset_Ioi (div_nonneg (by norm_num) hν''.le)
    have hle : volume.restrict (Ioi (6 / 5 / ν'')) ≤ volume.restrict (Ioi (0 : ℝ)) :=
      Measure.restrict_mono hsub le_rfl
    have hf : AEMeasurable (fun s : ℝ => ENNReal.ofReal (s ^ (-1 / 2 : ℝ)))
        (volume.restrict (Ioi (0 : ℝ))) :=
      (measurable_ofReal_rpow _).aemeasurable
    have hne : ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))),
        ENNReal.ofReal (s ^ (-1 / 2 : ℝ)) ≠ 0 := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      exact (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos (Set.mem_Ioi.mp hs) _)).ne'
    exact (Measure.absolutelyContinuous_of_le hle).trans (withDensity_absolutelyContinuous' hf hne)
  have : SFinite (Cyl.avgμ c) := by
    unfold Cyl.avgμ
    infer_instance
  unfold oldMeasure ageμ
  exact Measure.AbsolutelyContinuous.prod hA (Measure.AbsolutelyContinuous.refl _)

/-- `cutRep Pl K L T` satisfies `OldThinFinite (cOf L.ν) ν''` for any `ν'' > 0` whenever
`oldN1 Pl K L T ≠ ⊤`. -/
theorem oldThinFinite_cutRep (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel)
    (hC0 : 0 < K.C0) (T : LStr Pl K L) (hN1 : oldN1 Pl K L T ≠ ⊤)
    {ν'' : ℝ} (hν'' : 0 < ν'') :
    OldThinFinite (cOf L.ν) ν'' (cutRep Pl K L T) := by
  have hc : 0 < cOf L.ν := cOf_pos L.ν_pos
  set c := cOf L.ν
  set MG : Chart → Mat3 := fun p => Ten3.toMatrix (thinG Pl K L T p)
  have hMG_meas : Measurable MG := by
    refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
    exact (EuclideanSpace.proj (i, j) : Ten3 →L[ℝ] ℝ).continuous.measurable.comp
      (thinG_meas Pl K L T)
  have hae_age : ∀ᵐ p ∂(ageμ c (-1 / 2)), MG p = cutRep Pl K L T p := by
    filter_upwards [TWBridge.thinG_ae Pl K L hC0 T] with p hp
    show Ten3.toMatrix (thinG Pl K L T p) = _
    rw [hp, PhasePrim.toMatrix_smul]
    rfl
  have hae : MG =ᵐ[oldMeasure c ν''] cutRep Pl K L T :=
    (oldMeasure_ac_ageμ hν'').ae_le hae_age
  refine ⟨hMG_meas.aestronglyMeasurable.congr hae, ?_⟩
  have hInt_MG : Integrable (fun p : Chart => p.1 ^ (-(3 / 2 : ℝ)) * frob (MG p))
      (oldMeasure c ν'') := by
    have hmeas : Measurable (fun p : Chart => p.1 ^ (-(3 / 2 : ℝ)) * frob (MG p)) :=
      (measurable_fst.pow_const _).mul (continuous_frob.measurable.comp hMG_meas)
    refine ⟨hmeas.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal]
    · have hle1 : (∫⁻ p, ENNReal.ofReal (p.1 ^ (-(3 / 2 : ℝ)) * frob (MG p))
            ∂(oldMeasure c ν'')) ≤
          IIIa.firstMoment c 0 MG := by
        have hI : Measurable (fun p : Chart =>
            ENNReal.ofReal (p.1 ^ (-(3 / 2 : ℝ)) * frob (MG p))) := hmeas.ennreal_ofReal
        rw [slOld_prod _ hI, tm_firstMoment_eq]
        have hsub : Ioi (6 / 5 / ν'') ⊆ Ioi (0 : ℝ) :=
          Set.Ioi_subset_Ioi (div_nonneg (by norm_num) hν''.le)
        refine le_trans (lintegral_mono_set hsub) ?_
        refine lintegral_mono_ae ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
        have hs0 : 0 < s := hs
        have hsr : 0 ≤ s ^ (-(3 / 2 : ℝ)) := Real.rpow_nonneg hs0.le _
        have hpull : (∫⁻ y, ENNReal.ofReal (s ^ (-(3 / 2 : ℝ)) * frob (MG (s, y)))
              ∂(Cyl.avgμ c)) =
            ENNReal.ofReal (s ^ (-(3 / 2 : ℝ))) *
              ∫⁻ y, ENNReal.ofReal (frob (MG (s, y))) ∂(Cyl.avgμ c) := by
          simp_rw [ENNReal.ofReal_mul hsr]
          exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
        rw [hpull]
        unfold tmInt
        rw [show (-3 / 2 : ℝ) = -(3 / 2 : ℝ) by ring]
        gcongr
        unfold Cyl.avgμ
        rw [lintegral_smul_measure, smul_eq_mul, Cyl.cellμ_eq_prod, neg_div]
        have hF_meas : Measurable (fun y : ℝ × ℝ => ENNReal.ofReal (frob (MG (s, y)))) :=
          (continuous_frob.measurable.comp (hMG_meas.comp (measurable_const.prodMk measurable_id))).ennreal_ofReal
        rw [lintegral_prod_symm _ hF_meas.aemeasurable,
          ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine lintegral_mono fun η => ?_
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        have hq_meas : Measurable (fun q : ℝ => frob (MG (s, (q, η)))) :=
          continuous_frob.measurable.comp
            (hMG_meas.comp (measurable_const.prodMk (measurable_id.prodMk measurable_const)))
        have hcs := cell_q_cs hc (fun q => frob_nonneg' _) hq_meas
        have hsq_eq : ∀ q : ℝ, frob (MG (s, (q, η))) ^ 2 = IIIa.frobSq (MG (s, (q, η))) := by
          intro q
          unfold frob IIIa.frobSq
          exact Real.sq_sqrt (by positivity)
        simp_rw [hsq_eq] at hcs
        have h1le : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (1 + |η| / Real.sqrt s) := by
          rw [← ENNReal.ofReal_one]
          have hdiv : 0 ≤ |η| / Real.sqrt s := by positivity
          exact ENNReal.ofReal_le_ofReal (by linarith)
        calc (∫⁻ q in Ico (-(c / 2)) (c / 2),
              ENNReal.ofReal c⁻¹ * ENNReal.ofReal (frob (MG (s, (q, η)))))
            ≤ 1 * (∫⁻ q in Ico (-(c / 2)) (c / 2),
                ENNReal.ofReal c⁻¹ * ENNReal.ofReal (IIIa.frobSq (MG (s, (q, η))))) ^ (1 / 2 : ℝ) := by
              rw [one_mul]; exact hcs
          _ ≤ ENNReal.ofReal (1 + |η| / Real.sqrt s) *
              (∫⁻ q in Ico (-(c / 2)) (c / 2),
                ENNReal.ofReal c⁻¹ * ENNReal.ofReal (IIIa.frobSq (MG (s, (q, η))))) ^ (1 / 2 : ℝ) := by
              gcongr
      rw [firstMoment_thinG Pl K L hC0 T] at hle1
      exact lt_of_le_of_lt hle1 (lt_top_iff_ne_top.2 hN1)
    · filter_upwards [ae_old_pos c ν''] with p hp
      have hs0 : 0 < p.1 := lt_trans (div_pos (by norm_num) hν'') hp
      exact mul_nonneg (Real.rpow_nonneg hs0.le _) (frob_nonneg' _)
  refine hInt_MG.congr ?_
  filter_upwards [hae] with p hp
  rw [hp]

/-! ## 3. Zero-width collapse and Newton identification without `OldThinFinite (thinRep T)` -/

/-- The zero-width collapse of `meanSrc` under `ThinAziZero` and `oldN1 ≠ ⊤` alone. -/
theorem sigmaCollapse_cut (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel)
    (hC0 : 0 < K.C0) (T : LStr Pl K L) (hAzi : ThinAziZero Pl K L T)
    (hN1 : oldN1 Pl K L T ≠ ⊤) :
    ∀ᵐ x' : ℝ × ℝ ∂(volume : Measure (ℝ × ℝ)), ∀ j k : Fin 3,
      ∫ Y : ℝ, meanSrc Pl K L T x' Y j k =
        (sigmaM (cOf L.ν) L.ν K.χo (thinRep T) x' j k +
          sigmaM (cOf L.ν) L.ν K.χo (thinRep T) x' k j) / 2 := by
  have hν : 0 < L.ν := L.ν_pos
  have hν' : 0 < 13 / 12 * L.ν := by positivity
  have hc : 0 < cOf L.ν := cOf_pos hν
  have hOld := oldThinFinite_cutRep Pl K L hC0 T hN1 hν'
  set θ' : ℝ := 6 / 5 / (13 / 12 * L.ν)
  have hθ'_pos : 0 < θ' := div_pos (by norm_num) hν'
  have ha := ageμ_slice' (cOf L.ν) hc hAzi
  have hb := ageμ_slice' (cOf L.ν) hc (TWBridge.thinG_ae Pl K L hC0 T)
  have hc1 := hOld.2.prod_right_ae
  have hc2 := hOld.1.prodMk_left
  have hS_meas : MeasurableSet (Ioi θ') := measurableSet_Ioi
  have hθ_sub : Ioi θ' ⊆ Ioi (0 : ℝ) := Ioi_subset_Ioi hθ'_pos.le
  have ha' := ae_restrict_of_ae_restrict_of_subset hθ_sub ha
  have hb' := ae_restrict_of_ae_restrict_of_subset hθ_sub hb
  have hgood : ∀ᵐ s ∂(volume : Measure ℝ), s ∈ Ioi θ' →
      (∀ᵐ x ∂(Cyl.avgμ (cOf L.ν)), ∀ i j : Fin 3, (i = 1 ∨ j = 1) →
        cutRep Pl K L T (s, x) i j = 0) ∧
      (∀ᵐ x ∂(Cyl.avgμ (cOf L.ν)), ∀ i j : Fin 3,
        thinG Pl K L T (s, x) (i, j) = χo_fast ((13 / 12 * L.ν) * s) * cutRep Pl K L T (s, x) i j) ∧
      (∀ i j : Fin 3, Integrable (fun x : ℝ × ℝ => cutRep Pl K L T (s, x) i j)
        (Cyl.avgμ (cOf L.ν))) := by
    rw [← ae_restrict_iff' hS_meas]
    filter_upwards [ha', hb', hc1, hc2, ae_restrict_mem hS_meas] with s hsa hsb hsc hsm hsmem
    refine ⟨?_, ?_, fun i j => ?_⟩
    · filter_upwards [hsa] with x hx i j hij
      rw [cutRep_apply, hx i j hij, mul_zero]
    · filter_upwards [hsb] with x hx i j
      rw [hx]
      show K.χo (L.ν * s) * thinRep T (s, x) i j =
        χo_fast ((13 / 12 * L.ν) * s) * (K.χo (L.ν * s) * thinRep T (s, x) i j)
      rw [← mul_assoc, χo_fast_mul_eq hν K.hχo s]
    · have hpos : 0 < s ^ (-(3 / 2 : ℝ)) := Real.rpow_pos_of_pos (lt_trans hθ'_pos hsmem) _
      have hf : Integrable (fun x => frob (cutRep Pl K L T (s, x))) (Cyl.avgμ (cOf L.ν)) := by
        have := hsc.const_mul (s ^ (-(3 / 2 : ℝ)))⁻¹
        refine this.congr (Eventually.of_forall fun x => ?_)
        simp only
        rw [← mul_assoc, inv_mul_cancel₀ hpos.ne', one_mul]
      refine hf.mono' ?_ (Eventually.of_forall fun x => TWBridge.entry_le_frob' _ i j)
      exact ((continuous_apply j).comp (continuous_apply i)).comp_aestronglyMeasurable hsm
  obtain ⟨t, hsubt, htm, ht0⟩ := exists_measurable_superset_of_null (ae_iff.1 hgood)
  have hpolar := polar_null htm ht0
  have hne : ∀ᵐ x' : ℝ × ℝ ∂(volume : Measure (ℝ × ℝ)), x' ≠ 0 := by
    rw [ae_iff]
    simp
  filter_upwards [hpolar, hne] with x' hx' hx0
  have hS : 0 < x'.1 ^ 2 + x'.2 ^ 2 := by
    rcases lt_or_eq_of_le (add_nonneg (sq_nonneg x'.1) (sq_nonneg x'.2)) with h | h
    · exact h
    · exfalso
      apply hx0
      have h1 : x'.1 = 0 := by nlinarith [sq_nonneg x'.1, sq_nonneg x'.2]
      have h2 : x'.2 = 0 := by nlinarith [sq_nonneg x'.1, sq_nonneg x'.2]
      exact Prod.ext h1 h2
  intro j k
  by_cases hout : Real.sqrt (5 * L.ν / 6) < Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2)
  · rw [show (fun Y => meanSrc Pl K L T x' Y j k) = fun _ => 0 from
      funext fun Y => by rw [YBComm.meanSrc_support Pl K L T x' Y hout]; rfl]
    simp only [integral_zero]
    have h1 : 5 * L.ν / 6 < x'.1 ^ 2 + x'.2 ^ 2 :=
      (Real.sqrt_lt_sqrt_iff (by positivity)).1 hout
    have h0 := sigmaM_eq_zero_of_ge (cOf L.ν) L.ν K.χo (thinRep T) hν K.hχo x' h1.le
    simp [h0]
  · rw [not_lt] at hout
    have hcut : ∀ Y, meanSrc Pl K L T x' Y =
        IIIa.phaseMean (cOf L.ν) (plift (cOf L.ν) (thinG Pl K L T)) x' Y := by
      intro Y
      unfold meanSrc liftSrc
      simp only [phaseMean_cutLift, hout, ↓reduceIte]
    have hu : plS x' ∈ Ioi θ' := by
      have hρ2 : x'.1 ^ 2 + x'.2 ^ 2 ≤ 5 * L.ν / 6 :=
        (Real.sqrt_le_sqrt_iff (by positivity)).1 hout
      have hge : 6 / 5 / L.ν ≤ plS x' := by
        have e : 6 / 5 / L.ν = (5 * L.ν / 6)⁻¹ := by field_simp
        rw [e]
        exact inv_anti₀ hS hρ2
      have hlt : θ' < 6 / 5 / L.ν := by
        show 6 / 5 / (13 / 12 * L.ν) < 6 / 5 / L.ν
        rw [div_lt_div_iff₀ hν' hν]
        linarith
      exact lt_of_lt_of_le hlt hge
    have hG : (∀ᵐ x ∂(Cyl.avgμ (cOf L.ν)), ∀ i j : Fin 3, (i = 1 ∨ j = 1) →
          cutRep Pl K L T (plS x', x) i j = 0) ∧
        (∀ᵐ x ∂(Cyl.avgμ (cOf L.ν)), ∀ i j : Fin 3,
          thinG Pl K L T (plS x', x) (i, j) =
            χo_fast ((13 / 12 * L.ν) * plS x') * cutRep Pl K L T (plS x', x) i j) ∧
        (∀ i j : Fin 3, Integrable (fun x : ℝ × ℝ => cutRep Pl K L T (plS x', x) i j)
          (Cyl.avgμ (cOf L.ν))) := by
      by_contra hbad
      exact hx' ⟨hS, hsubt (fun h => hbad (h hu))⟩
    obtain ⟨ha1, hb1, hc1⟩ := hG
    have key := TWBridge.inner_collapse (cOf L.ν) (13 / 12 * L.ν) hc χo_fast
      (thinG Pl K L T) (cutRep Pl K L T) x' hS
      (fun i j => TWBridge.integrable_cell_of_avg _ hc (hc1 i j))
      (TWBridge.ae_cell_of_avg _ hc ha1)
      (TWBridge.ae_cell_of_avg _ hc hb1) j k
    have hcongr : (∫ Y : ℝ, meanSrc Pl K L T x' Y j k) =
        ∫ Y : ℝ, IIIa.phaseMean (cOf L.ν) (plift (cOf L.ν) (thinG Pl K L T)) x' Y j k :=
      integral_congr_ae (Eventually.of_forall fun Y => congr_fun (congr_fun (hcut Y) j) k)
    rw [hcongr, key, sigmaM_cutRep]

/-- Pointwise identification `sepVmu0 (μ' : ℂ) (meanSrc T) x = ↑(newtonV ... (ofLp x))`
on `{5ν/6 < x₀² + x₁²}` under `ThinAziZero` and `oldN1 ≠ ⊤` alone. -/
theorem sepVmu0_eq_newtonV_cut (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel)
    (hC0 : 0 < K.C0) (T : LStr Pl K L) (hAzi : ThinAziZero Pl K L T)
    (hN1 : oldN1 Pl K L T ≠ ⊤) (μ' : ℝ) {x : Space} (hx : 5 * L.ν / 6 < x 0 ^ 2 + x 1 ^ 2)
    (i : Fin 3) :
    IIIa.sepVmu0 (μ' : ℂ) (meanSrc Pl K L T) x i =
      (newtonV (cOf L.ν) L.ν μ' K.χo (thinRep T) (WithLp.ofLp x) i : ℂ) := by
  have hS_ae := sigmaCollapse_cut Pl K L hC0 T hAzi hN1
  have hinner_real : ∀ {l : ℝ}, l ∈ Ioo (0 : ℝ) 1 →
      (∫ w : (ℝ × ℝ) × ℝ, ∑ j : Fin 3, ∑ k : Fin 3,
        kerK0 x l i j k w.1 * meanSrc Pl K L T w.1 w.2 j k) =
      ∫ a : ℝ × ℝ, ∑ j : Fin 3, ∑ k : Fin 3,
        newtonD3 (WithLp.ofLp x - l • embPlane a) i j k *
          sigmaM (cOf L.ν) L.ν K.χo (thinRep T) a j k := by
    intro l hl
    have hint : ∀ j k : Fin 3, Integrable (fun w : (ℝ × ℝ) × ℝ =>
        kerK0 x l i j k w.1 * meanSrc Pl K L T w.1 w.2 j k) volume :=
      fun j k => kerK0_mul_meanSrc_integrable kernelDict Pl K L hC0 T hN1 hx hl i j k
    rw [integral_finsetSum _ (fun j _ => integrable_finsetSum _ (fun k _ => hint j k))]
    have hstep1 : ∀ j : Fin 3,
        (∫ w : (ℝ × ℝ) × ℝ, ∑ k : Fin 3, kerK0 x l i j k w.1 * meanSrc Pl K L T w.1 w.2 j k) =
        ∑ k : Fin 3, ∫ a : ℝ × ℝ,
          newtonD3 (WithLp.ofLp x - l • embPlane a) i j k *
            ((sigmaM (cOf L.ν) L.ν K.χo (thinRep T) a j k +
              sigmaM (cOf L.ν) L.ν K.χo (thinRep T) a k j) / 2) := by
      intro j
      rw [integral_finsetSum _ (fun k _ => hint j k)]
      refine Finset.sum_congr rfl fun k _ => ?_
      have hprod : (∫ w : (ℝ × ℝ) × ℝ, kerK0 x l i j k w.1 * meanSrc Pl K L T w.1 w.2 j k) =
          ∫ a : ℝ × ℝ, kerK0 x l i j k a * ∫ Y : ℝ, meanSrc Pl K L T a Y j k := by
        have hp := MeasureTheory.integral_prod
          (fun w : (ℝ × ℝ) × ℝ => kerK0 x l i j k w.1 * meanSrc Pl K L T w.1 w.2 j k) (hint j k)
        refine hp.trans (integral_congr_ae (Eventually.of_forall fun a => ?_))
        exact integral_const_mul (kerK0 x l i j k a) (fun Y => meanSrc Pl K L T a Y j k)
      rw [hprod]
      refine integral_congr_ae ?_
      filter_upwards [hS_ae] with a ha
      rw [ha j k]
      by_cases haD : a.1 ^ 2 + a.2 ^ 2 ≤ 5 * L.ν / 6
      · rw [kerK0_eq_newtonD3_of_le kernelDict hl.1.le hl.2.le haD hx i j k]
      · have haD' : 5 * L.ν / 6 < a.1 ^ 2 + a.2 ^ 2 := not_le.1 haD
        have h0 : sigmaM (cOf L.ν) L.ν K.χo (thinRep T) a = 0 :=
          sigmaM_eq_zero_of_ge (cOf L.ν) L.ν K.χo (thinRep T) L.ν_pos K.hχo a haD'.le
        simp [h0]
    simp_rw [hstep1]
    have hint_sym : ∀ j k : Fin 3, Integrable (fun a : ℝ × ℝ =>
        newtonD3 (WithLp.ofLp x - l • embPlane a) i j k *
          ((sigmaM (cOf L.ν) L.ν K.χo (thinRep T) a j k +
            sigmaM (cOf L.ν) L.ν K.χo (thinRep T) a k j) / 2)) volume := by
      intro j k
      have h1 : Integrable (fun a : ℝ × ℝ =>
          ∫ Y : ℝ, kerK0 x l i j k a * meanSrc Pl K L T a Y j k) volume :=
        (hint j k).integral_prod_left
      refine h1.congr ?_
      filter_upwards [hS_ae] with a ha
      rw [integral_const_mul, ha j k]
      by_cases haD : a.1 ^ 2 + a.2 ^ 2 ≤ 5 * L.ν / 6
      · rw [kerK0_eq_newtonD3_of_le kernelDict hl.1.le hl.2.le haD hx i j k]
      · have haD' : 5 * L.ν / 6 < a.1 ^ 2 + a.2 ^ 2 := not_le.1 haD
        have h0 : sigmaM (cOf L.ν) L.ν K.χo (thinRep T) a = 0 :=
          sigmaM_eq_zero_of_ge (cOf L.ν) L.ν K.χo (thinRep T) L.ν_pos K.hχo a haD'.le
        simp [h0]
    have hsum_int : (∑ j : Fin 3, ∑ k : Fin 3, ∫ a : ℝ × ℝ,
        newtonD3 (WithLp.ofLp x - l • embPlane a) i j k *
          ((sigmaM (cOf L.ν) L.ν K.χo (thinRep T) a j k +
            sigmaM (cOf L.ν) L.ν K.χo (thinRep T) a k j) / 2)) =
      ∫ a : ℝ × ℝ, ∑ j : Fin 3, ∑ k : Fin 3,
        newtonD3 (WithLp.ofLp x - l • embPlane a) i j k *
          ((sigmaM (cOf L.ν) L.ν K.χo (thinRep T) a j k +
            sigmaM (cOf L.ν) L.ν K.χo (thinRep T) a k j) / 2) := by
      rw [integral_finsetSum _ (fun j _ => integrable_finsetSum _ (fun k _ => hint_sym j k))]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [integral_finsetSum _ (fun k _ => hint_sym j k)]
    rw [hsum_int]
    refine integral_congr_ae (Eventually.of_forall fun a => ?_)
    exact sum_newtonD3_symm_sigmaM kernelDict (cOf L.ν) L.ν K.χo (thinRep T) L.ν_pos K.hχo hx hl i a
  unfold IIIa.sepVmu0 newtonV
  have hcongr : EqOn
      (fun l : ℝ => (l : ℂ) ^ (2 * (μ' : ℂ) + 2) *
        ∫ w : (ℝ × ℝ) × ℝ, ∑ j : Fin 3, ∑ k : Fin 3,
          ((kerK0 x l i j k w.1 : ℝ) : ℂ) * ((meanSrc Pl K L T w.1 w.2 j k : ℝ) : ℂ))
      (fun l : ℝ => ((l ^ (2 * μ' + 2) *
        ∫ a : ℝ × ℝ, ∑ j : Fin 3, ∑ k : Fin 3,
          newtonD3 (WithLp.ofLp x - l • embPlane a) i j k *
            sigmaM (cOf L.ν) L.ν K.χo (thinRep T) a j k : ℝ) : ℂ))
      (Ioo (0 : ℝ) 1) := by
    intro l hl
    dsimp only
    have hcast : (fun w : (ℝ × ℝ) × ℝ => ∑ j : Fin 3, ∑ k : Fin 3,
        ((kerK0 x l i j k w.1 : ℝ) : ℂ) * ((meanSrc Pl K L T w.1 w.2 j k : ℝ) : ℂ)) =
      fun w : (ℝ × ℝ) × ℝ =>
        ((∑ j : Fin 3, ∑ k : Fin 3, kerK0 x l i j k w.1 * meanSrc Pl K L T w.1 w.2 j k : ℝ) : ℂ) := by
      funext w
      simp only [Complex.ofReal_sum, Complex.ofReal_mul]
    have hor1 : (∫ w : (ℝ × ℝ) × ℝ, ∑ j : Fin 3, ∑ k : Fin 3,
        ((kerK0 x l i j k w.1 : ℝ) : ℂ) * ((meanSrc Pl K L T w.1 w.2 j k : ℝ) : ℂ)) =
      ((∫ a : ℝ × ℝ, ∑ j : Fin 3, ∑ k : Fin 3,
        newtonD3 (WithLp.ofLp x - l • embPlane a) i j k *
          sigmaM (cOf L.ν) L.ν K.χo (thinRep T) a j k : ℝ) : ℂ) := by
      rw [hcast, ← hinner_real hl]
      exact integral_ofReal
    rw [hor1]
    have hpow : (l : ℂ) ^ (2 * (μ' : ℂ) + 2) = ((l ^ (2 * μ' + 2) : ℝ) : ℂ) := by
      have hexp : (2 * (μ' : ℂ) + 2 : ℂ) = ((2 * μ' + 2 : ℝ) : ℂ) := by push_cast; rfl
      rw [hexp, Complex.ofReal_cpow hl.1.le]
    rw [hpow, ← Complex.ofReal_mul]
  change -2 * ∫ l in Ioo (0 : ℝ) 1, (l : ℂ) ^ (2 * (μ' : ℂ) + 2) *
    ∫ w : (ℝ × ℝ) × ℝ, ∑ j : Fin 3, ∑ k : Fin 3,
      ((kerK0 x l i j k w.1 : ℝ) : ℂ) * ((meanSrc Pl K L T w.1 w.2 j k : ℝ) : ℂ) = _
  rw [setIntegral_congr_fun measurableSet_Ioo hcongr,
    ← MeasureTheory.integral_Ioc_eq_integral_Ioo]
  have hor : (∫ l in Ioc (0 : ℝ) 1, ((l ^ (2 * μ' + 2) *
      ∫ a : ℝ × ℝ, ∑ j : Fin 3, ∑ k : Fin 3,
        newtonD3 (WithLp.ofLp x - l • embPlane a) i j k *
          sigmaM (cOf L.ν) L.ν K.χo (thinRep T) a j k : ℝ) : ℂ)) =
    ((∫ l in Ioc (0 : ℝ) 1, l ^ (2 * μ' + 2) *
      ∫ a : ℝ × ℝ, ∑ j : Fin 3, ∑ k : Fin 3,
        newtonD3 (WithLp.ofLp x - l • embPlane a) i j k *
          sigmaM (cOf L.ν) L.ν K.χo (thinRep T) a j k : ℝ) : ℂ) :=
    integral_ofReal
  rw [hor]
  push_cast
  rfl

/-- Pointwise equality `zMt = newtonX0` on `{5ν/6 < (εy)₀² + (εy)₁²}`. -/
theorem zMt_eq_newtonX0_of_gt (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ)
    (hC0 : 0 < K.C0) (T : LStr Pl K L) (hAzi : ThinAziZero Pl K L T)
    (hN1 : oldN1 Pl K L T ≠ ⊤) (τ : ℝ) {y : Space}
    (hy : 5 * L.ν / 6 < (L.ε • y) 0 ^ 2 + (L.ε • y) 1 ^ 2) :
    zMt Pl K L μ T τ y = newtonX0 L.ε μ (meanSrc Pl K L T) τ y := by
  ext i
  unfold zMt newtonX0 youngW
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, reMap_apply,
    PiLp.smul_apply]
  have h1 := sepVmu0_eq_newtonV_cut Pl K L hC0 T hAzi hN1 μ hy i
  have h2 := sepVmu0_eq_newtonV_cut Pl K L hC0 T hAzi hN1 (μ + 1) hy i
  have hofLp : WithLp.ofLp (L.ε • y) = L.ε • WithLp.ofLp y := rfl
  rw [show ((μ : ℂ) + 1) = ((μ + 1 : ℝ) : ℂ) by push_cast; rfl,
    h1, h2, hofLp, ← Complex.ofReal_sub, Complex.ofReal_re, mul_sub]

end YBWidth

end UnforcedLeray.Short.PartIIIb.Concrete
