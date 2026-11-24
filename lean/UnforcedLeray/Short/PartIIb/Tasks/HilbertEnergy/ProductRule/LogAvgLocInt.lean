import UnforcedLeray.Short.PartIIb.Sub.T15_2

/-!
# Part II-b, task `PartII-b:T15/2` leaf `LogAvgLocInt`: local integrability of the translate average

Source of record: `the November 2 reference manuscript`, lines 1975-1979.

This file proves `LogAvgLocInt` (`Sub/T15_2.lean`) with no extra hypotheses.

Strategy.
* `G` is `logMeas c`-a.e. equal to a strongly measurable `G'`. The averages of `G` and `G'` agree
  `logMeas c`-a.e.: the null set `{G ≠ G'}` is enlarged to a measurable null set `E`, and Fubini
  (`Measure.prod_apply_symm`) with translation invariance shows that for a.e. `x` the set of `σ`
  with `(x.1 + σ, x.2) ∈ E` is null.
* The average of `G'` is strongly measurable (`StronglyMeasurable.integral_prod_right`).
* Integrability on `K_{T,L}`: `K_{T,L}` is a product set of finite `logMeas c`-measure. Fubini on
  `(logMeas c).restrict K_{T,L} ⊗ volume.restrict (uIoc 0 h)` bounds the `L¹` norm by
  `volume(uIoc 0 h) · ∫⁻_{K_{T+|h|,L}} ‖G'‖ₑ`, using translation invariance. The latter is finite
  because `G ∈ L²` on a finite-measure set, hence `L¹` there.

Every auxiliary declaration is prefixed `logAL_`. The sibling file `LogTranslateContinuous.lean`
is not imported; its measure facts are copied here.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIb

/-! ## Measure facts about `logMeas c` -/

/-- The normalized cell measure is `s`-finite (instance search does not unfold `Cyl.avgμ`). -/
instance logAL_sFinite_avgμ (c : ℝ) : SFinite (Cyl.avgμ c) := by
  unfold Cyl.avgμ
  infer_instance

/-- `logMeas c` is `s`-finite. -/
instance logAL_sFinite_logMeas (c : ℝ) : SFinite (logMeas c) := by
  unfold logMeas
  infer_instance

/-- The translation `x ↦ (x.1 + σ, x.2)` preserves `logMeas c`. -/
theorem logAL_measurePreserving (c σ : ℝ) :
    MeasurePreserving (fun x : Coord => (x.1 + σ, x.2)) (logMeas c) (logMeas c) := by
  unfold logMeas
  exact (measurePreserving_add_right volume σ).prod (MeasurePreserving.id _)

/-- The box `{|x.1| ≤ T, |x.2.2| ≤ L}` is a product set. -/
theorem logAL_box_eq (T L : ℝ) :
    {x : Coord | |x.1| ≤ T ∧ |x.2.2| ≤ L} = Icc (-T) T ×ˢ (univ ×ˢ Icc (-L) L) := by
  ext x
  simp [abs_le, Set.mem_prod, and_assoc]

/-- The box is measurable. -/
theorem logAL_box_meas (T L : ℝ) : MeasurableSet {x : Coord | |x.1| ≤ T ∧ |x.2.2| ≤ L} := by
  rw [logAL_box_eq]
  exact measurableSet_Icc.prod (MeasurableSet.univ.prod measurableSet_Icc)

/-- The normalized cell measure of `univ ×ˢ [-L, L]` is finite (the cell is `[-c/2, c/2) × ℝ`). -/
theorem logAL_avg_lt_top (c L : ℝ) : Cyl.avgμ c (univ ×ˢ Icc (-L) L) < ⊤ := by
  unfold Cyl.avgμ Cyl.cellμ
  rw [Measure.smul_apply, Measure.restrict_apply (MeasurableSet.univ.prod measurableSet_Icc),
    smul_eq_mul]
  refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
  have hcomp : IsCompact (Icc (-c / 2) (c / 2) ×ˢ Icc (-L) L) := isCompact_Icc.prod isCompact_Icc
  refine lt_of_le_of_lt (measure_mono ?_) hcomp.measure_lt_top
  rintro ⟨q, η⟩ ⟨⟨_, hη⟩, ⟨hq, _⟩⟩
  exact ⟨⟨hq.1, hq.2.le⟩, hη⟩

/-- `logMeas c` of the box `{|x.1| ≤ T, |x.2.2| ≤ L}` is finite. -/
theorem logAL_box_lt_top (c T L : ℝ) :
    logMeas c {x : Coord | |x.1| ≤ T ∧ |x.2.2| ≤ L} < ⊤ := by
  rw [logAL_box_eq]
  unfold logMeas
  rw [Measure.prod_prod]
  exact ENNReal.mul_lt_top measure_Icc_lt_top (logAL_avg_lt_top c L)

/-- `|σ| ≤ |h|` for `σ` in the interval between `0` and `h`. -/
theorem logAL_abs_le_of_mem_uIoc (h σ : ℝ) (hσ : σ ∈ Set.uIoc 0 h) : |σ| ≤ |h| := by
  rcases Set.mem_uIcc.mp (Set.uIoc_subset_uIcc hσ) with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · calc |σ| = σ := abs_of_nonneg h1
      _ ≤ h := h2
      _ ≤ |h| := le_abs_self h
  · calc |σ| = -σ := abs_of_nonpos h2
      _ ≤ -h := neg_le_neg h1
      _ ≤ |h| := neg_le_abs h

/-! ## The main statement -/

theorem logAvgLocInt : LogAvgLocInt := by
  intro c G _hc hG h
  -- Step 1: a strongly measurable representative `G'` of `G`.
  obtain ⟨G', hG'sm, hGG'⟩ : ∃ G' : Coord → ℂ, StronglyMeasurable G' ∧ G =ᵐ[logMeas c] G' :=
    ⟨hG.aestronglyMeasurable.mk G, hG.aestronglyMeasurable.stronglyMeasurable_mk,
      hG.aestronglyMeasurable.ae_eq_mk⟩
  have hG'meas : Measurable G' := hG'sm.measurable
  have hmeasΨ : Measurable (fun p : Coord × ℝ => (p.1.1 + p.2, p.1.2)) := by fun_prop
  have hmeasF : Measurable (fun p : Coord × ℝ => G' (p.1.1 + p.2, p.1.2)) :=
    hG'meas.comp hmeasΨ
  -- Step 2: the averages of `G` and `G'` agree `logMeas c`-a.e.
  have hslice : ∀ᵐ x ∂(logMeas c), ∀ᵐ σ ∂(volume : Measure ℝ),
      G (x.1 + σ, x.2) = G' (x.1 + σ, x.2) := by
    have hN : logMeas c {y : Coord | ¬ (G y = G' y)} = 0 := ae_iff.mp hGG'
    obtain ⟨E, hNE, hEm, hE0⟩ := exists_measurable_superset_of_null hN
    have hprod0 : ((logMeas c).prod (volume : Measure ℝ))
        ((fun p : Coord × ℝ => (p.1.1 + p.2, p.1.2)) ⁻¹' E) = 0 := by
      rw [Measure.prod_apply_symm (hEm.preimage hmeasΨ)]
      have hsl : ∀ σ : ℝ, logMeas c ((fun x : Coord => (x, σ)) ⁻¹'
          ((fun p : Coord × ℝ => (p.1.1 + p.2, p.1.2)) ⁻¹' E)) = 0 := by
        intro σ
        have hpre : (fun x : Coord => (x, σ)) ⁻¹'
            ((fun p : Coord × ℝ => (p.1.1 + p.2, p.1.2)) ⁻¹' E) =
              (fun x : Coord => (x.1 + σ, x.2)) ⁻¹' E := rfl
        rw [hpre, ← Measure.map_apply (logAL_measurePreserving c σ).measurable hEm,
          (logAL_measurePreserving c σ).map_eq]
        exact hE0
      simp only [hsl, lintegral_zero]
    have hae : ∀ᵐ z ∂((logMeas c).prod (volume : Measure ℝ)),
        z ∉ (fun p : Coord × ℝ => (p.1.1 + p.2, p.1.2)) ⁻¹' E := by
      rw [ae_iff]
      simpa only [not_not, Set.ofPred_mem_eq] using hprod0
    filter_upwards [Measure.ae_ae_of_ae_prod hae] with x hx
    filter_upwards [hx] with σ hσ
    by_contra hne
    have hmem : (x.1 + σ, x.2) ∈ {y : Coord | ¬ (G y = G' y)} := hne
    exact hσ (hNE hmem)
  -- Step 3: the interval averages of `G` and `G'` agree `logMeas c`-a.e.
  have hAA : (fun x : Coord => ∫ σ in (0:ℝ)..h, G (x.1 + σ, x.2)) =ᵐ[logMeas c]
      (fun x : Coord => ∫ σ in (0:ℝ)..h, G' (x.1 + σ, x.2)) := by
    filter_upwards [hslice] with x hx
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hx] with σ hσ
    exact fun _ => hσ
  -- Step 4: integrability of the `uIoc` average of `G'` on each box.
  have hB : ∀ T L : ℝ, IntegrableOn (fun x : Coord => ∫ σ in Set.uIoc 0 h, G' (x.1 + σ, x.2))
      {x : Coord | |x.1| ≤ T ∧ |x.2.2| ≤ L} (logMeas c) := by
    intro T L
    have hK'm : MeasurableSet {x : Coord | |x.1| ≤ T + |h| ∧ |x.2.2| ≤ L} :=
      logAL_box_meas _ _
    have hK'fin : logMeas c {x : Coord | |x.1| ≤ T + |h| ∧ |x.2.2| ≤ L} < ⊤ :=
      logAL_box_lt_top c _ _
    have : IsFiniteMeasure ((logMeas c).restrict
        {x : Coord | |x.1| ≤ T + |h| ∧ |x.2.2| ≤ L}) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact hK'fin⟩
    -- finiteness of the `L¹` norm of `G'` on the enlarged box
    have hG'L2 : MemLp G' 2 (logMeas c) := MemLp.ae_eq hGG' hG
    have hC : ∫⁻ y in {x : Coord | |x.1| ≤ T + |h| ∧ |x.2.2| ≤ L}, ‖G' y‖ₑ ∂(logMeas c) < ⊤ :=
      (MemLp.integrable (one_le_two : (1 : ℝ≥0∞) ≤ 2)
        (MemLp.restrict {x : Coord | |x.1| ≤ T + |h| ∧ |x.2.2| ≤ L} hG'L2)).2
    have hνfin : (volume.restrict (Set.uIoc 0 h)) univ < ⊤ := by
      rw [Measure.restrict_apply_univ]
      exact lt_of_le_of_lt (measure_mono Set.uIoc_subset_uIcc) isCompact_uIcc.measure_lt_top
    -- the product integrand is integrable on `(logMeas c).restrict K ⊗ volume.restrict (uIoc 0 h)`
    have hprodInt : Integrable (fun p : Coord × ℝ => G' (p.1.1 + p.2, p.1.2))
        (((logMeas c).restrict {x : Coord | |x.1| ≤ T ∧ |x.2.2| ≤ L}).prod
          (volume.restrict (Set.uIoc 0 h))) := by
      refine ⟨hmeasF.aestronglyMeasurable, ?_⟩
      have hT1 : ∫⁻ p, ‖G' (p.1.1 + p.2, p.1.2)‖ₑ
          ∂(((logMeas c).restrict {x : Coord | |x.1| ≤ T ∧ |x.2.2| ≤ L}).prod
            (volume.restrict (Set.uIoc 0 h)))
          = ∫⁻ σ, ∫⁻ x, ‖G' (x.1 + σ, x.2)‖ₑ
              ∂((logMeas c).restrict {x : Coord | |x.1| ≤ T ∧ |x.2.2| ≤ L})
              ∂(volume.restrict (Set.uIoc 0 h)) := by
        rw [lintegral_prod _ hmeasF.enorm.aemeasurable]
        exact lintegral_lintegral_swap (f := fun (x : Coord) (σ : ℝ) => ‖G' (x.1 + σ, x.2)‖ₑ)
          hmeasF.enorm.aemeasurable
      -- inner bound: uniform in `σ ∈ uIoc 0 h`
      have hinner : ∀ σ ∈ Set.uIoc 0 h,
          ∫⁻ x, ‖G' (x.1 + σ, x.2)‖ₑ
              ∂((logMeas c).restrict {x : Coord | |x.1| ≤ T ∧ |x.2.2| ≤ L})
            ≤ ∫⁻ y in {x : Coord | |x.1| ≤ T + |h| ∧ |x.2.2| ≤ L}, ‖G' y‖ₑ ∂(logMeas c) := by
        intro σ hσ
        have hσ' : |σ| ≤ |h| := logAL_abs_le_of_mem_uIoc h σ hσ
        have hfm : Measurable (Set.indicator {x : Coord | |x.1| ≤ T + |h| ∧ |x.2.2| ≤ L}
            (fun y : Coord => ‖G' y‖ₑ)) :=
          hG'meas.enorm.indicator hK'm
        calc ∫⁻ x, ‖G' (x.1 + σ, x.2)‖ₑ
              ∂((logMeas c).restrict {x : Coord | |x.1| ≤ T ∧ |x.2.2| ≤ L})
            = ∫⁻ x, (Set.indicator {x : Coord | |x.1| ≤ T ∧ |x.2.2| ≤ L}
                (fun x : Coord => ‖G' (x.1 + σ, x.2)‖ₑ)) x ∂(logMeas c) :=
              (lintegral_indicator (logAL_box_meas T L) _).symm
          _ ≤ ∫⁻ x, (Set.indicator {x : Coord | |x.1| ≤ T + |h| ∧ |x.2.2| ≤ L}
                (fun y : Coord => ‖G' y‖ₑ)) (x.1 + σ, x.2) ∂(logMeas c) := by
              apply lintegral_mono
              intro x
              by_cases hx : x ∈ {x : Coord | |x.1| ≤ T ∧ |x.2.2| ≤ L}
              · have hmem : (x.1 + σ, x.2) ∈ {x : Coord | |x.1| ≤ T + |h| ∧ |x.2.2| ≤ L} := by
                  refine ⟨?_, hx.2⟩
                  have h1 : |x.1 + σ| ≤ |x.1| + |σ| := abs_add_le _ _
                  have h2 : |x.1| ≤ T := hx.1
                  show |x.1 + σ| ≤ T + |h|
                  linarith
                dsimp only
                rw [Set.indicator_of_mem hx, Set.indicator_of_mem hmem]
              · rw [Set.indicator_of_notMem hx]
                exact zero_le
          _ = ∫⁻ y, (Set.indicator {x : Coord | |x.1| ≤ T + |h| ∧ |x.2.2| ≤ L}
                (fun y : Coord => ‖G' y‖ₑ)) y ∂(logMeas c) :=
              (logAL_measurePreserving c σ).lintegral_comp
                (f := fun y : Coord => (Set.indicator {x : Coord | |x.1| ≤ T + |h| ∧ |x.2.2| ≤ L}
                  (fun y : Coord => ‖G' y‖ₑ)) y) hfm
          _ = ∫⁻ y in {x : Coord | |x.1| ≤ T + |h| ∧ |x.2.2| ≤ L}, ‖G' y‖ₑ ∂(logMeas c) :=
              lintegral_indicator hK'm _
      -- the outer integral over `σ ∈ uIoc 0 h`
      have hbound : ∫⁻ σ, ∫⁻ x, ‖G' (x.1 + σ, x.2)‖ₑ
            ∂((logMeas c).restrict {x : Coord | |x.1| ≤ T ∧ |x.2.2| ≤ L})
            ∂(volume.restrict (Set.uIoc 0 h))
          ≤ (∫⁻ y in {x : Coord | |x.1| ≤ T + |h| ∧ |x.2.2| ≤ L}, ‖G' y‖ₑ ∂(logMeas c))
            * (volume.restrict (Set.uIoc 0 h)) univ := by
        calc ∫⁻ σ, ∫⁻ x, ‖G' (x.1 + σ, x.2)‖ₑ
              ∂((logMeas c).restrict {x : Coord | |x.1| ≤ T ∧ |x.2.2| ≤ L})
              ∂(volume.restrict (Set.uIoc 0 h))
            ≤ ∫⁻ _σ, (∫⁻ y in {x : Coord | |x.1| ≤ T + |h| ∧ |x.2.2| ≤ L}, ‖G' y‖ₑ
                ∂(logMeas c)) ∂(volume.restrict (Set.uIoc 0 h)) := by
              apply lintegral_mono_ae
              filter_upwards [ae_restrict_mem measurableSet_uIoc] with σ hσ
              exact hinner σ hσ
          _ = _ := lintegral_const _
      exact hT1.trans_lt (lt_of_le_of_lt hbound (ENNReal.mul_lt_top hC hνfin))
    have hBint : Integrable (fun x : Coord => ∫ σ in Set.uIoc 0 h, G' (x.1 + σ, x.2))
        ((logMeas c).restrict {x : Coord | |x.1| ≤ T ∧ |x.2.2| ≤ L}) :=
      Integrable.integral_prod_left hprodInt
    exact hBint
  -- Step 5: assemble.
  have hpt : ∀ x : Coord, (∫ σ in (0:ℝ)..h, G' (x.1 + σ, x.2)) =
      (if 0 ≤ h then (1:ℝ) else -1) • ∫ σ in Set.uIoc 0 h, G' (x.1 + σ, x.2) :=
    fun x => intervalIntegral.intervalIntegral_eq_integral_uIoc _ _ _ _
  have hsm' : StronglyMeasurable (fun x : Coord => ∫ σ in Set.uIoc 0 h, G' (x.1 + σ, x.2)) :=
    StronglyMeasurable.integral_prod_right (ν := volume.restrict (Set.uIoc 0 h))
      (f := fun (x : Coord) (σ : ℝ) => G' (x.1 + σ, x.2)) (hG'sm.comp_measurable hmeasΨ)
  have hA'sm : StronglyMeasurable (fun x : Coord => ∫ σ in (0:ℝ)..h, G' (x.1 + σ, x.2)) := by
    have hfun : (fun x : Coord => ∫ σ in (0:ℝ)..h, G' (x.1 + σ, x.2)) =
        fun x : Coord => (if 0 ≤ h then (1:ℝ) else -1) •
          ∫ σ in Set.uIoc 0 h, G' (x.1 + σ, x.2) :=
      funext hpt
    rw [hfun]
    exact hsm'.const_smul (if 0 ≤ h then (1:ℝ) else -1)
  have hAae : AEStronglyMeasurable (fun x : Coord => ∫ σ in (0:ℝ)..h, G (x.1 + σ, x.2))
      (logMeas c) :=
    hA'sm.aestronglyMeasurable.congr hAA.symm
  refine ⟨hAae, fun T L => ?_⟩
  have hsB : IntegrableOn (fun x : Coord => (if 0 ≤ h then (1:ℝ) else -1) •
      ∫ σ in Set.uIoc 0 h, G' (x.1 + σ, x.2)) {x : Coord | |x.1| ≤ T ∧ |x.2.2| ≤ L} (logMeas c) :=
    Integrable.smul (if 0 ≤ h then (1:ℝ) else -1) (hB T L)
  have hIA' : IntegrableOn (fun x : Coord => ∫ σ in (0:ℝ)..h, G' (x.1 + σ, x.2))
      {x : Coord | |x.1| ≤ T ∧ |x.2.2| ≤ L} (logMeas c) :=
    hsB.congr_fun (fun x _ => (hpt x).symm) (logAL_box_meas T L)
  exact Integrable.congr hIA' (ae_restrict_of_ae hAA.symm)

end UnforcedLeray.Short.IIb
