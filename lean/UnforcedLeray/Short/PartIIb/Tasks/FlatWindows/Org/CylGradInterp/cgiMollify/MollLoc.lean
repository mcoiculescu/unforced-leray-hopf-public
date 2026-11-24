import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T13_1_5_5

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

open MeasureTheory Set Filter
open scoped ENNReal ContDiff Topology

/-- The `q`-shift `x ↦ qShift a x` preserves Lebesgue measure on `Coord`. -/
theorem mollLoc_mp (a : ℝ) : MeasurePreserving (qShift a) volume volume := by
  have h1 : MeasurePreserving (fun t : ℝ => t + a) volume volume :=
    measurePreserving_add_right volume a
  exact (MeasurePreserving.id (volume : Measure ℝ)).prod
    (h1.prod (MeasurePreserving.id (volume : Measure ℝ)))

theorem mollLoc_qShift_qShift (s t : ℝ) (x : Coord) :
    qShift s (qShift t x) = qShift (s + t) x := by
  simp only [qShift]
  congr 2
  ring

theorem mollLoc_qShift_zero (x : Coord) : qShift 0 x = x := by
  simp [qShift]

theorem mollLoc_ae_add {G : Coord → ℂ} {s t : ℝ} (hs : ∀ᵐ x : Coord, G (qShift s x) = G x)
    (ht : ∀ᵐ x : Coord, G (qShift t x) = G x) : ∀ᵐ x : Coord, G (qShift (s + t) x) = G x := by
  have h : ∀ᵐ x : Coord, G (qShift s (qShift t x)) = G (qShift t x) :=
    (mollLoc_mp t).quasiMeasurePreserving.ae hs
  filter_upwards [h, ht] with x hx1 hx2
  rw [← mollLoc_qShift_qShift]
  exact hx1.trans hx2

theorem mollLoc_ae_neg {G : Coord → ℂ} {c : ℝ} (hper : ∀ᵐ x : Coord, G (qShift c x) = G x) :
    ∀ᵐ x : Coord, G (qShift (-c) x) = G x := by
  filter_upwards [(mollLoc_mp (-c)).quasiMeasurePreserving.ae hper] with x hx
  rw [mollLoc_qShift_qShift, add_neg_cancel, mollLoc_qShift_zero] at hx
  exact hx.symm

theorem mollLoc_ae_int {G : Coord → ℂ} {c : ℝ} (hper : ∀ᵐ x : Coord, G (qShift c x) = G x)
    (k : ℤ) : ∀ᵐ x : Coord, G (qShift ((k : ℝ) * c) x) = G x := by
  refine Int.induction_on k ?_ ?_ ?_
  · filter_upwards with x
    simp [qShift]
  · intro n ih
    have e : (((n : ℤ) + 1 : ℤ) : ℝ) * c = ((n : ℤ) : ℝ) * c + c := by
      push_cast
      ring
    rw [e]
    exact mollLoc_ae_add ih hper
  · intro n ih
    have e : ((-(n : ℤ) - 1 : ℤ) : ℝ) * c = ((-(n : ℤ) : ℤ) : ℝ) * c + (-c) := by
      push_cast
      ring
    rw [e]
    exact mollLoc_ae_add ih (mollLoc_ae_neg hper)

/-- Integer shifts: the indicator of a preimage pulls back to the indicator on the set. -/
theorem mollLoc_shift_lintegral {g : Coord → ℂ} (hg : Measurable g) {c : ℝ}
    (hper : ∀ᵐ x : Coord, g (qShift c x) = g x) {T : Set Coord} (hT : MeasurableSet T)
    (k : ℤ) :
    ∫⁻ x, (qShift ((k : ℝ) * c) ⁻¹' T).indicator (fun y => ‖g y‖ₑ) x
      = ∫⁻ y in T, ‖g y‖ₑ := by
  have hae := mollLoc_ae_int hper k
  have hmeas : Measurable (T.indicator (fun y => ‖g y‖ₑ)) :=
    hg.enorm.indicator hT
  rw [← lintegral_indicator hT]
  rw [lintegral_congr_ae (g := fun x => T.indicator (fun y => ‖g y‖ₑ) (qShift ((k : ℝ) * c) x))
    ?_]
  · exact (mollLoc_mp ((k : ℝ) * c)).lintegral_comp hmeas
  · filter_upwards [hae] with x hx
    by_cases h : qShift ((k : ℝ) * c) x ∈ T
    · have hx' : x ∈ qShift ((k : ℝ) * c) ⁻¹' T := h
      rw [Set.indicator_of_mem hx', Set.indicator_of_mem h]
      simp only [hx]
    · have hx' : x ∉ qShift ((k : ℝ) * c) ⁻¹' T := h
      rw [Set.indicator_of_notMem hx', Set.indicator_of_notMem h]

/-- The index of the translate that puts `q` into the centred cell. -/
theorem mollLoc_index (c M q : ℝ) (hc : 0 < c) (hq : |q| ≤ M) :
    ∃ k : ℤ, -(⌈M / c⌉ + 2) ≤ k ∧ k ≤ ⌈M / c⌉ + 2 ∧
      q + (k : ℝ) * c ∈ Ico (-c / 2) (c / 2) := by
  have hq1 : -M ≤ q := (abs_le.1 hq).1
  have hq2 : q ≤ M := (abs_le.1 hq).2
  set m : ℤ := ⌊(q + c / 2) / c⌋ with hm
  have h1 : (m : ℝ) ≤ (q + c / 2) / c := Int.floor_le _
  have h2 : (q + c / 2) / c < (m : ℝ) + 1 := Int.lt_floor_add_one _
  have h1' : (m : ℝ) * c ≤ q + c / 2 := (le_div_iff₀ hc).1 h1
  have h2' : q + c / 2 < ((m : ℝ) + 1) * c := (div_lt_iff₀ hc).1 h2
  have hceil : M ≤ (⌈M / c⌉ : ℝ) * c := by
    have := Int.le_ceil (M / c)
    rwa [div_le_iff₀ hc] at this
  have hup : (m : ℝ) ≤ (⌈M / c⌉ : ℝ) + 2 := by
    by_contra hcon
    push_neg at hcon
    nlinarith [mul_lt_mul_of_pos_right hcon hc]
  have hlow : -((⌈M / c⌉ : ℝ) + 2) ≤ (m : ℝ) := by
    by_contra hcon
    push_neg at hcon
    nlinarith [mul_lt_mul_of_pos_right hcon hc]
  have hup' : m ≤ ⌈M / c⌉ + 2 := by exact_mod_cast hup
  have hlow' : -(⌈M / c⌉ + 2) ≤ m := by exact_mod_cast hlow
  refine ⟨-m, by linarith, by linarith, ?_⟩
  constructor
  · push_cast
    linarith
  · push_cast
    linarith

theorem mollLoc_mem_ball {x : Coord} {M : ℝ} (h : x ∈ Metric.closedBall (0 : Coord) M) :
    |x.1| ≤ M ∧ |x.2.1| ≤ M ∧ |x.2.2| ≤ M := by
  simp only [mem_closedBall_zero_iff, Prod.norm_def, max_le_iff, Real.norm_eq_abs] at h
  exact ⟨h.1, h.2.1, h.2.2⟩

/-- Covering the ball by finitely many `q`-translates of the strip `T`. -/
theorem mollLoc_cover {g : Coord → ℂ} (hg : Measurable g) {c : ℝ} (hc : 0 < c)
    (hper : ∀ᵐ x : Coord, g (qShift c x) = g x) (M : ℝ) :
    ∫⁻ x in Metric.closedBall (0 : Coord) M, ‖g x‖ₑ ≤
      ∑ k ∈ Finset.Icc (-(⌈M / c⌉ + 2)) (⌈M / c⌉ + 2),
        ∫⁻ y in Icc (-M) M ×ˢ (Ico (-c / 2) (c / 2) ×ˢ Icc (-M) M), ‖g y‖ₑ := by
  set T : Set Coord := Icc (-M) M ×ˢ (Ico (-c / 2) (c / 2) ×ˢ Icc (-M) M) with hTdef
  have hT : MeasurableSet T :=
    measurableSet_Icc.prod (measurableSet_Ico.prod measurableSet_Icc)
  have hB : MeasurableSet (Metric.closedBall (0 : Coord) M) := measurableSet_closedBall
  rw [← lintegral_indicator hB]
  calc ∫⁻ x, (Metric.closedBall (0 : Coord) M).indicator (fun y => ‖g y‖ₑ) x
      ≤ ∫⁻ x, ∑ k ∈ Finset.Icc (-(⌈M / c⌉ + 2)) (⌈M / c⌉ + 2),
          (qShift ((k : ℝ) * c) ⁻¹' T).indicator (fun y => ‖g y‖ₑ) x := by
        apply lintegral_mono
        intro x
        by_cases hx : x ∈ Metric.closedBall (0 : Coord) M
        · obtain ⟨hxa, hxb, hxc⟩ := mollLoc_mem_ball hx
          obtain ⟨k, hk1, hk2, hk3⟩ := mollLoc_index c M x.2.1 hc hxb
          have hmem : x ∈ qShift ((k : ℝ) * c) ⁻¹' T := by
            show qShift ((k : ℝ) * c) x ∈ T
            rw [hTdef]
            exact ⟨abs_le.1 hxa, ⟨hk3, abs_le.1 hxc⟩⟩
          have hle := Finset.single_le_sum
            (f := fun k : ℤ => (qShift ((k : ℝ) * c) ⁻¹' T).indicator (fun y => ‖g y‖ₑ) x)
            (fun j _ => zero_le) (Finset.mem_Icc.2 ⟨hk1, hk2⟩)
          rw [Set.indicator_of_mem hx]
          calc ‖g x‖ₑ = (qShift ((k : ℝ) * c) ⁻¹' T).indicator (fun y => ‖g y‖ₑ) x :=
                (Set.indicator_of_mem hmem (fun y => ‖g y‖ₑ)).symm
            _ ≤ _ := hle
        · rw [Set.indicator_of_notMem hx]
          exact zero_le
    _ = ∑ k ∈ Finset.Icc (-(⌈M / c⌉ + 2)) (⌈M / c⌉ + 2),
          ∫⁻ x, (qShift ((k : ℝ) * c) ⁻¹' T).indicator (fun y => ‖g y‖ₑ) x := by
        rw [lintegral_finset_sum]
        intro k _
        exact (hg.enorm.indicator ((mollLoc_mp ((k : ℝ) * c)).measurable hT))
    _ = _ := Finset.sum_congr rfl (fun k _ => mollLoc_shift_lintegral hg hper hT k)

/-- The strip `T` carries finite `L^1`-mass of `f` (Hölder on the finite-measure strip). -/
theorem mollLoc_T_finite {f : Coord → ℂ} (hfm : AEStronglyMeasurable f volume) {c r : ℝ}
    (hc : 0 < c) (hr : 1 < r)
    (hfin : eLpNorm f (ENNReal.ofReal r) (UnforcedLeray.Short.IIb.cylMeas c) < ⊤) (M : ℝ) :
    ∫⁻ y in Icc (-M) M ×ˢ (Ico (-c / 2) (c / 2) ×ˢ Icc (-M) M), ‖f y‖ₑ < ⊤ := by
  set T : Set Coord := Icc (-M) M ×ˢ (Ico (-c / 2) (c / 2) ×ˢ Icc (-M) M) with hTdef
  have hsub : T ⊆ Icc (-M) M ×ˢ (Icc (-c / 2) (c / 2) ×ˢ Icc (-M) M) :=
    Set.prod_mono subset_rfl (Set.prod_mono Set.Ico_subset_Icc_self subset_rfl)
  have hTfin : volume T < ⊤ :=
    lt_of_le_of_lt (measure_mono hsub)
      (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)).measure_lt_top
  have hBsub : (Ico (-c / 2) (c / 2) ×ˢ Icc (-M) M : Set (ℝ × ℝ)) ⊆
      UnforcedLeray.Cyl.cell c :=
    Set.prod_mono subset_rfl (Set.subset_univ _)
  have hcellμ : ENNReal.ofReal c • UnforcedLeray.Cyl.avgμ c
      = volume.restrict (UnforcedLeray.Cyl.cell c) := by
    unfold UnforcedLeray.Cyl.avgμ UnforcedLeray.Cyl.cellμ
    rw [smul_smul, ← ENNReal.ofReal_mul hc.le, mul_inv_cancel₀ hc.ne', ENNReal.ofReal_one,
      one_smul]
  have hcomp : volume.restrict T ≤ ENNReal.ofReal c • UnforcedLeray.Short.IIb.cylMeas c := by
    calc volume.restrict T
        = (volume.restrict (Icc (-M) M)).prod
            (volume.restrict (Ico (-c / 2) (c / 2) ×ˢ Icc (-M) M : Set (ℝ × ℝ))) := by
          rw [hTdef, Measure.volume_eq_prod, Measure.prod_restrict]
      _ ≤ (volume : Measure ℝ).prod (volume.restrict (UnforcedLeray.Cyl.cell c)) :=
          Measure.prod_mono Measure.restrict_le_self
            (Measure.restrict_mono hBsub le_rfl)
      _ = (volume : Measure ℝ).prod (ENNReal.ofReal c • UnforcedLeray.Cyl.avgμ c) := by
          rw [hcellμ]
      _ = ENNReal.ofReal c • UnforcedLeray.Short.IIb.cylMeas c := by
          rw [Measure.prod_smul_right]
          rfl
  have hfin' : eLpNorm f (ENNReal.ofReal r) (volume.restrict T) < ⊤ := by
    calc eLpNorm f (ENNReal.ofReal r) (volume.restrict T)
        ≤ eLpNorm f (ENNReal.ofReal r) (ENNReal.ofReal c • UnforcedLeray.Short.IIb.cylMeas c) :=
          eLpNorm_mono_measure f hcomp
      _ < ⊤ := by
          rw [eLpNorm_smul_measure_of_ne_top ENNReal.ofReal_ne_top, smul_eq_mul]
          exact ENNReal.mul_lt_top
            (ENNReal.rpow_lt_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top) hfin
  have hr1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal r := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hr.le
  have hH := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := volume.restrict T) hr1 hfm.restrict
  rw [eLpNorm_one_eq_lintegral_enorm] at hH
  refine lt_of_le_of_lt hH (ENNReal.mul_lt_top hfin' (ENNReal.rpow_lt_top_of_nonneg ?_ ?_))
  · simp only [ENNReal.toReal_one, ENNReal.toReal_ofReal (by linarith : (0 : ℝ) ≤ r)]
    have h1r : r⁻¹ ≤ 1 := (inv_le_one₀ (by linarith)).2 hr.le
    norm_num
    linarith
  · rw [Measure.restrict_apply_univ]
    exact hTfin.ne

/-- **Local integrability** (`MollLoc`). -/
theorem mollLoc_proof : UnforcedLeray.Short.IIb.MollLoc := by
  intro c r hc hr f hper hfm hfin
  have hper' : ∀ᵐ x : Coord, f (qShift c x) = f x := hper
  set g := hfm.mk f with hgdef
  have hgm : Measurable g := hfm.stronglyMeasurable_mk.measurable
  have hfg : f =ᵐ[volume] g := hfm.ae_eq_mk
  have hperg : ∀ᵐ x : Coord, g (qShift c x) = g x := by
    filter_upwards [hper', hfg, (mollLoc_mp c).quasiMeasurePreserving.ae hfg] with x h1 h2 h3
    rw [← h3, h1, h2]
  have hgfin : ∀ M : ℝ, IntegrableOn g (Metric.closedBall (0 : Coord) M) volume := by
    intro M
    refine ⟨hgm.aestronglyMeasurable, ?_⟩
    show ∫⁻ x in Metric.closedBall (0 : Coord) M, ‖g x‖ₑ < ⊤
    refine lt_of_le_of_lt (mollLoc_cover hgm hc hperg M) ?_
    refine ENNReal.sum_lt_top.2 (fun k _ => ?_)
    have hgf : ∀ᵐ y ∂(volume.restrict (Icc (-M) M ×ˢ (Ico (-c / 2) (c / 2) ×ˢ Icc (-M) M))),
        ‖g y‖ₑ = ‖f y‖ₑ :=
      ae_restrict_of_ae (by
        filter_upwards [hfg.symm] with y hy
        rw [hy])
    rw [lintegral_congr_ae hgf]
    exact mollLoc_T_finite hfm hc hr hfin M
  rw [locallyIntegrable_iff]
  intro k hk
  obtain ⟨R, hR⟩ := hk.isBounded.subset_closedBall 0
  exact ((hgfin R).mono_set hR).congr_fun_ae (ae_restrict_of_ae hfg.symm)

end UnforcedLeray.Short.IIb
