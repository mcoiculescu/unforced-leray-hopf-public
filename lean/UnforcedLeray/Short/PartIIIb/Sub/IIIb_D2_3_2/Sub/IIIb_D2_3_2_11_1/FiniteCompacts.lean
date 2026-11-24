import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.Sub.IIIb_D2_3_2_11_1

/-!
# Finiteness on compacts of the gain-weighted chart measures (`PartIII-b:IIIb-D2/3/2/11/1`, source 2666-2700)

`gainZ1Measure` and `gainHTMeasure` are finite on compact sets: the age measure
`ageμ c (-1/2)` is finite on compacts (the density `s^{-1/2}` is integrable at `0`), the
transverse weight is continuous on `s ≥ 0` and the gain factor `ginv²` is continuous.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- A measure finite on compacts, with a density bounded a.e. on each compact, gives a measure
finite on compacts. -/
theorem fc_withDensity_finiteOnCompacts {μ : Measure Chart} [IsFiniteMeasureOnCompacts μ]
    (f : Chart → ℝ≥0∞)
    (h : ∀ K : Set Chart, IsCompact K → ∃ M : ℝ≥0∞, M ≠ ⊤ ∧ ∀ᵐ x ∂μ, x ∈ K → f x ≤ M) :
    IsFiniteMeasureOnCompacts (μ.withDensity f) := by
  refine ⟨fun K hK => ?_⟩
  obtain ⟨M, hM, hfM⟩ := h K hK
  rw [withDensity_apply _ hK.isClosed.measurableSet]
  have hle : ∫⁻ x in K, f x ∂μ ≤ ∫⁻ _ in K, M ∂μ := by
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_of_ae hfM, ae_restrict_mem hK.isClosed.measurableSet]
      with x hx1 hx2
    exact hx1 hx2
  rw [setLIntegral_const] at hle
  exact lt_of_le_of_lt hle (ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hM) hK.measure_lt_top)

/-- The `s`-factor of `ageμ c (-1/2)` is finite on bounded sets. -/
theorem fc_s_part (D : ℝ) (hD : 0 < D) :
    ((volume.restrict (Ioi (0 : ℝ))).withDensity fun s => ENNReal.ofReal (s ^ (-1 / 2 : ℝ)))
      (Icc (-D) D) < ⊤ := by
  rw [withDensity_apply _ measurableSet_Icc, Measure.restrict_restrict measurableSet_Icc]
  have hsub : Icc (-D) D ∩ Ioi (0 : ℝ) ⊆ Ioo (0 : ℝ) (D + 1) := by
    rintro x ⟨⟨_, h2⟩, h3⟩
    exact ⟨h3, by linarith⟩
  have hint : Integrable (fun x : ℝ => x ^ (-1 / 2 : ℝ)) (volume.restrict (Ioo (0 : ℝ) (D + 1))) :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff (by linarith : (0 : ℝ) < D + 1)).2 (by norm_num)
  calc ∫⁻ x in Icc (-D) D ∩ Ioi (0 : ℝ), ENNReal.ofReal (x ^ (-1 / 2 : ℝ))
      ≤ ∫⁻ x in Ioo (0 : ℝ) (D + 1), ENNReal.ofReal (x ^ (-1 / 2 : ℝ)) :=
        lintegral_mono' (Measure.restrict_mono hsub le_rfl) le_rfl
    _ < ⊤ := hint.lintegral_lt_top

/-- `ageμ c (-1/2)` is finite on compact sets. -/
theorem fc_ageμ_finiteOnCompacts (c : ℝ) :
    IsFiniteMeasureOnCompacts (UnforcedLeray.Axi.ageμ c (-1 / 2)) := by
  have hAvg : IsFiniteMeasureOnCompacts (UnforcedLeray.Cyl.avgμ c) := by
    unfold UnforcedLeray.Cyl.avgμ UnforcedLeray.Cyl.cellμ
    exact IsFiniteMeasureOnCompacts.smul _ ENNReal.ofReal_ne_top
  haveI := hAvg
  refine ⟨fun K hK => ?_⟩
  have hcont : Continuous fun x : Chart => |x.1| + |x.2.1| + |x.2.2| := by fun_prop
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont.continuousOn
  obtain ⟨D, hD, hDK⟩ : ∃ D : ℝ, 0 < D ∧ ∀ x ∈ K, |x.1| + |x.2.1| + |x.2.2| ≤ D := by
    refine ⟨max C 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun x hx => ?_⟩
    have h := hC x hx
    simp only [Real.norm_eq_abs] at h
    exact le_trans ((le_abs_self _).trans h) (le_max_left _ _)
  have hbox : K ⊆ Icc (-D) D ×ˢ (Icc (-D) D ×ˢ Icc (-D) D) := by
    intro x hx
    have h := hDK x hx
    have h1 := abs_nonneg x.1
    have h2 := abs_nonneg x.2.1
    have h3 := abs_nonneg x.2.2
    exact ⟨abs_le.mp (by linarith), abs_le.mp (by linarith), abs_le.mp (by linarith)⟩
  have hbox_fin : UnforcedLeray.Axi.ageμ c (-1 / 2)
      (Icc (-D) D ×ˢ (Icc (-D) D ×ˢ Icc (-D) D)) < ⊤ := by
    unfold UnforcedLeray.Axi.ageμ
    rw [Measure.prod_prod]
    exact ENNReal.mul_lt_top (fc_s_part D hD) (isCompact_Icc.prod isCompact_Icc).measure_lt_top
  exact (measure_mono hbox).trans_lt hbox_fin

/-- `ginv²` is continuous for `ν > 0`. -/
theorem fc_ginv_sq_continuous (γ ν : ℝ) (hν : 0 < ν) :
    Continuous fun p : Chart => ginv γ ν p ^ 2 := by
  have hm : Continuous fun p : Chart => max p.1 0 := continuous_fst.max continuous_const
  have hden : Continuous fun p : Chart => 1 + ν * max p.1 0 :=
    continuous_const.add (continuous_const.mul hm)
  have hpos : ∀ p : Chart, 1 + ν * max p.1 0 ≠ 0 := fun p => by
    have h := mul_nonneg hν.le (le_max_right p.1 0)
    exact (by linarith : (0 : ℝ) < 1 + ν * max p.1 0).ne'
  have hq : Continuous fun p : Chart => γ * max p.1 0 / (1 + ν * max p.1 0) :=
    (continuous_const.mul hm).div hden hpos
  have hg : Continuous fun p : Chart => ginv γ ν p := by
    unfold ginv UnforcedLeray.Short.IIIa.gainG
    exact (Real.continuous_exp.comp hq).inv₀ fun p => (Real.exp_pos _).ne'
  exact hg.pow 2

/-- `ageμ c a` is carried by `s > 0`. -/
theorem fc_ae_pos (c a : ℝ) : ∀ᵐ p ∂(UnforcedLeray.Axi.ageμ c a), 0 < p.1 := by
  rw [ae_iff]
  have hset : {p : Chart | ¬ 0 < p.1} = Iic (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)) := by
    ext p; simp
  rw [hset]
  unfold UnforcedLeray.Axi.ageμ
  haveI : SFinite (Cyl.avgμ c) := by
    unfold Cyl.avgμ
    infer_instance
  have h0 : (volume.restrict (Ioi (0 : ℝ))).restrict (Iic (0 : ℝ)) = 0 := by
    rw [Measure.restrict_restrict measurableSet_Iic]
    have hempty : Iic (0 : ℝ) ∩ Ioi (0 : ℝ) = ∅ := by
      ext x; simp
    rw [hempty, Measure.restrict_empty]
  rw [Measure.prod_prod, withDensity_apply _ measurableSet_Iic, h0, lintegral_zero_measure,
    zero_mul]

/-- `z1Measure` is finite on compact sets. -/
theorem fc_z1_finiteOnCompacts (c mZ : ℝ) :
    IsFiniteMeasureOnCompacts (z1Measure c mZ) := by
  haveI := fc_ageμ_finiteOnCompacts c
  unfold z1Measure
  apply fc_withDensity_finiteOnCompacts
  intro K hK
  have hg : Continuous fun p : Chart =>
      (1 + (p.2.2 / Real.sqrt (1 + max p.1 0)) ^ 2) ^ (mZ / 2) := by
    have hden : Continuous fun p : Chart => Real.sqrt (1 + max p.1 0) :=
      Real.continuous_sqrt.comp (continuous_const.add (continuous_fst.max continuous_const))
    have hdpos : ∀ p : Chart, Real.sqrt (1 + max p.1 0) ≠ 0 := fun p =>
      (Real.sqrt_pos.2 (by linarith [le_max_right p.1 0])).ne'
    have hdiv : Continuous fun p : Chart => p.2.2 / Real.sqrt (1 + max p.1 0) :=
      (continuous_snd.comp continuous_snd).div hden hdpos
    have hne : ∀ p : Chart, (1 + (p.2.2 / Real.sqrt (1 + max p.1 0)) ^ 2 : ℝ) ≠ 0 :=
      fun p => by positivity
    exact (continuous_const.add (hdiv.pow 2)).rpow_const fun p => Or.inl (hne p)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hg.continuousOn
  refine ⟨ENNReal.ofReal (C ^ 2), ENNReal.ofReal_ne_top, ?_⟩
  filter_upwards [fc_ae_pos c (-1 / 2)] with p hp
  intro hpK
  apply ENNReal.ofReal_le_ofReal
  have hgp : UnforcedLeray.Short.IIIa.transWeight mZ p
      = (1 + (p.2.2 / Real.sqrt (1 + max p.1 0)) ^ 2) ^ (mZ / 2) := by
    unfold UnforcedLeray.Short.IIIa.transWeight
    rw [max_eq_left hp.le]
  have hb := hC p hpK
  simp only [Real.norm_eq_abs] at hb
  obtain ⟨h1, h2⟩ := abs_le.mp hb
  rw [hgp]
  exact sq_le_sq' h1 h2

/-- `z1Measure` gain-weighted by `ginv²` is finite on compacts. -/
theorem fc_gainZ1_finiteOnCompacts (c mZ γ ν : ℝ) (hν : 0 < ν) :
    IsFiniteMeasureOnCompacts (gainZ1Measure c mZ γ ν) := by
  haveI := fc_z1_finiteOnCompacts c mZ
  unfold gainZ1Measure
  apply fc_withDensity_finiteOnCompacts
  intro K hK
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (fc_ginv_sq_continuous γ ν hν).continuousOn
  refine ⟨ENNReal.ofReal C, ENNReal.ofReal_ne_top, ?_⟩
  refine Filter.Eventually.of_forall fun p hpK => ?_
  apply ENNReal.ofReal_le_ofReal
  have hb := hC p hpK
  simp only [Real.norm_eq_abs] at hb
  exact le_trans (le_abs_self _) hb

/-- `htRhoMeasure` gain-weighted by `ginv²` is finite on compacts. -/
theorem fc_gainHT_finiteOnCompacts (c ρb γ ν : ℝ) (hν : 0 < ν) :
    IsFiniteMeasureOnCompacts (gainHTMeasure c ρb γ ν) := by
  haveI := fc_ageμ_finiteOnCompacts c
  haveI : IsFiniteMeasureOnCompacts (htRhoMeasure c ρb) := by
    unfold htRhoMeasure
    exact IsFiniteMeasureOnCompacts.smul _ ENNReal.ofReal_ne_top
  unfold gainHTMeasure
  apply fc_withDensity_finiteOnCompacts
  intro K hK
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (fc_ginv_sq_continuous γ ν hν).continuousOn
  refine ⟨ENNReal.ofReal C, ENNReal.ofReal_ne_top, ?_⟩
  refine Filter.Eventually.of_forall fun p hpK => ?_
  apply ENNReal.ofReal_le_ofReal
  have hb := hC p hpK
  simp only [Real.norm_eq_abs] at hb
  exact le_trans (le_abs_self _) hb

theorem gainMeasures_finiteOnCompacts (c mZ ρb γ ν : ℝ) (hc : 0 < c) (hν : 0 < ν) : IsFiniteMeasureOnCompacts (gainZ1Measure c mZ γ ν) ∧ IsFiniteMeasureOnCompacts (gainHTMeasure c ρb γ ν) :=
  ⟨fc_gainZ1_finiteOnCompacts c mZ γ ν hν, fc_gainHT_finiteOnCompacts c ρb γ ν hν⟩

end UnforcedLeray.Short.PartIIIb.Concrete
