import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_3_6_1_2

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace K2cAux

open UnforcedLeray

theorem bandSet_measurable' (d R : ℝ) :
    MeasurableSet (UnforcedLeray.Short.IIIa.AdjE1.bandSet d R) :=
  (B0579.measurableSet_cell d).inter (measurableSet_le (continuous_snd.abs).measurable
    measurable_const)

/-- On a band the weight `jb^(-m)` is bounded below by a positive constant. -/
theorem band_density_lower {d m R : ℝ} (hd : 0 < d) :
    ∃ c : ℝ, 0 < c ∧ ∀ x ∈ UnforcedLeray.Short.IIIa.AdjE1.bandSet d R, c ≤ B0579.jb x ^ (-m) := by
  refine ⟨min 1 ((1 + d ^ 2 + R ^ 2) ^ (-m)), lt_min one_pos ?_, ?_⟩
  · exact Real.rpow_pos_of_pos (by positivity) _
  intro x hx
  obtain ⟨h1, h2⟩ : -(d / 2) ≤ x.1 ∧ x.1 < d / 2 := hx.1.1
  have hR2 : |x.2| ≤ R := hx.2
  have hR0 : 0 ≤ R := le_trans (abs_nonneg _) hR2
  have hxsq : x.2 ^ 2 ≤ R ^ 2 := by nlinarith [sq_abs x.2, abs_nonneg x.2]
  have hq2 : x.1 ^ 2 ≤ d ^ 2 := by nlinarith
  have hjb : B0579.jb x ≤ 1 + d ^ 2 + R ^ 2 := by
    unfold B0579.jb
    linarith
  have hjb1 : 1 ≤ B0579.jb x := by
    unfold B0579.jb
    nlinarith [sq_nonneg x.1, sq_nonneg x.2]
  have hjbpos : 0 < B0579.jb x := by linarith
  rcases le_total 0 (-m) with hm | hm
  · exact (min_le_left _ _).trans (Real.one_le_rpow hjb1 hm)
  · exact (min_le_right _ _).trans (Real.rpow_le_rpow_of_nonpos hjbpos hjb hm)

theorem band_le_cellMeasure {d m R c : ℝ} (hc : 0 < c)
    (hcS : ∀ x ∈ UnforcedLeray.Short.IIIa.AdjE1.bandSet d R, c ≤ B0579.jb x ^ (-m)) :
    volume.restrict (UnforcedLeray.Short.IIIa.AdjE1.bandSet d R) ≤
      (ENNReal.ofReal c)⁻¹ • B0579.cellMeasure d (-m) := by
  rw [Measure.le_iff]
  intro t ht
  rw [Measure.restrict_apply ht, Measure.smul_apply, smul_eq_mul]
  have hc0 : ENNReal.ofReal c ≠ 0 := (ENNReal.ofReal_pos.2 hc).ne'
  have hctop : ENNReal.ofReal c ≠ ⊤ := ENNReal.ofReal_ne_top
  have hμ : B0579.cellMeasure d (-m) t =
      ∫⁻ x in t, (B0579.density (-m) x : ℝ≥0∞) ∂(volume.restrict (B0579.cell d)) := by
    unfold B0579.cellMeasure
    exact withDensity_apply _ ht
  have hlow : ENNReal.ofReal c * volume (t ∩ UnforcedLeray.Short.IIIa.AdjE1.bandSet d R) ≤
      ∫⁻ x in t, (B0579.density (-m) x : ℝ≥0∞) ∂(volume.restrict (B0579.cell d)) := by
    rw [Measure.restrict_restrict ht]
    have hsub : t ∩ UnforcedLeray.Short.IIIa.AdjE1.bandSet d R ⊆ t ∩ B0579.cell d :=
      inter_subset_inter_right _ (fun x hx => hx.1)
    calc ENNReal.ofReal c * volume (t ∩ UnforcedLeray.Short.IIIa.AdjE1.bandSet d R)
        = ∫⁻ _ in t ∩ UnforcedLeray.Short.IIIa.AdjE1.bandSet d R, ENNReal.ofReal c :=
          (setLIntegral_const _ _).symm
      _ ≤ ∫⁻ x in t ∩ UnforcedLeray.Short.IIIa.AdjE1.bandSet d R,
            (B0579.density (-m) x : ℝ≥0∞) := by
          refine setLIntegral_mono (B0579.measurable_density (-m)).coe_nnreal_ennreal ?_
          intro x hx
          rw [← ENNReal.ofReal_coe_nnreal, B0579.coe_density]
          exact ENNReal.ofReal_le_ofReal (hcS x hx.2)
      _ ≤ ∫⁻ x in t ∩ B0579.cell d, (B0579.density (-m) x : ℝ≥0∞) :=
          lintegral_mono_set hsub
  rw [hμ]
  calc volume (t ∩ UnforcedLeray.Short.IIIa.AdjE1.bandSet d R)
      = (ENNReal.ofReal c)⁻¹ * (ENNReal.ofReal c * volume
          (t ∩ UnforcedLeray.Short.IIIa.AdjE1.bandSet d R)) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hc0 hctop, one_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left hlow zero_le

theorem band_finite_volume {d R : ℝ} :
    volume (UnforcedLeray.Short.IIIa.AdjE1.bandSet d R) < ⊤ := by
  have hsub : UnforcedLeray.Short.IIIa.AdjE1.bandSet d R ⊆
      Icc (-(d / 2)) (d / 2) ×ˢ Icc (-R) R := by
    intro x hx
    exact ⟨Ico_subset_Icc_self hx.1.1, abs_le.1 hx.2⟩
  exact lt_of_le_of_lt (measure_mono hsub)
    ((isCompact_Icc.prod isCompact_Icc).measure_lt_top)

end K2cAux

open K2cAux UnforcedLeray in
/-- **Leaf C** (SP 3044-3047, 3052-3058): an a.e. measurable field of finite `X_{-m,d}` norm is
integrable on every band. -/
theorem bandIntOfL2 : UnforcedLeray.Short.IIIa.AdjE1.BandIntOfL2 := by
  intro d m f hd hne R hf
  obtain ⟨c, hc, hcS⟩ := band_density_lower (m := m) (R := R) hd
  have hle := band_le_cellMeasure (d := d) (m := m) (R := R) hc hcS
  have hlt : eLpNorm f 2 (B0579.cellMeasure d (-m)) < ⊤ := lt_top_iff_ne_top.2 hne
  have hbound : eLpNorm f 2 (volume.restrict (UnforcedLeray.Short.IIIa.AdjE1.bandSet d R)) < ⊤ := by
    refine lt_of_le_of_lt (eLpNorm_mono_measure f hle) ?_
    rw [eLpNorm_smul_measure_of_ne_top (by norm_num) f, smul_eq_mul]
    refine ENNReal.mul_lt_top ?_ hlt
    exact ENNReal.rpow_lt_top_of_nonneg (by positivity) (ENNReal.inv_ne_top.2
      (ENNReal.ofReal_pos.2 hc).ne')
  have : IsFiniteMeasure (volume.restrict (UnforcedLeray.Short.IIIa.AdjE1.bandSet d R)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact band_finite_volume (d := d) (R := R)⟩
  have hmem : MemLp f 2 (volume.restrict (UnforcedLeray.Short.IIIa.AdjE1.bandSet d R)) :=
    ⟨hf, hbound⟩
  exact hmem.integrable one_le_two

#print axioms bandIntOfL2
