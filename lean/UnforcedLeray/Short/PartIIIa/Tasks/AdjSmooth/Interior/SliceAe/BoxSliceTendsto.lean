import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_7_2_1_1_9

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

theorem boxSliceTendsto : UnforcedLeray.Short.IIIa.BoxSliceTendsto := by
  intro t s G hG r₀ hr₀ R
  have hKc : IsCompact (sliceBox R) := by
    unfold sliceBox
    exact isCompact_Icc.prod isCompact_Icc
  have hKm : MeasurableSet (sliceBox R) := hKc.isClosed.measurableSet
  have hmin_pos : 0 < min (r₀ - t) (s - r₀) :=
    lt_min (by linarith [hr₀.1]) (by linarith [hr₀.2])
  set δ : ℝ := min (r₀ - t) (s - r₀) / 2 with hδdef
  have hδ : 0 < δ := by rw [hδdef]; positivity
  have hm1 : min (r₀ - t) (s - r₀) ≤ r₀ - t := min_le_left _ _
  have hm2 : min (r₀ - t) (s - r₀) ≤ s - r₀ := min_le_right _ _
  have hIcc : Icc (r₀ - δ) (r₀ + δ) ⊆ Ioo t s := by
    intro r hr
    constructor <;> linarith [hr.1, hr.2]
  have hQc : IsCompact (Icc (r₀ - δ) (r₀ + δ) ×ˢ sliceBox R) := isCompact_Icc.prod hKc
  have hQsub : Icc (r₀ - δ) (r₀ + δ) ×ˢ sliceBox R ⊆ Ioo t s ×ˢ (univ : Set (ℝ × ℝ)) :=
    fun p hp => ⟨hIcc hp.1, mem_univ _⟩
  have hUC : UniformContinuousOn G (Icc (r₀ - δ) (r₀ + δ) ×ˢ sliceBox R) :=
    hQc.uniformContinuousOn_of_continuous (hG.mono hQsub)
  have hLfin : (volume.restrict (sliceBox R)) univ ≠ ⊤ := by
    rw [Measure.restrict_apply_univ]
    exact hKc.measure_lt_top.ne
  have hL : (volume.restrict (sliceBox R)) univ ^ (2 : ℝ≥0∞).toReal⁻¹ ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (inv_nonneg.2 ENNReal.toReal_nonneg) hLfin
  refine ENNReal.tendsto_nhds_zero.2 fun ε hε => ?_
  by_cases hεtop : ε = ⊤
  · exact Eventually.of_forall fun r => by rw [hεtop]; exact le_top
  have hεr : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' hεtop
  set L := (volume.restrict (sliceBox R)) univ ^ (2 : ℝ≥0∞).toReal⁻¹ with hLdef
  have hL0 : 0 ≤ L.toReal := ENNReal.toReal_nonneg
  set e : ℝ := ε.toReal / (L.toReal + 1) with hedef
  have hepos : 0 < e := div_pos hεr (by linarith)
  have hLe : L * ENNReal.ofReal e ≤ ε := by
    have hLr : L = ENNReal.ofReal L.toReal := (ENNReal.ofReal_toReal hL).symm
    have hmul : e * (L.toReal + 1) = ε.toReal :=
      div_mul_cancel₀ _ (ne_of_gt (by linarith))
    have hle : L.toReal * e ≤ ε.toReal := by nlinarith
    calc L * ENNReal.ofReal e = ENNReal.ofReal (L.toReal * e) := by
          rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ← hLr]
      _ ≤ ENNReal.ofReal ε.toReal := ENNReal.ofReal_le_ofReal hle
      _ = ε := ENNReal.ofReal_toReal hεtop
  obtain ⟨δ', hδ', hUCδ⟩ := Metric.uniformContinuousOn_iff.1 hUC e hepos
  have hm : 0 < min δ' δ := lt_min hδ' hδ
  filter_upwards [nhdsWithin_le_nhds (Metric.ball_mem_nhds r₀ hm)] with r hr
  rw [Metric.mem_ball, Real.dist_eq] at hr
  obtain ⟨hr1, hr2⟩ := abs_lt.1 hr
  refine le_trans (eLpNorm_le_of_ae_bound (μ := volume.restrict (sliceBox R)) (C := e) ?_) hLe
  filter_upwards [ae_restrict_mem hKm] with x hx
  have hxQ : (r, x) ∈ Icc (r₀ - δ) (r₀ + δ) ×ˢ sliceBox R :=
    ⟨⟨by linarith [min_le_right δ' δ], by linarith [min_le_right δ' δ]⟩, hx⟩
  have hx0Q : (r₀, x) ∈ Icc (r₀ - δ) (r₀ + δ) ×ˢ sliceBox R :=
    ⟨⟨by linarith, by linarith⟩, hx⟩
  have hd : dist ((r, x) : ℝ × (ℝ × ℝ)) (r₀, x) < δ' := by
    show max (dist r r₀) (dist x x) < δ'
    rw [dist_self, max_eq_left dist_nonneg, Real.dist_eq]
    exact lt_of_lt_of_le hr (min_le_left _ _)
  have key := hUCδ (r, x) hxQ (r₀, x) hx0Q hd
  rw [dist_eq_norm] at key
  exact key.le

end UnforcedLeray.Short.IIIa
