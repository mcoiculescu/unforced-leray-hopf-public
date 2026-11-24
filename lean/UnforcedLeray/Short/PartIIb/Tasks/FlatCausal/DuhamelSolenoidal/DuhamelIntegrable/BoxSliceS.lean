import UnforcedLeray.Short.PartIIb.Sub.T12_6_2

set_option autoImplicit false

noncomputable section

open Set MeasureTheory

namespace UnforcedLeray.Short.IIb

theorem boxSliceS : UnforcedLeray.Short.IIb.BoxSliceS := by
  unfold UnforcedLeray.Short.IIb.BoxSliceS
  intro a σ H hσ
  have hc1 : ContinuousOn (fun s : ℝ => s ^ a) (Icc σ H) := by
    intro s hs
    exact (Real.continuousAt_rpow_const s a
      (Or.inl (lt_of_lt_of_le hσ hs.1).ne')).continuousWithinAt
  have hcont : ContinuousOn (fun s : ℝ => (s ^ a)⁻¹) (Icc σ H) :=
    hc1.inv₀ (fun s hs => (Real.rpow_pos_of_pos (lt_of_lt_of_le hσ hs.1) a).ne')
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  refine ⟨max M 0 * max (H - σ) 0, fun t ht _htH => ?_⟩
  have hM'0 : 0 ≤ max M 0 := le_max_right _ _
  have hta : 0 ≤ t ^ a := Real.rpow_nonneg ht.le a
  have hpt : ∀ s ∈ Icc σ H ∩ Ioi t,
      ENNReal.ofReal ((t / s) ^ a) ≤ ENNReal.ofReal (max M 0 * t ^ a) := by
    intro s hs
    apply ENNReal.ofReal_le_ofReal
    have hsp : 0 < s := lt_of_lt_of_le hσ hs.1.1
    rw [Real.div_rpow ht.le hsp.le, div_eq_mul_inv]
    have hb := hM s hs.1
    simp only [Real.norm_eq_abs] at hb
    have hinv : (s ^ a)⁻¹ ≤ max M 0 := (le_abs_self _).trans (hb.trans (le_max_left _ _))
    calc t ^ a * (s ^ a)⁻¹ ≤ t ^ a * max M 0 := mul_le_mul_of_nonneg_left hinv hta
      _ = max M 0 * t ^ a := mul_comm _ _
  have hmeas : MeasurableSet (Icc σ H ∩ Ioi t) := measurableSet_Icc.inter measurableSet_Ioi
  calc ∫⁻ s in Icc σ H ∩ Ioi t, ENNReal.ofReal ((t / s) ^ a)
      ≤ ∫⁻ s in Icc σ H ∩ Ioi t, ENNReal.ofReal (max M 0 * t ^ a) :=
        setLIntegral_mono' hmeas hpt
    _ = ENNReal.ofReal (max M 0 * t ^ a) * volume (Icc σ H ∩ Ioi t) := by
        rw [setLIntegral_const]
    _ ≤ ENNReal.ofReal (max M 0 * t ^ a) * volume (Icc σ H) :=
        mul_le_mul_of_nonneg_left (measure_mono inter_subset_left) zero_le
    _ = ENNReal.ofReal (max M 0 * t ^ a) * ENNReal.ofReal (H - σ) := by
        rw [Real.volume_Icc]
    _ ≤ ENNReal.ofReal (max M 0 * t ^ a) * ENNReal.ofReal (max (H - σ) 0) :=
        mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal (le_max_left _ _)) zero_le
    _ = ENNReal.ofReal (max M 0 * max (H - σ) 0 * t ^ a) := by
        rw [← ENNReal.ofReal_mul (mul_nonneg hM'0 hta)]
        congr 1
        ring

end UnforcedLeray.Short.IIb
