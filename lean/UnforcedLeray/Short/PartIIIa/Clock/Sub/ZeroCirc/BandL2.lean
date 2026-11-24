import UnforcedLeray.Short.PartIIIa.Clock.Sub.ZeroCircLeaves

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

theorem zcBandL2 : ZCBandL2 := by
  intro c hc g M L hM hL _hcont hbound hzero
  set S : Set (ℝ × ℝ) := Ico (-(c / 2)) (c / 2) ×ˢ Icc (-L) L with hSdef
  have hSmeas : MeasurableSet S := measurableSet_Ico.prod measurableSet_Icc
  have hSsub : S ⊆ B0579.cell c := by
    intro x hx
    exact ⟨hx.1, mem_univ _⟩
  have hae : g =ᵐ[volume.restrict (B0579.cell c)] S.indicator g := by
    refine (ae_restrict_iff' (B0579.measurableSet_cell c)).2 (Eventually.of_forall fun x hx => ?_)
    by_cases hxS : x ∈ S
    · rw [Set.indicator_of_mem hxS]
    · rw [Set.indicator_of_notMem hxS]
      apply hzero x
      by_contra hlt
      exact hxS ⟨hx.1, abs_le.1 (not_lt.1 hlt)⟩
  have hvol : volume S = ENNReal.ofReal (c * (2 * L)) := by
    rw [hSdef, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ico, Real.volume_Icc,
      ← ENNReal.ofReal_mul (show (0 : ℝ) ≤ c / 2 - -(c / 2) by linarith)]
    congr 1
    ring
  have hbd : ∀ᵐ x ∂(volume.restrict S), ‖g x‖ ≤ M := by
    refine (ae_restrict_iff' hSmeas).2 (Eventually.of_forall fun x _ => ?_)
    rw [Real.norm_eq_abs]
    exact hbound x
  calc eLpNorm g 2 (volume.restrict (B0579.cell c))
      = eLpNorm (S.indicator g) 2 (volume.restrict (B0579.cell c)) := eLpNorm_congr_ae hae
    _ = eLpNorm g 2 ((volume.restrict (B0579.cell c)).restrict S) :=
        eLpNorm_indicator_eq_eLpNorm_restrict hSmeas
    _ = eLpNorm g 2 (volume.restrict S) := by
        rw [Measure.restrict_restrict hSmeas, Set.inter_eq_left.2 hSsub]
    _ ≤ (volume.restrict S) univ ^ (2 : ℝ≥0∞).toReal⁻¹ * ENNReal.ofReal M :=
        eLpNorm_le_of_ae_bound hbd
    _ = ENNReal.ofReal (M * Real.sqrt (c * (2 * L))) := by
        rw [Measure.restrict_apply_univ, hvol, ENNReal.toReal_ofNat,
          ENNReal.ofReal_rpow_of_nonneg (mul_nonneg hc.le (mul_nonneg zero_le_two hL))
            (by norm_num),
          ← ENNReal.ofReal_mul (Real.rpow_nonneg (mul_nonneg hc.le (mul_nonneg zero_le_two hL)) _),
          Real.sqrt_eq_rpow, one_div, mul_comm]

end UnforcedLeray.Short.IIIa
