import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_2_6_3.Defs

/-!
# `YrLocIntCell`

A phase `L²` field is integrable on `[0,P] × B_R`. The phase-`L²` norm bounds
`∫_{[0,P]} ∫_{ℝ³} ‖Ψ‖²`, which by Tonelli (`Measure.setLIntegral_prod`) bounds the square integral
over the cell `[0,P] × B_R`; the cell has finite measure, so `L²` implies `L¹` there.
Source `the November 2 reference manuscript` lines 1334-1337 and 1351-1362.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem yrLocIntCell : YrLocIntCell := by
  intro P hP Ψ hΨ R
  have hfm : AEMeasurable (fun p : ℝ × Space => ‖Ψ p‖ₑ ^ (2 : ℝ)) (volume : Measure (ℝ × Space)) :=
    ((hΨ.meas.aemeasurable).enorm).pow_const (2 : ℝ)
  have hfAE : AEMeasurable (fun p : ℝ × Space => ‖Ψ p‖ₑ ^ (2 : ℝ))
      (((volume : Measure ℝ).prod (volume : Measure Space)).restrict
        (Ioc 0 P ×ˢ closedBall (0 : Space) R)) :=
    hfm.mono_measure Measure.restrict_le_self
  -- finiteness of the phase-`L²` integral over one period
  have hfin : ∫⁻ x in Ioc 0 P, ∫⁻ y : Space, ‖Ψ (x, y)‖ₑ ^ (2 : ℝ) < ⊤ := by
    have h := hΨ.finite
    unfold UnforcedLeray.Short.IIb.phaseLpNorm at h
    rw [ENNReal.rpow_lt_top_iff_of_pos (by norm_num)] at h
    rcases ENNReal.mul_lt_top_iff.1 h with ⟨_, h2⟩ | h2 | h2
    · exact h2
    · exact absurd h2 (ENNReal.ofReal_pos.2 (inv_pos.2 hP)).ne'
    · rw [h2]
      exact ENNReal.zero_lt_top
  -- Tonelli on the cell
  have hI : ∫⁻ z in Ioc 0 P ×ˢ closedBall (0 : Space) R, ‖Ψ z‖ₑ ^ (2 : ℝ) < ⊤ := by
    rw [Measure.volume_eq_prod, setLIntegral_prod _ hfAE]
    exact lt_of_le_of_lt
      (lintegral_mono fun x => lintegral_mono' Measure.restrict_le_self le_rfl) hfin
  have hmemLp : MemLp Ψ 2 (volume.restrict (Ioc 0 P ×ˢ closedBall (0 : Space) R)) := by
    refine ⟨hΨ.meas.mono_measure Measure.restrict_le_self, ?_⟩
    rw [eLpNorm_eq_lintegral_rpow_enorm (by norm_num) (by norm_num)]
    simp only [ENNReal.toReal_ofNat]
    exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hI.ne
  haveI : IsFiniteMeasure (volume.restrict (Ioc 0 P ×ˢ closedBall (0 : Space) R)) := by
    constructor
    rw [Measure.restrict_apply_univ, Measure.volume_eq_prod, Measure.prod_prod]
    exact ENNReal.mul_lt_top (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top)
      measure_closedBall_lt_top
  exact MemLp.integrable one_le_two hmemLp

end UnforcedLeray.Short.PartIIIb.Concrete
