import UnforcedLeray.Short.PartI.Sub.PartI_C06
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.PartI

theorem tailIntegralProps : TailIntegralProps := by
  intro φ b K r hb hr hrb
  have hK : 0 ≤ K := by
    have h1 := hrb b le_rfl
    have h2 : 0 ≤ K / b := (norm_nonneg _).trans h1
    rcases div_nonneg_iff.mp h2 with h | h
    · exact h.1
    · exact (not_le.mpr hb h.2).elim
  have hbound : ∀ s, b ≤ s → ‖φ (r s) / s‖ ≤ ‖φ‖ * K * s ^ (-2:ℝ) := by
    intro s hs
    have hs0 : 0 < s := lt_of_lt_of_le hb hs
    have h1 : ‖φ (r s)‖ ≤ ‖φ‖ * (K / s) :=
      (φ.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hrb s hs) (norm_nonneg _))
    have hpow : s ^ (-2:ℝ) = (s ^ 2)⁻¹ := by
      rw [show (-2:ℝ) = -((2:ℕ):ℝ) by norm_num, Real.rpow_neg hs0.le, Real.rpow_natCast]
    rw [hpow, norm_div, Complex.norm_real, Real.norm_of_nonneg hs0.le]
    calc ‖φ (r s)‖ / s ≤ ‖φ‖ * (K / s) / s := div_le_div_of_nonneg_right h1 hs0.le
      _ = ‖φ‖ * K * (s ^ 2)⁻¹ := by ring
  have hfc : ContinuousOn (fun s => φ (r s) / s) (Ici b) := by
    refine ContinuousOn.div (φ.continuous.comp_continuousOn hr) Complex.continuous_ofReal.continuousOn ?_
    intro s hs
    exact Complex.ofReal_ne_zero.mpr (lt_of_lt_of_le hb hs).ne'
  have hae : ∀ θ, b ≤ θ → ∀ᵐ s ∂(volume.restrict (Ioi θ)),
      ‖φ (r s) / s‖ ≤ ‖φ‖ * K * s ^ (-2:ℝ) := by
    intro θ hθ
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun s hs => ?_)
    exact hbound s (le_trans hθ (le_of_lt hs))
  have hint : ∀ θ, b ≤ θ → IntegrableOn (fun s => φ (r s) / s) (Ioi θ) := by
    intro θ hθ
    have hθ0 : 0 < θ := lt_of_lt_of_le hb hθ
    have hmeas : AEStronglyMeasurable (fun s => φ (r s) / s) (volume.restrict (Ioi θ)) :=
      (hfc.mono (fun s hs => le_trans hθ (le_of_lt hs))).aestronglyMeasurable measurableSet_Ioi
    have hg : IntegrableOn (fun s : ℝ => ‖φ‖ * K * s ^ (-2:ℝ)) (Ioi θ) :=
      (integrableOn_Ioi_rpow_of_lt (a := -2) (by norm_num) hθ0).const_mul _
    exact Integrable.mono' hg hmeas (hae θ hθ)
  have hI : ∀ θ, b ≤ θ → ∫ s in Ioi θ, s ^ (-2:ℝ) = θ⁻¹ := by
    intro θ hθ
    have hθ0 : 0 < θ := lt_of_lt_of_le hb hθ
    rw [integral_Ioi_rpow_of_lt (a := -2) (by norm_num) hθ0,
      show (-2:ℝ) + 1 = -1 by norm_num, Real.rpow_neg_one]
    ring
  have hmain : ∀ θ, b ≤ θ → ‖∫ s in Ioi θ, φ (r s) / s‖ ≤ ‖φ‖ * K / θ := by
    intro θ hθ
    have hg : IntegrableOn (fun s : ℝ => ‖φ‖ * K * s ^ (-2:ℝ)) (Ioi θ) :=
      (integrableOn_Ioi_rpow_of_lt (a := -2) (by norm_num) (lt_of_lt_of_le hb hθ)).const_mul _
    have h := norm_integral_le_of_norm_le hg (hae θ hθ)
    rw [integral_const_mul, hI θ hθ] at h
    rw [div_eq_mul_inv]
    exact h
  have hsplit : ∀ θ, b ≤ θ → ∫ s in Ioi b, φ (r s) / s =
      (∫ s in b..θ, φ (r s) / s) + ∫ s in Ioi θ, φ (r s) / s := by
    intro θ hθ
    have hcont : ContinuousOn (fun s => φ (r s) / s) (Icc b θ) := hfc.mono (fun s hs => hs.1)
    have hI1 : IntegrableOn (fun s => φ (r s) / s) (Ioc b θ) :=
      hcont.integrableOn_Icc.mono_set Ioc_subset_Icc_self
    rw [intervalIntegral.integral_of_le hθ, ← Ioc_union_Ioi_eq_Ioi hθ]
    rw [setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi hI1 (hint θ hθ)]
  have hP : ContinuousOn (fun θ => ∫ s in b..θ, φ (r s) / s) (Ici b) := by
    intro θ0 hθ0
    have hθ0' : b ≤ θ0 := hθ0
    have hbN : b ≤ θ0 + 1 := by linarith
    have hcont : ContinuousOn (fun s => φ (r s) / s) (Icc b (θ0 + 1)) :=
      hfc.mono (fun s hs => hs.1)
    have hPN := intervalIntegral.continuousOn_primitive_interval (μ := volume) (a := b)
      (b := θ0 + 1) (f := fun s => φ (r s) / s)
      (by rw [uIcc_of_le hbN]; exact hcont.integrableOn_Icc)
    rw [uIcc_of_le hbN] at hPN
    have hnhds : Icc b (θ0 + 1) ∈ 𝓝[Ici b] θ0 := by
      rw [mem_nhdsWithin]
      exact ⟨Iio (θ0 + 1), isOpen_Iio, show θ0 < θ0 + 1 by linarith,
        fun x hx => ⟨hx.2, le_of_lt hx.1⟩⟩
    exact (hPN.continuousWithinAt ⟨hθ0', by linarith⟩).mono_of_mem_nhdsWithin hnhds
  have hcontF : ContinuousOn (fun θ => ∫ s in Ioi θ, φ (r s) / s) (Ici b) := by
    have hEq : EqOn (fun θ => ∫ s in Ioi θ, φ (r s) / s)
        (fun θ => (∫ s in Ioi b, φ (r s) / s) - ∫ s in b..θ, φ (r s) / s) (Ici b) := by
      intro θ hθ
      dsimp only
      rw [hsplit θ hθ]
      ring
    exact (continuousOn_const.sub hP).congr hEq
  exact ⟨hcontF, fun θ hθ => ⟨hint θ hθ, hmain θ hθ⟩⟩

end UnforcedLeray.Short.PartI
