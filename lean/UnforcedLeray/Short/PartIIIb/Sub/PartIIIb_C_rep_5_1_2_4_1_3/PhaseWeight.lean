import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_1_2_4_1_3.Kernel

/-!
# `PartIII-b:C/rep/5/1/2/4/1/3/3/15`: the phase factor of one atom

Source `the November 2 reference manuscript` (phase factor of one atom).
Proves `PhaseWeight`: `∫_{(0,P]} 1_{σ<τ} e^{σ-τ}/4 dτ ≤ omega2 P σ`.
Case `P ≤ σ`: the integrand vanishes on `(0,P]`.  Case `σ < P`: on `(0,P]` the integrand is
at most `min 1 (e^σ)/4`, since `σ - τ < 0` and `σ - τ < σ` (as `τ > 0`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete.WYCore

theorem phaseWeight : PhaseWeight := by
  intro P σ hP
  unfold omega2
  by_cases hσ : σ < P
  · rw [if_pos hσ]
    have hpt : ∀ τ ∈ Ioc (0 : ℝ) P,
        (if σ < τ then ENNReal.ofReal (Real.exp (σ - τ) / 4) else 0) ≤
          ENNReal.ofReal (min 1 (Real.exp σ) / 4) := by
      intro τ hτ
      split_ifs with h
      · apply ENNReal.ofReal_le_ofReal
        have h1 : Real.exp (σ - τ) ≤ min 1 (Real.exp σ) := by
          apply le_min
          · rw [Real.exp_le_one_iff]
            linarith [hτ.1]
          · rw [Real.exp_le_exp]
            linarith [hτ.1]
        linarith [h1]
      · exact bot_le
    have hnn : 0 ≤ min 1 (Real.exp σ) / 4 :=
      div_nonneg (le_min zero_le_one (Real.exp_pos σ).le) (by norm_num)
    calc ∫⁻ τ in Ioc 0 P, (if σ < τ then ENNReal.ofReal (Real.exp (σ - τ) / 4) else 0)
        ≤ ∫⁻ _τ in Ioc 0 P, ENNReal.ofReal (min 1 (Real.exp σ) / 4) :=
          setLIntegral_mono' measurableSet_Ioc hpt
      _ = ENNReal.ofReal (min 1 (Real.exp σ) / 4) * ENNReal.ofReal (P - 0) := by
          rw [setLIntegral_const, Real.volume_Ioc]
      _ = ENNReal.ofReal (P / 4 * min 1 (Real.exp σ)) := by
          rw [← ENNReal.ofReal_mul hnn]
          congr 1
          ring
  · rw [if_neg hσ, ENNReal.ofReal_zero]
    have h0 : ∀ τ ∈ Ioc (0 : ℝ) P,
        (if σ < τ then ENNReal.ofReal (Real.exp (σ - τ) / 4) else 0) ≤ 0 := by
      intro τ hτ
      split_ifs with h
      · exfalso
        linarith [hτ.2, not_lt.mp hσ, h]
      · exact le_refl _
    calc ∫⁻ τ in Ioc 0 P, (if σ < τ then ENNReal.ofReal (Real.exp (σ - τ) / 4) else 0)
        ≤ ∫⁻ _τ in Ioc 0 P, (0 : ℝ≥0∞) := setLIntegral_mono' measurableSet_Ioc h0
      _ = 0 := by simp

end UnforcedLeray.Short.PartIIIb.Concrete.WYCore

end
