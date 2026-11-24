import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_1_3.Bound.Fin4

/-!
# `RingFrameD2Bound` (`PartIII-b:C/rep/8/2/1/3/b`)

Source `the November 2 reference manuscript`
lines 5460-5465, 1206-1216, 5036-5045.  In the dilation variable `z = (σ,(q,η))`, `σ = log s`, the
profile operators of the ring chart become `D_ρ = e^{σ/2}(∂_q - ε(2∂_σ + η∂_η))` and
`D_z = e^{σ/2}∂_η` (`Lift.lean`); on `B = e^{σ/2} b̂` the six second-order entries are
`e^{3σ/2}·{P₂P₁, ∂_ηP₁, P₂∂_η, ∂_η∂_η} b̂` and `ε e^{3σ/2}·{P₂ b̂, P₁ b̂, ∂_η b̂}` (`Chain.lean`), with
`P_m = ∂_q - ε(2∂_σ + η∂_η + m)` and `b̂ = ṽ + ε (H e_z)`.  Each differs from its flat part
by `ε` times jets of `ṽ` (order 2) and `ψ̃` (order 3) with `(1+|η|)^3` weights
(`Est2.lean`, `Fin3.lean`, `Fin4.lean`), and these are controlled by `trainWeight 3`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

open RingFrameD2BoundAux

theorem ringFrameD2Bound : RingFrameD2Bound := by
  refine ⟨343, fun L hε p hp j l => ?_⟩
  have hphi := phi_log hp
  have key : ‖ringFrameD2 L.ε (bSqrt (bRaw L)) (phi (Real.log p.1, p.2)) j l -
      (phi (Real.log p.1, p.2)).1 ^ (3 / 2 : ℝ) •
        vecSp (flatD2 L (phi (Real.log p.1, p.2)).1 (phi (Real.log p.1, p.2)).2 j l)‖ ≤
      343 * L.ε * wt (3 / 2) (Real.log p.1, p.2) * (1 + |p.2.2|) ^ 3 *
        Mz L (Real.log p.1, p.2) := by
    fin_cases j <;> fin_cases l
    · exact diff00 L hε _
    · exact diff01 L hε _
    · exact diff02 L hε _
    · exact diff10 L hε _
    · exact diff11 L hε _
    · exact diff12 L hε _
    · exact diff20 L hε _
    · exact diff21 L hε _
    · exact diff22 L hε _
  rw [hphi] at key
  have hwt : wt (3 / 2) (Real.log p.1, p.2) = p.1 ^ (3 / 2 : ℝ) := by
    rw [wt_three_half]
    simp [Real.exp_log hp]
  rw [hwt] at key
  have hW := weight_ge L (p := p)
  have h0 : 0 ≤ 343 * L.ε * p.1 ^ (3 / 2 : ℝ) :=
    mul_nonneg (mul_nonneg (by norm_num) L.ε_pos.le) (Real.rpow_nonneg hp.le _)
  have := mul_le_mul_of_nonneg_left hW h0
  unfold Mz at key
  refine key.trans ?_
  nlinarith

end UnforcedLeray.Short.PartIIIb.Concrete
