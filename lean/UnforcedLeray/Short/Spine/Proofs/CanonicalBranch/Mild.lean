import UnforcedLeray.Short.Spine.Sub.SP_CAN
import UnforcedLeray.Short.Spine.Proofs.CanonicalBranch.Mild.ExpJoint
import UnforcedLeray.Short.Spine.Proofs.CanonicalBranch.Mild.Duhamel
import UnforcedLeray.Short.Spine.Proofs.CanonicalBranch.Mild.Gronwall

/-!
# Spine `SP-CAN`, Bridge 3: strong canonical solutions are mild

Target: `UnforcedLeray.Short.Spine.StrongCanonicalIsMild` (declared in `Short/Spine/Sub/SP_CAN.lean`,
Bridge 3; source `the November 2 reference manuscript` lines 1094-1150, old
manuscript lines 1809-1840).

Statement: for every `V : ℝ → X_G` with `PartI.IsCanonicalSolution V`, and `0 < θ ≤ θ'`,
`V θ = S θ θ' (V θ')`, where `S = Cons.G3b.S` is the backward Dyson evolution.

Proof. Let `Z(s) = V(s) - S(s,θ')V(θ')` on `[θ, θ']`.
1. The vector Duhamel identity for `V` (`canonical_duhamel`, coefficientwise in the eigenbasis of `D`)
   and the Duhamel identity for `S` (`S_mild_interval`) hold at every base point `s`, with the same
   free part `e^{log(θ'/s)D} V(θ')`. Subtracting, `Z(s) = ∫_s^{θ'} e^{log(v/s)D} L₀ Z(v) dv`.
2. Since `‖e^{aD}‖ ≤ 1`, `‖Z(s)‖ ≤ ‖L₀‖ ∫_s^{θ'} ‖Z(v)‖ dv`, and `‖Z‖` is continuous on `[θ, θ']`.
3. The backward Grönwall inequality (`backward_gronwall`) gives `Z = 0` on `[θ, θ']`.
Helpers: `Mild/ExpJoint.lean`, `Mild/Duhamel.lean`, `Mild/Gronwall.lean`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped InnerProductSpace ContDiff

namespace UnforcedLeray.Short.Spine

open UnforcedLeray.B0010 UnforcedLeray.B0123 UnforcedLeray.Cons.G3b
open UnforcedLeray.Short.Spine.CanonicalMild

/-- **Bridge 3** (`Spine:SP-CAN`): every `X_G`-valued canonical solution is the mild solution
through the backward evolution `S`. -/
theorem strongCanonicalIsMild : UnforcedLeray.Short.Spine.StrongCanonicalIsMild := by
  intro V hV θ θ' hθ hθθ'
  have hVc : ContinuousOn V (Icc θ θ') :=
    hV.smooth.continuousOn.mono (fun v hv => lt_of_lt_of_le hθ hv.1)
  have hSc : ContinuousOn (fun v => S v θ' (V θ')) (Icc θ θ') :=
    continuousOn_S_left hθ (V θ')
  have hZc : ContinuousOn (fun v => ‖V v - S v θ' (V θ')‖) (Icc θ θ') :=
    (hVc.sub hSc).norm
  have hineq : ∀ s ∈ Icc θ θ',
      ‖V s - S s θ' (V θ')‖ ≤ ‖B0012.L0‖ * ∫ v in s..θ', ‖V v - S v θ' (V θ')‖ := by
    intro s hs
    have hs0 : 0 < s := lt_of_lt_of_le hθ hs.1
    have hsub : Icc s θ' ⊆ Icc θ θ' := Icc_subset_Icc hs.1 le_rfl
    have hF1 : ContinuousOn (fun v => B0012.L0 (V v)) (Icc s θ') :=
      B0012.L0.continuous.comp_continuousOn (hVc.mono hsub)
    have hF2 : ContinuousOn (fun v => B0012.L0 (S v θ' (V θ'))) (Icc s θ') :=
      B0012.L0.continuous.comp_continuousOn (hSc.mono hsub)
    have hI1 : IntervalIntegrable (fun v => expD (Real.log v - Real.log s) (B0012.L0 (V v)))
        volume s θ' := intervalIntegrable_expD_log hs0 hs.2 hF1
    have hI2 : IntervalIntegrable
        (fun v => expD (Real.log v - Real.log s) (B0012.L0 (S v θ' (V θ')))) volume s θ' :=
      intervalIntegrable_expD_log hs0 hs.2 hF2
    have hcongr : ∫ v in s..θ', expD (Real.log v - Real.log s)
          (B0012.L0 (V v - S v θ' (V θ'))) =
        (∫ v in s..θ', expD (Real.log v - Real.log s) (B0012.L0 (V v))) -
          ∫ v in s..θ', expD (Real.log v - Real.log s) (B0012.L0 (S v θ' (V θ'))) := by
      rw [← intervalIntegral.integral_sub hI1 hI2]
      apply intervalIntegral.integral_congr
      intro v _
      simp only [map_sub]
    have hdiff : V s - S s θ' (V θ') = ∫ v in s..θ', expD (Real.log v - Real.log s)
        (B0012.L0 (V v - S v θ' (V θ'))) := by
      rw [hcongr, canonical_duhamel hV hs0 hs.2, S_mild_interval hs0 hs.2 (V θ')]
      abel
    have hbd : ‖∫ v in s..θ', expD (Real.log v - Real.log s)
          (B0012.L0 (V v - S v θ' (V θ')))‖ ≤
        ∫ v in s..θ', ‖B0012.L0‖ * ‖V v - S v θ' (V θ')‖ := by
      apply intervalIntegral.norm_integral_le_of_norm_le hs.2
      · apply Filter.Eventually.of_forall
        intro v hv
        have hvI : v ∈ Icc θ θ' := ⟨le_trans hs.1 hv.1.le, hv.2⟩
        calc ‖expD (Real.log v - Real.log s) (B0012.L0 (V v - S v θ' (V θ')))‖
            ≤ ‖expD (Real.log v - Real.log s)‖ * ‖B0012.L0 (V v - S v θ' (V θ'))‖ :=
              (expD (Real.log v - Real.log s)).le_opNorm _
          _ ≤ 1 * (‖B0012.L0‖ * ‖V v - S v θ' (V θ')‖) :=
              mul_le_mul (norm_expD_le _) (B0012.L0.le_opNorm _) (norm_nonneg _) zero_le_one
          _ = ‖B0012.L0‖ * ‖V v - S v θ' (V θ')‖ := one_mul _
      · apply ContinuousOn.intervalIntegrable
        rw [uIcc_of_le hs.2]
        exact continuousOn_const.mul (hZc.mono hsub)
    rw [hdiff]
    refine hbd.trans (le_of_eq ?_)
    exact intervalIntegral.integral_const_mul _ _
  have hG := backward_gronwall (norm_nonneg _) hZc (fun s _ => norm_nonneg _) hineq
  have h0 : ‖V θ - S θ θ' (V θ')‖ = 0 := hG θ ⟨le_rfl, hθθ'⟩
  exact sub_eq_zero.1 (norm_eq_zero.1 h0)

end UnforcedLeray.Short.Spine
