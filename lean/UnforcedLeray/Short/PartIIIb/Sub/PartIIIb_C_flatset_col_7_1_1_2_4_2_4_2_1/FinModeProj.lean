import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_4_2_1.FlatLerayDefs
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_4_2_1.CoefSmoothBand
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_4_2_1.ModePotentials
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_4_2_1.TruncStreamEq
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.GradMember
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.StreamMember
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.NonzeroMode.FlatMembership
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.NonzeroMode.FinPotentials.Identity
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.NonzeroMode.FinPotentials.SmoothPer
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.NonzeroMode.FinPotentials.Band
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.NonzeroMode.FinPotentials.ExpDecay

/-!
# `FinModeProj` (organize task `PartIII-b:C/flatset/col/7/1/1/2/4/2/4/2/1/1/18`)

Source of record `the November 2 reference manuscript`
lines 1713-1716 (flat gradient and stream potentials per mode) and 1744-1745 (finite mode sums).

For a smooth test `f` and `F =ᵐ nzTrunc c N (fOsc c f)`, the truncation is the finite mode sum
`nzModeSum c (truncSet N) (fun n => nzCoeff c n (fOsc c f))`, which equals
`cgradC 0 Φ + streamC 0 Ψ` pointwise (`nzFpIdentity`) with `Φ = nzModeSum (phiN)` and
`Ψ = nzModeSum (psiN)`. The flat membership lemma `nzFlatMembership` puts `cgradC 0 Φ` in
`(solenoidalHC 0 c)ᗮ` and `streamC 0 Ψ` in `solenoidalHC 0 c`, so `PepsC 0 c F` is the stream part,
which is `lerayTrunc c f N` by `truncStreamEq`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.FlatLeray

open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.Short.PartIIa

theorem finModeProj : FinModeProj := by
  intro c hc f hf N F hF
  -- per-mode potentials
  have hall : ∀ n ∈ truncSet N, NzDecay2 (phiN c f n) ∧ NzDecay2 (psiN c f n) ∧
      NzModeEq (nzk c n) (coefR c f n) (coefZ c f n) (phiN c f n) (psiN c f n) :=
    fun n hn => modePotentials c hc f hf n (Finset.ne_of_mem_erase hn)
  have hsm : ∀ n ∈ truncSet N, ContDiff ℝ ∞ (phiN c f n) ∧ ContDiff ℝ ∞ (psiN c f n) :=
    fun n hn => ⟨(hall n hn).1.1, (hall n hn).2.1.1⟩
  -- the identity of the truncation with the sum of the two mode sums
  have hid : ∀ p : Profile,
      nzModeSum c (truncSet N) (fun n => nzCoeff c n (fOsc c f)) p =
        cgradC 0 (nzModeSum c (truncSet N) (phiN c f)) p +
          streamC 0 (nzModeSum c (truncSet N) (psiN c f)) p :=
    nzFpIdentity c hc (truncSet N) (fun n => nzCoeff c n (fOsc c f)) (phiN c f) (psiN c f)
      hsm (fun n hn => (hall n hn).2.2)
  -- smoothness, periodicity, band and decay of the two mode sums
  have hΦs := nzFpSmoothPer c hc (truncSet N) (phiN c f) (fun n hn => (hsm n hn).1)
  have hΨs := nzFpSmoothPer c hc (truncSet N) (psiN c f) (fun n hn => (hsm n hn).2)
  obtain ⟨s0Φ, s1Φ, hs0Φ, hbΦ⟩ := nzFpBand c (truncSet N) (phiN c f) (phiN c f)
    (fun n hn => (hall n hn).1.2.1) (fun n hn => (hall n hn).1.2.1)
  obtain ⟨s0Ψ, s1Ψ, hs0Ψ, hbΨ⟩ := nzFpBand c (truncSet N) (psiN c f) (psiN c f)
    (fun n hn => (hall n hn).2.1.2.1) (fun n hn => (hall n hn).2.1.2.1)
  have hEΦ := nzFpExpDecay c hc (truncSet N) (phiN c f) (fun n hn => (hall n hn).1)
  have hEΨ := nzFpExpDecay c hc (truncSet N) (psiN c f) (fun n hn => (hall n hn).2.1)
  -- flat membership of the two mode sums
  have hFM : NzFlatMembership := nzFlatMembership
  obtain ⟨⟨hG, hGm⟩, _⟩ := hFM nearGradMember_proof nearStreamMember_proof c hc
    (nzModeSum c (truncSet N) (phiN c f)) hΦs.1 hΦs.2
    ⟨s0Φ, s1Φ, hs0Φ, fun p hp => hbΦ p (Or.inl hp)⟩ hEΦ
  obtain ⟨_, ⟨hS, hSm⟩⟩ := hFM nearGradMember_proof nearStreamMember_proof c hc
    (nzModeSum c (truncSet N) (psiN c f)) hΨs.1 hΨs.2
    ⟨s0Ψ, s1Ψ, hs0Ψ, fun p hp => hbΨ p (Or.inl hp)⟩ hEΨ
  -- F is the sum of its gradient and stream parts
  have hFsum : F = hG.toLp _ + hS.toLp _ := by
    apply Lp.ext
    filter_upwards [hF, Lp.coeFn_add (hG.toLp _) (hS.toLp _), hG.coeFn_toLp, hS.coeFn_toLp]
      with p h1 h2 h3 h4
    rw [h1, h2, Pi.add_apply, h3, h4]
    exact hid p
  -- the projection kills the gradient part and fixes the stream part
  have hP : PepsC 0 c F = hS.toLp _ := by
    rw [hFsum, map_add]
    have h0 : PepsC 0 c (hG.toLp _) = 0 := by
      unfold PepsC
      exact (Submodule.starProjection_apply_eq_zero_iff _).2 hGm
    have h1 : PepsC 0 c (hS.toLp _) = hS.toLp _ := by
      unfold PepsC
      exact Submodule.starProjection_eq_self_iff.2 hSm
    rw [h0, h1, zero_add]
  rw [hP]
  filter_upwards [hS.coeFn_toLp] with p hp
  rw [hp]
  exact truncStreamEq c hc f hf N p

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.FlatLeray
