import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T10_org_3_2_2_of
import UnforcedLeray.Short.PartIIa.Tasks.F01BodyResolvent
import UnforcedLeray.Short.PartIIa.Tasks.F02BodyResolventEquation
import UnforcedLeray.Short.PartIIa.Tasks.F05HomogeneousUniqueness
import UnforcedLeray.Short.PartIIa.Sub.PartIIa_F14_1_3

/-!
# `PartII-b:T10/org/3/2/2`: Leray commutes with `1 + L` on tests (the resolvent leaf)

Source `the November 2 reference manuscript`
lines 1370-1376 (the inverse `ℛ_μ f(τ) = ∫₀^∞ e^{-μt} S(t) f(τ - t) dt` of `μ + L`), 1445-1455
(uniqueness of distributional `Y_r` solutions), 1474-1475 ("Leray commutes with heat, dilation and
phase translation, so projection preserves all identities").

`LerayResolventTestComm` (`Sub/PartII-b_T10_org_3_2_2_of.lean`) at `r = 2`, `μ = 1`: the Laplace
integral `ℛ₁` solves `(1 + L)w = f` (`PartIIa.bodyResolvent_solves`); a phase test `g` solves
`(1 + L)g = (1 + L₀)g` (`schwartzOpGraph`), so `ℛ₁(1 + L₀)g = g` by uniqueness
(`PartIIa.bodyOp_uniqueness`); `𝐏ℛ₁ = ℛ₁𝐏` (`PartIIa.lerayYResolventComm`), hence
`𝐏g = ℛ₁ 𝐏(1 + L₀)g`, which solves `(1 + L)w = 𝐏(1 + L₀)g`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIb.LTC

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.RieszLp

theorem lerayResolventTestComm : LerayResolventTestComm := by
  intro P _ ν hν Φ g hΦ hg
  have h3 : (2 : ℝ≥0∞) < 3 := by norm_num
  have hmu : 0 < (1 : ℂ).re + PartIIa.gammaR 2 := by norm_num [PartIIa.gammaR]
  obtain ⟨Rm, -, hRm⟩ := PartIIa.bodyResolvent_exists 2 ENNReal.one_lt_two h3 P ν hν 1 hmu
  -- `ℛ₁` inverts `1 + L` on the test `g`
  have hinv : Rm (testElem P 2 ((1 : ℂ) • g + L0 ν g)) = testElem P 2 g := by
    refine sub_eq_zero.1 (PartIIa.bodyOp_uniqueness 2 ENNReal.one_lt_two h3 P ν hν 1 hmu _ ?_)
    intro Ψ hΨ
    have e1 : phasePair P 2 ((1 : ℂ) • Ψ + L0T ν Ψ) (Rm (testElem P 2 ((1 : ℂ) • g + L0 ν g))) =
        phasePair P 2 Ψ (testElem P 2 ((1 : ℂ) • g + L0 ν g)) :=
      PartIIa.bodyResolvent_solves 2 ENNReal.one_lt_two h3 P ν hν 1 hmu Rm hRm _ Ψ hΨ
    have e2 : phasePair P 2 ((1 : ℂ) • Ψ + L0T ν Ψ) (testElem P 2 g) =
        phasePair P 2 Ψ (testElem P 2 ((1 : ℂ) • g + L0 ν g)) :=
      schwartzOpGraph P 2 ν 1 g (hg.isPhaseSchwartz 2) Ψ hΨ
    show phasePair P 2 ((1 : ℂ) • Ψ + L0T ν Ψ)
        (Rm (testElem P 2 ((1 : ℂ) • g + L0 ν g)) - testElem P 2 g) = phasePair P 2 Ψ 0
    rw [map_sub, e1, e2, sub_self, map_zero]
  -- `𝐏` commutes with `ℛ₁`, and `ℛ₁ 𝐏(1 + L₀)g` solves the equation with datum `𝐏(1 + L₀)g`
  have hc := PartIIa.lerayYResolventComm 2 ENNReal.one_lt_two h3 P ν hν 1 hmu Rm hRm
    (testElem P 2 ((1 : ℂ) • g + L0 ν g))
  have hR2 := PartIIa.bodyResolvent_solves 2 ENNReal.one_lt_two h3 P ν hν 1 hmu Rm hRm
    (lerayY P 2 ENNReal.one_lt_two (ne_top_of_lt h3) (testElem P 2 ((1 : ℂ) • g + L0 ν g)))
  rw [← hc, hinv] at hR2
  exact hR2 Φ hΦ

end UnforcedLeray.Short.IIb.LTC
