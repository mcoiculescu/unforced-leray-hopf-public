import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T10_org_3
import UnforcedLeray.Lib.PhaseSpace.ExtendedTest

/-!
# `PartII-b:T10/org/3/2`: decomposition of `AdjointLerayCommute`

Source `the November 2 reference manuscript`
lines 1359-1361, 1474-1475 ("Leray commutes with heat, dilation and phase translation, so
projection preserves all identities"), 1498-1500.

Proof of `AdjointLerayCommute` (here, `adjointLerayCommute_of`): given `HasPhaseOp (μ̄ + L₀) W F`
in `Y_2` and a phase test `Φ`, let `Ψ` be the smooth `L²`-representative of the slice-wise Leray
projection `𝐏Φ` (`LerayTestSchwartz`), and `Ψ'` the one of `𝐏((μ̄ + L₀)Φ)`.  Then `Ψ' = (μ̄ + L₀)Ψ`
(`LerayTestComm`: Leray commutes with `∂_τ`, `Δ`, `y·∇` on tests), the tested equation extends to
the Schwartz-type test `Ψ` (`hasPhaseOp_extend_op`, proved below from the existing cutoff
convergence), and the self-adjointness of `𝐏` moves `𝐏` back onto `W, F`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

open Set MeasureTheory Filter Topology
open scoped ENNReal
open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.RieszLp

/-- Pointwise: `μ̄ Φ + L₀ Φ = (μ̄ + 1) Φ - T₀ᵗΦ - νΔΦ`, i.e. `T₀ = 3/2 - T₀ᵗ`. -/
theorem op_eq_driftT (ν μ : ℝ) (Φ : ℝ × Space → CVec3) :
    (starRingEnd ℂ) (μ : ℂ) • Φ + L0 ν Φ =
      ((starRingEnd ℂ) (μ : ℂ) + 1) • Φ - driftT Φ - nuLapT ν Φ := by
  funext p
  simp only [L0, T0, driftT, nuLapT, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    add_smul]
  module

/-- The operator `μ̄ + L₀` preserves phase tests. -/
theorem isPhaseTest_op {P : ℝ} (ν μ : ℝ) {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ) :
    IsPhaseTest P ((starRingEnd ℂ) (μ : ℂ) • Φ + L0 ν Φ) := by
  rw [op_eq_driftT]
  exact ((hΦ.const_smul _).sub hΦ.driftT).sub (hΦ.lapT.const_smul ν)

/-- On a Schwartz-type test, `testElem` of `μ̄Φ + L₀Φ` splits along `op_eq_driftT`. -/
theorem testElem_op {P : ℝ} [Fact (0 < P)] {r : ℝ≥0∞} [Fact (1 ≤ r)] (ν μ : ℝ)
    {Ψ : ℝ × Space → CVec3} (hΨ : IsPhaseSchwartz P r Ψ) :
    testElem P r ((starRingEnd ℂ) (μ : ℂ) • Ψ + L0 ν Ψ) =
      ((starRingEnd ℂ) (μ : ℂ) + 1) • testElem P r Ψ - testElem P r (driftT Ψ) -
        (ν : ℂ) • testElem P r (lapT Ψ) := by
  rw [op_eq_driftT]
  have h1 : IsSliceTest P r (((starRingEnd ℂ) (μ : ℂ) + 1) • Ψ) := hΨ.sliceTest.const_smul _
  have h2 : IsSliceTest P r (driftT Ψ) := hΨ.sliceTest_driftT
  have e : nuLapT ν Ψ = (ν : ℂ) • lapT Ψ := by
    funext p
    simp [nuLapT, Complex.coe_smul]
  have h3 : IsSliceTest P r (nuLapT ν Ψ) := by
    rw [e]; exact hΨ.sliceTest_lapT.const_smul _
  rw [sub_eq_add_neg, sub_eq_add_neg, testElem_add (h1.add h2.neg) h3.neg, testElem_add h1 h2.neg,
    testElem_neg h2, testElem_neg h3, e, testElem_const_smul hΨ.sliceTest,
    testElem_const_smul hΨ.sliceTest_lapT]
  abel

/-- **Extension to Schwartz-type tests** for the combined operator `μ̄ + L₀`
(analogue of `HasPhaseOp.extend_lap`/`extend_drift`). -/
theorem hasPhaseOp_extend_op {P : ℝ} [Fact (0 < P)] {q : ℝ≥0∞} [Fact (1 ≤ q)] (hq : 1 < q)
    (ν μ : ℝ) {f g : Yq P q}
    (h : HasPhaseOp (fun Φ => (starRingEnd ℂ) (μ : ℂ) • Φ + L0 ν Φ) f g)
    {Ψ : ℝ × Space → CVec3} (hΨ : IsPhaseSchwartz P (conjExp q) Ψ) :
    phasePair P q ((starRingEnd ℂ) (μ : ℂ) • Ψ + L0 ν Ψ) f = phasePair P q Ψ g := by
  refine h.extend_of_tendsto hΨ.isPhaseTest_cut (tendsto_cut (conjExp_ne_top hq) hΨ) ?_
  have hc : ∀ n, IsPhaseSchwartz P (conjExp q) (mulT (cutχ n) Ψ) := fun n =>
    (hΨ.isPhaseTest_cut n).isPhaseSchwartz _
  simp only [testElem_op ν μ hΨ, testElem_op ν μ (hc _)]
  exact (((tendsto_cut (conjExp_ne_top hq) hΨ).const_smul _).sub
    (tendsto_cut_driftT (conjExp_ne_top hq) hΨ)).sub
    ((tendsto_cut_lapT (conjExp_ne_top hq) hΨ).const_smul _)

open UnforcedLeray.Short.PartIIa in
/-- **Smooth representative of the Leray projection of a phase test** (lines 1364, 1474-1475,
1498-1500): for a phase test `Φ` there is a smooth Schwartz-type `L²`-phase test `Ψ` (the
slice-wise Cartesian Leray projection `𝐏Φ = Φ - ∇Δ⁻¹ div Φ`, a smooth field with all derivatives
`O(|y|⁻³)`, hence in `L²(ℝ³)`, as are `∂_jΨ`, `ΔΨ`, `y·∇Ψ`, `∂_τΨ`) such that `⟪Φ, 𝐏f⟫ = ⟪Ψ, f⟫`
for every `f ∈ Y_2` (self-adjointness of `𝐏` on `Y_2`). -/
def LerayTestSchwartz : Prop :=
  ∀ (P : ℝ) [Fact (0 < P)] (Φ : ℝ × Space → CVec3), IsPhaseTest P Φ →
    ∃ Ψ : ℝ × Space → CVec3, IsPhaseSchwartz P (conjExp 2) Ψ ∧
      ∀ f : Yq P 2, phasePair P 2 Φ (lerayY P 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top f) =
        phasePair P 2 Ψ f

open UnforcedLeray.Short.PartIIa in
/-- **Leray commutes with `μ̄ + L₀` on tests** (line 1474-1475: Leray commutes with heat, dilation
and phase translation): if `Ψ, Ψ'` are the smooth Schwartz-type representatives of `𝐏Φ` and
`𝐏((μ̄ + L₀)Φ)` (as in `LerayTestSchwartz`; they are determined by their pairings, being
continuous), then `Ψ' = (μ̄ + L₀)Ψ`.  Proof idea: `𝐏` commutes with `∂_τ`, `Δ`, `y·∇` and constants
(`lerayY_phase`, `lerayY_heat`, `lerayY_dilate` in `Lib/LerayC`), so `⟪(μ̄+L₀)Φ, 𝐏f⟫ =
⟪(μ̄+L₀)Ψ, f⟫` for all `f ∈ Y_2`; both sides of the claim are continuous `L²` slice tests with the
same pairing against `Y_2`, so they coincide. -/
def LerayTestComm : Prop :=
  ∀ (P ν μ : ℝ) [Fact (0 < P)] (Φ Ψ Ψ' : ℝ × Space → CVec3), IsPhaseTest P Φ →
    IsPhaseSchwartz P (conjExp 2) Ψ → IsPhaseSchwartz P (conjExp 2) Ψ' →
    (∀ f : Yq P 2, phasePair P 2 Φ (lerayY P 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top f) =
        phasePair P 2 Ψ f) →
    (∀ f : Yq P 2, phasePair P 2 ((starRingEnd ℂ) (μ : ℂ) • Φ + L0 ν Φ)
        (lerayY P 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top f) = phasePair P 2 Ψ' f) →
    Ψ' = (starRingEnd ℂ) (μ : ℂ) • Ψ + L0 ν Ψ

open UnforcedLeray.Short.PartIIa in
theorem adjointLerayCommute_of (h1 : LerayTestSchwartz) (h2 : LerayTestComm) :
    AdjointLerayCommute := by
  intro P ν μ _ hP1 hν hμ Fq Wq h Φ hΦ
  obtain ⟨Ψ, hΨ, hΨp⟩ := h1 P Φ hΦ
  obtain ⟨Ψ', hΨ', hΨ'p⟩ := h1 P _ (isPhaseTest_op ν μ hΦ)
  have hc := h2 P ν μ Φ Ψ Ψ' hΦ hΨ hΨ' hΨp hΨ'p
  calc phasePair P 2 ((starRingEnd ℂ) (μ : ℂ) • Φ + L0 ν Φ)
        (lerayY P 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top Wq) = phasePair P 2 Ψ' Wq := hΨ'p Wq
    _ = phasePair P 2 ((starRingEnd ℂ) (μ : ℂ) • Ψ + L0 ν Ψ) Wq := by rw [hc]
    _ = phasePair P 2 Ψ Fq := hasPhaseOp_extend_op (by norm_num) ν μ h hΨ
    _ = phasePair P 2 Φ (lerayY P 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top Fq) :=
      (hΨp Fq).symm

end UnforcedLeray.Short.IIb
