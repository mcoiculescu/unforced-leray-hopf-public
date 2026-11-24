import UnforcedLeray.Short.PartIIa.Sub.PartIIa_F09_3_1_1
import UnforcedLeray.Short.PartIIa.Tasks.F03aWindowEquation.LocalIdentityOfPhaseOp
import UnforcedLeray.Short.PartIIa.Tasks.F09Adjoint.GraphBound.Window.Equation.L0PerT

/-!


Source `the November 2 reference manuscript` lines 1426-1442 (reversed window).
Analogue of `localIdentityOfPhaseOp` (`Tasks/F03aWindowEquation/LocalIdentityOfPhaseOp.lean`) with
`L0T` replaced by `L0` and `μ` replaced by `μ̄`.

Route. For smooth compactly supported `Ψ`, the periodized test `perT P Ψ` is a phase test. Its image
under `μ̄ + L₀` is `perT P (μ̄Ψ + L₀Ψ)`, because `L₀` commutes with periodization (`L0_perT`) and
`perT` is additive and `ℂ`-homogeneous (`lioPerT_add_smul`). Applying `HasPhaseOp` to `perT P Ψ`,
unfolding both pairings with `periodizedPairing` (integrability from `repLocInt`), and cancelling
`P⁻¹ ≠ 0` gives the local identity.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.PhaseSpace UnforcedLeray.PhaseTrace UnforcedLeray.B0411 UnforcedLeray.Parabolic
  UnforcedLeray.Short.PartIIa.Rep

/-- `L₀ ν` (forward operator, `B0411.L0`) maps phase tests to phase tests:
`L₀ = ∂_τ − ½ y·∇ − ν Δ − ½` on smooth fields, and each summand preserves `IsPhaseTest`. -/
theorem adjIsPhaseTestL0 {P : ℝ} {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ) (ν : ℝ) :
    IsPhaseTest P (UnforcedLeray.B0411.L0 ν Φ) := by
  have h : UnforcedLeray.B0411.L0 ν Φ = PhaseSpace.dτ Φ - (1 / 2 : ℝ) • PhaseSpace.radialT Φ
      - ν • PhaseSpace.lapT Φ - (1 / 2 : ℝ) • Φ := by
    funext p
    simp only [UnforcedLeray.B0411.L0, UnforcedLeray.B0411.T0, Pi.sub_apply, Pi.smul_apply]
  rw [h]
  exact (((hΦ.dτ).sub ((hΦ.radialT).const_smul (1 / 2 : ℝ))).sub
    ((hΦ.lapT).const_smul ν)).sub (hΦ.const_smul (1 / 2 : ℝ))

/-- **`PartII-a:F09/3/1/1/3`**: from `HasPhaseOp (μ̄ + L₀) w f`, the adjoint local identity. -/
theorem adjLocalIdentityOfPhaseOp : AdjLocalIdentityOfPhaseOp := by
  unfold AdjLocalIdentityOfPhaseOp
  intro r hr1 hr P hP ν μ f w hHas W Fr hW hF
  unfold AdjLocalIdentity
  intro Ψ hΨs hΨc
  have hP0 : 0 < P := hP.out
  obtain ⟨R, -, hTΨ, hSΨ⟩ := UnforcedLeray.B0005.exists_window_of_hasCompactSupport hΨc
  have hΨT : IsPhaseTest 0 Ψ :=
    { smooth := hΨs
      periodic := fun τ y => by simp
      bounded_support := ⟨R, hSΨ⟩ }
  have hL0Ts : TimeSupp (-R) R (UnforcedLeray.B0411.L0 ν Ψ) := timeSupp_L0 hTΨ ν
  have hG₁T : TimeSupp (-R) R ((starRingEnd ℂ) μ • Ψ + UnforcedLeray.B0411.L0 ν Ψ) :=
    lioTS_add hTΨ hL0Ts _
  have hG₁P : IsPhaseTest 0 ((starRingEnd ℂ) μ • Ψ + UnforcedLeray.B0411.L0 ν Ψ) :=
    (hΨT.const_smul _).add (adjIsPhaseTestL0 hΨT ν)
  obtain ⟨R₁, hR₁⟩ := hG₁P.bounded_support
  have hG₁c : HasCompactSupport ((starRingEnd ℂ) μ • Ψ + UnforcedLeray.B0411.L0 ν Ψ) :=
    lioCompact hG₁T hR₁
  have hΦP : IsPhaseTest P (perT P Ψ) := isPhaseTest_perT hP0 hTΨ hΨT
  have hA : phasePair P r ((starRingEnd ℂ) μ • perT P Ψ + UnforcedLeray.B0411.L0 ν (perT P Ψ)) w =
      phasePair P r (perT P Ψ) f :=
    hHas _ hΦP
  have hEq : (starRingEnd ℂ) μ • perT P Ψ + UnforcedLeray.B0411.L0 ν (perT P Ψ) =
      perT P ((starRingEnd ℂ) μ • Ψ + UnforcedLeray.B0411.L0 ν Ψ) := by
    rw [UnforcedLeray.Short.PartIIa.L0_perT hP0 hTΨ hΨs ν,
      lioPerT_add_smul hP0 hTΨ hL0Ts _]
  rw [hEq] at hA
  have hB : phasePair P r (perT P Ψ) f = (P⁻¹ : ℝ) • ∫ p, dotL (Ψ p) (Fr p) :=
    periodizedPairing r hr P f Fr hF Ψ (-R) R hTΨ hΨT
      ((repLocInt r hr P f Fr hF).2 Ψ hΨs.continuous hΨc)
  have hC : phasePair P r (perT P ((starRingEnd ℂ) μ • Ψ + UnforcedLeray.B0411.L0 ν Ψ)) w =
      (P⁻¹ : ℝ) • ∫ p, dotL (((starRingEnd ℂ) μ • Ψ + UnforcedLeray.B0411.L0 ν Ψ) p) (W p) :=
    periodizedPairing r hr P w W hW _ (-R) R hG₁T hG₁P
      ((repLocInt r hr P w W hW).2 _ hG₁P.smooth.continuous hG₁c)
  rw [hC, hB] at hA
  exact smul_right_injective ℂ (inv_ne_zero hP0.ne') hA

end UnforcedLeray.Short.PartIIa
