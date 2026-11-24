import UnforcedLeray.Short.PartIIa.Sub.F03_1
import UnforcedLeray.Short.PartIIa.Tasks.F03aWindowEquation.RepLocInt
import UnforcedLeray.Short.PartIIa.Tasks.F03aWindowEquation.PeriodizedPairing

/-!
# Part II-a, task `PartII-a:F03/1/3`: from `HasPhaseOp` to the local identity

Target: `UnforcedLeray.Short.PartIIa.localIdentityOfPhaseOp : LocalIdentityOfPhaseOp`
(the Prop is defined in `Sub/F03_1.lean`).
Source of record: `the November 2 reference manuscript`, lines 1431-1434.

Route. For smooth compactly supported `Ψ`, the periodized test `perT P Ψ` is a phase test.
Its image under `μ + L₀ᵗ` is `perT P (μΨ + L₀ᵗΨ)`, because `L₀ᵗ` commutes with periodization
(`B0424.L0T_perT`) and `perT` is additive and `ℂ`-homogeneous (`lioPerT_add_smul`). Applying
`HasPhaseOp` to `perT P Ψ`, unfolding both pairings with `periodizedPairing` (integrability from
`repLocInt`), and cancelling the factor `P⁻¹ ≠ 0` gives the local identity.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.PhaseSpace UnforcedLeray.PhaseTrace UnforcedLeray.B0411 UnforcedLeray.Parabolic
  UnforcedLeray.Short.PartIIa.Rep

/-- A time-supported linear combination `c • G₁ + G₂` is time-supported on the same window. -/
theorem lioTS_add {A B : ℝ} {G₁ G₂ : ℝ × Space → CVec3} (h₁ : TimeSupp A B G₁)
    (h₂ : TimeSupp A B G₂) (c : ℂ) : TimeSupp A B (c • G₁ + G₂) := by
  intro τ y hτ
  simp [h₁ τ y hτ, h₂ τ y hτ]

/-- Periodization is additive and `ℂ`-homogeneous on time-supported fields. -/
theorem lioPerT_add_smul {P : ℝ} (hP : 0 < P) {A B : ℝ} {G₁ G₂ : ℝ × Space → CVec3}
    (h₁ : TimeSupp A B G₁) (h₂ : TimeSupp A B G₂) (c : ℂ) :
    perT P (c • G₁ + G₂) = c • perT P G₁ + perT P G₂ := by
  funext p
  have hm : p.1 ∈ Icc (p.1 - 1) (p.1 + 1) := ⟨by linarith, by linarith⟩
  have key : ∀ k : ℤ, p.1 + k * P ∈ Icc A B → k ∈ perIdx P A B (p.1 - 1) (p.1 + 1) :=
    fun k hk => mem_perIdx hP hm hk
  simp only [Pi.add_apply, Pi.smul_apply]
  rw [perT_eq_sum (lioTS_add h₁ h₂ c) _ p key, perT_eq_sum h₁ _ p key,
    perT_eq_sum h₂ _ p key]
  simp only [Pi.add_apply, Pi.smul_apply, Finset.sum_add_distrib, Finset.smul_sum]

/-- A field supported in the time window `[A, B]` and in the ball `‖y‖ ≤ R` is compactly
supported. -/
theorem lioCompact {G : ℝ × Space → CVec3} {A B R : ℝ} (hT : TimeSupp A B G)
    (hS : ∀ τ y, R < ‖y‖ → G (τ, y) = 0) : HasCompactSupport G := by
  refine HasCompactSupport.intro (K := Icc A B ×ˢ Metric.closedBall (0 : Space) R)
    (isCompact_Icc.prod (isCompact_closedBall _ _)) ?_
  rintro ⟨τ, y⟩ hx
  by_cases h1 : τ ∈ Icc A B
  · by_cases h2 : ‖y‖ ≤ R
    · exact absurd (mk_mem_prod h1 (by simpa using h2)) hx
    · exact hS τ y (not_le.mp h2)
  · exact hT τ y h1

/-- **From `HasPhaseOp` to the local identity** (task `PartII-a:F03/1/3`). -/
theorem localIdentityOfPhaseOp : UnforcedLeray.Short.PartIIa.LocalIdentityOfPhaseOp := by
  unfold LocalIdentityOfPhaseOp
  intro r hr1 hr P hP ν μ f w hHas W Fr hW hF
  unfold LocalIdentity
  intro Ψ hΨs hΨc
  have hP0 : 0 < P := hP.out
  obtain ⟨R, -, hTΨ, hSΨ⟩ := UnforcedLeray.B0005.exists_window_of_hasCompactSupport hΨc
  have hΨT : IsPhaseTest 0 Ψ :=
    { smooth := hΨs
      periodic := fun τ y => by simp
      bounded_support := ⟨R, hSΨ⟩ }
  have hL0Ts : TimeSupp (-R) R (L0T ν Ψ) := UnforcedLeray.B0424.timeSupp_L0T hTΨ ν
  have hG₁T : TimeSupp (-R) R (μ • Ψ + L0T ν Ψ) := lioTS_add hTΨ hL0Ts μ
  have hG₁P : IsPhaseTest 0 (μ • Ψ + L0T ν Ψ) :=
    (hΨT.const_smul μ).add (isPhaseTest_L0T hΨT ν)
  obtain ⟨R₁, hR₁⟩ := hG₁P.bounded_support
  have hG₁c : HasCompactSupport (μ • Ψ + L0T ν Ψ) := lioCompact hG₁T hR₁
  have hΦP : IsPhaseTest P (perT P Ψ) := isPhaseTest_perT hP0 hTΨ hΨT
  have hA : phasePair P r (μ • perT P Ψ + L0T ν (perT P Ψ)) w = phasePair P r (perT P Ψ) f :=
    hHas _ hΦP
  have hEq : μ • perT P Ψ + L0T ν (perT P Ψ) = perT P (μ • Ψ + L0T ν Ψ) := by
    rw [UnforcedLeray.B0424.L0T_perT hP0 hTΨ hΨs ν, lioPerT_add_smul hP0 hTΨ hL0Ts μ]
  rw [hEq] at hA
  have hB : phasePair P r (perT P Ψ) f = (P⁻¹ : ℝ) • ∫ p, dotL (Ψ p) (Fr p) :=
    periodizedPairing r hr P f Fr hF Ψ (-R) R hTΨ hΨT
      ((repLocInt r hr P f Fr hF).2 Ψ hΨs.continuous hΨc)
  have hC : phasePair P r (perT P (μ • Ψ + L0T ν Ψ)) w =
      (P⁻¹ : ℝ) • ∫ p, dotL ((μ • Ψ + L0T ν Ψ) p) (W p) :=
    periodizedPairing r hr P w W hW (μ • Ψ + L0T ν Ψ) (-R) R hG₁T hG₁P
      ((repLocInt r hr P w W hW).2 (μ • Ψ + L0T ν Ψ) hG₁P.smooth.continuous hG₁c)
  rw [hC, hB] at hA
  exact smul_right_injective ℂ (inv_ne_zero hP0.ne') hA

end UnforcedLeray.Short.PartIIa
