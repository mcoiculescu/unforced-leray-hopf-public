import UnforcedLeray.Short.PartIIa.Sub.R01

/-!
# Part II-a, task `PartII-a:R01`, target `ringEarlyA2_of`: the early `A₂` block

Target: `ringEarlyA2_of` proves `RingEarlyA2` (`Short/PartII-a/Sub/R01.lean`) from the calculus
`EarlyCalculus`, the zero-age stream bound `EarlyStreamProfile`, the pressure bound
`EarlyPressureProfile` (not used) and the profile smoothness `LateProfileSmooth`.

Source of record: `the November 2 reference manuscript`, lines 1294-1297.

Route. By `earlyStmt_of_groupBdd` it suffices to show `EarlyGroupBdd ρ (fun ν ψ _ => coeffA₂ ν ψ)`
for every `ρ > 1/2`. The base family is `ψ ↦ ψ` (`earlyBdd_stream`). With
`H = ageDefect ψ = ψ - Kψ`, `v₁ = streamV1 ψ = -∂_η ψ`, `v₂ = streamV2 ψ = ∂_q ψ`, the definition
`coeffA₂` reads
`(∂_s H + v₁ ∂_q H + v₂ ∂_η H - ν(∂_q² H + ∂_η² H)) + H ∂_η v₂ - v₁ (K+1) v₂ + 2ν (K+1) ∂_q v₂`,
which is exactly the closure tree built below. The equality of the closure tree with `coeffA₂` is
a pointwise identity, checked by `funext`, unfolding and `ring`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0184 UnforcedLeray.B0185 UnforcedLeray.B0187 UnforcedLeray.B0188
  UnforcedLeray.B0190

/-- Equal families have the same zero-age boundedness. -/
theorem earlyBdd_of_eq_family {ρ : ℝ} {X Y : ProfFam} (e : X = Y) (h : EarlyBdd ρ X) :
    EarlyBdd ρ Y := by
  subst e
  exact h

/-- **`PartII-a:R01`, block `A₂`** (source lines 1294-1297). -/
theorem ringEarlyA2_of (hC : EarlyCalculus) (hψ : EarlyStreamProfile) (hp : EarlyPressureProfile)
    (hS : LateProfileSmooth) : RingEarlyA2 := by
  show EarlyStmt (fun ν ψ _ => coeffA₂ ν ψ)
  apply earlyStmt_of_groupBdd
  intro ρ hρ
  have hPsi : EarlyBdd ρ (fun _ ψ _ => ψ) := earlyBdd_stream hS hψ hρ
  -- the age defect `H = ψ - Kψ`, the velocities `v₁ = -∂_η ψ`, `v₂ = ∂_q ψ`
  have hH : EarlyBdd ρ (fun _ ψ _ => ageDefect ψ) :=
    hC.sub ρ (fun _ ψ _ => ψ) (fun _ ψ _ => ageOperator ψ) hρ hPsi
      (hC.scaling ρ (fun _ ψ _ => ψ) hρ hPsi)
  have hv1 : EarlyBdd ρ (fun _ ψ _ => streamV1 ψ) :=
    hC.neg ρ (fun _ ψ _ => partialEta ψ) hρ (hC.dEta ρ (fun _ ψ _ => ψ) hρ hPsi)
  have hv2 : EarlyBdd ρ (fun _ ψ _ => streamV2 ψ) :=
    hC.dQ ρ (fun _ ψ _ => ψ) hρ hPsi
  -- the derivatives of `H`
  have dA := hC.dAge ρ _ hρ hH
  have dQH := hC.dQ ρ _ hρ hH
  have dEH := hC.dEta ρ _ hρ hH
  have lap := hC.add ρ _ _ hρ (hC.dQ ρ _ hρ dQH) (hC.dEta ρ _ hρ dEH)
  -- transport-diffusion `∂_s H + v₁ ∂_q H + v₂ ∂_η H - ν ΔH`
  have TD := hC.sub ρ _ _ hρ
    (hC.add ρ _ _ hρ (hC.add ρ _ _ hρ dA (hC.mul ρ _ _ hρ hv1 dQH)) (hC.mul ρ _ _ hρ hv2 dEH))
    (hC.nuMul ρ _ hρ lap)
  -- the remaining terms of `A₂`
  have dEv2 := hC.dEta ρ _ hρ hv2
  have sh1v2 := hC.shift ρ 1 _ hρ hv2
  have sh1dQv2 := hC.shift ρ 1 _ hρ (hC.dQ ρ _ hρ hv2)
  have W := hC.add ρ _ _ hρ
    (hC.sub ρ _ _ hρ (hC.add ρ _ _ hρ TD (hC.mul ρ _ _ hρ hH dEv2)) (hC.mul ρ _ _ hρ hv1 sh1v2))
    (hC.nuMul ρ _ hρ (hC.constMul ρ 2 _ hρ sh1dQv2))
  have hX : EarlyBdd ρ (fun ν ψ _ => coeffA₂ ν ψ) := by
    refine earlyBdd_of_eq_family ?_ W
    funext ν ψ p x
    simp only [coeffA₂, transportDiffusion, profileLap, streamV1, streamV2, ageDefect, ageShift,
      Pi.add_apply, Pi.sub_apply, Pi.mul_apply]
    ring
  unfold EarlyGroupBdd
  exact ⟨hX, hC.dEta ρ _ hρ hX, hC.dQ ρ _ hρ hX, hC.shift ρ 3 _ hρ hX⟩

end UnforcedLeray.Short.PartIIa
