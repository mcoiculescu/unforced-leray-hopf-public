import UnforcedLeray.Short.PartIIa.Sub.R01

/-!
# Part II-a, task `PartII-a:R01`, target `ringEarlyB2_of`: the early `B₂` block

Target: `ringEarlyB2_of` proves `RingEarlyB2` (`Short/PartII-a/Sub/R01.lean`) from the calculus
`EarlyCalculus`, the zero-age stream bound `EarlyStreamProfile`, the pressure bound
`EarlyPressureProfile` (not used) and the profile smoothness `LateProfileSmooth`.

Source of record: `the November 2 reference manuscript`, lines 1294-1297, and the
definition of `B₂` at lines 2908-2909 (`coeffB₂` in `Units/B0188.lean`, line 111).

Route. By `earlyStmt_of_groupBdd` it suffices to show `EarlyGroupBdd ρ (fun ν ψ _ => coeffB₂ ν ψ)`
for every `ρ > 1/2`. The base family is `ψ ↦ ψ` (`earlyBdd_stream`). With
`H = ageDefect ψ = ψ - Kψ`, `v₁ = streamV1 ψ = -∂_η ψ`, `v₂ = streamV2 ψ = ∂_q ψ`, the definition
`coeffB₂` reads

`-(v₁ (K+1) H) + H ∂_η H + 2ν (K+1) ∂_q H - ν (K+1)² v₂`,

which is exactly the closure tree built below. The equality of the closure tree with `coeffB₂` is
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
private theorem earlyBdd_eq_family_B2 {ρ : ℝ} {X Y : ProfFam} (e : X = Y) (h : EarlyBdd ρ X) :
    EarlyBdd ρ Y := by
  subst e
  exact h

/-- **`PartII-a:R01`, block `B₂`** (source lines 1294-1297). -/
theorem ringEarlyB2_of (hC : EarlyCalculus) (hψ : EarlyStreamProfile) (hp : EarlyPressureProfile)
    (hS : LateProfileSmooth) : RingEarlyB2 := by
  show EarlyStmt (fun ν ψ _ => coeffB₂ ν ψ)
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
  -- `-v₁ (K+1) H`
  have sh1H := hC.shift ρ 1 _ hρ hH
  have t1 := hC.neg ρ _ hρ (hC.mul ρ _ _ hρ hv1 sh1H)
  -- `H ∂_η H`
  have dEH := hC.dEta ρ _ hρ hH
  have t2 := hC.mul ρ _ _ hρ hH dEH
  -- `2ν (K+1) ∂_q H`
  have dQH := hC.dQ ρ _ hρ hH
  have t3 := hC.nuMul ρ _ hρ (hC.constMul ρ 2 _ hρ (hC.shift ρ 1 _ hρ dQH))
  -- `-ν (K+1)² v₂`
  have t4 := hC.nuMul ρ _ hρ (hC.shift ρ 1 _ hρ (hC.shift ρ 1 _ hρ hv2))
  have W := hC.sub ρ _ _ hρ (hC.add ρ _ _ hρ (hC.add ρ _ _ hρ t1 t2) t3) t4
  have hX : EarlyBdd ρ (fun ν ψ _ => coeffB₂ ν ψ) := by
    refine earlyBdd_eq_family_B2 ?_ W
    funext ν ψ p x
    simp only [coeffB₂, streamV1, streamV2, ageDefect, ageShift,
      Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.neg_apply]
    ring
  unfold EarlyGroupBdd
  exact ⟨hX, hC.dEta ρ _ hρ hX, hC.dQ ρ _ hρ hX, hC.shift ρ 3 _ hρ hX⟩

end UnforcedLeray.Short.PartIIa
