import UnforcedLeray.Short.PartIIa.Sub.R01

/-!


Source of record: `the November 2 reference manuscript`, lines 1294-1297.

The coefficient `coeffB₁ ν ψ = -ν * K (K+2) v₁` with `v₁ = streamV1 ψ = -∂_η ψ` is built from the
zero-age bounded stream profile `ψ` (`earlyBdd_stream`) by the closure lemmas of `EarlyCalculus`:
negation, `(K+2)`, `K`, multiplication by `ν`, and multiplication by `-1`.  The four weighted groups
`X, ∂_η X, ∂_q X, (K+3) X` then follow from the closure lemmas for `∂_η, ∂_q` and `K+a`, and
`earlyStmt_of_groupBdd` gives `RingEarlyB1`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0184 UnforcedLeray.B0185 UnforcedLeray.B0187 UnforcedLeray.B0188
  UnforcedLeray.B0190

/-- **`PartII-a:R01`, `B₁` block** (source lines 1294-1297): the zero-age table for `B₁`, from the
closure calculus and the zero-age bound on the stream profile. -/
theorem ringEarlyB1_of (hC : EarlyCalculus) (hψ : EarlyStreamProfile) (hp : EarlyPressureProfile)
    (hS : LateProfileSmooth) : RingEarlyB1 := by
  unfold RingEarlyB1
  apply earlyStmt_of_groupBdd
  intro ρ hρ
  unfold EarlyGroupBdd
  -- transport a bound along an equality of families
  have cong : ∀ X Y : ProfFam, X = Y → EarlyBdd ρ Y → EarlyBdd ρ X := by
    intro X Y h hY
    subst h
    exact hY
  -- zero-age bounded input: the stream profile
  have hPsi : EarlyBdd ρ (fun _ ψ _ => ψ) := earlyBdd_stream hS hψ hρ
  -- `v₁ = streamV1 ψ = -∂_η ψ`
  have hV : EarlyBdd ρ (fun _ ψ _ => streamV1 ψ) :=
    hC.neg ρ (fun _ ψ _ => partialEta ψ) hρ (hC.dEta ρ (fun _ ψ _ => ψ) hρ hPsi)
  -- `(K+2) v₁`, then `K (K+2) v₁`, then `ν K (K+2) v₁`
  have hS2 : EarlyBdd ρ (fun _ ψ _ => ageShift 2 (streamV1 ψ)) :=
    hC.shift ρ 2 (fun _ ψ _ => streamV1 ψ) hρ hV
  have hK : EarlyBdd ρ (fun _ ψ _ => ageOperator (ageShift 2 (streamV1 ψ))) :=
    hC.scaling ρ (fun _ ψ _ => ageShift 2 (streamV1 ψ)) hρ hS2
  have hN := hC.nuMul ρ (fun _ ψ _ => ageOperator (ageShift 2 (streamV1 ψ))) hρ hK
  -- `-1` times the above, which is `-ν K (K+2) v₁ = coeffB₁`
  have hM := hC.constMul ρ (-1) _ hρ hN
  -- identify the family with `coeffB₁` pointwise
  have hX : EarlyBdd ρ (fun ν ψ _ => coeffB₁ ν ψ) := by
    refine cong _ _ ?_ hM
    funext ν ψ p x
    show -ν * ageOperator (ageShift 2 (streamV1 ψ)) x
      = (-1 : ℝ) * (ν * ageOperator (ageShift 2 (streamV1 ψ)) x)
    ring
  -- the four weighted groups: `X`, `∂_η X`, `∂_q X`, `(K+3) X`
  exact ⟨hX, hC.dEta ρ _ hρ hX, hC.dQ ρ _ hρ hX, hC.shift ρ 3 _ hρ hX⟩

end UnforcedLeray.Short.PartIIa
