import UnforcedLeray.Short.PartIIa.Sub.R01

/-!


Source of record: `the November 2 reference manuscript`, lines 1294-1297.

The coefficient `coeffA₁ = -(v₁ K v₁) + H (∂_η v₁) - v₁² + 2ν (K+1) ∂_q v₁ - (K+2) p` with
`v₁ = streamV1 ψ = -∂_η ψ` and `H = ageDefect ψ = ψ - Kψ` is built from the zero-age bounded
families `ψ` and `p` (`earlyBdd_stream`, `earlyBdd_pressure`) by the closure lemmas of
`EarlyCalculus`, and then `earlyStmt_of_groupBdd` gives `RingEarlyA1`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0184 UnforcedLeray.B0185 UnforcedLeray.B0187 UnforcedLeray.B0188
  UnforcedLeray.B0190

/-- **`PartII-a:R01`, `A₁` block** (source lines 1294-1297): the zero-age table for `A₁`, from the
closure calculus and the zero-age bounds on the stream and pressure profiles. -/
theorem ringEarlyA1_of (hC : EarlyCalculus) (hψ : EarlyStreamProfile) (hp : EarlyPressureProfile)
    (hS : LateProfileSmooth) : RingEarlyA1 := by
  unfold RingEarlyA1
  apply earlyStmt_of_groupBdd
  intro ρ hρ
  unfold EarlyGroupBdd
  -- transport a bound along an equality of families
  have cong : ∀ X Y : ProfFam, X = Y → EarlyBdd ρ Y → EarlyBdd ρ X := by
    intro X Y h hY
    subst h
    exact hY
  -- zero-age bounded inputs: the stream profile and the pressure profile
  have hPsi : EarlyBdd ρ (fun _ ψ _ => ψ) := earlyBdd_stream hS hψ hρ
  have hPr : EarlyBdd ρ (fun _ _ p => p) := earlyBdd_pressure hS hp hρ
  -- `v₁ = streamV1 ψ = -∂_η ψ`
  have hV : EarlyBdd ρ (fun _ ψ _ => streamV1 ψ) :=
    hC.neg ρ (fun _ ψ _ => partialEta ψ) hρ (hC.dEta ρ (fun _ ψ _ => ψ) hρ hPsi)
  -- `H = ageDefect ψ = ψ - Kψ`
  have hH : EarlyBdd ρ (fun _ ψ _ => ageDefect ψ) :=
    hC.sub ρ (fun _ ψ _ => ψ) (fun _ ψ _ => ageOperator ψ) hρ hPsi
      (hC.scaling ρ (fun _ ψ _ => ψ) hρ hPsi)
  -- the factors of the coefficient
  have hKV : EarlyBdd ρ (fun _ ψ _ => ageOperator (streamV1 ψ)) :=
    hC.scaling ρ (fun _ ψ _ => streamV1 ψ) hρ hV
  have hdEtaV : EarlyBdd ρ (fun _ ψ _ => partialEta (streamV1 ψ)) :=
    hC.dEta ρ (fun _ ψ _ => streamV1 ψ) hρ hV
  have hdQV : EarlyBdd ρ (fun _ ψ _ => partialQ (streamV1 ψ)) :=
    hC.dQ ρ (fun _ ψ _ => streamV1 ψ) hρ hV
  have hsh1 : EarlyBdd ρ (fun _ ψ _ => ageShift 1 (partialQ (streamV1 ψ))) :=
    hC.shift ρ 1 (fun _ ψ _ => partialQ (streamV1 ψ)) hρ hdQV
  have hsh2 : EarlyBdd ρ (fun _ _ p => ageShift 2 p) :=
    hC.shift ρ 2 (fun _ _ p => p) hρ hPr
  -- the five terms of `A₁`
  have hMA : EarlyBdd ρ (fun _ ψ _ => streamV1 ψ * ageOperator (streamV1 ψ)) :=
    hC.mul ρ (fun _ ψ _ => streamV1 ψ) (fun _ ψ _ => ageOperator (streamV1 ψ)) hρ hV hKV
  have hMB : EarlyBdd ρ (fun _ ψ _ => ageDefect ψ * partialEta (streamV1 ψ)) :=
    hC.mul ρ (fun _ ψ _ => ageDefect ψ) (fun _ ψ _ => partialEta (streamV1 ψ)) hρ hH hdEtaV
  have hMC : EarlyBdd ρ (fun _ ψ _ => streamV1 ψ * streamV1 ψ) :=
    hC.mul ρ (fun _ ψ _ => streamV1 ψ) (fun _ ψ _ => streamV1 ψ) hρ hV hV
  have hNU := hC.nuMul ρ _ hρ (hC.constMul ρ 2 _ hρ hsh1)
  -- the sum `-(v₁ K v₁) + H ∂_η v₁ - v₁ v₁ + ν (2 (K+1) ∂_q v₁) - (K+2) p`
  have hX1 := hC.neg ρ _ hρ hMA
  have hX2 := hC.add ρ _ _ hρ hX1 hMB
  have hX3 := hC.sub ρ _ _ hρ hX2 hMC
  have hX4 := hC.add ρ _ _ hρ hX3 hNU
  have hX5 := hC.sub ρ _ _ hρ hX4 hsh2
  -- identify the family with `coeffA₁` pointwise
  have hA1 : EarlyBdd ρ (fun ν ψ p => coeffA₁ ν ψ p) := by
    refine cong _ _ ?_ hX5
    funext ν ψ p x
    simp only [coeffA₁, ageDefect, ageShift, streamV1, Pi.add_apply, Pi.sub_apply,
      Pi.mul_apply, Pi.neg_apply]
    ring
  exact ⟨hA1, hC.dEta ρ _ hρ hA1, hC.dQ ρ _ hρ hA1, hC.shift ρ 3 _ hρ hA1⟩

end UnforcedLeray.Short.PartIIa
