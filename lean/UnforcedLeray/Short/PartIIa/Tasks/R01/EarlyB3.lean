import UnforcedLeray.Short.PartIIa.Sub.R01

/-!


Source of record: `the November 2 reference manuscript`, lines 1294-1297.

The coefficient is `coeffB₃ ν ψ = -ν * (K+1)² H` with `H = ageDefect ψ = ψ - Kψ` (`Units/B0188`,
`coeffB₃`; `Units/B0185`, `ageDefect`).  It is built from the zero-age bounded family `ψ`
(`earlyBdd_stream`) by the closure lemmas of `EarlyCalculus`: `scaling` and `sub` give `H`, `shift 1`
twice gives `(K+1)² H`, `nuMul` and `constMul (-1)` give `-ν (K+1)² H`.  Then
`earlyStmt_of_groupBdd` gives `RingEarlyB3`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0184 UnforcedLeray.B0185 UnforcedLeray.B0187 UnforcedLeray.B0188
  UnforcedLeray.B0190

/-- **`PartII-a:R01`, `B₃` block** (source lines 1294-1297): the zero-age table for `B₃`, from the
closure calculus and the zero-age bound on the stream profile. -/
theorem ringEarlyB3_of (hC : EarlyCalculus) (hψ : EarlyStreamProfile) (hp : EarlyPressureProfile)
    (hS : LateProfileSmooth) : RingEarlyB3 := by
  unfold RingEarlyB3
  refine earlyStmt_of_groupBdd (fun ρ hρ => ?_)
  have hΨ : EarlyBdd ρ (fun _ ψ _ => ψ) := earlyBdd_stream hS hψ hρ
  have hO : EarlyBdd ρ (fun _ ψ _ => ageOperator ψ) :=
    hC.scaling ρ (fun _ ψ _ => ψ) hρ hΨ
  have hD : EarlyBdd ρ (fun _ ψ _ => ageDefect ψ) :=
    hC.sub ρ (fun _ ψ _ => ψ) (fun _ ψ _ => ageOperator ψ) hρ hΨ hO
  have hS1 : EarlyBdd ρ (fun _ ψ _ => ageShift 1 (ageDefect ψ)) :=
    hC.shift ρ 1 (fun _ ψ _ => ageDefect ψ) hρ hD
  have hS2 : EarlyBdd ρ (fun _ ψ _ => ageShift 1 (ageShift 1 (ageDefect ψ))) :=
    hC.shift ρ 1 (fun _ ψ _ => ageShift 1 (ageDefect ψ)) hρ hS1
  have hN := hC.nuMul ρ (fun _ ψ _ => ageShift 1 (ageShift 1 (ageDefect ψ))) hρ hS2
  have hM := hC.constMul ρ (-1) _ hρ hN
  have key : (fun (ν : ℝ) (ψ _ : ProfilePoint → ℝ) => coeffB₃ ν ψ) =
      (fun (ν : ℝ) (ψ _ : ProfilePoint → ℝ) (x : ProfilePoint) =>
        (-1 : ℝ) * (ν * ageShift 1 (ageShift 1 (ageDefect ψ)) x)) := by
    funext ν ψ p x
    simp only [coeffB₃]
    ring
  have hX : EarlyBdd ρ (fun (ν : ℝ) (ψ _ : ProfilePoint → ℝ) => coeffB₃ ν ψ) :=
    (congrArg (EarlyBdd ρ) key).mpr hM
  exact ⟨hX, hC.dEta ρ _ hρ hX, hC.dQ ρ _ hρ hX, hC.shift ρ 3 _ hρ hX⟩

end UnforcedLeray.Short.PartIIa
