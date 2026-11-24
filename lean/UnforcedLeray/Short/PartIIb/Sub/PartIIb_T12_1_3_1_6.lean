import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T12_1_3_1_5

/-!


Source: `the November 2 reference manuscript` lines 1670, 1923-1926.
Same route as `CylMollWeakDiv` (`PartIIb_T12_1_3_1_5.lean`, which defines `testMoll`), with the
componentwise reflected mollification `Ψ_ρ` of a `CylSolTest`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Complex
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-- **Leaf `T12/1/3/1/6/1`**: `Ψ_ρ = (testMoll ρ Ψ_i)_i` is again a `CylSolTest`
(components by `TestMollIsTest`; divergence by `TestMollDeriv` and `div_free`). -/
def SolTestMollIsSolTest : Prop :=
  ∀ (c : ℝ) (ρ : ContDiffBump (0 : ℝ × ℝ)) (Ψ : ℝ × ℝ → Fin 2 → ℝ), CylSolTest c Ψ →
    CylSolTest c (fun z i => testMoll ρ (fun w => Ψ w i) z)

/-- **Leaf `T12/1/3/1/6/2`** (Fubini + cell shift): `∫_cell (ρ*D)·Ψ = ∫_cell D·Ψ_ρ`. -/
def CylMollSwapSol : Prop :=
  ∀ c r : ℝ, 0 < c → 1 < r → ∀ D : ℝ × ℝ → CMerid, CylLp c r D →
    ∀ (ρ : ContDiffBump (0 : ℝ × ℝ)) (Ψ : ℝ × ℝ → Fin 2 → ℝ), CylSolTest c Ψ →
      ∫ z, ∑ i : Fin 2, cylMoll ρ D z i * (Ψ z i : ℂ) ∂(UnforcedLeray.Cyl.avgμ c) =
        ∫ u, ∑ i : Fin 2, D u i * (testMoll ρ (fun w => Ψ w i) u : ℂ) ∂(UnforcedLeray.Cyl.avgμ c)

theorem cylMollWeakSol_of (h1 : SolTestMollIsSolTest) (h2 : CylMollSwapSol) : CylMollWeakSol := by
  intro c r hc hr D hD hsol ρ Ψ hΨ
  rw [h2 c r hc hr D hD ρ Ψ hΨ]
  exact hsol _ (h1 c ρ Ψ hΨ)

end UnforcedLeray.Short.IIb
