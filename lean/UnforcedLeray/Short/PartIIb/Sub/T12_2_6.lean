import UnforcedLeray.Short.PartIIb.Sub.T12_2_5

/-!
# Part II-b, task `PartII-b:T12/2/6` (`SlicePerpPlanar`): sub-lemma Props

Source of record: `the November 2 reference manuscript`, lines 1901-1903 and 1923-1926
(`P_0` applied at each age; `F - P_0F` is a gradient in `(q, η)`). Target: `LerayLiftSub.SlicePerpPlanar`
(`Sub/T12_2.lean`).

Route: `F' = F` a.e. on `s > 0` transfers the `H_r` norm (`HrAeTransfer`), so `F'` and `G` are integrable
on compact subsets of `{s > 0}` (`IntegrableOnCompact`, `IntegrableTestPair` of `Sub/T12_2_5.lean`);
a planar solenoidal test periodized in `q` is a cell solenoidal test (`SlicePerSolTest`); at a fixed age
the unfolding gives the planar orthogonality (`SlicePlanarPerpZero`); Fubini in `s` and `F = F'` a.e. on
`s > 0` (the tests vanish for `s ≤ 0`) give `PerpPlanarSol (F - G)`. No proofs here: each Prop is a task.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb.LerayLiftSub

/-- **Sub-lemma `T12/2/6/1`** (the `H_r` norm only sees `s > 0`, Lebesgue-a.e.). The measure
`hMeas c r = Axi.ageμ c (r/2 - 5/2)` is absolutely continuous with respect to Lebesgue measure
(`qd_ageμ_ac`, `Tasks/HilbertEnergy/QDecomposition.lean`) and lives on `s > 0` (`Axi.ae_ageμ_mem`), so
profiles agreeing Lebesgue-a.e. on `s > 0` have the same `H_r` norm (`eLpNorm_congr_ae`). -/
def HrAeTransfer : Prop :=
  ∀ (c r : ℝ) (F F' : CProf), 0 < c →
    (∀ᵐ x ∂(volume : Measure Coord), 0 < x.1 → F x = F' x) → hNorm c r F' = hNorm c r F

/-- **Sub-lemma `T12/2/6/2`** (periodized planar solenoidal test is a cell solenoidal test;
SP 1923-1926). For a planar solenoidal test `Ψ` (`IsPlanarSolTest`) and an age `s`, the field
`z ↦ (pcellPer c Ψ_i (s, z))_i` is a `CylSolTest c`: each component is a cell test
(`SlicePerCylTest`), and its divergence is the periodization of `∂_qΨ_0 + ∂_ηΨ_1 = 0`
(`SlicePerFDeriv`; the two periodization sums are finitely supported, so they add). -/
def SlicePerSolTest : Prop :=
  ∀ (c : ℝ) (Ψ : Coord → Fin 2 → ℝ), 0 < c → IsPlanarSolTest Ψ → ∀ s : ℝ,
    CylSolTest c (fun z i => pcellPer c (fun x => Ψ x i) (s, z))

/-- **Sub-lemma `T12/2/6/3`** (one age: planar orthogonality from cell orthogonality; SP 1923-1926).
Let `u, w` be exactly periodic strongly measurable cell fields with `∫_cell (u - w)·Ψ = 0` for every
cell solenoidal test (the gradient clause of `IsCylHelmholtz`). For a planar solenoidal test `Ψ` and an
age `s` with each `(u_i - w_i) Ψ_i(s,·)` integrable on the plane, `∫_{ℝ²} (u - w)·Ψ(s,·) = 0`: with the
periodized test of `SlicePerSolTest`, `Cyl.integral_cell_periodize_mul` and
`CellPeriodizeMulIntegrable` give `c ∫ (u - w)·Ψ_per d(avgμ c) = 0`. -/
def SlicePlanarPerpZero : Prop :=
  ∀ (c : ℝ) (u w : ℝ × ℝ → CMerid), 0 < c → StronglyMeasurable u → StronglyMeasurable w →
    (∀ z : ℝ × ℝ, u (z.1 + c, z.2) = u z) → (∀ z : ℝ × ℝ, w (z.1 + c, z.2) = w z) →
    (∀ Ψ : ℝ × ℝ → Fin 2 → ℝ, CylSolTest c Ψ →
        Integrable (fun z => ∑ i : Fin 2, (u z i - w z i) * (Ψ z i : ℂ)) (UnforcedLeray.Cyl.avgμ c) ∧
          ∫ z, ∑ i : Fin 2, (u z i - w z i) * (Ψ z i : ℂ) ∂(UnforcedLeray.Cyl.avgμ c) = 0) →
    ∀ (Ψ : Coord → Fin 2 → ℝ) (s : ℝ), IsPlanarSolTest Ψ →
      (∀ i : Fin 2, Integrable (fun z : ℝ × ℝ => (u z i - w z i) * (Ψ (s, z) i : ℂ))) →
      ∫ z : ℝ × ℝ, ∑ i : Fin 2, (u z i - w z i) * (Ψ (s, z) i : ℂ) = 0

end UnforcedLeray.Short.IIb.LerayLiftSub
