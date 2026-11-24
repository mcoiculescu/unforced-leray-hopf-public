import UnforcedLeray.Short.PartIIb.Defs
import UnforcedLeray.Lib.Cylinder.Basic

/-!
# Helpers for `PartII-a:N05/2/2/1`: the cylinder heat equation on `ℝ × ℝ²` (local copies)

Verbatim copies of the definitions of `IIb.cylMeas`, `IIb.QPeriodicS`, `IIb.IsSTTestCoord`,
`IIb.cylHeatT`, `IIb.IsCylHeat` and of the statement `IIb.CylHeatMaxReg`
(`Short/PartII-b/Tasks/FlatWindows/Org/FlatGraphOrg.lean`), so that the reduction of
`FlatBodyCutLaplacianLocal` to the cylinder heat estimate compiles independently of the rest of
Part II-b. `cylHeatMaxRegL_of` (in the target file) converts `IIb.CylHeatMaxReg` to
`CylHeatMaxRegL`; the definitions agree definitionally.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIa.FBCLL

open UnforcedLeray.Short.IIb (Coord cpd cdir qShift)

/-- The unweighted cylinder measure `ds × dq/c dη` (`IIb.cylMeas`). -/
def cylMeasL (c : ℝ) : Measure Coord := (volume : Measure ℝ).prod (UnforcedLeray.Cyl.avgμ c)

/-- Scalar `c`-periodicity in `q`, almost everywhere (`IIb.QPeriodicS`). -/
def QPeriodicSL (c : ℝ) (u : Coord → ℂ) : Prop := ∀ᵐ x : Coord, u (qShift c x) = u x

/-- A space-time test on `ℝ × ℝ²` (`IIb.IsSTTestCoord`). -/
structure IsSTTestCoordL (φ : Coord → ℝ) : Prop where
  smooth : ContDiff ℝ ∞ φ
  compact : HasCompactSupport φ

/-- The transpose `-∂_sφ - νΔ_{q,η}φ` (`IIb.cylHeatT`). -/
def cylHeatTL (ν : ℝ) (φ : Coord → ℝ) (x : Coord) : ℝ :=
  -cpd 0 φ x - ν * (cpd 1 (fun y => cpd 1 φ y) x + cpd 2 (fun y => cpd 2 φ y) x)

/-- `(∂_s - νΔ_{q,η}) u = f` in distributions on `ℝ × ℝ²` (`IIb.IsCylHeat`). -/
def IsCylHeatL (ν : ℝ) (u f : Coord → ℂ) : Prop :=
  ∀ φ, IsSTTestCoordL φ → ∫ x, u x * (cylHeatTL ν φ x : ℂ) = ∫ x, f x * (φ x : ℂ)

/-- The cylinder heat estimate (`IIb.CylHeatMaxReg`, proved as `IIb.cylHeatMaxReg`). -/
def CylHeatMaxRegL : Prop :=
  ∀ r : ℝ, 1 < r → ∃ C : ℝ, 0 < C ∧ ∀ ν c : ℝ, 0 < ν → 0 < c → ∀ u f : Coord → ℂ,
    QPeriodicSL c u → QPeriodicSL c f → AEStronglyMeasurable u volume →
    AEStronglyMeasurable f volume → eLpNorm u (ENNReal.ofReal r) (cylMeasL c) < ⊤ →
    eLpNorm f (ENNReal.ofReal r) (cylMeasL c) < ⊤ → IsCylHeatL ν u f →
    ∃ (Dt : Coord → ℂ) (D2 : Fin 2 → Fin 2 → Coord → ℂ),
      (QPeriodicSL c Dt ∧ AEStronglyMeasurable Dt volume) ∧
      (∀ i j, QPeriodicSL c (D2 i j) ∧ AEStronglyMeasurable (D2 i j) volume) ∧
      (∀ φ, IsSTTestCoordL φ → ∫ x, u x * (cpd 0 φ x : ℂ) = -∫ x, Dt x * (φ x : ℂ)) ∧
      (∀ (i j : Fin 2) (φ : Coord → ℝ), IsSTTestCoordL φ →
        ∫ x, u x * (cpd i.succ (fun y => cpd j.succ φ y) x : ℂ) = ∫ x, D2 i j x * (φ x : ℂ)) ∧
      eLpNorm Dt (ENNReal.ofReal r) (cylMeasL c) ≤
        ENNReal.ofReal C * eLpNorm f (ENNReal.ofReal r) (cylMeasL c) ∧
      ∀ i j, eLpNorm (fun x => (ν : ℂ) * D2 i j x) (ENNReal.ofReal r) (cylMeasL c) ≤
        ENNReal.ofReal C * eLpNorm f (ENNReal.ofReal r) (cylMeasL c)

end UnforcedLeray.Short.PartIIa.FBCLL
