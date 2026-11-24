import UnforcedLeray.Short.PartIIb.Tasks.BodyLift
import UnforcedLeray.Short.PartIIb.Tasks.ResponseOperator
import UnforcedLeray.Short.PartIIb.Tasks.RowOrdRel
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.FrozenStream

/-!
# Part II-b, task `PartII-b:P4`: `PhysicalRowReduction` assembly

Source of record: `the November 2 reference manuscript`, lines 2490-2504.

Assembles `bodyLift_iso` (`PartII-b:P1`), `responseTheta` (`PartII-b:P2`), and `row_ordRel`
(`PartII-b:P3`), together with `frozenStreamBounds` (`PartII-b:G4/2`) and
`contDiff_Efun_of_periodicStream` (`RowOrdRel.lean`).

* `physicalRowReduction_of_continuous_Efun`: the exact statement of `PhysicalRowReduction` under
  the continuity hypothesis `∀ i : Fin 2, Continuous (p.Efun i)` required by `row_ordRel`
  (`PartII-b:P3`) to split `pairF` of `L0T p.ν Φ + convT p.raw Φ` in `IsCop` into the sum of
  two `pairF`s in `Params.OrdRel`.
* `physicalRowReduction_of_growingEigenpair`: for any growing eigenpair
  `Blueprint.Planar.IsGrowingEigenpair lam p.mode` and `p.ν ≤ 1`, `frozenStreamBounds` gives
  `ContDiff ℝ ∞ (periodicStream p.mode p.c)`, hence `Continuous (p.Efun i)`, discharging the
  continuity hypothesis automatically.
* `physicalRowReduction_proof`: unconditional proof of `PhysicalRowReduction` (`PartII-b:P4`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.Blueprint UnforcedLeray.PhaseSpace
  UnforcedLeray.B0411 UnforcedLeray.B0412

/-- Assembly of `PartII-b:P1` (`bodyLift_iso`), `PartII-b:P2` (`responseTheta`), and
`PartII-b:P3` (`row_ordRel`) under `∀ i : Fin 2, Continuous (p.Efun i)`. -/
theorem physicalRowReduction_of_continuous_Efun :
    ∀ dm dp : ℝ, 0 < dm → ∃ C : ℝ, 0 < C ∧
      ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.period ≤ 1 →
      (∀ i : Fin 2, Continuous (p.Efun i)) →
      ∀ (Ke : HpR p.c →L[ℝ] HpR p.c) (Ce : E2 →L[ℝ] HpR p.c), IsKop p Ke → IsCop p Ce →
        ∃ (Θ : RowSpace p.c →L[ℝ] p.Z) (J : p.Y →L[ℝ] HpR p.c),
          ‖Θ‖ ≤ C * (Real.pi * p.R ^ 2) ^ (1 / bgp) ∧
          ‖J‖ ≤ ((Real.pi * p.R ^ 2) ^ (1 / bgp))⁻¹ ∧
          (∀ f : p.Y, ∀ᵐ x : ℝ × Space, rep (f : Yq p.period q0E) x.1 x.2 =
            NvC p.R (toProf p.c (J f)) x) ∧
          ∀ (y : RowSpace p.c) (f : p.Y), rowOp Ke Ce y = J f →
            p.OrdRel (Θ y) (f : Yq p.period q0E) := by
  intro dm dp hdm
  obtain ⟨C, hCpos, hResp⟩ := responseTheta dm dp hdm
  refine ⟨C, hCpos, fun p d hreg hp1 hE Ke Ce hK hC => ?_⟩
  obtain ⟨J, hJn, hJrep, -⟩ := bodyLift_iso dm dp hdm p d hreg
  obtain ⟨Θ, hΘn, hΘcoord, -, hΘrep⟩ := hResp p d hreg hp1 Ke Ce hK hC
  refine ⟨Θ, J, hΘn, hJn, hJrep, fun y f hrow => ?_⟩
  exact row_ordRel p d dm dp hreg hE Ke Ce hK hC Θ hΘcoord hΘrep J hJrep y f hrow

/-- When `p.mode` is a growing eigenprofile (`Planar.IsGrowingEigenpair lam p.mode`) and `p.ν ≤ 1`,
`frozenStreamBounds` gives `ContDiff ℝ ∞ (periodicStream p.mode p.c)`, hence `Continuous (p.Efun i)`
for each `i : Fin 2`. -/
theorem continuous_Efun_of_growingEigenpair {p : Params} {d dm dp : ℝ}
    (hreg : BgRegime p d dm dp) (hν1 : p.ν ≤ 1)
    {lam : ℂ} (hq : Planar.IsGrowingEigenpair lam p.mode) (i : Fin 2) :
    Continuous (p.Efun i) := by
  obtain ⟨_, _, _, -, -, hper⟩ := frozenStreamBounds lam p.mode hq 0
  have hνpos : 0 < p.ν := p.ν_pos
  have hc1 : 1 ≤ p.c := by
    rw [hreg.c_eq, one_le_inv₀ (by positivity)]
    nlinarith
  exact (contDiff_Efun_of_periodicStream (hper p.c hc1).1 i).continuous

/-- Assembly of `PhysicalRowReduction` for any growing eigenpair `IsGrowingEigenpair lam p.mode`
with `p.ν ≤ 1` (the setting of `exactInverse_of` in `Compose.lean`). -/
theorem physicalRowReduction_of_growingEigenpair :
    ∀ dm dp : ℝ, 0 < dm → ∃ C : ℝ, 0 < C ∧
      ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.period ≤ 1 → p.ν ≤ 1 →
      ∀ (lam : ℂ), Planar.IsGrowingEigenpair lam p.mode →
      ∀ (Ke : HpR p.c →L[ℝ] HpR p.c) (Ce : E2 →L[ℝ] HpR p.c), IsKop p Ke → IsCop p Ce →
        ∃ (Θ : RowSpace p.c →L[ℝ] p.Z) (J : p.Y →L[ℝ] HpR p.c),
          ‖Θ‖ ≤ C * (Real.pi * p.R ^ 2) ^ (1 / bgp) ∧
          ‖J‖ ≤ ((Real.pi * p.R ^ 2) ^ (1 / bgp))⁻¹ ∧
          (∀ f : p.Y, ∀ᵐ x : ℝ × Space, rep (f : Yq p.period q0E) x.1 x.2 =
            NvC p.R (toProf p.c (J f)) x) ∧
          ∀ (y : RowSpace p.c) (f : p.Y), rowOp Ke Ce y = J f →
            p.OrdRel (Θ y) (f : Yq p.period q0E) := by
  intro dm dp hdm
  obtain ⟨C, hCpos, hPR⟩ := physicalRowReduction_of_continuous_Efun dm dp hdm
  refine ⟨C, hCpos, fun p d hreg hp1 hν1 lam hq Ke Ce hK hC => ?_⟩
  exact hPR p d hreg hp1 (continuous_Efun_of_growingEigenpair hreg hν1 hq) Ke Ce hK hC

/-- Unconditional proof of `PhysicalRowReduction` (`PartII-b:P4`, SP 2048-2049, 2347-2358,
2490-2504). -/
theorem physicalRowReduction_proof : UnforcedLeray.Short.IIb.PhysicalRowReduction :=
  physicalRowReduction_of_growingEigenpair

end UnforcedLeray.Short.IIb

end
