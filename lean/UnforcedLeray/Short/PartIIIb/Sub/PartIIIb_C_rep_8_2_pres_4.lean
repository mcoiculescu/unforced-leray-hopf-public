import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2.PresCoef

/-!
# Decomposition of `coefChg` (task `PartIII-b:C/rep/8/2/pres/4`)

Source `the November 2 reference manuscript`,
5287-5289, 2669, 2697-2713, 5134-5139, 2715-2725, 5007-5008.  `CoefChgAt` has three clauses:
measurability, the `Y_{11/4}` bound of the change, and the pointwise sup bound.
-/

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Measurability of the coefficient-change density in the ring chart (`L.U`, `L.V` smooth off the
axis; source 1217-1222, `IsExactProfile`). -/
def CoefChgMeas (D : SeqData) : Prop :=
  ∀ᶠ n : ℕ in atTop,
    AEStronglyMeasurable
      (ringRead (D.level n).ε⁻¹ fun τ => coefChgDens ((D.level n).U τ) ((D.level n).V τ))
      (ringPhysμ (D.level n).ε⁻¹ (cOf (D.level n).ν))

/-- The `Y_{11/4}` bound of `U - U_raw` and its two derivatives (source 5287-5289, 2669,
2697-2713, 5134-5139: `U - U_raw = r_b + E_εα_bg`, `r_b` from `RepairDerivBound` and
`ExactSplitII.energy` via `phaseAvg_ringChart`, entrance part from the ball bound on `α` and the
inlet columns), together with the pointwise bound `|U| + |U_raw| ≤ C ν⁻ᵏ` at chart points (source
2715-2725: `sup √s W|v| ≤ P_ν`; 5007-5008), with common constants. -/
def CoefChgQuant (D : SeqData) : Prop :=
  ∃ (C : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop,
    eLpNorm (ringRead (D.level n).ε⁻¹ fun τ =>
        coefChgDens ((D.level n).U τ) ((D.level n).V τ)) (11 / 4)
        (ringPhysμ (D.level n).ε⁻¹ (cOf (D.level n).ν)) ≤
      ENNReal.ofReal (C * (D.level n).ν⁻¹ ^ k * rhoRep D.K (D.level n)) ∧
    ∀ p : Chart, 0 < p.1 →
      ‖(D.level n).U (NearInst.chartTau (D.level n).ε⁻¹ p) (NearInst.chartY (D.level n).ε⁻¹ p)‖ +
          ‖(D.level n).V (NearInst.chartTau (D.level n).ε⁻¹ p) (NearInst.chartY (D.level n).ε⁻¹ p)‖ +
          ‖rawU D.Pl (D.level n) (NearInst.chartTau (D.level n).ε⁻¹ p)
            (NearInst.chartY (D.level n).ε⁻¹ p)‖ ≤ C * (D.level n).ν⁻¹ ^ k

theorem coefChg_of (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp)
    (h1 : CoefChgMeas D) (h2 : CoefChgQuant D) : D.CoefChg := by
  obtain ⟨C, k, hb⟩ := h2
  exact ⟨C, k, (h1.and hb).mono fun n hn => ⟨hn.1, hn.2.1, hn.2.2⟩⟩

end UnforcedLeray.Short.PartIIIb.Concrete
