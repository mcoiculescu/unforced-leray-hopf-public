import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2.PresCoef

/-!
# Decomposition of `presFlat` (task `PartIII-b:C/rep/8/2/pres/3`)

Source `the November 2 reference manuscript`,
lines 5272-5281, 1205-1225, 5245-5260.  `PresFlatAt` is a measurability clause and a norm bound;
they are separate facts (smoothness of `L.pres`, `liftP` off the axis, versus the Leray-complement
estimate).
-/

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Measurability of the pressure-change density in the ring chart (source 1205-1225: `L.pres` is
smooth by `IsActualLevel.profile`, `liftP` is smooth off the axis; Carathéodory). -/
def PresFlatMeas (D : SeqData) : Prop :=
  ∀ᶠ n : ℕ in atTop,
    AEStronglyMeasurable
      (ringRead (D.level n).ε⁻¹ fun τ => presChgDens ((D.level n).pres τ) (liftP (D.level n) τ))
      (ringPhysμ (D.level n).ε⁻¹ (cOf (D.level n).ν))

/-- The `Y_{11/4}` bound of `∇p - ∇p_lift` in chart form (source 5272-5281 with 5245-5260, 1205-1225:
`∇(p_raw - p_lift) = -(I-ℙ)F_raw`, `‖F_R‖ ≤ P_p ε^{1-2/p}`, the entrance convection terms and the
radial pressure completion, `(I-ℙ)` bounded on `L^{11/4}`). -/
def PresFlatBound (D : SeqData) : Prop :=
  ∃ (C : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop,
    eLpNorm (ringRead (D.level n).ε⁻¹ fun τ => presChgDens ((D.level n).pres τ) (liftP (D.level n) τ))
        (11 / 4) (ringPhysμ (D.level n).ε⁻¹ (cOf (D.level n).ν)) ≤
      ENNReal.ofReal (C * (D.level n).ν⁻¹ ^ k * rhoRep D.K (D.level n))

theorem presFlat_of (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp)
    (h1 : PresFlatMeas D) (h2 : PresFlatBound D) : D.PresFlat := by
  obtain ⟨C, k, hb⟩ := h2
  exact ⟨C, k, (h1.and hb).mono fun n hn => ⟨hn.1, hn.2⟩⟩

end UnforcedLeray.Short.PartIIIb.Concrete
