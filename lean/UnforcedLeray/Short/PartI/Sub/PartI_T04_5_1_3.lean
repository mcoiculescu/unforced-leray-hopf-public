import UnforcedLeray.Short.PartI.Sub.PartI_T04_5_1

/-!
# `PartI:T04/5/1/3`: `APEnergyRhsEstimate` from four term estimates (source 278-286)

Source `the November 2 reference manuscript`
lines 278-286: in the cutoff energy identity the dissipation `-2ν∫χ_R|∇v|²` has a sign and the
three error integrals (cross term, transport, pressure) are `O(R^{-1/2})`, using
`|χ_R'| ≤ (C₀/R)1_{R≤|η|≤2R}`, `|v|,|Dv| ≤ B`, the pressure bound and `jet_l2`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec)
open UnforcedLeray.Cyl (Plane)

/-- **Leaf 1 (dissipation sign)**: `∫_cell χ_R |∇v|² ≥ 0` (`χ_R ≥ 0`, `gradNormSq ≥ 0`). -/
def APEnergyDissipationSign : Prop :=
  ∀ (ν c T : ℝ) (v : ℝ → Plane → Vec) (p : ℝ → Plane → ℝ), 0 < ν → 1 ≤ c →
    IsAPrioriClass ν c T v p → ∀ R : ℝ, 1 ≤ R → ∀ s : ℝ,
      0 ≤ ∫ z in Cyl.cell c, etaCutoff R z.2 * gradNormSq (v s) z

/-- **Leaf 2 (cross term)**: `|∫ χ_R' ⟨v, ∂_η v⟩| ≤ C/√R` (strip `R ≤ |η| ≤ 2R` of cell measure
`≤ 2cR`, `|χ_R'| ≤ C₀/R`, Cauchy-Schwarz with `hcls.jet_l2` at `j = 0, 1`). -/
def APEnergyCrossEstimate : Prop :=
  ∀ (ν c T : ℝ) (v : ℝ → Plane → Vec) (p : ℝ → Plane → ℝ), 0 < ν → 1 ≤ c →
    IsAPrioriClass ν c T v p → ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 1 ≤ R → ∀ s ∈ Ioo (0 : ℝ) T,
      |∫ z in Cyl.cell c, deriv (etaCutoff R) z.2 * inner ℝ (v s z) (Cyl.partialEta (v s) z)|
        ≤ C / Real.sqrt R

/-- **Leaf 3 (transport term)**: `|∫ |v|² v_η χ_R'| ≤ C/√R` (`|v| ≤ B` by `hcls.bounded`, `|v|²`
integrable by `jet_l2` at `j = 0`, `|χ_R'| ≤ C₀/R` on the strip). -/
def APEnergyTransportEstimate : Prop :=
  ∀ (ν c T : ℝ) (v : ℝ → Plane → Vec) (p : ℝ → Plane → ℝ), 0 < ν → 1 ≤ c →
    IsAPrioriClass ν c T v p → ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 1 ≤ R → ∀ s ∈ Ioo (0 : ℝ) T,
      |∫ z in Cyl.cell c, ‖v s z‖ ^ 2 * v s z 1 * deriv (etaCutoff R) z.2| ≤ C / Real.sqrt R

/-- **Leaf 4 (pressure term)**: `|∫ χ_R' p v_η| ≤ C/√R` (pressure bound `|p| ≤ M_p` on `[0,T]`
from `classicalPressureBound_of` as in `Sub/T04/Compose.lean`; then as the transport term). -/
def APEnergyPressureEstimate : Prop :=
  ∀ (ν c T : ℝ) (v : ℝ → Plane → Vec) (p : ℝ → Plane → ℝ), 0 < ν → 1 ≤ c →
    IsAPrioriClass ν c T v p → ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 1 ≤ R → ∀ s ∈ Ioo (0 : ℝ) T,
      |∫ z in Cyl.cell c, deriv (etaCutoff R) z.2 * p s z * v s z 1| ≤ C / Real.sqrt R

/-- `APEnergyRhsEstimate` from the four term estimates. -/
theorem apEnergyRhsEstimate_of (h1 : APEnergyDissipationSign) (h2 : APEnergyCrossEstimate)
    (h3 : APEnergyTransportEstimate) (h4 : APEnergyPressureEstimate) : APEnergyRhsEstimate := by
  intro ν c T v p hν hc hcls
  obtain ⟨C2, hC2, e2⟩ := h2 ν c T v p hν hc hcls
  obtain ⟨C3, hC3, e3⟩ := h3 ν c T v p hν hc hcls
  obtain ⟨C4, hC4, e4⟩ := h4 ν c T v p hν hc hcls
  refine ⟨2 * ν * C2 + C3 + 2 * C4, by positivity, fun R hR s hs => ?_⟩
  have hs0 : 0 < Real.sqrt R := Real.sqrt_pos.2 (by linarith)
  have d := h1 ν c T v p hν hc hcls R hR s
  have a2 := abs_le.1 (e2 R hR s hs)
  have a3 := abs_le.1 (e3 R hR s hs)
  have a4 := abs_le.1 (e4 R hR s hs)
  unfold apEnergyRhs
  have key : (2 * ν * C2 + C3 + 2 * C4) / Real.sqrt R =
      2 * ν * (C2 / Real.sqrt R) + C3 / Real.sqrt R + 2 * (C4 / Real.sqrt R) := by ring
  rw [key]
  nlinarith [a2.1, a2.2, a3.1, a3.2, a4.1, a4.2, d]

end UnforcedLeray.Short.PartI
