import UnforcedLeray.Short.PartI.Sub.PartI_T04_5
import UnforcedLeray.Short.PartI.Sub.T05b_2
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# `PartI:T04/5/1`: `APEnergyCutoffIneq` from three leaves (source 278-286)

Source `the November 2 reference manuscript`
lines 278-286: testing the momentum equation with `χ_R v` gives, on `(0,T)`,
`F_R' = -2ν∫χ_R|∇v|² - 2ν∫χ_R'⟨v,∂_η v⟩ + ∫ χ_R' v_η|v|² + 2∫ χ_R' p v_η`,
the dissipation having a sign and the three error integrals being `O(R^{-1/2})`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec)
open UnforcedLeray.Cyl (Plane)

/-- Right side of the cutoff energy identity (lines 278-286), single-solution case:
`-2ν∫χ_R|∇v|² - 2ν∫χ_R'⟨v,∂_η v⟩ + ∫ χ_R' v_η |v|² + 2∫ χ_R' p v_η`. -/
def apEnergyRhs (ν c : ℝ) (v : ℝ → Plane → Vec) (p : ℝ → Plane → ℝ) (R s : ℝ) : ℝ :=
  -2 * ν * (∫ z in Cyl.cell c, etaCutoff R z.2 * gradNormSq (v s) z)
    - 2 * ν * (∫ z in Cyl.cell c,
        deriv (etaCutoff R) z.2 * inner ℝ (v s z) (Cyl.partialEta (v s) z))
    + (∫ z in Cyl.cell c, ‖v s z‖ ^ 2 * v s z 1 * deriv (etaCutoff R) z.2)
    + 2 * (∫ z in Cyl.cell c, deriv (etaCutoff R) z.2 * p s z * v s z 1)

/-- **Leaf 1 (continuity)**: `F_R` is continuous on `[0,T]` (jointly continuous integrand supported
in a compact set, `ν c T v p` of the a priori class). -/
def APEnergyContinuous : Prop :=
  ∀ (ν c T : ℝ) (v : ℝ → Plane → Vec) (p : ℝ → Plane → ℝ), 0 < ν → 1 ≤ c →
    IsAPrioriClass ν c T v p → ∀ R : ℝ, 1 ≤ R →
      ContinuousOn (apCutoffEnergy c v R) (Icc 0 T)

/-- **Leaf 2 (derivative identity)**: for `s ∈ (0,T)`, `F_R' = apEnergyRhs` (momentum equation,
`div v = 0`, periodicity in `q`, compact `η`-support of `χ_R`; single-solution analogue of
`CcEnergyHasDeriv`, `CcIntegrandDecomp`, `Cc*Identity` in `Sub/T02_3_11.lean`, no stretching term). -/
def APEnergyHasDeriv : Prop :=
  ∀ (ν c T : ℝ) (v : ℝ → Plane → Vec) (p : ℝ → Plane → ℝ), 0 < ν → 1 ≤ c →
    IsAPrioriClass ν c T v p → ∀ R : ℝ, 1 ≤ R → ∀ s ∈ Ioo (0 : ℝ) T,
      HasDerivAt (apCutoffEnergy c v R) (apEnergyRhs ν c v p R s) s

/-- **Leaf 3 (strip estimate)**: the pressure bound `|p| ≤ M_p` (`classicalPressureBound_of`), the
bounds `hcls.bounded`, `hcls.jet_l2` (`j=0,1`), `|χ_R'| ≤ (C₀/R)1_{R≤|η|≤2R}` and Cauchy-Schwarz on the
strip of measure `≤ 2cR` give `apEnergyRhs ≤ C/√R` (dissipation term has the sign `≤ 0`). -/
def APEnergyRhsEstimate : Prop :=
  ∀ (ν c T : ℝ) (v : ℝ → Plane → Vec) (p : ℝ → Plane → ℝ), 0 < ν → 1 ≤ c →
    IsAPrioriClass ν c T v p → ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 1 ≤ R → ∀ s ∈ Ioo (0 : ℝ) T,
      apEnergyRhs ν c v p R s ≤ C / Real.sqrt R

/-- `APEnergyCutoffIneq` from the three leaves (mean value inequality). -/
theorem apEnergyCutoffIneq_of (h1 : APEnergyContinuous) (h2 : APEnergyHasDeriv)
    (h3 : APEnergyRhsEstimate) : APEnergyCutoffIneq := by
  intro ν c T v p hν hc hcls
  obtain ⟨C, hC0, hC⟩ := h3 ν c T v p hν hc hcls
  refine ⟨T * C, mul_nonneg hcls.pos.le hC0, fun R hR s hs => ?_⟩
  have hRpos : 0 < Real.sqrt R := Real.sqrt_pos.2 (by linarith)
  have hD : ∀ x ∈ interior (Icc (0 : ℝ) T), deriv (apCutoffEnergy c v R) x ≤ C / Real.sqrt R := by
    intro x hx
    rw [interior_Icc] at hx
    rw [(h2 ν c T v p hν hc hcls R hR x hx).deriv]
    exact hC R hR x hx
  have hdiff : DifferentiableOn ℝ (apCutoffEnergy c v R) (interior (Icc (0 : ℝ) T)) := by
    intro x hx
    rw [interior_Icc] at hx
    exact (h2 ν c T v p hν hc hcls R hR x hx).differentiableAt.differentiableWithinAt
  have := (convex_Icc (0 : ℝ) T).image_sub_le_mul_sub_of_deriv_le (h1 ν c T v p hν hc hcls R hR)
    hdiff hD 0 ⟨le_rfl, hcls.pos.le⟩ s hs hs.1
  have h4 : (s - 0) * (C / Real.sqrt R) ≤ T * C / Real.sqrt R := by
    rw [sub_zero, mul_div_assoc]
    exact mul_le_mul_of_nonneg_right hs.2 (div_nonneg hC0 hRpos.le)
  linarith

end UnforcedLeray.Short.PartI
