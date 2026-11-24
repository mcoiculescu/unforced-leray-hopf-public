import UnforcedLeray.Short.PartI.Sub.PartI_T04_5
import UnforcedLeray.Short.PartI.Sub.T05b_2
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# `PartI:T04/6/1`: `APEnstrophyCutoffIneq` from four leaves (source 285-287)

Source `the November 2 reference manuscript`
lines 285-287: testing the scalar vorticity equation `ω_s + v·∇ω = νΔω` with `χ_R ω` gives, on
`(0,T)`, `G_R' = -2ν∫χ_R|∇ω|² - 2ν∫χ_R'ω∂_ηω + ∫χ_R' v_η ω²`; the dissipation has a sign and the
other two integrals are `O(R^{-1/2})`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec)
open UnforcedLeray.Cyl (Plane)

/-- Right side of the cutoff enstrophy identity (lines 285-287), `ω = curl v`:
`-2ν∫χ_R|∇ω|² - 2ν∫χ_R'ω∂_ηω + ∫χ_R' v_η ω²`. -/
def apEnstrophyRhs (ν c : ℝ) (v : ℝ → Plane → Vec) (R s : ℝ) : ℝ :=
  -2 * ν * (∫ z in Cyl.cell c, etaCutoff R z.2 *
      (Cyl.partialQ (Cyl.curl (v s)) z ^ 2 + Cyl.partialEta (Cyl.curl (v s)) z ^ 2))
    - 2 * ν * (∫ z in Cyl.cell c, deriv (etaCutoff R) z.2 * Cyl.curl (v s) z *
        Cyl.partialEta (Cyl.curl (v s)) z)
    + (∫ z in Cyl.cell c, Cyl.curl (v s) z ^ 2 * v s z 1 * deriv (etaCutoff R) z.2)

/-- **Leaf 0 (integrability)**: `ω(s)² ∈ L¹(cell)` for `s ∈ [0,T]`
(`|ω| ≤ 2‖Dv‖` pointwise, `hcls.jet_l2` at `j = 1`, measurability from smoothness). -/
def APEnstrophyIntegrable : Prop :=
  ∀ (ν c T : ℝ) (v : ℝ → Plane → Vec) (p : ℝ → Plane → ℝ), 0 < ν → 1 ≤ c →
    IsAPrioriClass ν c T v p → ∀ s ∈ Icc (0 : ℝ) T,
      IntegrableOn (fun z => (Cyl.curl (v s) z) ^ 2) (Cyl.cell c)

/-- **Leaf 1 (continuity)**: `G_R` is continuous on `[0,T]` (jointly continuous integrand,
`χ_R` compactly supported in `η`; `Tasks/VorticityFirstMoment/CurlRegularity.lean`). -/
def APEnstrophyContinuous : Prop :=
  ∀ (ν c T : ℝ) (v : ℝ → Plane → Vec) (p : ℝ → Plane → ℝ), 0 < ν → 1 ≤ c →
    IsAPrioriClass ν c T v p → ∀ R : ℝ, 1 ≤ R →
      ContinuousOn (apCutoffEnstrophy c v R) (Icc 0 T)

/-- **Leaf 2 (derivative identity)**: for `s ∈ (0,T)`, `G_R' = apEnstrophyRhs`
(`localVorticityEquation`, `div v = 0`, periodicity in `q`, compact `η`-support of `χ_R`;
analogue of `APEnergyHasDeriv` with `ω²` in place of `|v|²`). -/
def APEnstrophyHasDeriv : Prop :=
  ∀ (ν c T : ℝ) (v : ℝ → Plane → Vec) (p : ℝ → Plane → ℝ), 0 < ν → 1 ≤ c →
    IsAPrioriClass ν c T v p → ∀ R : ℝ, 1 ≤ R → ∀ s ∈ Ioo (0 : ℝ) T,
      HasDerivAt (apCutoffEnstrophy c v R) (apEnstrophyRhs ν c v R s) s

/-- **Leaf 3 (strip estimate)**: `|ω| ≤ 2‖Dv‖`, `|∇ω| ≤ 2‖D²v‖`, `hcls.bounded`, `hcls.jet_l2`
(`j = 1, 2`), `|χ_R'| ≤ (C₀/R)1_{R≤|η|≤2R}` and Cauchy-Schwarz on the strip of measure `≤ 2cR`
give `apEnstrophyRhs ≤ C/√R` (dissipation term has the sign `≤ 0`). -/
def APEnstrophyRhsEstimate : Prop :=
  ∀ (ν c T : ℝ) (v : ℝ → Plane → Vec) (p : ℝ → Plane → ℝ), 0 < ν → 1 ≤ c →
    IsAPrioriClass ν c T v p → ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 1 ≤ R → ∀ s ∈ Ioo (0 : ℝ) T,
      apEnstrophyRhs ν c v R s ≤ C / Real.sqrt R

/-- `APEnstrophyCutoffIneq` from the four leaves. -/
theorem apEnstrophyCutoffIneq_of (h0 : APEnstrophyIntegrable) (h1 : APEnstrophyContinuous)
    (h2 : APEnstrophyHasDeriv) (h3 : APEnstrophyRhsEstimate) : APEnstrophyCutoffIneq := by
  intro ν c T v p hν hc hcls
  refine ⟨h0 ν c T v p hν hc hcls, ?_⟩
  obtain ⟨C, hC0, hC⟩ := h3 ν c T v p hν hc hcls
  refine ⟨T * C, mul_nonneg hcls.pos.le hC0, fun R hR s hs => ?_⟩
  have hRpos : 0 < Real.sqrt R := Real.sqrt_pos.2 (by linarith)
  have hD : ∀ x ∈ interior (Icc (0 : ℝ) T), deriv (apCutoffEnstrophy c v R) x ≤ C / Real.sqrt R := by
    intro x hx
    rw [interior_Icc] at hx
    rw [(h2 ν c T v p hν hc hcls R hR x hx).deriv]
    exact hC R hR x hx
  have hdiff : DifferentiableOn ℝ (apCutoffEnstrophy c v R) (interior (Icc (0 : ℝ) T)) := by
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
