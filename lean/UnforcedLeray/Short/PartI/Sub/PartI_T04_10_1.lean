import UnforcedLeray.Short.PartI.Sub.PartI_T04_10

/-!
# Part I, `PartI:T04/10/1`: `APLevel3Integrated` split into a qualitative and an energy leaf

Source of record: `the November 2 reference manuscript`, lines 285-288.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec)
open UnforcedLeray.Cyl (Plane)

/-- **Leaf Q3 (qualitative jet bounds)** (lines 285-288, `jet_l2` of `IsAPrioriClass`, `apElliptic`):
for a class solution, `r ↦ ‖D³ω(r)‖²₂`, `r ↦ commJet2 r`, `r ↦ ‖D²ω(r)‖²₂` are integrable on `[0,T]`
(measurability from continuity/joint regularity of the classical solution, plus the uniform bounds
of `jet_l2`; `commJet2` by Hölder from the uniform jet bounds) and `‖D²ω(r)‖²₂` is bounded. -/
def APLevel3Qual : Prop :=
  ∀ (ν c T : ℝ) (v : ℝ → Plane → Vec) (p : ℝ → Plane → ℝ), 0 < ν → 1 ≤ c →
    IsAPrioriClass ν c T v p →
      IntegrableOn (fun r => vortJet c 3 v r) (Icc (0 : ℝ) T) ∧
      IntegrableOn (fun r => commJet2 c v r) (Icc (0 : ℝ) T) ∧
      IntegrableOn (fun r => vortJet c 2 v r) (Icc (0 : ℝ) T) ∧
      (∃ M : ℝ, ∀ r ∈ Icc (0 : ℝ) T, vortJet c 2 v r ≤ M)

/-- **Leaf E3 (integrated energy inequality, cutoff `R → ∞`)** (lines 285-288): given the
qualitative integrability (`APLevel3Qual` conclusions), for `s ∈ [0,T]`,
`‖D²ω(s)‖² + ν ∫_0^s ‖D³ω‖² ≤ 16 ‖D²ω(0)‖² + 4 ∫_0^s commJet2` (operator norms).
Route: the word-sum cutoff energy `G_R(s) = ∫_cell χ_R Σ_{|u|=2} (∂_uω)²` satisfies
`G_R' ≤ -2ν∫χ_R Σ_{|u|=3}(∂_uω)² + commJet2 + O(1/R)` (lines 285-287: `∂_s∂_uω = νΔ∂_uω -
∂_u(v·∇ω)`, transport term `∫χ_R' v_η (∂_uω)²`, commutator `[∂_u, v·∇]ω`); integrate in time,
compare word sums with operator norms (`2^j`), let `R → ∞` (`Sub/PartI_T04_10_1_2.lean`,
`Sub/PartI_T04_10_1_2_1.lean`). -/
def APLevel3Energy : Prop :=
  ∀ (ν c T : ℝ) (v : ℝ → Plane → Vec) (p : ℝ → Plane → ℝ), 0 < ν → 1 ≤ c →
    IsAPrioriClass ν c T v p →
      IntegrableOn (fun r => vortJet c 3 v r) (Icc (0 : ℝ) T) →
      IntegrableOn (fun r => commJet2 c v r) (Icc (0 : ℝ) T) →
      ∀ s ∈ Icc (0 : ℝ) T,
        vortJet c 2 v s + ν * ∫ r in (0 : ℝ)..s, vortJet c 3 v r ≤
          16 * vortJet c 2 v 0 + 4 * ∫ r in (0 : ℝ)..s, commJet2 c v r

theorem apLevel3Integrated_of (hQ : APLevel3Qual) (hE : APLevel3Energy) : APLevel3Integrated := by
  intro ν c T v p hν hc hcls
  obtain ⟨h3, hC, h2, hM⟩ := hQ ν c T v p hν hc hcls
  exact ⟨h3, hC, h2, hM, hE ν c T v p hν hc hcls h3 hC⟩

end UnforcedLeray.Short.PartI
