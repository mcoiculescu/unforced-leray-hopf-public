import UnforcedLeray.Short.PartI.Sub.PartI_T04_10_1
import UnforcedLeray.Short.PartI.Sub.T05

/-!
# Part I, `PartI:T04/10/1/2`: the energy leaf `APLevel3Energy` through transverse cutoffs

Source of record: `the November 2 reference manuscript`, lines 285-288
("Approximation and transverse cutoffs then give the velocity and vorticity energy identities").
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec)
open UnforcedLeray.Cyl (Plane)

/-- The transverse-cutoff vorticity jet energy `∫_cell χ_R(η) ‖D^j ω(s)‖²` (lines 285-287). -/
def cutoffVortJet (c : ℝ) (j : ℕ) (v : ℝ → Plane → Vec) (R s : ℝ) : ℝ :=
  ∫ z in Cyl.cell c, etaCutoff R z.2 * ‖iteratedFDeriv ℝ j (Cyl.curl (v s)) z‖ ^ 2

/-- **Leaf A (cutoff energy inequality with vanishing error)** (lines 285-288).  For a class
solution there is `E(R) → 0` such that for `R ≥ 1`, `s ∈ [0,T]`,
`G_R(s) + ν ∫_0^s ∫χ_R|D³ω|² ≤ 16 G_R(0) + 4 ∫_0^s commJet2 + E(R)`, `G_R = cutoffVortJet 2 R`
(operator norms).  The identity of lines 285-287 is the word-sum one: for
`H_R = ∫χ_R Σ_{|u|=2}(∂_uω)²`, `H_R' ≤ -2ν∫χ_R Σ_{|u|=3}(∂_uω)² + commJet2 + C/R`
(`∂_s∂_uω = νΔ∂_uω - ∂_u(v·∇ω)`; viscous term by cell integration by parts against `χ_R`;
transport `∫χ_R' v_η(∂_uω)²`; commutator `|Σ_u 2∂_uω[∂_u,v·∇]ω| ≤ 16|D²ω|(|D²v||Dω| + 2|Dv||D²ω|)`;
cutoff errors `O(1/R)` from `|χ_R'| ≤ C₀/R` and `jet_l2`); integrate in time and compare
`2^{-j}‖D^jω‖² ≤ Σ_{|u|=j}(∂_uω)² ≤ 2^j‖D^jω‖²`.  Decomposed in `Sub/PartI_T04_10_1_2_1.lean`
(`apCutoffIneq_of`). -/
def APCutoffIneq : Prop :=
  ∀ (ν c T : ℝ) (v : ℝ → Plane → Vec) (p : ℝ → Plane → ℝ), 0 < ν → 1 ≤ c →
    IsAPrioriClass ν c T v p →
      IntegrableOn (fun r => vortJet c 3 v r) (Icc (0 : ℝ) T) →
      IntegrableOn (fun r => commJet2 c v r) (Icc (0 : ℝ) T) →
      ∃ E : ℝ → ℝ, Tendsto E atTop (𝓝 0) ∧ ∀ R : ℝ, 1 ≤ R → ∀ s ∈ Icc (0 : ℝ) T,
        cutoffVortJet c 2 v R s + ν * ∫ r in (0 : ℝ)..s, cutoffVortJet c 3 v R r ≤
          16 * cutoffVortJet c 2 v R 0 + 4 * (∫ r in (0 : ℝ)..s, commJet2 c v r) + E R

/-- **Leaf B (`R → ∞`)** (lines 285-288): for a class solution with `r ↦ ‖D³ω(r)‖²₂` integrable on
`[0,T]`, `G_R(s) → ‖D²ω(s)‖²` for `s ∈ [0,T]` (dominated convergence in `z`, `0 ≤ χ_R ≤ 1`,
`χ_R → 1`, `‖D^kω‖² ∈ L¹(cell)` from `jet_l2` and `‖D^k curl v‖ ≤ C‖D^{k+1}v‖`) and
`∫_0^s ∫χ_R|D³ω|² → ∫_0^s ‖D³ω‖²` (dominated convergence in `r`, bound `vortJet 3`). -/
def APCutoffLimit : Prop :=
  ∀ (ν c T : ℝ) (v : ℝ → Plane → Vec) (p : ℝ → Plane → ℝ), 0 < ν → 1 ≤ c →
    IsAPrioriClass ν c T v p →
      IntegrableOn (fun r => vortJet c 3 v r) (Icc (0 : ℝ) T) →
      ∀ s ∈ Icc (0 : ℝ) T,
        Tendsto (fun R => cutoffVortJet c 2 v R s) atTop (𝓝 (vortJet c 2 v s)) ∧
        Tendsto (fun R => cutoffVortJet c 2 v R 0) atTop (𝓝 (vortJet c 2 v 0)) ∧
        Tendsto (fun R => ∫ r in (0 : ℝ)..s, cutoffVortJet c 3 v R r) atTop
          (𝓝 (∫ r in (0 : ℝ)..s, vortJet c 3 v r))

theorem apLevel3Energy_of (hA : APCutoffIneq) (hB : APCutoffLimit) : APLevel3Energy := by
  intro ν c T v p hν hc hcls h3 hC s hs
  obtain ⟨E, hE, hI⟩ := hA ν c T v p hν hc hcls h3 hC
  obtain ⟨t1, t2, t3⟩ := hB ν c T v p hν hc hcls h3 s hs
  have hlim1 : Tendsto (fun R => cutoffVortJet c 2 v R s + ν *
      ∫ r in (0 : ℝ)..s, cutoffVortJet c 3 v R r) atTop
      (𝓝 (vortJet c 2 v s + ν * ∫ r in (0 : ℝ)..s, vortJet c 3 v r)) :=
    t1.add (t3.const_mul _)
  have hlim2 : Tendsto (fun R => 16 * cutoffVortJet c 2 v R 0 +
      4 * (∫ r in (0 : ℝ)..s, commJet2 c v r) + E R)
      atTop (𝓝 (16 * vortJet c 2 v 0 + 4 * ∫ r in (0 : ℝ)..s, commJet2 c v r)) := by
    have h := ((t2.const_mul 16).add
      (tendsto_const_nhds (x := 4 * ∫ r in (0 : ℝ)..s, commJet2 c v r))).add hE
    simpa using h
  exact le_of_tendsto_of_tendsto hlim1 hlim2
    (eventually_atTop.2 ⟨1, fun R hR => hI R hR s hs⟩)

end UnforcedLeray.Short.PartI
