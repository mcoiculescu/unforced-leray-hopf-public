import UnforcedLeray.Short.PartI.Sub.C03
import UnforcedLeray.Short.PartI.Tasks.ComplementBlockLimit.SharpBoundAll
import UnforcedLeray.Short.PartI.Tasks.ComplementBlockLimit.StrongSmall
import UnforcedLeray.Short.PartI.Tasks.ComplementBlockLimit.AdjointSmall
import UnforcedLeray.Short.PartI.Tasks.ComplementBlockLimit.DysonBridge
import UnforcedLeray.Short.PartI.Tasks.ComplementBlockLimit.FreeEvolutionFamily
import UnforcedLeray.Short.PartI.Tasks.ComplementBlockLimit.ComplementDysonFamily

/-!
# Part I, task `PartI:C03`: final assembly of the block limit of the complementary evolution

Source of record: `the November 2 reference manuscript`, lines 1031-1049
(proof of Lemma `lem:short-diffusion-complement`).

This file discharges the six leaf hypotheses of `complement_block_limit_of` (in `Sub/C03.lean`)
with the leaf theorems `freeSharpBoundAll`, `freeStrongSmall`, `freeAdjointSmall`, `dysonBridge`,
`freeEvolutionFamily` and `complementDysonFamily`.
-/

namespace UnforcedLeray.Short.PartI

open MeasureTheory Set Filter Topology
open scoped InnerProductSpace ComplexConjugate
open UnforcedLeray
open UnforcedLeray.Infra.Dunford (rankOneProj)

/-- **`PartI:C03`** (source lines 1031-1049): the block remainder `(U_β - F_β)(s+B,s)` is uniformly
close to `e^{B(L₀-λ-P)} - e^{B(T-λ)}` for small `β_*`. Assembled from the six leaves. -/
theorem complement_block_limit {lam : ℂ} {q : B0010.XG} {l : B0010.XG →L[ℂ] ℂ} (hI : IsSeedXG lam q l) {qd : B0010.XG} (hl : ∀ f, l f = inner ℂ qd f) (hq : q ∈ B0094.D.domain) (hqd : qd ∈ B0094.D.domain) (B : ℝ) (hB : 0 < B) (ε : ℝ) (hε : 0 < ε) : ∃ βs > 0, ∀ β : ℝ → ℝ, Measurable β → (∀ t, 0 ≤ β t ∧ β t ≤ βs) → ∀ U F : ℝ → ℝ → B0010.XG →L[ℂ] B0010.XG, IsMildComplementEvolution lam (seedKappa l q hq) l q (seedRf l q qd hq hqd) β U → IsFreeDiffusionEvolution lam (seedKappa l q hq) β F → ∀ s : ℝ, ‖(U (s + B) s - F (s + B) s) - (NormedSpace.exp ((B : ℂ) • (Planar.L0 - lam • (1 : B0010.XG →L[ℂ] B0010.XG) - rankOneProj l q)) - NormedSpace.exp ((B : ℂ) • ((-2 * Complex.I) • B0012.omegaOp - lam • (1 : B0010.XG →L[ℂ] B0010.XG))))‖ < ε :=
  complement_block_limit_of freeSharpBoundAll freeStrongSmall freeAdjointSmall dysonBridge
    freeEvolutionFamily complementDysonFamily hI hl hq hqd B hB ε hε

end UnforcedLeray.Short.PartI
