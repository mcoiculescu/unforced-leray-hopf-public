import UnforcedLeray.Short.PartI.Sub.PartI_C06
import UnforcedLeray.Short.PartI.Tasks.SmallDiffusionAssembly
import UnforcedLeray.Short.PartI.Tasks.SmallDiffusionAssembly.MildCocycle
import UnforcedLeray.Short.PartI.Tasks.CanonicalFixedPoint.MildUnique
import UnforcedLeray.Short.PartI.Tasks.CanonicalFixedPoint.ContStart
import UnforcedLeray.Short.PartI.Tasks.CanonicalFixedPoint.RABound
import UnforcedLeray.Short.PartI.Tasks.CanonicalFixedPoint.RAContinuous
import UnforcedLeray.Short.PartI.Tasks.CanonicalFixedPoint.TailIntegral
import UnforcedLeray.Short.PartI.Tasks.CanonicalFixedPoint.FixedPointIci
import UnforcedLeray.Short.PartI.Tasks.CanonicalFixedPoint.FixedMild
import UnforcedLeray.Short.PartI.Tasks.CanonicalFixedPoint.NormalizedUnique
import UnforcedLeray.Short.PartI.Tasks.CanonicalFixedPoint.AsymptoticBounds

/-!
# Part I, task `PartI:C06`: the canonical branch at infinity (final assembly)

Source of record: `the November 2 reference manuscript`, proof of
Proposition `prop:short-canonical`, lines 1094-1122. The conditional theorem
`canonical_infinity_fixed_point_of` (in `Sub/PartI_C06.lean`) is applied to the
leaf results proved in the sibling files of this folder.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.PartI

/-- Lines 1094-1122: for a seed `(lam, q, l)` with `IsSeedXG`, and the functional `ℓ = ⟨qd, ·⟩`
with `qd ∈ 𝒟(D)`, there is a threshold `b > 0` and a mild solution `V` of the canonical system on
`[b, ∞)` with the asymptotic `e^{-λθ}θ^{-κ}{q + O(θ⁻¹)}`; any other mild solution with the same
asymptotic agrees with `V` on `[b, ∞)`. -/
theorem canonical_infinity_fixed_point {lam : ℂ} {q : B0010.XG} {l : B0010.XG →L[ℂ] ℂ}
    (hI : IsSeedXG lam q l) {qd : B0010.XG} (hl : ∀ f, l f = inner ℂ qd f)
    (hq : q ∈ B0094.D.domain) (hqd : qd ∈ B0094.D.domain) :
    ∃ b > 0, ∃ V : ℝ → B0010.XG, IsCanonicalMild lam q l qd hq hqd b V ∧
      HasCanonicalAsymptotic lam (seedKappa l q hq) q V ∧
      ∀ V' : ℝ → B0010.XG, IsCanonicalMild lam q l qd hq hqd b V' →
        HasCanonicalAsymptotic lam (seedKappa l q hq) q V' → ∀ θ : ℝ, b ≤ θ → V' θ = V θ :=
  canonical_infinity_fixed_point_of smallDiffusionComplement_proof mildComplementCocycle
    mildComplementUnique mildComplementContStart canonicalRABound canonicalRAContinuous
    tailIntegralProps fixedPointIci canonicalFixedMild canonicalNormalizedUnique
    canonicalAsymptoticBounds hI hl hq hqd

end UnforcedLeray.Short.PartI
