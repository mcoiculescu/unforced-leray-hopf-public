import UnforcedLeray.Short.PartI.Sub.PartI_C10
import UnforcedLeray.Short.PartI.Tasks.CanonicalGraphNorm.WDuhamel
import UnforcedLeray.Short.PartI.Tasks.CanonicalGraphNorm.WZero
import UnforcedLeray.Short.PartI.Tasks.CanonicalGraphNorm.FreeGain
import UnforcedLeray.Short.PartI.Tasks.CanonicalGraphNorm.IntegralGain

/-!
# `PartI:C10`: the derivative budget `‖e^{λθ}θ^κ V_can(θ)‖_{X_{G,j}} ≤ C_j (1+θ)^{j/2}`

Assembly: `wGraphBound_of` applied to the Duhamel identity and continuity (`wDuh_of_canonical`),
the `j = 0` bound (`wGraphBound_zero`), and the one-derivative gains (`freeTermGain`,
`integralTermGain`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartI

open UnforcedLeray UnforcedLeray.B0123

/-- **Derivative budget (C10)**: for the canonical solution `V` of a seed triple, the rescaled
function `θ ↦ e^{λθ} θ^κ V(θ)` with `κ = seedKappa l q hq` satisfies the `X_{G,j}` graph bound with
budget `(1+θ)^{j/2}` for every `j`, for all sufficiently large `θ`. -/
theorem canonical_graphNorm_bounds {lam : ℂ} {q : B0010.XG} {l : B0010.XG →L[ℂ] ℂ}
    (hI : IsSeedXG lam q l) (hq : q ∈ B0094.D.domain) {V : ℝ → B0010.XG} (hV : IsCanonicalSolution V)
    (hA : HasCanonicalAsymptotic lam (seedKappa l q hq) q V) :
    ∀ j : ℕ, ∃ C b : ℝ, 0 < b ∧ ∀ θ : ℝ, b ≤ θ → ∃ hj : Complex.exp (lam * θ) • (θ : ℂ) ^ (seedKappa l q hq) • V θ ∈ (B0121.fracPow j).domain, B0121.graphNormSq j ⟨_, hj⟩ ≤ (C * (1 + θ) ^ ((j : ℝ) / 2)) ^ 2 := by
  obtain ⟨hDuh, hcont⟩ := wDuh_of_canonical (lam := lam) (κ := seedKappa l q hq) hV
  exact wGraphBound_of hDuh hcont (wGraphBound_zero hA)
    (fun j => freeTermGain lam (seedKappa l q hq) j)
    (fun j => integralTermGain lam (seedKappa l q hq) j)

end UnforcedLeray.Short.PartI
