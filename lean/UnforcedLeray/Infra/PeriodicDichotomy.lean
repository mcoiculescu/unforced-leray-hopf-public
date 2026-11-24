import UnforcedLeray.Infra.PeriodicDichotomy.Basic
import UnforcedLeray.Infra.PeriodicDichotomy.Evolution
import UnforcedLeray.Infra.PeriodicDichotomy.Rates
import UnforcedLeray.Infra.PeriodicDichotomy.Volterra

/-!
# Exponential dichotomy of a periodic evolution from a Riesz splitting of the monodromy

Abstract form of `paper/main.tex`, lines 359-404. Let `X` be a complex Banach space and
`E(τ, s)` a `P`-periodic evolution family (`E(s,s) = 1`, `E(τ,r) E(r,s) = E(τ,s)` for
`s ≤ r ≤ τ`, `E(τ + P, s + P) = E(τ, s)`) with monodromy `ℳ = E(P, 0)`, and let the circle
`|z| = r = e^{βP}` lie in the resolvent set of `ℳ` (`PeriodicSplitting`). With
`P₋ = rieszProj ℳ r`, `P₊ = 1 - P₋`, `ℳ₊ = ℳ|_{P₊X}`:

* `F θ = E(θ,0)|_{P₊X}`, `G θ = ℳ₊⁻¹ P₊ E(P,θ)`, `G θ F θ = 1` (`G_comp_F`);
* `Π₊(θ) = F θ G θ`, `Π₋ = 1 - Π₊`, projections with `Π₊(0) = Π₊(P) = P₊`, extended
  `P`-periodically (`piPlus`, `piMinus`);
* intertwining `E(τ,s) Π_±(s) = Π_±(τ) E(τ,s)` for `τ ≥ s`;
* the exterior evolution `E₊(kP + θ, lP + φ) Π₊(φ) = F_θ ℳ₊^{k-l} G_φ` (`extEvol`), a two-sided
  evolution on the ranges of `Π₊`, agreeing with `E` forward in time;
* rates `β₋ < β < β₊`: `‖E(τ,s) Π₋(s)‖ ≤ K e^{β₋(τ-s)}` (`τ ≥ s`) and
  `‖E₊(τ,s) Π₊(s)‖ ≤ K e^{β₊(τ-s)}` (`τ ≤ s`), given a strip bound `‖E(τ,s)‖ ≤ C` for
  `0 ≤ τ - s ≤ P`.

If `P₊X = {0}` all exterior operators vanish and the statements hold as written.

Files: `Basic` (splitting, phase operators), `Evolution` (phases, periodic projections,
intertwining, exterior evolution), `Rates` (exponential bounds), `Volterra` (the Volterra
evolution of `UnforcedLeray.Infra.VolterraEvolution` as a `PeriodicSplitting`, with its strip
bound).

The `X → Z` smoothing bounds of `(loc:eq:past-bound)`/`(loc:eq:future-bound)` (the factor
`(1 + (τ-s)^{-1/2})` and the target space `Z`) and the Green operator `(loc:eq:mixed-inverse)`
are not part of this file.
-/

set_option autoImplicit false

noncomputable section

open Metric Complex Set

namespace UnforcedLeray.Infra.PeriodicDichotomy

namespace PeriodicSplitting

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  (D : PeriodicSplitting X)

/-- **Algebraic part of the periodic dichotomy** (`paper/main.tex`, lines 371-385). -/
theorem periodic_dichotomy_algebra :
    (∀ θ : ℝ, 0 ≤ θ → θ ≤ D.P →
        (D.G θ).comp (D.F θ) = ContinuousLinearMap.id ℂ D.exterior) ∧
      (∀ θ : ℝ, 0 ≤ θ → θ ≤ D.P →
        IsIdempotentElem (D.piPlusPhase θ) ∧ IsIdempotentElem (1 - D.piPlusPhase θ)) ∧
      D.piPlusPhase 0 = D.projPlus ∧ D.piPlusPhase D.P = D.projPlus ∧
      (∀ θ ∈ Ico 0 D.P, D.piPlus θ = D.piPlusPhase θ) ∧
      (∀ t : ℝ, D.piPlus (t + D.P) = D.piPlus t) ∧
      (∀ t : ℝ, IsIdempotentElem (D.piPlus t) ∧ IsIdempotentElem (D.piMinus t)) ∧
      (∀ s τ : ℝ, s ≤ τ → D.E τ s * D.piPlus s = D.piPlus τ * D.E τ s) ∧
      (∀ s τ : ℝ, s ≤ τ → D.E τ s * D.piMinus s = D.piMinus τ * D.E τ s) ∧
      (∀ (k l : ℤ) (θ φ : ℝ), θ ∈ Ico 0 D.P → φ ∈ Ico 0 D.P →
        D.extEvol (k * D.P + θ) (l * D.P + φ) * D.piPlus φ =
          (D.F θ).comp ((D.zpowPlus (k - l)).comp (D.G φ))) ∧
      (∀ τ r s : ℝ, D.extEvol τ r * D.extEvol r s = D.extEvol τ s) ∧
      (∀ τ r s : ℝ, r ≤ τ →
        D.E τ r * (D.extEvol r s * D.piPlus s) = D.extEvol τ s * D.piPlus s) ∧
      (∀ s τ : ℝ, s ≤ τ → D.extEvol τ s * D.piPlus s = D.E τ s * D.piPlus s) := by
  refine ⟨fun θ h0 hP => D.G_comp_F h0 hP,
    fun θ h0 hP => ⟨D.isIdempotentElem_piPlusPhase h0 hP,
      D.isIdempotentElem_one_sub_piPlusPhase h0 hP⟩,
    D.piPlusPhase_zero, D.piPlusPhase_period, fun θ hθ => D.piPlus_of_mem hθ,
    D.piPlus_add_period, fun t => ⟨D.isIdempotentElem_piPlus t, D.isIdempotentElem_piMinus t⟩,
    fun s τ h => D.E_mul_piPlus h, fun s τ h => D.E_mul_piMinus h,
    fun k l θ φ hθ hφ => D.extEvol_intCast_mul_add k l hθ hφ, D.extEvol_mul_extEvol,
    fun τ r s h => D.E_mul_extEvol_mul_piPlus h s,
    fun s τ h => (D.E_mul_piPlus_eq_extEvol_mul_piPlus h).symm⟩

/-- **Rates of the periodic dichotomy** (`paper/main.tex`, lines 361-404, without the `X → Z`
smoothing). If the circle `|z| = e^{βP}` lies in the resolvent set of the monodromy and
`‖E(τ, s)‖ ≤ C` for `0 ≤ τ - s ≤ P`, there are `β₋ < β < β₊` and `K` with
`‖Π_±(t)‖ ≤ K`, `‖E(τ,s) Π₋(s)‖ ≤ K e^{β₋(τ-s)}` for `τ ≥ s` and
`‖E₊(τ,s) Π₊(s)‖ ≤ K e^{β₊(τ-s)}` for `τ ≤ s`. -/
theorem periodic_dichotomy_rates {β : ℝ} (hβ : D.r = Real.exp (β * D.P)) {C : ℝ}
    (hC : ∀ s τ, s ≤ τ → τ ≤ s + D.P → ‖D.E τ s‖ ≤ C) :
    ∃ βm βp K : ℝ, βm < β ∧ β < βp ∧ 0 ≤ K ∧
      (∀ t, ‖D.piPlus t‖ ≤ K) ∧ (∀ t, ‖D.piMinus t‖ ≤ K) ∧
      (∀ s τ, s ≤ τ → ‖D.E τ s * D.piMinus s‖ ≤ K * Real.exp (βm * (τ - s))) ∧
      (∀ s τ, τ ≤ s → ‖D.extEvol τ s * D.piPlus s‖ ≤ K * Real.exp (βp * (τ - s))) := by
  have hlog : Real.log D.r / D.P = β := by
    rw [hβ, Real.log_exp, mul_div_assoc, div_self D.P_pos.ne', mul_one]
  obtain ⟨βm, βp, K, h1, h2, h3⟩ := D.exists_dichotomy_rates hC
  rw [hlog] at h1 h2
  exact ⟨βm, βp, K, h1, h2, h3⟩

end PeriodicSplitting

end UnforcedLeray.Infra.PeriodicDichotomy
