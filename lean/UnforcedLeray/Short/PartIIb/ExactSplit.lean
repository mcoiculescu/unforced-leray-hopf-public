import UnforcedLeray.Short.PartIIb.StatementsNonlinear

/-!
# Part II-b export `ExactSplitII` (SP 2664-2723, `stress-spaces.tex`; SP 2563-2643)

The exact split background of the stress module: `U = V + r_b`, `V = U_raw + E_ε α_bg`, `r_b = w`
the energy repair, with `ρ_b = P_ν ε^{3/11} e^{m₀/ν}` an upper bound for
`sup_τ(‖r_b(τ)‖_{11/4} + ‖r_b(τ)‖_∞)` (SP 2706-2713), and the compact-age inlet support `S_in`
(the inlet columns vanish at ages `s > S_in`, SP 2716).

Everything is over the concrete `Cons.C03.Concrete.Params`, its state space `Params.Z`, and its
concrete fields `Params.raw`, `Params.inlet`, `Params.coord`, `Params.corr`; nothing is a free
predicate.  `ExactSplitExport` is the Part II output used by Part III-a; the bridge from
`BackgroundResult` and `StrongRegularity` is the theorem `exactSplitExport_of`
(task `PartIII-a:T23/7`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete

/-- The repair bound `ρ_b = C₀ ν^{-k₀} e^{m₀/ν} ε^{3/11}` (SP 2706-2713: `P_ν ε^{3/11} e^{m₀/ν}`). -/
def rhoB (p : Params) (m0 C0 : ℝ) (k0 : ℕ) : ℝ :=
  C0 * (p.ν ^ k0)⁻¹ * Real.exp (m0 / p.ν) * p.ε ^ (3 / 11 : ℝ)

/-- **The exact split `(V, r_b)` at level `p`** (SP 2664-2713, with `ρ_b` the repair bound and
`S_in` the compact-age inlet support): there is a solution `z = (w, A)` of the projected equation
(`ProjectedEquation`, SP 2519-2524) with `V = U_raw + E_ε α` (`α = coord z`, `|α_i| ≤ ρ_b`, the
consequence `|α| ≤ P_ν e^{m/ν} ε ≤ ρ_b` of `short-bg:result`), `r_b = w`; the energy repair
satisfies `‖r_b(τ)‖_{11/4} + ‖r_b(τ)‖_∞ ≤ ρ_b` for every phase `τ`; and the inlet columns vanish
at ages `s = R²/ϱ² > S_in` (`ϱ² = y₀² + y₁²`, written without division). -/
structure ExactSplitII (p : Params) (ρb S_in : ℝ) (V rb : ℝ → SpatialField) : Prop where
  state : ∃ z : p.Z, ProjectedEquation p z ∧
    (∀ τ y, V τ y = p.raw τ y + ∑ i : Fin 2, p.coord z i • p.inlet i τ y) ∧
    rb = p.corr z ∧ ∀ i, |p.coord z i| ≤ ρb
  energy : ∀ τ, eLpNorm (rb τ) (ENNReal.ofReal bgp) volume + eLpNorm (rb τ) ⊤ volume ≤
    ENNReal.ofReal ρb
  inlet_support : ∀ (i : Fin 2) (τ : ℝ) (y : Space),
    S_in * (y 0 ^ 2 + y 1 ^ 2) < p.R ^ 2 → p.inlet i τ y = 0

/-- **Part II export** (SP 2563-2643 and 2664-2713): for the growing eigenpair `(λ, q)`
(`Planar.IsGrowingEigenpair`, carried by the level as `p.mode = q`), every `m₀ > 0` and window
`[d₋, d₊]` there is a slow age `Σ₀` such that for every `Σ ≥ Σ₀` (`p.ageCut = Σ`) there are
`C₀, k₀, ν₀` such that at every level of the regime with `ν ≤ ν₀` an exact split exists with
`ρ_b = C₀ ν^{-k₀} e^{m₀/ν} ε^{3/11}`. (The inlet `E_ε` is linear in `p.mode` and depends on `Σ`,
and `Σ` is chosen large from `m`, SP 2337-2342; see the note in `StatementsNonlinear.lean`.)
Proved from `BackgroundResult` and `StrongRegularity` by `exactSplitExport_of` (task
`PartIII-a:T23/7`). -/
def ExactSplitExport : Prop :=
  ∀ (lam : ℂ) (q : Blueprint.Planar.Profile), Blueprint.Planar.IsGrowingEigenpair lam q →
  ∀ m0 : ℝ, 0 < m0 → ∀ dm dp : ℝ, 0 < dm → ∃ Sig₀ : ℝ, 0 < Sig₀ ∧ ∀ Sig : ℝ, Sig₀ ≤ Sig →
    ∃ (C0 : ℝ) (k0 : ℕ) (ν₀ : ℝ), 0 < C0 ∧ 0 < ν₀ ∧
    ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ → p.ageCut = Sig → p.mode = q →
      ∃ S_in V rb, ExactSplitII p (rhoB p m0 C0 k0) S_in V rb

end UnforcedLeray.Short.IIb
