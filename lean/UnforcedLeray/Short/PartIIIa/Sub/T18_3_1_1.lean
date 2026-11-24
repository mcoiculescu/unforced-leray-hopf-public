import UnforcedLeray.Short.PartIIIa.Sub.T18_3_1

/-!
# Part III-a, task `PartIII-a:T18/3/1/1`: density of compactly `η`-supported divergence-free fields
(conditional)

Target (`Sub/T18_3_1.lean`): `DivFreeCutoffDensity`. Source of record:
`the November 2 reference manuscript`, lines 3541-3552 (the energy identity is used
with the solution itself as test field, which needs the density of the compactly `η`-supported
divergence-free fields in the divergence-free `H¹` class); see also 3427-3440. (The line numbers
3541-3552 of the task sketch carry the causality/uniqueness paragraph; the density argument is the
standard stream-function argument below, which the source uses as a known fact.)

## Mathematics (checked)

Let `φ = (φ₀, φ₁)` be smooth, `c`-periodic in `q`, divergence free (`∂_q φ₀ + ∂_η φ₁ = 0`), with
`φ, ∇φ ∈ L²(cell)` (`cell = [-c/2, c/2) × ℝ`).

**(i) A stream potential.** Let `M(η) = ∫_{-c/2}^{c/2} φ₁(q, η) dq`. Then `M' = ∫ ∂_η φ₁ = -∫ ∂_q φ₀
= 0` (periodicity), `M ∈ L²(ℝ)` (Cauchy-Schwarz), hence `M = 0`. So
`P(q, η) = ∫_{-c/2}^{q} φ₁` is `c`-periodic and `θ = -P + c⁻¹ ∫_{-c/2}^{c/2} P dq` is smooth, periodic,
`∂_q θ = -φ₁`, and (differentiating under the integral, `∂_η φ₁ = -∂_q φ₀`)
`∂_η θ = φ₀ - m(η)`, `m(η) = c⁻¹ ∫ φ₀ dq`. Both `θ` and `∂_η θ` are in `L²(cell)` by Cauchy-Schwarz
in `q` (no Poincaré inequality, no second derivatives, no `m'` needed).

**(ii) The cutoff.** Let `u_k(η) = χ(η/(k+1))` with `χ` a smooth cutoff (`1` on `[-1,1]`, `0` off
`[-2,2]`) and put `φ_k = u_k φ + (u_k' θ, 0)`, i.e. `φ_k = ∇^⊥(u_k θ) + (u_k m, 0)` in the earlier
notation. Then `φ_k` is smooth, `c`-periodic, vanishes for `|η| > 2(k+1)`, and is divergence free:
`∂_q(u_k φ₀ + u_k' θ) + ∂_η(u_k φ₁) = u_k (div φ) + u_k' (∂_q θ + φ₁) = 0`. Moreover
`φ_k - φ = ((u_k - 1) φ₀ + u_k' θ, (u_k - 1) φ₁)` and its derivatives involve only
`(u_k - 1)`, `u_k'`, `u_k''` times `φ, ∇φ, θ, ∂_η θ, ∂_q θ = -φ₁`, so the `H¹(cell)` convergence is
dominated convergence (`|u_k - 1| ≤ 1`, `u_k', u_k''` uniformly bounded and `→ 0` pointwise).

## The cut

* `DfcPotentialExists` (i) is assembled from `DfcQMeanZero`, `DfcPotentialFormulas`,
  `DfcPotentialL2`; these use the calculus facts `DfcQPrimSmooth`, `DfcQPrimDeriv`, `DfcQPeriodic`,
  `DfcQL2` (tasks `PartIII-a:T18/3/1/1/1` ... `/7`).
* `DfcCutoffFromPotential` (ii) is assembled from `DfcScaledExists`, `DfcCutFlat`, `DfcCutConverge`;
  the last two use the product-rule formulas `DfcCutPd` (tasks `/8` ... `/11`).

Proved here: `dfcPotentialExists_of`, `dfcCutoffFromPotential_of`, `divFreeCutoffDensity_of`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-! ## Definitions -/

/-- The `q`-integral over one period: `dfcQInt c f η = ∫_{-c/2}^{c/2} f(t, η) dt`. -/
def dfcQInt (c : ℝ) (f : ℝ × ℝ → ℝ) (η : ℝ) : ℝ := ∫ t in (-(c / 2))..(c / 2), f (t, η)

/-- The `q`-primitive from the left edge of the cell:
`dfcQPrim c f (q, η) = ∫_{-c/2}^{q} f(t, η) dt`. -/
def dfcQPrim (c : ℝ) (f : ℝ × ℝ → ℝ) (x : ℝ × ℝ) : ℝ := ∫ t in (-(c / 2))..x.1, f (t, x.2)

/-- The stream potential of a divergence-free field `φ`:
`θ = -P + c⁻¹ ∫_{-c/2}^{c/2} P dq`, where `P = ∫_{-c/2}^q φ₁` (`φ₁ = φ · 1`, the `η`-component). -/
def dfcPotential (c : ℝ) (φ : ℝ × ℝ → Fin 2 → ℝ) : ℝ × ℝ → ℝ := fun x =>
  -(dfcQPrim c (fun y => φ y 1) x) + c⁻¹ * dfcQInt c (dfcQPrim c (fun y => φ y 1)) x.2

/-- A stream potential `θ` of `φ`: smooth, `c`-periodic in `q`, `∂_q θ = -φ₁`, and `θ, ∂_η θ` in
`L²(cell)`. -/
structure DfcPotential (c : ℝ) (φ : ℝ × ℝ → Fin 2 → ℝ) (θ : ℝ × ℝ → ℝ) : Prop where
  smooth : ContDiff ℝ ∞ θ
  periodic : ∀ x : ℝ × ℝ, θ (x.1 + c, x.2) = θ x
  pd0 : ∀ x : ℝ × ℝ, B0579.pd 0 θ x = -φ x 1
  l2 : MemLp θ 2 (volume.restrict (B0579.cell c))
  l2_pd1 : MemLp (fun x => B0579.pd 1 θ x) 2 (volume.restrict (B0579.cell c))

/-- A family of `η`-cutoffs `u_k` (the abstract interface of `u_k(η) = χ(η/(k+1))` with `χ` a
smooth cutoff, `1` on `[-1,1]`, `0` off `[-2,2]`): smooth, values in `[0,1]`, vanishing together
with the derivative for `|η| > 2(k+1)`, first and second derivatives uniformly bounded, `u_k → 1`
(eventually equal to `1`) and `u_k', u_k'' → 0` pointwise. -/
structure DfcScaled (u : ℕ → ℝ → ℝ) : Prop where
  smooth : ∀ k, ContDiff ℝ ∞ (u k)
  range : ∀ k t, 0 ≤ u k t ∧ u k t ≤ 1
  vanish : ∀ (k : ℕ) (t : ℝ), 2 * ((k : ℝ) + 1) < |t| → u k t = 0 ∧ deriv (u k) t = 0
  bound1 : ∃ C : ℝ, ∀ k t, |deriv (u k) t| ≤ C
  bound2 : ∃ C : ℝ, ∀ k t, |deriv (deriv (u k)) t| ≤ C
  lim_one : ∀ t, ∀ᶠ k in atTop, u k t = 1
  lim_d1 : ∀ t, Tendsto (fun k => deriv (u k) t) atTop (𝓝 0)
  lim_d2 : ∀ t, Tendsto (fun k => deriv (deriv (u k)) t) atTop (𝓝 0)

/-- The cut-off field `φ_k = u_k φ + (u_k' θ, 0)`. -/
def dfcCut (u : ℕ → ℝ → ℝ) (k : ℕ) (φ : ℝ × ℝ → Fin 2 → ℝ) (θ : ℝ × ℝ → ℝ) :
    ℝ × ℝ → Fin 2 → ℝ :=
  fun x => ![u k x.2 * φ x 0 + deriv (u k) x.2 * θ x, u k x.2 * φ x 1]

/-! ## Part (i): the stream potential -/

/-- **Smoothness of `q`-primitives and `q`-integrals** (`PartIII-a:T18/3/1/1/1`). For `f` smooth,
`(q, η) ↦ ∫_{-c/2}^{q} f(t, η) dt` and `η ↦ ∫_{-c/2}^{c/2} f(t, η) dt` are smooth. (Route: substitute
`t = -c/2 + s (q + c/2)`: `dfcQPrim c f (q, η) = (q + c/2) ∫₀¹ f(-c/2 + s (q + c/2), η) ds`, a
parametric integral over the fixed interval `[0,1]` of a family smooth in `(q, η)` with all
derivatives continuous in `(s, q, η)` hence locally uniformly bounded; use
`UnforcedLeray.L09.contDiffOn_integral` in `lean/UnforcedLeray/Loc/L09CompactDatum/ParamIntegral.lean`,
`U = univ`; then `dfcQInt c f η = dfcQPrim c f (c/2, η)`.) -/
def DfcQPrimSmooth : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ f : ℝ × ℝ → ℝ, ContDiff ℝ ∞ f →
    ContDiff ℝ ∞ (dfcQPrim c f) ∧ ContDiff ℝ ∞ (dfcQInt c f)

/-- **Derivatives of `q`-primitives and `q`-integrals** (`PartIII-a:T18/3/1/1/2`). For `f` smooth:
`∂_q ∫_{-c/2}^{q} f = f` (fundamental theorem of calculus), `∂_η ∫_{-c/2}^{q} f = ∫_{-c/2}^{q} ∂_η f`
and `d/dη ∫_{-c/2}^{c/2} f = ∫_{-c/2}^{c/2} ∂_η f` (differentiation under the integral sign). -/
def DfcQPrimDeriv : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ f : ℝ × ℝ → ℝ, ContDiff ℝ ∞ f →
    (∀ x, B0579.pd 0 (dfcQPrim c f) x = f x) ∧
    (∀ x, B0579.pd 1 (dfcQPrim c f) x = ∫ t in (-(c / 2))..x.1, B0579.pd 1 f (t, x.2)) ∧
    (∀ η, deriv (dfcQInt c f) η = dfcQInt c (B0579.pd 1 f) η)

/-- **Periodicity facts** (`PartIII-a:T18/3/1/1/3`). For `f` smooth and `c`-periodic in `q`:
the `q`-integral of `∂_q f` over a period is `0`; and if the `q`-integral of `f` over a period
vanishes for every `η`, then the primitive `∫_{-c/2}^{q} f` is `c`-periodic in `q`. -/
def DfcQPeriodic : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ f : ℝ × ℝ → ℝ, ContDiff ℝ ∞ f → (∀ x, f (x.1 + c, x.2) = f x) →
    (∀ η, dfcQInt c (B0579.pd 0 f) η = 0) ∧
    ((∀ η, dfcQInt c f η = 0) → ∀ x, dfcQPrim c f (x.1 + c, x.2) = dfcQPrim c f x)

/-- **`L²` bounds for `q`-primitives and `q`-integrals** (`PartIII-a:T18/3/1/1/4`). For `f`
continuous with `f ∈ L²(cell)`: `η ↦ ∫_{-c/2}^{c/2} f(t, η) dt` is in `L²(ℝ)` and
`(q, η) ↦ ∫_{-c/2}^{q} f(t, η) dt` is in `L²(cell)` (Cauchy-Schwarz in `q`:
`|∫ f(t, η) dt|² ≤ c ∫ f(t, η)² dt` for the primitive over `[-c/2, q]`, `q` in the cell, and Tonelli
for `∫_ℝ ∫_{cell-q} f² = ‖f‖²_{L²(cell)}`). -/
def DfcQL2 : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ f : ℝ × ℝ → ℝ, Continuous f →
    MemLp f 2 (volume.restrict (B0579.cell c)) →
    MemLp (dfcQInt c f) 2 volume ∧ MemLp (dfcQPrim c f) 2 (volume.restrict (B0579.cell c))

/-- **The `q`-mean of the second component vanishes** (`PartIII-a:T18/3/1/1/5`). For an `H¹`
divergence-free test field the function `M(η) = ∫_{-c/2}^{c/2} φ₁(q, η) dq` is identically `0`.
(`M' = ∫ ∂_η φ₁ = -∫ ∂_q φ₀ = 0` by `DfcQPrimDeriv`, divergence-freeness and `DfcQPeriodic`; so `M`
is constant, and `M ∈ L²(ℝ)` by `DfcQL2`; a constant in `L²(ℝ)` is `0`, `memLp_const_iff`.) -/
def DfcQMeanZero : Prop :=
  ∀ c : ℝ, 0 < c → ∀ φ : ℝ × ℝ → Fin 2 → ℝ, IsH1DivFreeTest c φ →
    ∀ η : ℝ, dfcQInt c (fun x => φ x 1) η = 0

/-- **Calculus of the stream potential** (`PartIII-a:T18/3/1/1/6`). If `M ≡ 0` then
`θ = dfcPotential c φ` is smooth, `c`-periodic in `q`, `∂_q θ = -φ₁` and
`∂_η θ = φ₀ - c⁻¹ ∫_{-c/2}^{c/2} φ₀ dq`. (Smoothness: `DfcQPrimSmooth`; `∂_q`: `DfcQPrimDeriv` and
the second summand is independent of `q`; periodicity: `DfcQPeriodic` (`M ≡ 0`) and the second summand
is independent of `q`; `∂_η`: `∂_η P(q, η) = ∫_{-c/2}^q ∂_η φ₁ = -∫_{-c/2}^q ∂_q φ₀ = -φ₀(q, η) +
φ₀(-c/2, η)` and `d/dη ∫ P dq = ∫ ∂_η P dq = -∫ φ₀ dq + c φ₀(-c/2, η)`.) -/
def DfcPotentialFormulas : Prop :=
  ∀ c : ℝ, 0 < c → ∀ φ : ℝ × ℝ → Fin 2 → ℝ, IsH1DivFreeTest c φ →
    (∀ η, dfcQInt c (fun x => φ x 1) η = 0) →
    ContDiff ℝ ∞ (dfcPotential c φ) ∧
    (∀ x : ℝ × ℝ, dfcPotential c φ (x.1 + c, x.2) = dfcPotential c φ x) ∧
    (∀ x : ℝ × ℝ, B0579.pd 0 (dfcPotential c φ) x = -φ x 1) ∧
    (∀ x : ℝ × ℝ, B0579.pd 1 (dfcPotential c φ) x = φ x 0 - c⁻¹ * dfcQInt c (fun y => φ y 0) x.2)

/-- **`L²` bounds for the stream potential** (`PartIII-a:T18/3/1/1/7`). If `M ≡ 0`, then
`θ = dfcPotential c φ` and `∂_η θ` are in `L²(cell)`. (`DfcQL2` applied to `φ₁`, then to `P`, and to
`φ₀`; a function of `η` alone in `L²(ℝ)` is in `L²(cell)` since `cell = [-c/2, c/2) × ℝ`; use the
formula for `∂_η θ` of `DfcPotentialFormulas`.) -/
def DfcPotentialL2 : Prop :=
  ∀ c : ℝ, 0 < c → ∀ φ : ℝ × ℝ → Fin 2 → ℝ, IsH1DivFreeTest c φ →
    (∀ η, dfcQInt c (fun x => φ x 1) η = 0) →
    MemLp (dfcPotential c φ) 2 (volume.restrict (B0579.cell c)) ∧
    MemLp (fun x => B0579.pd 1 (dfcPotential c φ) x) 2 (volume.restrict (B0579.cell c))

/-- **(i) Existence of a stream potential** for every `H¹` divergence-free test field. -/
def DfcPotentialExists : Prop :=
  ∀ c : ℝ, 0 < c → ∀ φ : ℝ × ℝ → Fin 2 → ℝ, IsH1DivFreeTest c φ → ∃ θ, DfcPotential c φ θ

theorem dfcPotentialExists_of (hD : DfcQMeanZero) (hF : DfcPotentialFormulas)
    (hL : DfcPotentialL2) : DfcPotentialExists := by
  intro c hc φ hφ
  have hq := hD c hc φ hφ
  obtain ⟨h1, h2, h3, _⟩ := hF c hc φ hφ hq
  obtain ⟨h5, h6⟩ := hL c hc φ hφ hq
  exact ⟨dfcPotential c φ, ⟨h1, h2, h3, h5, h6⟩⟩

/-! ## Part (ii): the cutoff -/

/-- **The cutoff family** (`PartIII-a:T18/3/1/1/8`). There is a family `u_k(η) = χ(η/(k+1))`
(`χ` smooth, `0 ≤ χ ≤ 1`, `χ = 1` on `[-1,1]`, `χ = 0` off `[-2,2]`; e.g. `ContDiffBump` with
`rIn = 1`, `rOut = 2` at `0`) satisfying `DfcScaled`. Derivatives: `u_k' (t) = χ'(t/(k+1))/(k+1)`,
`u_k'' (t) = χ''(t/(k+1))/(k+1)²`; `χ', χ''` are continuous with compact support, hence bounded;
`u_k(t) = 1` once `k + 1 ≥ |t|`. -/
def DfcScaledExists : Prop := ∃ u : ℕ → ℝ → ℝ, DfcScaled u

/-- **Product-rule formulas for the cut-off field** (`PartIII-a:T18/3/1/1/9`). For smooth `u_k`,
smooth `φ` (componentwise) and smooth `θ`, the partial derivatives of the two components of
`dfcCut u k φ θ = (u_k φ₀ + u_k' θ, u_k φ₁)` are
`∂_q (·)₀ = u_k ∂_q φ₀ + u_k' ∂_q θ`,
`∂_η (·)₀ = u_k' φ₀ + u_k ∂_η φ₀ + u_k'' θ + u_k' ∂_η θ`,
`∂_q (·)₁ = u_k ∂_q φ₁`, `∂_η (·)₁ = u_k' φ₁ + u_k ∂_η φ₁`
(`u_k, u_k', u_k''` evaluated at `x.2`; they do not depend on `q`). -/
def DfcCutPd : Prop :=
  ∀ (u : ℕ → ℝ → ℝ), (∀ k, ContDiff ℝ ∞ (u k)) →
    ∀ (φ : ℝ × ℝ → Fin 2 → ℝ) (θ : ℝ × ℝ → ℝ), (∀ i, ContDiff ℝ ∞ fun x => φ x i) →
    ContDiff ℝ ∞ θ → ∀ (k : ℕ) (x : ℝ × ℝ),
      B0579.pd 0 (fun y => dfcCut u k φ θ y 0) x =
        u k x.2 * B0579.pd 0 (fun y => φ y 0) x + deriv (u k) x.2 * B0579.pd 0 θ x ∧
      B0579.pd 1 (fun y => dfcCut u k φ θ y 0) x =
        deriv (u k) x.2 * φ x 0 + u k x.2 * B0579.pd 1 (fun y => φ y 0) x +
          deriv (deriv (u k)) x.2 * θ x + deriv (u k) x.2 * B0579.pd 1 θ x ∧
      B0579.pd 0 (fun y => dfcCut u k φ θ y 1) x = u k x.2 * B0579.pd 0 (fun y => φ y 1) x ∧
      B0579.pd 1 (fun y => dfcCut u k φ θ y 1) x =
        deriv (u k) x.2 * φ x 1 + u k x.2 * B0579.pd 1 (fun y => φ y 1) x

/-- **The cut-off fields are spatial flat tests** (`PartIII-a:T18/3/1/1/10`). Smooth (componentwise
products and sums of smooth functions, `deriv (u k)` is smooth), `c`-periodic in `q`, vanishing for
`|η| > 2(k+1)` (`DfcScaled.vanish`) and divergence free: by `DfcCutPd`,
`div = u_k (∂_q φ₀ + ∂_η φ₁) + u_k' (∂_q θ + φ₁) = 0`. -/
def DfcCutFlat : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ (u : ℕ → ℝ → ℝ), DfcScaled u → ∀ (φ : ℝ × ℝ → Fin 2 → ℝ) (θ : ℝ × ℝ → ℝ),
    IsH1DivFreeTest c φ → DfcPotential c φ θ → ∀ k : ℕ, IsFlatSpatialTest c (dfcCut u k φ θ)

/-- **`H¹(cell)` convergence of the cut-off fields** (`PartIII-a:T18/3/1/1/11`). By `DfcCutPd`,
`φ_k - φ = ((u_k - 1) φ₀ + u_k' θ, (u_k - 1) φ₁)` and the derivative differences are
`∂_q: (u_k - 1) ∂_q φ₀ + u_k' ∂_q θ`, `(u_k - 1) ∂_q φ₁`;
`∂_η: u_k' φ₀ + (u_k - 1) ∂_η φ₀ + u_k'' θ + u_k' ∂_η θ`, `u_k' φ₁ + (u_k - 1) ∂_η φ₁`,
with `∂_q θ = -φ₁`. Each term tends to `0` pointwise (`DfcScaled.lim_*`) and the integrand is
dominated by `K (φ² + |∇φ|² + θ² + (∂_η θ)²)` which has finite integral over the cell
(`tendsto_lintegral_of_dominated_convergence`). -/
def DfcCutConverge : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ (u : ℕ → ℝ → ℝ), DfcScaled u → ∀ (φ : ℝ × ℝ → Fin 2 → ℝ) (θ : ℝ × ℝ → ℝ),
    IsH1DivFreeTest c φ → DfcPotential c φ θ →
    Tendsto (fun k => ∫⁻ x in B0579.cell c, ENNReal.ofReal (∑ i : Fin 2,
        ((dfcCut u k φ θ x i - φ x i) ^ 2 +
          ∑ j : Fin 2, (B0579.pd j (fun y => dfcCut u k φ θ y i) x -
            B0579.pd j (fun y => φ y i) x) ^ 2)))
      atTop (𝓝 0)

/-- **(ii) Cutoff approximation** from a stream potential. -/
def DfcCutoffFromPotential : Prop :=
  ∀ c : ℝ, 0 < c → ∀ (φ : ℝ × ℝ → Fin 2 → ℝ) (θ : ℝ × ℝ → ℝ),
    IsH1DivFreeTest c φ → DfcPotential c φ θ →
    ∃ φk : ℕ → ℝ × ℝ → Fin 2 → ℝ, (∀ k, IsFlatSpatialTest c (φk k)) ∧
      Tendsto (fun k => ∫⁻ x in B0579.cell c, ENNReal.ofReal (∑ i : Fin 2,
        ((φk k x i - φ x i) ^ 2 +
          ∑ j : Fin 2, (B0579.pd j (fun y => φk k y i) x - B0579.pd j (fun y => φ y i) x) ^ 2)))
        atTop (𝓝 0)

theorem dfcCutoffFromPotential_of (hF : DfcScaledExists) (hG : DfcCutFlat)
    (hH : DfcCutConverge) : DfcCutoffFromPotential := by
  intro c hc φ θ hφ hθ
  obtain ⟨u, hu⟩ := hF
  exact ⟨fun k => dfcCut u k φ θ, fun k => hG c hc u hu φ θ hφ hθ k,
    hH c hc u hu φ θ hφ hθ⟩

/-- **Reduction**: `DivFreeCutoffDensity` follows from the stream potential (i) and the cutoff (ii). -/
theorem divFreeCutoffDensity_of (hi : DfcPotentialExists) (hii : DfcCutoffFromPotential) :
    DivFreeCutoffDensity := by
  intro c hc φ hφ
  obtain ⟨θ, hθ⟩ := hi c hc φ hφ
  exact hii c hc φ θ hφ hθ

end UnforcedLeray.Short.IIIa
