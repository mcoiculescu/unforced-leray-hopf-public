import UnforcedLeray.Short.PartI.StatementsSeed
import UnforcedLeray.Units.B0104
import UnforcedLeray.Units.B0123

/-!
# Part I, module `seed-train/canonical.tex`: the canonical heat branch (statements)

Source of record: `the November 2 reference manuscript`, lines 960-1177
(Lemma `lem:short-compact-duhamel` lines 978-1003; Lemma `lem:short-diffusion-complement`
lines 1005-1058; Proposition `prop:short-canonical` statement 1076-1093, proof 1094-1153;
Corollary `cor:short-mellin` lines 1155-1174).  `Prop`-valued definitions only.

## Reused Lean objects (existing names)

* `B0104.StrongTendstoOnBlocks`, `NormTendstoOnBlocks`, `IsDuhamelEvolution`, `IsDysonSum`,
  `DysonDefined`, `compact_duhamel`, `compact_duhamel_dyson` (`Units/B0104*`): Lemma
  `short-compact-duhamel` is already proved there for an arbitrary complex Hilbert space.
* `B0123.expD a = e^{aD}` on `X_G` (spectral calculus of `B0094.D`), `B0094.D`,
  `B0121.XGj j`, `B0121.fracPow j`, `B0121.graphNormSq j`.
* `Planar.L0`, `IsSeedXG` (`StatementsSeed.lean`), `Blueprint.Planar.quadrupole`
  (`𝔐(f) = ∫₀^∞ r³ f₂(r) dr`).

## Conventions

`L = L₀` is the Euler operator on `X_G`, `Q = I - P`, `P = qℓ`, `κ = ℓ(Dq)` (needs `q ∈ 𝒟(D)`,
supplied by `SeedOscillator`).  "All positive real powers use the real logarithm"
(line 1177): `(θ : ℂ) ^ κ` for `θ > 0` is `exp(κ log θ)`.  `qd` below is the Gaussian adjoint
vector `q†` with `ℓ = ⟨q†, ·⟩` in Lean's inner product (conjugate-linear in the first slot).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Real
open scoped ENNReal ContDiff Topology ComplexConjugate

namespace UnforcedLeray.Short.PartI

/-! ### Lemma `short-compact-duhamel` -/

/-- **Compact Duhamel comparison** (lines 978-1003), in the generality of the source: a complex
Hilbert space `H`, an index set `ι` of auxiliary parameters, and a time length `B`.  Uniformly
bounded free evolutions `F n → F₀` strongly together with their adjoints (uniformly in both times
and the parameter); strongly measurable interactions `A n` converging in operator norm,
uniformly, to `A₀`, a norm-precompact family of compact operators; `U n`, `U₀` the Dyson
(Duhamel iteration) evolutions.  Then `U n → U₀` strongly, the adjoints converge strongly, and
`(U n - F n) - (U₀ - F₀) → 0` in operator norm, uniformly on blocks. -/
def CompactDuhamelLemma (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (ι : Type*) : Prop :=
  ∀ {B : ℝ} {F : ℕ → ι → ℝ → ℝ → H →L[ℂ] H} {F₀ : ι → ℝ → ℝ → H →L[ℂ] H}
    {A : ℕ → ι → ℝ → H →L[ℂ] H} {A₀ : ι → ℝ → H →L[ℂ] H}
    {U : ℕ → ι → ℝ → ℝ → H →L[ℂ] H} {U₀ : ι → ℝ → ℝ → H →L[ℂ] H},
    (∃ M, ∀ n p t s, s ≤ t → t ≤ s + B → ‖F n p t s‖ ≤ M ∧ ‖F₀ p t s‖ ≤ M) →
    B0104.StrongTendstoOnBlocks B F F₀ →
    B0104.StrongTendstoOnBlocks B (fun n p t s => ContinuousLinearMap.adjoint (F n p t s))
      (fun p t s => ContinuousLinearMap.adjoint (F₀ p t s)) →
    (∃ K, ∀ n p r, ‖A n p r‖ ≤ K) →
    (∀ ε > 0, ∀ᶠ n in atTop, ∀ p r, ‖A n p r - A₀ p r‖ < ε) →
    (∀ p r, IsCompactOperator (A₀ p r)) →
    TotallyBounded (range fun q : ι × ℝ => A₀ q.1 q.2) →
    (∀ n, B0104.DysonDefined B (F n) (A n)) → B0104.DysonDefined B F₀ A₀ →
    (∀ n, B0104.IsDysonSum B (F n) (A n) (U n)) → B0104.IsDysonSum B F₀ A₀ U₀ →
      B0104.StrongTendstoOnBlocks B U U₀ ∧
      B0104.StrongTendstoOnBlocks B (fun n p t s => ContinuousLinearMap.adjoint (U n p t s))
        (fun p t s => ContinuousLinearMap.adjoint (U₀ p t s)) ∧
      B0104.NormTendstoOnBlocks B (fun n p t s => U n p t s - F n p t s)
        (fun p t s => U₀ p t s - F₀ p t s)

/-! ### Lemma `short-diffusion-complement` -/

/-- `κ = ℓ(Dq)` (lines 970-975), for `q ∈ 𝒟(D)`. -/
def seedKappa (ℓ : B0010.XG →L[ℂ] ℂ) (q : B0010.XG) (hq : q ∈ B0094.D.domain) : ℂ :=
  ℓ (B0094.D ⟨q, hq⟩)

/-- The bounded finite-rank operator `R_f = -DP - PD + PDP + κP` (lines 1014-1030), with `DP = ℓ(·)Dq`,
`PD = ⟨Dq†, ·⟩ q` (the bounded extension of `P D`), `PDP = κ P`:
`R_f f = -ℓ(f) Dq - ⟨Dq†, f⟩ q + 2κ ℓ(f) q`. -/
def seedRf (ℓ : B0010.XG →L[ℂ] ℂ) (q qd : B0010.XG) (hq : q ∈ B0094.D.domain)
    (hqd : qd ∈ B0094.D.domain) : B0010.XG →L[ℂ] B0010.XG :=
  -(ℓ.smulRight (B0094.D ⟨q, hq⟩)) -
    (innerSL ℂ (B0094.D ⟨qd, hqd⟩)).smulRight q +
    ((2 : ℂ) * seedKappa ℓ q hq) • ℓ.smulRight q

/-- `U` is the forward evolution on `X_G` of `G_β = L - λ - P + β Q(D - κ)Q` (lines 1014-1030): `G_β = βD + B_β`, `B_β(r) = L - λ - P - β(r)κ + β(r) R_f` bounded, and `U(t,s)x` is the mild
solution `U(t,s)x = e^{D∫_s^tβ} x + ∫_s^t e^{D∫_r^tβ} B_β(r) U(r,s) x dr`, strongly continuous,
`U(s,s) = I`. -/
structure IsMildComplementEvolution (lam κ : ℂ) (ℓ : B0010.XG →L[ℂ] ℂ) (q : B0010.XG)
    (Rf : B0010.XG →L[ℂ] B0010.XG) (β : ℝ → ℝ)
    (U : ℝ → ℝ → B0010.XG →L[ℂ] B0010.XG) : Prop where
  self_eq : ∀ s, U s s = 1
  cont : ∀ s (x : B0010.XG), ContinuousOn (fun t => U t s x) (Ici s)
  integrable : ∀ s t, s ≤ t → ∀ x : B0010.XG, IntervalIntegrable
    (fun r => B0123.expD (∫ u in r..t, β u)
      ((Planar.L0 - lam • (1 : B0010.XG →L[ℂ] B0010.XG) - ℓ.smulRight q -
          (β r * κ) • (1 : B0010.XG →L[ℂ] B0010.XG) + (β r : ℂ) • Rf) (U r s x))) volume s t
  duhamel : ∀ s t, s ≤ t → ∀ x : B0010.XG,
    U t s x = B0123.expD (∫ u in s..t, β u) x +
      ∫ r in s..t, B0123.expD (∫ u in r..t, β u)
        ((Planar.L0 - lam • (1 : B0010.XG →L[ℂ] B0010.XG) - ℓ.smulRight q -
          (β r * κ) • (1 : B0010.XG →L[ℂ] B0010.XG) + (β r : ℂ) • Rf) (U r s x))

/-- **Small diffusion on the complementary space** (lines 1005-1058): there are
`β_*, g, C > 0` such that for every measurable `0 ≤ β(t) ≤ β_*` the forward evolution generated by
`Q{L - λ + β(t)(D - κ)}Q` exists on `X_G`, leaves `QX_G = ker ℓ` invariant and has norm at most
`C e^{-g(t-s)}` there, `t ≥ s`. -/
def SmallDiffusionComplement : Prop :=
  ∀ (lam : ℂ) (q : B0010.XG) (ℓ : B0010.XG →L[ℂ] ℂ), IsSeedXG lam q ℓ →
    ∀ (qd : B0010.XG), (∀ f, ℓ f = inner ℂ qd f) →
    ∀ (hq : q ∈ B0094.D.domain) (hqd : qd ∈ B0094.D.domain),
      ∃ βs g C : ℝ, 0 < βs ∧ 0 < g ∧ 0 < C ∧
        ∀ β : ℝ → ℝ, Measurable β → (∀ t, 0 ≤ β t ∧ β t ≤ βs) →
          ∃ U : ℝ → ℝ → B0010.XG →L[ℂ] B0010.XG,
            IsMildComplementEvolution lam (seedKappa ℓ q hq) ℓ q (seedRf ℓ q qd hq hqd) β U ∧
            ∀ s t : ℝ, s ≤ t → ∀ x : B0010.XG, ℓ x = 0 →
              ℓ (U t s x) = 0 ∧ ‖U t s x‖ ≤ C * Real.exp (-(g * (t - s))) * ‖x‖

/-! ### Proposition `short-canonical` -/

/-- `V : (0,∞) → X_G` solves `-V' = (L + θ⁻¹D)V` for `θ > 0`: `V(θ) ∈ 𝒟(D)`, `V` is smooth as an
`X_G`-valued map on `(0,∞)`, and the equation holds in `X_G` (line 1077). -/
structure IsCanonicalSolution (V : ℝ → B0010.XG) : Prop where
  mem_domain : ∀ θ : ℝ, 0 < θ → V θ ∈ B0094.D.domain
  smooth : ContDiffOn ℝ ∞ V (Ioi 0)
  equation : ∀ (θ : ℝ) (hθ : 0 < θ),
    -(deriv V θ) = Planar.L0 (V θ) + ((θ : ℂ)⁻¹) • B0094.D ⟨V θ, mem_domain θ hθ⟩

/-- The normalization at infinity, eq. `short-canonical-asymptotic`:
`V(θ) = e^{-λθ} θ^{-κ}{q + O_{X_G}(θ⁻¹)}` as `θ → ∞`. -/
def HasCanonicalAsymptotic (lam κ : ℂ) (q : B0010.XG) (V : ℝ → B0010.XG) : Prop :=
  ∃ C b : ℝ, 0 < b ∧ ∀ θ : ℝ, b ≤ θ →
    ‖Complex.exp (lam * θ) • (θ : ℂ) ^ κ • V θ - q‖ ≤ C / θ

/-- **The canonical branch** (lines 1076-1093): there is a unique solution `V_can` of
`-V' = (L + θ⁻¹D)V` on `θ > 0` with the asymptotic `e^{-λθ}θ^{-κ}{q + O(θ⁻¹)}`; it is bounded in
`X_G` as `θ ↓ 0` and smooth for positive `θ`; and for each fixed `j`, `θ ≥ b` with `b` large,
`‖e^{λθ}θ^κ V_can(θ)‖_{X_{G,j}} ≤ C_j (1+θ)^{j/2}` (graph norm of `X_{G,j}`). -/
def CanonicalBranch : Prop :=
  ∀ (lam : ℂ) (q : B0010.XG) (ℓ : B0010.XG →L[ℂ] ℂ), IsSeedXG lam q ℓ →
    ∀ hq : q ∈ B0094.D.domain,
      ∃ V : ℝ → B0010.XG,
        IsCanonicalSolution V ∧ HasCanonicalAsymptotic lam (seedKappa ℓ q hq) q V ∧
        (∃ C : ℝ, ∀ θ : ℝ, 0 < θ → θ ≤ 1 → ‖V θ‖ ≤ C) ∧
        (∀ V' : ℝ → B0010.XG, IsCanonicalSolution V' →
          HasCanonicalAsymptotic lam (seedKappa ℓ q hq) q V' → ∀ θ : ℝ, 0 < θ → V' θ = V θ) ∧
        ∀ j : ℕ, ∃ C b : ℝ, 0 < b ∧ ∀ θ : ℝ, b ≤ θ →
          ∃ hj : Complex.exp (lam * θ) • (θ : ℂ) ^ (seedKappa ℓ q hq) • V θ ∈
              (B0121.fracPow j).domain,
            B0121.graphNormSq j ⟨_, hj⟩ ≤ (C * (1 + θ) ^ ((j : ℝ) / 2)) ^ 2

/-! ### Corollary `short-mellin` -/

/-- The Mellin transform `𝒥(μ) = ∫₀^∞ θ^{μ+1/2} 𝔐(V_can(θ)) dθ`, `𝔐(f) = ∫₀^∞ r³ f₂(r) dr`
(line 1157). -/
def mellinJ (V : ℝ → B0010.XG) (μ : ℂ) : ℂ :=
  ∫ θ in Ioi (0 : ℝ), (θ : ℂ) ^ (μ + 1 / 2) * Blueprint.Planar.quadrupole (V θ : ℝ → ℂ)

/-- **Nontrivial full-age output** (lines 1155-1174): with `M_q = 𝔐(q) ≠ 0`, the integral defining
`𝒥(μ)` converges absolutely for `Re μ > -3/2`, `𝒥` is holomorphic there and not identically
zero. -/
def CanonicalMellin : Prop :=
  ∀ (lam : ℂ) (q : B0010.XG) (ℓ : B0010.XG →L[ℂ] ℂ), IsSeedXG lam q ℓ →
    ∀ hq : q ∈ B0094.D.domain, Blueprint.Planar.quadrupole (q : ℝ → ℂ) ≠ 0 →
      ∀ V : ℝ → B0010.XG, IsCanonicalSolution V →
        HasCanonicalAsymptotic lam (seedKappa ℓ q hq) q V →
          (∀ μ : ℂ, -(3 / 2) < μ.re → IntegrableOn
            (fun θ : ℝ => (θ : ℂ) ^ (μ + 1 / 2) * Blueprint.Planar.quadrupole (V θ : ℝ → ℂ))
            (Ioi 0) volume) ∧
          AnalyticOnNhd ℂ (mellinJ V) {μ : ℂ | -(3 / 2) < μ.re} ∧
          ∃ μ : ℂ, -(3 / 2) < μ.re ∧ mellinJ V μ ≠ 0

end UnforcedLeray.Short.PartI
