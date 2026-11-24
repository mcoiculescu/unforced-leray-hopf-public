import UnforcedLeray.Units.B0012
import UnforcedLeray.Units.B0123

/-!
# Part I, task `PartI:C02`: the free diffusion-transport evolution (conditional)

Source of record: `the November 2 reference manuscript`, lines 1014-1030
(proof of Lemma `lem:short-diffusion-complement`): the free generator
`T - λ - βκ + βD`, `T = -2iΩ` (line 967) is solved for measurable `0 ≤ β ≤ β_*` by the Dyson
series based on `exp(D ∫β)`; dissipativity of `D` and skew-adjointness of `T` give
`‖F_β(t,s)‖ ≤ exp{-γ(t-s) + |Re κ| β_* (t-s)}`, "first proved for bounded nonpositive Yosida
approximants of `D` and then passed to the strong limit".

## Well-formed reading of the original target


an evolution `F` with `F t t = 1`, strong continuity in `t`, the Duhamel identity based on
`e^{D∫β}` with the bounded interaction `T - λ - β κ` (`T = (-2i) • B0012.omegaOp`, equal to
`Planar.L0 - 2i • kROp`, `B0012.L0 = (-2I)•omegaOp + (2I)•kROp`), and the sharp norm bound.
The Duhamel integrand is recorded as integrable, so that no Lean integral is the junk value `0`
(the same convention as `IsMildComplementEvolution` of `StatementsCanonical.lean`).

## Where the work already is

`Cons/L2/CanonicalBranch/DysonStage.lean` (`canonicalTransportDysonFamily`: the Dyson sum of
`freeDiffusionFamily β` (`UniformComplement.lean`) with `transportDysonPert`) and
`Lib/EvolutionFamilies/Dyson.lean` (`dyson`, `dyson_left`, `dyson_unique`, `hasSum_dyson`,
`norm_dysonTerm_le_of_le`) give existence, strong continuity, the Duhamel identity and uniqueness
for measurable `β`.  `Cons/L2/CanonicalBranch/DysonLimit.lean`
(`canonicalTransportDysonFamily_sharp_norm_le`) gives the sharp bound, but only for `β`
continuous on the block (the Yosida energy estimate there is a classical ODE argument).  The
measurable case is obtained by approximating `β` by continuous `β_k` and passing to the limit
(`FreeDiffusionStability`).

## What this file proves

The four missing facts are the `Prop`s `FreeDiffusionEvolutionExists`,
`FreeDiffusionSharpBoundContinuous`, `FreeDiffusionStability`, `ContinuousApproximation`;
`exists_freeDiffusionEvolution_of` derives the target from them.  The unconditional target is
task `PartI:C02` (`Short/PartI/Tasks/FreeDiffusionEvolution.lean`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray

/-- The bounded interaction `T - λ - β(r) κ` of the free generator
`T - λ - βκ + βD` (source lines 967, 1014-1030), with `T = -2iΩ`
(`(-2 * Complex.I) • B0012.omegaOp`, bounded and skew-adjoint). -/
def freeCoeff (lam kappa : ℂ) (β : ℝ → ℝ) (r : ℝ) : B0010.XG →L[ℂ] B0010.XG :=
  (-2 * Complex.I) • B0012.omegaOp - lam • (1 : B0010.XG →L[ℂ] B0010.XG) -
    ((β r : ℂ) * kappa) • (1 : B0010.XG →L[ℂ] B0010.XG)

/-- `F` is the forward evolution of the free generator `T - λ - βκ + βD` (source lines
1014-1030): `F(t,t) = 1`, `t ↦ F(t,s)x` is continuous on `[s,∞)`, and `F` is the mild solution
`F(t,s)x = e^{D∫_s^tβ} x + ∫_s^t e^{D∫_r^tβ} (T - λ - β(r)κ) F(r,s)x dr` (the Duhamel integrand is
integrable, so the Lean integral is the genuine Bochner integral). -/
structure IsFreeDiffusionEvolution (lam kappa : ℂ) (β : ℝ → ℝ)
    (F : ℝ → ℝ → B0010.XG →L[ℂ] B0010.XG) : Prop where
  self_eq : ∀ t, F t t = 1
  cont : ∀ (x : B0010.XG) (s : ℝ), ContinuousOn (fun t => F t s x) (Ici s)
  integrable : ∀ s t : ℝ, s ≤ t → ∀ x : B0010.XG, IntervalIntegrable
    (fun r => B0123.expD (∫ u in r..t, β u) (freeCoeff lam kappa β r (F r s x))) volume s t
  duhamel : ∀ s t : ℝ, s ≤ t → ∀ x : B0010.XG,
    F t s x = B0123.expD (∫ u in s..t, β u) x +
      ∫ r in s..t, B0123.expD (∫ u in r..t, β u) (freeCoeff lam kappa β r (F r s x))

/-- **Target `PartI:C02`** (well-formed reading; source lines 1014-1030): for every measurable
`0 ≤ β ≤ β_*` the free evolution of `T - λ - βκ + βD` exists and has norm at most
`exp(-Re λ (t-s) + |Re κ| β_* (t-s))`. -/
def FreeDiffusionEvolutionTarget : Prop :=
  ∀ (lam kappa : ℂ) (βs : ℝ) (β : ℝ → ℝ), Measurable β → (∀ t, 0 ≤ β t ∧ β t ≤ βs) →
    ∃ F : ℝ → ℝ → B0010.XG →L[ℂ] B0010.XG, IsFreeDiffusionEvolution lam kappa β F ∧
      ∀ s t : ℝ, s ≤ t →
        ‖F t s‖ ≤ Real.exp (-(lam.re * (t - s)) + |kappa.re| * βs * (t - s))

/-- **Sub-lemma 1 (existence)** (source lines 1019-1021, "the evolution exists for measurable
`β` by the Dyson series based on `exp(D∫β)`"): for measurable `0 ≤ β ≤ β_*` there is an `F` with
`IsFreeDiffusionEvolution`.  Proof: for a block `[a,b]` the Dyson family
`Evolution.dyson (freeDiffusionFamily β ..) (transportDysonPert ((-2I) • omegaOp) lam κ β a b ..)`
of `Cons/L2/CanonicalBranch/DysonStage.lean` is strongly continuous (`U_cont`), satisfies the
Duhamel identity (`dyson_left`, integrable by `intervalIntegrable_dysonU`); take
`F t s := (dyson .. (a := s) (b := t)).U t s` for `s ≤ t` (the Dyson sum does not depend on the
block: `dysonTerm` only uses `F.U` and `A.A`; `dyson_unique` also identifies two blocks). -/
def FreeDiffusionEvolutionExists : Prop :=
  ∀ (lam kappa : ℂ) (βs : ℝ) (β : ℝ → ℝ), Measurable β → (∀ t, 0 ≤ β t ∧ β t ≤ βs) →
    ∃ F : ℝ → ℝ → B0010.XG →L[ℂ] B0010.XG, IsFreeDiffusionEvolution lam kappa β F

/-- **Sub-lemma 2 (sharp bound for continuous `β`)** (source lines 1024-1028): if `β` is
continuous with `0 ≤ β ≤ β_*`, every `F` with `IsFreeDiffusionEvolution` satisfies
`‖F(t,s)‖ ≤ exp(-Re λ (t-s) + |Re κ| β_* (t-s))`.  Proof: on the block `[s,t]` the family `F` is
the Dyson family (`Evolution.dyson_unique` of `Lib/EvolutionFamilies/Dyson.lean`, using `cont` and
`duhamel`), and `canonicalTransportDysonFamily_sharp_norm_le`
(`Cons/L2/CanonicalBranch/DysonLimit.lean`, `δ := β_*`) bounds it; conclude with
`ContinuousLinearMap.opNorm_le_bound`. -/
def FreeDiffusionSharpBoundContinuous : Prop :=
  ∀ (lam kappa : ℂ) (βs : ℝ) (β : ℝ → ℝ), Continuous β → (∀ t, 0 ≤ β t ∧ β t ≤ βs) →
    ∀ F : ℝ → ℝ → B0010.XG →L[ℂ] B0010.XG, IsFreeDiffusionEvolution lam kappa β F →
      ∀ s t : ℝ, s ≤ t →
        ‖F t s‖ ≤ Real.exp (-(lam.re * (t - s)) + |kappa.re| * βs * (t - s))

/-- **Sub-lemma 3 (stability under almost-everywhere convergence of `β`)** (source lines
1031-1049, "the Dyson series give the corresponding strong limits"): if measurable
`β_k, β ∈ [0, β_*]` with `β_k → β` almost everywhere, and `F_k, F` are the free evolutions for
`β_k, β`, then `F_k(t,s)x → F(t,s)x` for every `s ≤ t` and `x`.  Proof: on `[s,t]` both are Dyson
sums (`Evolution.dyson_unique`); `e^{D∫_r^tβ_k} → e^{D∫_r^tβ}` strongly by dominated convergence
for `∫_r^t β_k` and continuity of `a ↦ e^{aD}x` (`B0123.expD`); `freeCoeff β_k r → freeCoeff β r`
in norm for a.e. `r`; hence each Dyson term converges by induction and dominated convergence; the
series converges by `tendsto_tsum_of_dominated_convergence` with the uniform majorant
`norm_dysonTerm_le_of_le` (`M = 1`, `ω = 0`, `C = ‖T‖ + ‖λ‖ + β_*‖κ‖`). -/
def FreeDiffusionStability : Prop :=
  ∀ (lam kappa : ℂ) (βs : ℝ) (βk : ℕ → ℝ → ℝ) (β : ℝ → ℝ)
    (Fk : ℕ → ℝ → ℝ → B0010.XG →L[ℂ] B0010.XG) (F : ℝ → ℝ → B0010.XG →L[ℂ] B0010.XG),
    (∀ k, Measurable (βk k)) → Measurable β →
    (∀ k t, 0 ≤ βk k t ∧ βk k t ≤ βs) → (∀ t, 0 ≤ β t ∧ β t ≤ βs) →
    (∀ᵐ t ∂(volume : Measure ℝ), Tendsto (fun k => βk k t) atTop (𝓝 (β t))) →
    (∀ k, IsFreeDiffusionEvolution lam kappa (βk k) (Fk k)) →
    IsFreeDiffusionEvolution lam kappa β F →
    ∀ s t : ℝ, s ≤ t → ∀ x : B0010.XG, Tendsto (fun k => Fk k t s x) atTop (𝓝 (F t s x))

/-- **Sub-lemma 4 (continuous approximation)**: a measurable `β` with values in `[0, β_*]` is the
almost everywhere limit of continuous functions with values in `[0, β_*]`.  Proof: apply
`MemLp.exists_boundedContinuous_eLpNorm_sub_le` (`p = 1`) on `ℝ` with the finite equivalent
measure `volume.withDensity (ENNReal.ofReal ∘ exp(-t²))` (weakly regular, same null sets as
`volume`), clamp the approximants to `[0, β_*]` by `max 0 (min · β_*)` (continuous, and
`|clamp g - β| ≤ |g - β|`), and extract an almost everywhere convergent subsequence
(`TendstoInMeasure.exists_seq_tendsto_ae`). -/
def ContinuousApproximation : Prop :=
  ∀ (βs : ℝ) (β : ℝ → ℝ), Measurable β → (∀ t, 0 ≤ β t ∧ β t ≤ βs) →
    ∃ βk : ℕ → ℝ → ℝ, (∀ k, Continuous (βk k)) ∧ (∀ k t, 0 ≤ βk k t ∧ βk k t ≤ βs) ∧
      ∀ᵐ t ∂(volume : Measure ℝ), Tendsto (fun k => βk k t) atTop (𝓝 (β t))

/-- **The conditional theorem**: the target follows from the four sub-lemmas.  The `F` is the
existence family `F` (sub-lemma 1); its sharp bound is the limit of the sharp bounds of the
families `F_k` for continuous approximants `β_k` (sub-lemmas 4, 1, 2), which converge
(sub-lemma 3). -/
theorem exists_freeDiffusionEvolution_of
    (h₁ : FreeDiffusionEvolutionExists) (h₂ : FreeDiffusionSharpBoundContinuous)
    (h₃ : FreeDiffusionStability) (h₄ : ContinuousApproximation) :
    FreeDiffusionEvolutionTarget := by
  intro lam kappa βs β hβm hβ
  obtain ⟨F, hF⟩ := h₁ lam kappa βs β hβm hβ
  obtain ⟨βk, hβkc, hβk, hae⟩ := h₄ βs β hβm hβ
  have hex : ∀ k, ∃ Fk : ℝ → ℝ → B0010.XG →L[ℂ] B0010.XG,
      IsFreeDiffusionEvolution lam kappa (βk k) Fk := fun k =>
    h₁ lam kappa βs (βk k) (hβkc k).measurable (hβk k)
  choose Fk hFk using hex
  refine ⟨F, hF, fun s t hst => ?_⟩
  refine ContinuousLinearMap.opNorm_le_bound _ (Real.exp_pos _).le fun x => ?_
  have hlim := h₃ lam kappa βs βk β Fk F (fun k => (hβkc k).measurable) hβm hβk hβ hae hFk hF
    s t hst x
  have hbound : ∀ k, ‖Fk k t s x‖ ≤
      Real.exp (-(lam.re * (t - s)) + |kappa.re| * βs * (t - s)) * ‖x‖ := fun k =>
    ((Fk k t s).le_opNorm x).trans
      (mul_le_mul_of_nonneg_right (h₂ lam kappa βs (βk k) (hβkc k) (hβk k) (Fk k) (hFk k) s t hst)
        (norm_nonneg x))
  exact le_of_tendsto hlim.norm (Eventually.of_forall hbound)

end UnforcedLeray.Short.PartI
