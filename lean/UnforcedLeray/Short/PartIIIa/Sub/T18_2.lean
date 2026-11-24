import UnforcedLeray.Short.PartIIIa.Sub.T18

/-!
# Part III-a, task `PartIII-a:T18/2`: existence for the free causal solver (conditional)

Target (`Sub/T18.lean`): `FreeCausalExistence`. For `P` a planar reference, `K ⋐ {0 < Re μ < 1/4}`,
`ν ≤ ν₀`, `μ ∈ K` and every symmetric measurable `F` with `‖g⁻¹F‖_𝒯 < ∞`, there is a causal
zero-entrance energy solution `(b, G)` of the free equation with force `F`.
Source of record: `the November 2 reference manuscript`, lines 3427-3440 (the free
instance of the zero-entrance construction, "start from zero at `s = δ`, let `δ ↓ 0`") and 3541-3552
(energy class, the homogeneous difference).

## Mathematical proof and the cut into six statements


Duhamel and no periodic-cell weighted solve. The proof used here is

1. (approximation, `NiceForceApprox`) the force `F` is the `𝒯`-limit (in the gain-conjugated norm)
   of smooth periodic symmetric forces `F^k` compactly supported in `s ∈ [a_k, B_k]`, `|η| ≤ R_k`
   (truncate in `s`, `η` by dominated convergence, periodize in `q`, mollify);
2. (classical solve, `NiceForceSolution`) for a nice force the Duhamel formula
   `b(s) = ∫_a^s (t/s)^μ e^{ν(s-t)Δ} 𝒫₀ div F(t) dt` (`b = 0` for `s ≤ a`) is a causal zero-entrance
   energy solution: this is the periodic-cell heat semigroup `Lib/HeatCylinder/*` and the cylinder
   Leray projector `Lib/CylinderB/Leray.lean`, `Lib/LerayC/*`;
3. (a priori bound, `FreeCausalEnergyBound`, task `T18/3`, and linearity `CausalSolSub`, task `T18/1`)
   the differences `b_k - b_l` solve the equation with force `F^k - F^l`, hence
   `‖g⁻¹(b_k - b_l)‖_𝓗 ≤ A‖g⁻¹(F^k - F^l)‖_𝒯` and `‖g⁻¹(G_k - G_l)‖_𝒯 ≤ A'‖g⁻¹(F^k - F^l)‖_𝒯`
   (`A = (2√(k_*ν))⁻¹`, `A' = ν⁻¹`): the sequence is Cauchy;
4. (limit, `CausalLimitAE`) the `L²` limit `(b, G)` solves the equation with force `F` in the energy
   class except that `divFree`, `weakGrad` hold only for a.e. `s` (`IsCausalEnergySolutionAE`);
5. (null set, `CausalNullModification`) redefining `(b, G) := 0` on a measurable null set of `s`
   gives the class with `divFree`, `weakGrad` for every `s > 0`.

Proved here: `freeCausalExistence_of` (steps 3 and the wiring of 1, 2, 4, 5), from the five Props
`CausalSolSub`, `FreeCausalEnergyBound` (both in `Sub/T18.lean`), `NiceForceApprox`,
`NiceForceSolution`, `CausalLimitAE`, `CausalNullModification` (this file).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- **Nice forces**: symmetric `ℂ`-valued tensor fields on `ℝ × ℝ²`, jointly smooth in `(s, q, η)`,
`c`-periodic in `q`, vanishing for `s ∉ [a, B]` (with `a > 0`) and for `|η| > R`. For such a force
the Duhamel formula gives a classical solution (SP 3427-3440, "start from zero at `s = δ`"). -/
def NiceForce (c : ℝ) (F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ) : Prop :=
  (∀ p i j, F p i j = F p j i) ∧
  (∀ i j, ContDiff ℝ ∞ fun p : ℝ × (ℝ × ℝ) => F p i j) ∧
  (∀ s x i j, F (s, (x.1 + c, x.2)) i j = F (s, x) i j) ∧
  ∃ a B R : ℝ, 0 < a ∧ ∀ s x i j, (s < a ∨ B < s ∨ R < |x.2|) → F (s, x) i j = 0

/-- **Density of nice forces** (`PartIII-a:T18/2/3`; SP 3427-3440, "let `δ → 0`"). For `c, ν > 0`,
any real `γ` and every symmetric measurable `F` with `‖g⁻¹F‖_𝒯 < ∞` (`g = gainG γ ν`), there are
nice forces `F^k → F` in the gain-conjugated `𝒯` norm. The weight `s^{-1/2} g(s)^{-2}` is bounded
above and below on every compact subinterval of `(0,∞)`, and `g` is bounded above and below on
`(0,∞)` (`g ∈ [min(1,e^{γ/ν}), max(1,e^{γ/ν})]`), so this is density of smooth periodic compactly
supported (in `s` and `η`) fields in a weighted `L²`. -/
def NiceForceApprox : Prop :=
  ∀ (c ν γ : ℝ), 0 < c → 0 < ν →
    ∀ F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ, (∀ p i j, F p i j = F p j i) →
      (∀ i j, Measurable fun p => F p i j) →
      tCalNorm c (gainConj γ ν F) < ⊤ →
      ∃ Fk : ℕ → ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ, (∀ k, NiceForce c (Fk k)) ∧
        Tendsto (fun k => tCalNorm c (gainConj γ ν (fun p i j => Fk k p i j - F p i j)))
          atTop (𝓝 0)

/-- **Classical solve for nice forces** (`PartIII-a:T18/2/4`; SP 3427-3440). For `c, ν > 0`, any
`μ ∈ ℂ` and every nice force `F` (which vanishes for `s < a`, `a > 0`), the free equation
`b_s + (μ/s) b - νΔb = 𝒫₀ div F` has a causal zero-entrance energy solution, namely
`b(s) = ∫_a^s (t/s)^μ e^{ν(s-t)Δ} 𝒫₀ div F(t) dt` (`b = 0` for `s ≤ a`, so `zeroEntrance` is
trivial; for `s > a` the coefficient `μ/s` is bounded and `F` is smooth so `b(s)` is smooth). -/
def NiceForceSolution : Prop :=
  ∀ (c ν : ℝ) (μ : ℂ), 0 < c → 0 < ν →
    ∀ F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ, NiceForce c F →
      ∃ b G, IsCausalEnergySolution c ν μ (fun _ _ _ => 0) F b G

/-- The causal energy class with `divFree` and `weakGrad` required only for almost every age `s`
(the class that is closed under `L²` limits; `IsCausalEnergySolution` is recovered by redefining
`(b, G) := 0` on a null set of ages, `CausalNullModification`). All other clauses are as in
`IsCausalEnergySolution`. -/
structure IsCausalEnergySolutionAE (c ν : ℝ) (μ : ℂ) (vel : ℝ → ℝ × ℝ → Fin 2 → ℝ)
    (F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ) (b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ)
    (G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ) : Prop where
  measurable : ∀ i, Measurable fun p => b p i
  gradMeasurable : ∀ i j, Measurable fun p => G p i j
  energyLoc : ∀ s₁ s₂ : ℝ, 0 < s₁ → s₁ < s₂ →
    ∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c, ENNReal.ofReal (vnorm2 (b p) ^ 2 + tnorm2 (G p) ^ 2) < ⊤
  zeroEntrance : ∃ δ : ℝ, 0 < δ ∧ ∫⁻ p, ENNReal.ofReal (vnorm2 (b p) ^ 2)
    ∂((ageμ c (-3 / 2)).restrict (Ioo 0 δ ×ˢ univ)) < ⊤
  divFreeAE : ∀ᵐ s ∂(volume : Measure ℝ), 0 < s → ∀ ψ, B0579.IsCylTest c ψ →
    ∫ x in B0579.cell c, (b (s, x) 0 * (B0579.pd 0 ψ x : ℂ) + b (s, x) 1 * (B0579.pd 1 ψ x : ℂ)) = 0
  weakGradAE : ∀ᵐ s ∂(volume : Measure ℝ), 0 < s → ∀ i j,
    HasWeakCellDerivC c j (fun x => b (s, x) i) (fun x => G (s, x) i j)
  integrable : ∀ Φ, IsFlatTest c Φ →
    IntegrableOn (flatIntegrand ν μ vel F b Φ) (Ioi (0 : ℝ) ×ˢ B0579.cell c)
  weak : ∀ Φ, IsFlatTest c Φ →
    ∫ p in Ioi (0 : ℝ) ×ˢ B0579.cell c, flatIntegrand ν μ vel F b Φ p = 0

/-- **`L²` limit of causal solutions** (`PartIII-a:T18/2/1`; SP 3427-3440, "let `δ → 0`"). Let
`c, ν > 0`, `γ, μ`, `F` measurable with `‖g⁻¹F‖_𝒯 < ∞`, forces `Fn` (measurable) converging to `F`
in the gain-conjugated `𝒯` norm, and causal zero-entrance energy solutions `(bn, Gn)` of the free
equation with forces `Fn`, such that whenever `‖g⁻¹(Fn n - Fn m)‖_𝒯 < ∞` the differences satisfy the
a priori bounds `‖g⁻¹(bn n - bn m)‖_𝓗 ≤ A‖g⁻¹(Fn n - Fn m)‖_𝒯` and
`‖g⁻¹(Gn n - Gn m)‖_𝒯 ≤ A'‖g⁻¹(Fn n - Fn m)‖_𝒯` (these hold in the application by
`CausalSolSub` and `FreeCausalEnergyBound`). Then `(bn, Gn)` is Cauchy in the weighted norms
(`‖Fn n - Fn m‖ ≤ ‖Fn n - F‖ + ‖F - Fn m‖`, finite for `n, m` large), the `L²` limit `(b, G)` (take
a.e. limits along a subsequence; `g` is bounded above and below, so the weighted norms control the
unweighted ones on `[s₁, s₂] × cell`) is measurable and solves the free equation with force `F` in the
class `IsCausalEnergySolutionAE`: `energyLoc` from the weighted bounds (weights `s^{-3/2}`,
`s^{-1/2}` bounded on `[s₁, s₂]`), `zeroEntrance` from `b - bn N ∈ 𝓗` (`|x| ≤ g|g⁻¹x|`) and the
`zeroEntrance` of `bn N`, `divFreeAE`/`weakGradAE` for the a.e. `s` where `bn n (s) → b(s)` and
`Gn n (s) → G(s)` in `L²(cell)` along the subsequence (the test functions `ψ` have compact
`η`-support, so `∂ψ ∈ L²(cell)`), `integrable` and `weak` by passing to the limit with
Cauchy-Schwarz (`flatIntegrand` is linear in `(F, b)`, the test `Φ` is bounded with compact support in
`s ∈ [s₁, s₂]` and `|η| ≤ R`, and `|μ/s| ≤ |μ|/s₁`). -/
def CausalLimitAE : Prop :=
  ∀ (c ν γ : ℝ) (μ : ℂ), 0 < c → 0 < ν →
    ∀ F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ, (∀ i j, Measurable fun p => F p i j) →
      tCalNorm c (gainConj γ ν F) < ⊤ →
      ∀ (Fn : ℕ → ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ) (bn : ℕ → ℝ × (ℝ × ℝ) → Fin 2 → ℂ)
        (Gn : ℕ → ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ) (A A' : ℝ),
        (∀ n i j, Measurable fun p => Fn n p i j) →
        (∀ n, IsCausalEnergySolution c ν μ (fun _ _ _ => 0) (Fn n) (bn n) (Gn n)) →
        (∀ n m, tCalNorm c (gainConj γ ν (fun p i j => Fn n p i j - Fn m p i j)) < ⊤ →
          hCalNorm c (gainConj γ ν (fun p i => bn n p i - bn m p i)) ≤
              ENNReal.ofReal A *
                tCalNorm c (gainConj γ ν (fun p i j => Fn n p i j - Fn m p i j)) ∧
          tCalNorm c (gainConj γ ν (fun p i j => Gn n p i j - Gn m p i j)) ≤
              ENNReal.ofReal A' *
                tCalNorm c (gainConj γ ν (fun p i j => Fn n p i j - Fn m p i j))) →
        Tendsto (fun n => tCalNorm c (gainConj γ ν (fun p i j => Fn n p i j - F p i j)))
          atTop (𝓝 0) →
        ∃ b G, IsCausalEnergySolutionAE c ν μ (fun _ _ _ => 0) F b G

/-- **Null-set redefinition** (`PartIII-a:T18/2/2`; the class requires `divFree` and `weakGrad` for
EVERY `s > 0`). If `(b, G)` is in the a.e. class, let `N` be a measurable null set of ages containing
the bad ages (`exists_measurable_superset_of_null`) and put `b' p = 0`, `G' p = 0` when `p.1 ∈ N`,
`(b', G') = (b, G)` otherwise. The zero slice is divergence free with weak gradient `0`; the set
`{p | p.1 ∈ N}` is null for Lebesgue measure and for `ageμ c (-3/2)` (Fubini / product measure), so
`b' = b`, `G' = G` a.e. and the lintegral/integral clauses (`energyLoc`, `zeroEntrance`,
`integrable`, `weak`) are unchanged. -/
def CausalNullModification : Prop :=
  ∀ (c ν : ℝ) (μ : ℂ) (vel : ℝ → ℝ × ℝ → Fin 2 → ℝ), 0 < c →
    ∀ (F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ) (b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ)
      (G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ),
      IsCausalEnergySolutionAE c ν μ vel F b G →
        ∃ b' G', IsCausalEnergySolution c ν μ vel F b' G'

/-- **Existence from the five facts** (assembly; SP 3427-3440). Approximate `F` by nice forces
`F^k`, solve classically (`hNice`), bound the differences by linearity (`hLin`) and the free energy
bound (`hBd`), pass to the limit (`hLim`) and remove the null set of ages (`hNull`). -/
theorem freeCausalExistence_of (hLin : CausalSolSub) (hBd : FreeCausalEnergyBound)
    (hApp : NiceForceApprox) (hNice : NiceForceSolution) (hLim : CausalLimitAE)
    (hNull : CausalNullModification) : FreeCausalExistence := by
  intro P hP K hK
  obtain ⟨ν₀, hν₀, hbd⟩ := hBd P hP K hK
  refine ⟨ν₀, hν₀, fun ν hν μ hμ F hsym hmeas hfin => ?_⟩
  have hνpos : 0 < ν := hν.1
  have hc : 0 < ν ^ (-2 : ℝ) := Real.rpow_pos_of_pos hνpos _
  obtain ⟨Fk, hFk, hFkT⟩ := hApp (ν ^ (-2 : ℝ)) ν P.eigenvalue.re hc hνpos F hsym hmeas hfin
  choose b G hsol using fun k => hNice (ν ^ (-2 : ℝ)) ν μ hc hνpos (Fk k) (hFk k)
  have hFkmeas : ∀ n i j, Measurable fun p => Fk n p i j := fun n i j =>
    ((hFk n).2.1 i j).continuous.measurable
  obtain ⟨b', G', hAE⟩ := hLim (ν ^ (-2 : ℝ)) ν P.eigenvalue.re μ hc hνpos F hmeas hfin Fk b G
    (2 * Real.sqrt ((⨅ μ' : K, μ'.1.re + 1 / 4) * ν))⁻¹ ν⁻¹ hFkmeas hsol
    (fun n m hfin' => by
      have hs := hLin (ν ^ (-2 : ℝ)) ν μ (fun _ _ _ => 0) (Fk n) (Fk m) (b n) (b m) (G n) (G m)
        (hsol n) (hsol m)
      refine hbd ν hν μ hμ (fun p i j => Fk n p i j - Fk m p i j) ?_ ?_ hfin' _ _ hs
      · intro p i j
        rw [(hFk n).1 p i j, (hFk m).1 p i j]
      · intro i j
        exact (hFkmeas n i j).sub (hFkmeas m i j))
    hFkT
  exact hNull (ν ^ (-2 : ℝ)) ν μ (fun _ _ _ => 0) hc F b' G' hAE

end UnforcedLeray.Short.IIIa
