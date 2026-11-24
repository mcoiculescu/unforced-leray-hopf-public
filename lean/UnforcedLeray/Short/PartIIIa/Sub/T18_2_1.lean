import UnforcedLeray.Short.PartIIIa.Sub.T18_2
import UnforcedLeray.Short.PartIIIa.Sub.T18_2_Tri
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.Lin

/-!
# Part III-a, task `PartIII-a:T18/2/1`: the `L²` limit of causal solutions (conditional)

Target (`Sub/T18_2.lean`): `CausalLimitAE`. Source of record:
`the November 2 reference manuscript`, lines 3427-3440 ("let `δ → 0`": the limit of
the approximate solutions is a solution of the limit problem).


target is cut into seven statements, each a true statement of the source; the wiring is proved in
`causalLimitAE_of`.

1. `TCalNormTriangle` (`Sub/T18_2_Tri.lean`): triangle inequality for `‖g⁻¹·‖_𝒯`.
2. `CausalCompleteH`, `CausalCompleteT`: completeness of the weighted `L²` spaces `𝓗`, `𝒯`
   (a sequence whose differences are dominated by `K (a_n + a_m)`, `a_n → 0`, converges to a
   measurable limit).
3. `CausalSliceAE`: along a subsequence the `L²(cell)` slices converge for almost every age `s`
   (Tonelli + the summable-subsequence trick).
4. `CausalEnergyPerturb`: the clauses `energyLoc`, `zeroEntrance` are stable under adding an
   element of `𝓗 × 𝒯` (`g` is bounded above and below on `(0, ∞)`, the weights are bounded on
   `[s₁, s₂]`).
5. `CausalSliceClauses`: `divFree`, `weakGrad` pass to the limit at a.e. age where the slices
   converge in `L²(cell)` (Cauchy-Schwarz against the test and its derivatives).
6. `FlatIntegrandBound`: for a fixed flat test `Φ`, the tested equation is a bounded linear
   functional of `(F, b)` on `𝒯 × 𝓗` (bounded coefficients on the compact support of `Φ`,
   `|μ/s| ≤ |μ|/s₁`, Cauchy-Schwarz and comparison of `ageμ` with Lebesgue measure on `[s₁, s₂] × cell`).

The Cauchy bookkeeping (`tCalNorm(Fn n - Fn m) ≤ a n + a m`, the finite eventual norms), the
extraction of `(b, G)`, the choice of the comparison index `N` and the passage to the limit in the
weak identity from `FlatIntegrandBound` and `causalLin_flatIntegrand_sub` are proved here.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- **Completeness of `𝓗`** (`PartIII-a:T18/2/1/2`; SP 3427-3440). Let `bn` be measurable and
suppose that, for `n, m ≥ N₀`, `‖g⁻¹(bn n - bn m)‖_𝓗 ≤ K (a n + a m)` with `K < ∞` and `a n → 0`.
Then there is a measurable `b` with `‖g⁻¹(bn n - b)‖_𝓗 → 0`. (The `bn n` themselves need not have
finite `𝓗` norm: apply completeness of `L²(ageμ c (-3/2); ℂ²)` to `d_n = g⁻¹(bn n - bn N₀)`,
`n ≥ N₀`, take a measurable representative `d` of the limit and put `b = bn N₀ + g d`; `g > 0`
is a real scalar, so `gainConj` of the difference is `g⁻¹(bn n - bn N₀) - d`.)
Route: `MeasureTheory.Lp` is complete (`Lp.instCompleteSpace`, `LpSpace/Complete.lean`) applied to
`EuclideanSpace ℂ (Fin 2)`-valued functions, or a direct a.e.-convergent-subsequence argument. -/
def CausalCompleteH : Prop :=
  ∀ (c ν γ : ℝ), 0 < c → 0 < ν →
    ∀ (bn : ℕ → ℝ × (ℝ × ℝ) → Fin 2 → ℂ), (∀ n i, Measurable fun p => bn n p i) →
    ∀ (K : ℝ≥0∞) (a : ℕ → ℝ≥0∞), K ≠ ⊤ → Tendsto a atTop (𝓝 0) →
    (∃ N₀ : ℕ, ∀ n m, N₀ ≤ n → N₀ ≤ m →
      hCalNorm c (gainConj γ ν (fun p i => bn n p i - bn m p i)) ≤ K * (a n + a m)) →
    ∃ b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ, (∀ i, Measurable fun p => b p i) ∧
      Tendsto (fun n => hCalNorm c (gainConj γ ν (fun p i => bn n p i - b p i))) atTop (𝓝 0)

/-- **Completeness of `𝒯`** (`PartIII-a:T18/2/1/3`; SP 3427-3440). The tensor analogue of
`CausalCompleteH` (norm `tCalNorm c`, weight `s^{-1/2}`, values in `ℂ^{2×2}` with the Frobenius
norm `tnorm2`). -/
def CausalCompleteT : Prop :=
  ∀ (c ν γ : ℝ), 0 < c → 0 < ν →
    ∀ (Gn : ℕ → ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ), (∀ n i j, Measurable fun p => Gn n p i j) →
    ∀ (K : ℝ≥0∞) (a : ℕ → ℝ≥0∞), K ≠ ⊤ → Tendsto a atTop (𝓝 0) →
    (∃ N₀ : ℕ, ∀ n m, N₀ ≤ n → N₀ ≤ m →
      tCalNorm c (gainConj γ ν (fun p i j => Gn n p i j - Gn m p i j)) ≤ K * (a n + a m)) →
    ∃ G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ, (∀ i j, Measurable fun p => G p i j) ∧
      Tendsto (fun n => tCalNorm c (gainConj γ ν (fun p i j => Gn n p i j - G p i j)))
        atTop (𝓝 0)

/-- **Almost every slice converges along a subsequence** (`PartIII-a:T18/2/1/4`; SP 3427-3440).
If `‖g⁻¹(bn n - b)‖_𝓗 → 0` and `‖g⁻¹(Gn n - G)‖_𝒯 → 0` then, along a subsequence `φ`, for almost
every age `s > 0` the (unweighted, unconjugated) slices converge:
`∫_cell |bn (φ n)(s, ·) - b(s, ·)|² → 0` and `∫_cell |Gn (φ n)(s, ·) - G(s, ·)|² → 0`.
Route: `ageμ c a = (vol|_{Ioi 0}.withDensity s^a) ⊗ c⁻¹ vol|_cell`; with
`h_n(s) = ∫⁻_cell (…)` (measurable in `s`, Tonelli) the hypotheses say `∫⁻ s^{-3/2} g(s)^{-2} h_n → 0`
resp. `s^{-1/2}`; pick `φ` with the sum of the two integrals `≤ 2^{-n}`, so
`∑ (weighted h_{φ n}) < ∞` a.e. and the terms tend to `0` a.e. (e.g.
`ENNReal.tendsto_atTop_zero_of_tsum_ne_top`); the weights `s^{-3/2} g(s)^{-2}`, `s^{-1/2} g(s)^{-2}`
are positive finite constants at fixed `s > 0`. -/
def CausalSliceAE : Prop :=
  ∀ (c ν γ : ℝ), 0 < c → 0 < ν →
    ∀ (bn : ℕ → ℝ × (ℝ × ℝ) → Fin 2 → ℂ) (Gn : ℕ → ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ)
      (b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ) (G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ),
    (∀ n i, Measurable fun p => bn n p i) → (∀ i, Measurable fun p => b p i) →
    (∀ n i j, Measurable fun p => Gn n p i j) → (∀ i j, Measurable fun p => G p i j) →
    Tendsto (fun n => hCalNorm c (gainConj γ ν (fun p i => bn n p i - b p i))) atTop (𝓝 0) →
    Tendsto (fun n => tCalNorm c (gainConj γ ν (fun p i j => Gn n p i j - G p i j)))
      atTop (𝓝 0) →
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))),
        Tendsto (fun n => ∫⁻ x in B0579.cell c,
          ENNReal.ofReal (vnorm2 (fun i => bn (φ n) (s, x) i - b (s, x) i) ^ 2)) atTop (𝓝 0) ∧
        Tendsto (fun n => ∫⁻ x in B0579.cell c,
          ENNReal.ofReal (tnorm2 (fun i j => Gn (φ n) (s, x) i j - G (s, x) i j) ^ 2))
          atTop (𝓝 0)

/-- **Stability of `energyLoc` and `zeroEntrance` under an `𝓗 × 𝒯` perturbation**
(`PartIII-a:T18/2/1/5`; SP 3427-3440, "`b - bn N ∈ 𝓗`, `|x| ≤ g |g⁻¹x|`"). Let `(b', G')` satisfy
the clauses `energyLoc` and `zeroEntrance` and let `b, G` be measurable with
`‖g⁻¹(b' - b)‖_𝓗 < ∞`, `‖g⁻¹(G' - G)‖_𝒯 < ∞`. Then `(b, G)` satisfies them too.
Proof: `g(s) = exp(γ s/(1+νs)) ≤ exp(|γ|/ν)` for `s > 0` (`ν > 0`), so
`|b - b'| = g |g⁻¹(b - b')| ≤ e^{|γ|/ν} |g⁻¹(b - b')|`; `|b|² ≤ 2|b'|² + 2|b - b'|²`; on
`[s₁, s₂] × cell` the density of `ageμ c (-3/2)` (resp. `(-1/2)`) w.r.t. Lebesgue measure is
`c⁻¹ s^{-3/2} ≥ c⁻¹ s₂^{-3/2} > 0` (`Axi.lintegral_ageμ`); for `zeroEntrance` use the same `δ` as
for `b'` (`ageμ c (-3/2)` lives on `s > 0`). -/
def CausalEnergyPerturb : Prop :=
  ∀ (c ν γ : ℝ), 0 < c → 0 < ν →
    ∀ (b' b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ) (G' G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ),
    (∀ i, Measurable fun p => b p i) → (∀ i j, Measurable fun p => G p i j) →
    (∀ i, Measurable fun p => b' p i) → (∀ i j, Measurable fun p => G' p i j) →
    (∀ s₁ s₂ : ℝ, 0 < s₁ → s₁ < s₂ →
      ∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c,
        ENNReal.ofReal (vnorm2 (b' p) ^ 2 + tnorm2 (G' p) ^ 2) < ⊤) →
    (∃ δ : ℝ, 0 < δ ∧ ∫⁻ p, ENNReal.ofReal (vnorm2 (b' p) ^ 2)
      ∂((ageμ c (-3 / 2)).restrict (Ioo 0 δ ×ˢ univ)) < ⊤) →
    hCalNorm c (gainConj γ ν (fun p i => b' p i - b p i)) < ⊤ →
    tCalNorm c (gainConj γ ν (fun p i j => G' p i j - G p i j)) < ⊤ →
    (∀ s₁ s₂ : ℝ, 0 < s₁ → s₁ < s₂ →
      ∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c,
        ENNReal.ofReal (vnorm2 (b p) ^ 2 + tnorm2 (G p) ^ 2) < ⊤) ∧
    (∃ δ : ℝ, 0 < δ ∧ ∫⁻ p, ENNReal.ofReal (vnorm2 (b p) ^ 2)
      ∂((ageμ c (-3 / 2)).restrict (Ioo 0 δ ×ˢ univ)) < ⊤)

/-- **`divFree` and `weakGrad` pass to the limit at almost every age** (`PartIII-a:T18/2/1/6`;
SP 3427-3440). Let `(bn n, Gn n)` be measurable with `energyLoc`, and `divFree`, `weakGrad` at EVERY
`s > 0` (the clauses of `IsCausalEnergySolution`), and suppose that for almost every `s > 0` the
slices `bn n (s, ·) → b (s, ·)`, `Gn n (s, ·) → G (s, ·)` converge in `L²(cell)`. Then for almost
every `s > 0` the limit slices satisfy `divFree` and `weakGrad`. Proof: the set of ages `s > 0` where
all `bn n (s, ·), Gn n (s, ·)` lie in `L²(cell)` has full measure (`energyLoc` on `[1/k, k]`,
Tonelli, countable intersection), at such `s` the limit slices are in `L²(cell)` too; for an
`IsCylTest ψ`, `ψ` and `∂ψ` are bounded with `η`-compact support, hence in `L²(cell)`, so
`∫_cell bn n (s, ·) ∂_jψ → ∫_cell b (s, ·) ∂_jψ` (Cauchy-Schwarz, `vnorm2` bounds the entries) and
likewise for `∫ Gn n (s, ·) ψ`; the integrability conjuncts of `HasWeakCellDerivC` come from
`L² × L²`. -/
def CausalSliceClauses : Prop :=
  ∀ (c : ℝ), 0 < c →
    ∀ (bn : ℕ → ℝ × (ℝ × ℝ) → Fin 2 → ℂ) (Gn : ℕ → ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ)
      (b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ) (G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ),
    (∀ n i, Measurable fun p => bn n p i) → (∀ i, Measurable fun p => b p i) →
    (∀ n i j, Measurable fun p => Gn n p i j) → (∀ i j, Measurable fun p => G p i j) →
    (∀ n, ∀ s₁ s₂ : ℝ, 0 < s₁ → s₁ < s₂ →
      ∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c,
        ENNReal.ofReal (vnorm2 (bn n p) ^ 2 + tnorm2 (Gn n p) ^ 2) < ⊤) →
    (∀ n s, 0 < s → ∀ ψ, B0579.IsCylTest c ψ →
      ∫ x in B0579.cell c, (bn n (s, x) 0 * (B0579.pd 0 ψ x : ℂ) +
        bn n (s, x) 1 * (B0579.pd 1 ψ x : ℂ)) = 0) →
    (∀ n s, 0 < s → ∀ i j,
      HasWeakCellDerivC c j (fun x => bn n (s, x) i) (fun x => Gn n (s, x) i j)) →
    (∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))),
      Tendsto (fun n => ∫⁻ x in B0579.cell c,
        ENNReal.ofReal (vnorm2 (fun i => bn n (s, x) i - b (s, x) i) ^ 2)) atTop (𝓝 0) ∧
      Tendsto (fun n => ∫⁻ x in B0579.cell c,
        ENNReal.ofReal (tnorm2 (fun i j => Gn n (s, x) i j - G (s, x) i j) ^ 2))
        atTop (𝓝 0)) →
    ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))),
      (∀ ψ, B0579.IsCylTest c ψ →
        ∫ x in B0579.cell c, (b (s, x) 0 * (B0579.pd 0 ψ x : ℂ) +
          b (s, x) 1 * (B0579.pd 1 ψ x : ℂ)) = 0) ∧
      (∀ i j, HasWeakCellDerivC c j (fun x => b (s, x) i) (fun x => G (s, x) i j))

/-- **The tested free equation is a bounded functional on `𝒯 × 𝓗`** (`PartIII-a:T18/2/1/7`;
SP 3427-3440, "`|μ/s| ≤ |μ|/s₁`, `Φ` bounded with compact support"). For `c, ν > 0`, `γ, μ` and a
fixed flat test `Φ` there is `C ≥ 0` such that for all measurable `F, b` with `‖g⁻¹F‖_𝒯 < ∞` and
`‖g⁻¹b‖_𝓗 < ∞` the tested integrand `flatIntegrand ν μ 0 F b Φ` is integrable on `(0,∞) × cell`
and `|∫ flatIntegrand ν μ 0 F b Φ| ≤ C (‖g⁻¹b‖_𝓗 + ‖g⁻¹F‖_𝒯)`. Route: (i) pointwise
`|flatIntegrand ν μ 0 F b Φ p| ≤ C₀ (vnorm2 (b p) + tnorm2 (F p))` on `p ∈ [s₁, s₂] × cell ∩ {|η| ≤ R}`
and `= 0` elsewhere in `(0,∞) × cell` (`Φ` smooth, periodic in `q`, supported in `s ∈ [s₁, s₂]`,
`|η| ≤ R`: its `s`-derivative, gradient and Laplacian are continuous, hence bounded on the compact
`[s₁, s₂] × [-c/2, c/2] × [-R, R]`; `|μ/s| ≤ |μ|/s₁`); (ii) `|b| = g |g⁻¹b| ≤ e^{|γ|/ν}|g⁻¹b|`;
(iii) on `[s₁, s₂] × cell`, `ageμ c a` has density `c⁻¹ s^a ≥ c⁻¹ s₂^a` w.r.t. Lebesgue measure for
`a < 0`, so by Cauchy-Schwarz `∫_{[s₁,s₂]×cell} (|b| + |F|) ≤ C' (‖g⁻¹b‖_𝓗 + ‖g⁻¹F‖_𝒯)`. -/
def FlatIntegrandBound : Prop :=
  ∀ (c ν γ : ℝ) (μ : ℂ), 0 < c → 0 < ν →
    ∀ Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ, IsFlatTest c Φ →
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ (F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ) (b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ),
          (∀ i j, Measurable fun p => F p i j) → (∀ i, Measurable fun p => b p i) →
          tCalNorm c (gainConj γ ν F) < ⊤ → hCalNorm c (gainConj γ ν b) < ⊤ →
          IntegrableOn (flatIntegrand ν μ (fun _ _ _ => 0) F b Φ)
              (Ioi (0 : ℝ) ×ˢ B0579.cell c) ∧
          ENNReal.ofReal ‖∫ p in Ioi (0 : ℝ) ×ˢ B0579.cell c,
              flatIntegrand ν μ (fun _ _ _ => 0) F b Φ p‖ ≤
            ENNReal.ofReal C * (hCalNorm c (gainConj γ ν b) + tCalNorm c (gainConj γ ν F))

/-- **`L²` limit of causal solutions, from six facts** (assembly; SP 3427-3440). -/
theorem causalLimitAE_of (hTri : TCalNormTriangle) (hCH : CausalCompleteH)
    (hCT : CausalCompleteT) (hSl : CausalSliceAE) (hPert : CausalEnergyPerturb)
    (hCl : CausalSliceClauses) (hFl : FlatIntegrandBound) : CausalLimitAE := by
  intro c ν γ μ hc hν F hFm hFfin Fn bn Gn A A' hFnm hsol hbd hFn
  have hbnm : ∀ n i, Measurable fun p => bn n p i := fun n i => (hsol n).measurable i
  have hGnm : ∀ n i j, Measurable fun p => Gn n p i j := fun n i j => (hsol n).gradMeasurable i j
  obtain ⟨a, ha⟩ : ∃ a : ℕ → ℝ≥0∞, ∀ n,
      a n = tCalNorm c (gainConj γ ν (fun p i j => Fn n p i j - F p i j)) := ⟨_, fun _ => rfl⟩
  have hat : Tendsto a atTop (𝓝 0) := by
    have : a = fun n => tCalNorm c (gainConj γ ν (fun p i j => Fn n p i j - F p i j)) :=
      funext ha
    rw [this]
    exact hFn
  obtain ⟨N₀, hN₀⟩ : ∃ N₀ : ℕ, ∀ n, N₀ ≤ n → a n < ⊤ :=
    eventually_atTop.1 (hat.eventually (gt_mem_nhds ENNReal.zero_lt_top))
  -- the Cauchy bounds
  have key : ∀ n m, N₀ ≤ n → N₀ ≤ m →
      hCalNorm c (gainConj γ ν (fun p i => bn n p i - bn m p i)) ≤
        ENNReal.ofReal A * (a n + a m) ∧
      tCalNorm c (gainConj γ ν (fun p i j => Gn n p i j - Gn m p i j)) ≤
        ENNReal.ofReal A' * (a n + a m) := by
    intro n m hn hm
    have h1 : tCalNorm c (gainConj γ ν (fun p i j => Fn n p i j - Fn m p i j)) ≤ a n + a m := by
      rw [ha n, ha m]
      exact hTri c ν γ (Fn n) F (Fn m) (hFnm n) hFm (hFnm m)
    have hlt : tCalNorm c (gainConj γ ν (fun p i j => Fn n p i j - Fn m p i j)) < ⊤ :=
      lt_of_le_of_lt h1 (ENNReal.add_lt_top.2 ⟨hN₀ n hn, hN₀ m hm⟩)
    obtain ⟨hb1, hb2⟩ := hbd n m hlt
    exact ⟨hb1.trans (by gcongr), hb2.trans (by gcongr)⟩
  -- the limits
  obtain ⟨b, hbm, hbT⟩ := hCH c ν γ hc hν bn hbnm (ENNReal.ofReal A) a ENNReal.ofReal_ne_top hat
    ⟨N₀, fun n m hn hm => (key n m hn hm).1⟩
  obtain ⟨G, hGm, hGT⟩ := hCT c ν γ hc hν Gn hGnm (ENNReal.ofReal A') a ENNReal.ofReal_ne_top hat
    ⟨N₀, fun n m hn hm => (key n m hn hm).2⟩
  obtain ⟨φ, hφ, hae⟩ := hSl c ν γ hc hν bn Gn b G hbnm hbm hGnm hGm hbT hGT
  -- `energyLoc` and `zeroEntrance` from one good index
  obtain ⟨N, hNb, hNG⟩ : ∃ N : ℕ,
      hCalNorm c (gainConj γ ν (fun p i => bn N p i - b p i)) < ⊤ ∧
      tCalNorm c (gainConj γ ν (fun p i j => Gn N p i j - G p i j)) < ⊤ :=
    ((hbT.eventually (gt_mem_nhds ENNReal.zero_lt_top)).and
      (hGT.eventually (gt_mem_nhds ENNReal.zero_lt_top))).exists
  obtain ⟨hEn, hZe⟩ := hPert c ν γ hc hν (bn N) b (Gn N) G hbm hGm (hbnm N) (hGnm N)
    (hsol N).energyLoc (hsol N).zeroEntrance hNb hNG
  -- `divFree` and `weakGrad` at almost every age
  have hcl := hCl c hc (fun n => bn (φ n)) (fun n => Gn (φ n)) b G (fun n => hbnm _) hbm
    (fun n => hGnm _) hGm (fun n => (hsol (φ n)).energyLoc) (fun n => (hsol (φ n)).divFree)
    (fun n => (hsol (φ n)).weakGrad) hae
  have hcl' := (ae_restrict_iff' measurableSet_Ioi).1 hcl
  -- the weak identity
  have hweak : ∀ Φ, IsFlatTest c Φ →
      IntegrableOn (flatIntegrand ν μ (fun _ _ _ => 0) F b Φ) (Ioi (0 : ℝ) ×ˢ B0579.cell c) ∧
      ∫ p in Ioi (0 : ℝ) ×ˢ B0579.cell c, flatIntegrand ν μ (fun _ _ _ => 0) F b Φ p = 0 := by
    intro Φ hΦ
    obtain ⟨C, hC0, hC⟩ := hFl c ν γ μ hc hν Φ hΦ
    have hD : ∀ n, N₀ ≤ n → hCalNorm c (gainConj γ ν (fun p i => bn n p i - b p i)) < ⊤ →
        IntegrableOn (flatIntegrand ν μ (fun _ _ _ => 0) (fun p i j => Fn n p i j - F p i j)
          (fun p i => bn n p i - b p i) Φ) (Ioi (0 : ℝ) ×ˢ B0579.cell c) ∧
        ENNReal.ofReal ‖∫ p in Ioi (0 : ℝ) ×ˢ B0579.cell c,
          flatIntegrand ν μ (fun _ _ _ => 0) (fun p i j => Fn n p i j - F p i j)
            (fun p i => bn n p i - b p i) Φ p‖ ≤
          ENNReal.ofReal C * (hCalNorm c (gainConj γ ν (fun p i => bn n p i - b p i)) +
            tCalNorm c (gainConj γ ν (fun p i j => Fn n p i j - F p i j))) := by
      intro n hn hbn
      exact hC _ _ (fun i j => (hFnm n i j).sub (hFm i j)) (fun i => (hbnm n i).sub (hbm i))
        (by rw [← ha n]; exact hN₀ n hn) hbn
    have hDeq : ∀ n p, flatIntegrand ν μ (fun _ _ _ => 0) F b Φ p =
        flatIntegrand ν μ (fun _ _ _ => 0) (Fn n) (bn n) Φ p -
        flatIntegrand ν μ (fun _ _ _ => 0) (fun p i j => Fn n p i j - F p i j)
          (fun p i => bn n p i - b p i) Φ p := by
      intro n p
      rw [causalLin_flatIntegrand_sub ν μ (fun _ _ _ => 0) (Fn n) F (bn n) b Φ p]
      ring
    obtain ⟨N₂, hN₂⟩ : ∃ N₂ : ℕ, ∀ n, N₂ ≤ n → N₀ ≤ n ∧
        hCalNorm c (gainConj γ ν (fun p i => bn n p i - b p i)) < ⊤ := by
      obtain ⟨N₃, hN₃⟩ := eventually_atTop.1 (hbT.eventually (gt_mem_nhds ENNReal.zero_lt_top))
      exact ⟨max N₀ N₃, fun n hn => ⟨le_trans (le_max_left _ _) hn,
        hN₃ n (le_trans (le_max_right _ _) hn)⟩⟩
    have hfun : ∀ n, (fun p => flatIntegrand ν μ (fun _ _ _ => 0) F b Φ p) = fun p =>
        flatIntegrand ν μ (fun _ _ _ => 0) (Fn n) (bn n) Φ p -
        flatIntegrand ν μ (fun _ _ _ => 0) (fun p i j => Fn n p i j - F p i j)
          (fun p i => bn n p i - b p i) Φ p := fun n => funext (hDeq n)
    have hint : IntegrableOn (flatIntegrand ν μ (fun _ _ _ => 0) F b Φ)
        (Ioi (0 : ℝ) ×ˢ B0579.cell c) := by
      have h1 := (hsol N₂).integrable Φ hΦ
      have h2 := (hD N₂ (hN₂ N₂ le_rfl).1 (hN₂ N₂ le_rfl).2).1
      exact (Integrable.sub h1 h2).congr
        (Filter.Eventually.of_forall fun p => (hDeq N₂ p).symm)
    have hval : ∀ n, N₂ ≤ n →
        ∫ p in Ioi (0 : ℝ) ×ˢ B0579.cell c, flatIntegrand ν μ (fun _ _ _ => 0) F b Φ p =
        -∫ p in Ioi (0 : ℝ) ×ˢ B0579.cell c,
          flatIntegrand ν μ (fun _ _ _ => 0) (fun p i j => Fn n p i j - F p i j)
            (fun p i => bn n p i - b p i) Φ p := by
      intro n hn
      have hn' := hN₂ n hn
      have h1 := (hsol n).integrable Φ hΦ
      have h2 := (hD n hn'.1 hn'.2).1
      rw [hfun n, integral_sub h1 h2, (hsol n).weak Φ hΦ, zero_sub]
    have hr : Tendsto (fun n => ENNReal.ofReal C *
        (hCalNorm c (gainConj γ ν (fun p i => bn n p i - b p i)) +
          tCalNorm c (gainConj γ ν (fun p i j => Fn n p i j - F p i j)))) atTop (𝓝 0) := by
      have := ENNReal.Tendsto.const_mul (hbT.add hFn) (Or.inr (ENNReal.ofReal_ne_top (r := C)))
      simpa using this
    have hle : ENNReal.ofReal ‖∫ p in Ioi (0 : ℝ) ×ˢ B0579.cell c,
        flatIntegrand ν μ (fun _ _ _ => 0) F b Φ p‖ ≤ 0 := by
      refine ge_of_tendsto hr ?_
      rw [eventually_atTop]
      refine ⟨N₂, fun n hn => ?_⟩
      have hn' := hN₂ n hn
      rw [hval n hn, norm_neg]
      exact (hD n hn'.1 hn'.2).2
    refine ⟨hint, ?_⟩
    have h0 : ‖∫ p in Ioi (0 : ℝ) ×ˢ B0579.cell c,
        flatIntegrand ν μ (fun _ _ _ => 0) F b Φ p‖ = 0 :=
      le_antisymm (ENNReal.ofReal_eq_zero.1 (le_antisymm hle zero_le)) (norm_nonneg _)
    exact norm_eq_zero.1 h0
  exact ⟨b, G, hbm, hGm, hEn, hZe, hcl'.mono fun s hs h0 => (hs h0).1,
    hcl'.mono fun s hs h0 => (hs h0).2, fun Φ hΦ => (hweak Φ hΦ).1,
    fun Φ hΦ => (hweak Φ hΦ).2⟩

end UnforcedLeray.Short.IIIa
