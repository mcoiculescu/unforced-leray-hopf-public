import UnforcedLeray.Short.PartIIIa.Sub.T18_3

/-!
# Part III-a, task `PartIII-a:T18/3/1`: the weighted energy identity (conditional)

Target (`Sub/T18_3.lean`): `WeightedEnergyIdentity`. Source of record:
`the November 2 reference manuscript`, lines 3541-3552 (the weighted energy identity
on `[δ_j, B]` for `u = g⁻¹b`) and 3427-3440.

**Statement repair.** The target as first written had no measurability hypothesis on `F` and is FALSE
(junk value of a Bochner integral, see the docstring of `WeightedEnergyIdentity`); the hypothesis
`∀ i j, Measurable fun p => F p i j` was added in `Sub/T18_3.lean` (its only consumer,
`FreeEnergyInequalities`, has `F` measurable).

## Mathematical proof and the cut into four statements

Put `E(s) = ∫_cell |b(s)|²`, `N(s) = ∫_cell |G(s)|²`, `R(s) = ∫_cell Re⟨F(s), G(s)⟩`.

1. (`DivFreeCutoffDensity`, function-space density) every smooth, periodic, divergence-free field
   `φ` with `φ, ∇φ ∈ L²(cell)` is an `H¹(cell)`-limit of smooth periodic divergence-free fields with
   compact `η`-support (stream function `θ`, `φ = ∇^⊥θ + (m(η), 0)`, then cut off `θ`, `m` in `η`).
2. (`FlatWeakFromDensity`) hence the tested equation (`IsFlatTest`) extends to tests `ψ(s)φ(x)` with
   `φ` in that class, written with the weak gradient `G`: `ExtWeakH1`.
3. (`LionsMagenesCyl`) from `ExtWeakH1` and the energy class, the energy identity
   `∫ w' E = ∫ w (2 Re μ s⁻¹ E + 2ν N + 2R)` for every smooth weight `w` with compact support in
   `(0,∞)` (`CoreIdentity`): mollify in `x` with the heat semigroup of the cylinder (commutes with
   `∂`, preserves divergence-freeness, maps `L²` into the test class of step 2), apply the `H`-valued
   energy identity `Lib/BochnerTime/Energy.lean` (`HasWeakDerivTime.weighted_norm_sq_sub`) to the
   mollified field, let the mollification parameter go to `0` (dominated convergence in `s`).
4. (`CoreImpliesWeighted`) with `w = ψ s^{-1/2} g^{-2}` (`g = gainG γ ν`) one has
   `w' = (ψ' s^{-1/2} - ½ψ s^{-3/2} - 2hψ s^{-1/2}) g^{-2}`, `h = γ/(1+νs)² ≥ 0`; the conjugated
   quantities are `E_u = g⁻² E` etc., the `h` term has a good sign and is dropped, and
   `-Re⟨F̃, G̃⟩ ≤ |F̃||G̃|` (Cauchy-Schwarz in `ℂ^{2×2}`).

Proved here: `weightedEnergyIdentity_of` (the composition of the four statements).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- `F ∈ L²_loc((0,∞) × cell)`. -/
def L2locTensor (c : ℝ) (F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ) : Prop :=
  ∀ s₁ s₂ : ℝ, 0 < s₁ → s₁ < s₂ →
    ∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c, ENNReal.ofReal (tnorm2 (F p) ^ 2) < ⊤

/-- The standing hypotheses of `WeightedEnergyIdentity`: `c, ν > 0`, `F` measurable and
`L²_loc`, `(b, G)` a causal zero-entrance energy solution of the free equation with force `F`. -/
structure FreeSolData (c ν : ℝ) (μ : ℂ) (F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ)
    (b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ) (G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ) : Prop where
  pos_c : 0 < c
  pos_ν : 0 < ν
  l2loc : L2locTensor c F
  meas : ∀ i j, Measurable fun p => F p i j
  sol : IsCausalEnergySolution c ν μ (fun _ _ _ => 0) F b G

/-- **Smooth `H¹` divergence-free spatial fields on the cylinder**: smooth, `c`-periodic in `q`,
pointwise divergence free, with `φ` and `∇φ` in `L²(cell)` (no compact support in `η`). -/
structure IsH1DivFreeTest (c : ℝ) (φ : ℝ × ℝ → Fin 2 → ℝ) : Prop where
  smooth : ∀ i, ContDiff ℝ ∞ fun x => φ x i
  periodic : ∀ x i, φ (x.1 + c, x.2) i = φ x i
  divFree : ∀ x, B0579.pd 0 (fun y => φ y 0) x + B0579.pd 1 (fun y => φ y 1) x = 0
  l2 : ∀ i, MemLp (fun x => φ x i) 2 (volume.restrict (B0579.cell c))
  l2grad : ∀ i j, MemLp (fun x => B0579.pd j (fun y => φ y i) x) 2 (volume.restrict (B0579.cell c))

/-- **Spatial flat tests**: smooth, `c`-periodic in `q`, pointwise divergence free, vanishing for
`|η|` large (the `x`-profile of an `IsFlatTest`). -/
structure IsFlatSpatialTest (c : ℝ) (φ : ℝ × ℝ → Fin 2 → ℝ) : Prop where
  smooth : ∀ i, ContDiff ℝ ∞ fun x => φ x i
  periodic : ∀ x i, φ (x.1 + c, x.2) i = φ x i
  bounded : ∃ R : ℝ, ∀ x i, R < |x.2| → φ x i = 0
  divFree : ∀ x, B0579.pd 0 (fun y => φ y 0) x + B0579.pd 1 (fun y => φ y 1) x = 0

/-- The integrand of the tested free equation for a test `Φ(s, x) = ψ(s) φ(x)`, written with the weak
gradient `G` of `b`: `∑ᵢ [-bᵢ ψ' φᵢ + (μ/s) ψ bᵢ φᵢ + ∑ⱼ (ν Gᵢⱼ + Fᵢⱼ) ψ ∂ⱼφᵢ]`. (For a flat test the
term `-ν b·ΔΦ` of `flatIntegrand` equals `ν G:∇Φ` after integration by parts in `x` against
`weakGrad`.) -/
def extWeakIntegrand (ν : ℝ) (μ : ℂ) (F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ)
    (b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ) (G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ)
    (ψ : ℝ → ℝ) (φ : ℝ × ℝ → Fin 2 → ℝ) (p : ℝ × (ℝ × ℝ)) : ℂ :=
  ∑ i : Fin 2, (-(b p i * ((deriv ψ p.1 * φ p.2 i : ℝ) : ℂ)) +
    (μ / (p.1 : ℂ)) * b p i * ((ψ p.1 * φ p.2 i : ℝ) : ℂ) +
    ∑ j : Fin 2, ((ν : ℂ) * G p i j + F p i j) *
      ((ψ p.1 * B0579.pd j (fun y => φ y i) p.2 : ℝ) : ℂ))

/-- The tested equation holds for all `ψ(s) φ(x)`, `ψ ∈ C^∞_c(0,∞)`, `φ` an `H¹` divergence-free
test field (and the integrand is integrable). (`ψ` is smooth so that `ψ(s)φₖ(x)` is literally an
`IsFlatTest` when `φₖ` is a spatial flat test; the passage from the `C¹` weights of
`WeightedEnergyIdentity` to smooth weights is done in `CoreImpliesWeighted`.) -/
def ExtWeakH1 (c ν : ℝ) (μ : ℂ) (F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ)
    (b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ) (G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ) : Prop :=
  ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ Ioi 0 →
    ∀ φ : ℝ × ℝ → Fin 2 → ℝ, IsH1DivFreeTest c φ →
      IntegrableOn (extWeakIntegrand ν μ F b G ψ φ) (Ioi (0 : ℝ) ×ˢ B0579.cell c) ∧
      ∫ p in Ioi (0 : ℝ) ×ˢ B0579.cell c, extWeakIntegrand ν μ F b G ψ φ p = 0

/-- `E(s) = ∫_cell |b(s, x)|² dx`. -/
def energyE (c : ℝ) (b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ) (s : ℝ) : ℝ :=
  ∫ x in B0579.cell c, vnorm2 (b (s, x)) ^ 2

/-- `N(s) = ∫_cell |G(s, x)|² dx`. -/
def energyN (c : ℝ) (G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ) (s : ℝ) : ℝ :=
  ∫ x in B0579.cell c, tnorm2 (G (s, x)) ^ 2

/-- `R(s) = ∫_cell Re ∑ᵢⱼ Fᵢⱼ conj(Gᵢⱼ) dx`. -/
def energyR (c : ℝ) (F G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ) (s : ℝ) : ℝ :=
  ∫ x in B0579.cell c, ∑ i : Fin 2, ∑ j : Fin 2,
    ((F (s, x) i j).re * (G (s, x) i j).re + (F (s, x) i j).im * (G (s, x) i j).im)

/-- **The energy identity in weighted distributional form** (formally: test the equation
`b_s + (μ/s) b - νΔb = 𝒫₀ div F` with `2 w b` and use `Re⟨b_s, b⟩ = ½ (|b|²)_s`):
for every smooth weight `w` with compact support in `(0,∞)`,
`∫ w' E = ∫ w (2 Re μ s⁻¹ E + 2ν N + 2R)`. -/
def CoreIdentity (c ν : ℝ) (μ : ℂ) (F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ)
    (b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ) (G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ) : Prop :=
  ∀ w : ℝ → ℝ, ContDiff ℝ ∞ w → HasCompactSupport w → tsupport w ⊆ Ioi 0 →
    ∫ s in Ioi (0 : ℝ), deriv w s * energyE c b s =
      ∫ s in Ioi (0 : ℝ), w s * (2 * μ.re / s * energyE c b s + 2 * ν * energyN c G s +
        2 * energyR c F G s)

/-- The extended tested equation holds for every standing datum. -/
def FlatWeakAll : Prop :=
  ∀ (c ν : ℝ) (μ : ℂ) (F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ) (b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ)
    (G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ), FreeSolData c ν μ F b G → ExtWeakH1 c ν μ F b G

/-- The energy identity holds for every standing datum. -/
def CoreAll : Prop :=
  ∀ (c ν : ℝ) (μ : ℂ) (F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ) (b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ)
    (G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ), FreeSolData c ν μ F b G → CoreIdentity c ν μ F b G

/-- **Density of compactly `η`-supported divergence-free fields** (`PartIII-a:T18/3/1/1`;
SP 3541-3552, density of the test class). For `c > 0` and `φ` smooth, `c`-periodic, divergence free
with `φ, ∇φ ∈ L²(cell)` there are spatial flat tests `φₖ` with
`‖φₖ - φ‖_{L²(cell)}² + ‖∇φₖ - ∇φ‖_{L²(cell)}² → 0`.
Route (SIZE XL, expect a split): (i) the `q`-mean of `φ₂` is constant in `η` (divergence-free) and
square integrable, hence `0`; (ii) the stream function `θ` (`∂_qθ = -φ₂`, `q`-mean zero) satisfies
`∂_ηθ = φ₁ - m(η)`, `m` = `q`-mean of `φ₁`, so `φ = ∇^⊥θ + (m, 0)` with `θ, ∇θ, ∇²θ ∈ L²(cell)`,
`m, m' ∈ L²(ℝ)` (Poincaré in `q`); (iii) `φₖ = ∇^⊥(χ(η/k) θ) + (χ(η/k) m, 0)` with `χ` a smooth cutoff
is smooth, periodic, divergence free (symmetry of second derivatives) with compact `η`-support, and
converges to `φ` in `H¹(cell)` by dominated convergence. -/
def DivFreeCutoffDensity : Prop :=
  ∀ c : ℝ, 0 < c → ∀ φ : ℝ × ℝ → Fin 2 → ℝ, IsH1DivFreeTest c φ →
    ∃ φk : ℕ → ℝ × ℝ → Fin 2 → ℝ, (∀ k, IsFlatSpatialTest c (φk k)) ∧
      Tendsto (fun k => ∫⁻ x in B0579.cell c, ENNReal.ofReal (∑ i : Fin 2,
        ((φk k x i - φ x i) ^ 2 +
          ∑ j : Fin 2, (B0579.pd j (fun y => φk k y i) x - B0579.pd j (fun y => φ y i) x) ^ 2)))
        atTop (𝓝 0)

/-- **The tested equation extends to `H¹` divergence-free tests, given the density**
(`PartIII-a:T18/3/1/2`; SP 3541-3552). Assuming `DivFreeCutoffDensity`: for the standing data, every
`ψ ∈ C^∞_c(0,∞)` and `φ` an `H¹` divergence-free test field, `Φ = ψ(s)φₖ(x)` is an `IsFlatTest`
(smooth, periodic, compact support in `s ∈ supp ψ ⊂ (0,∞)` and in `η`, divergence free), so
`∫ flatIntegrand ν μ 0 F b Φₖ = 0`; the term `-ν b·ΔΦₖ` equals `ν G:∇Φₖ` after integration by parts
in `x` (`weakGrad` at every `s > 0` with the test `∂ⱼφₖ,ᵢ`, which is an `IsCylTest`); the resulting
integrand is `extWeakIntegrand ν μ F b G ψ φₖ`. Let `k → ∞`: the integrand is a sum of products
`(b, G, F)(p) × (φₖ - φ, ∇φₖ - ∇φ)(x) × (ψ, ψ', μ/s ψ)(s)` with `(b, G, F) ∈ L²([s₁,s₂] × cell)`
(`energyLoc`, `L2locTensor`), so by Cauchy-Schwarz the integral and the integrability pass to the
limit. -/
def FlatWeakFromDensity : Prop := DivFreeCutoffDensity → FlatWeakAll

/-- **Lions-Magenes on the cylinder** (`PartIII-a:T18/3/1/3`; SP 3541-3552; SIZE XL, expect a split).
Assuming the extended tested equation (`ExtWeakH1`), the energy identity `CoreIdentity` holds.
Route: let `J_ε` be the heat semigroup of the cylinder on `L²(cell; ℂ²)` (`Lib/HeatCylinder/*`; it
commutes with `∂_q, ∂_η`, preserves divergence-freeness, is a self-adjoint contraction, and maps
`L²` into the test class of `IsH1DivFreeTest`); `u_ε(s) = J_ε b(s)`. By `ExtWeakH1` with
`φ = J_ε φ₀` (`φ₀` flat tests, then all of the divergence-free `L²` by density), the `H`-valued
function `u_ε` has weak time derivative
`-(μ/s) u_ε + νΔ J_ε b + J_ε 𝒫₀ div F ∈ L²_loc((0,∞); H)` (`Lib/BochnerTime/Basic.lean`,
`HasWeakDerivTime`); `HasWeakDerivTime.weighted_norm_sq_sub` (`Lib/BochnerTime/Energy.lean`) gives
the weighted identity for `‖u_ε‖²`; let `ε → 0`: `‖u_ε(s)‖ → ‖b(s)‖`, `‖∇u_ε(s)‖ → ‖G(s)‖`,
`⟨F, ∇J_ε² b⟩ → ⟨F, G⟩` in `L¹_loc(ds)` (dominated convergence, `energyLoc`, `L2locTensor`). -/
def LionsMagenesCyl : Prop := FlatWeakAll → CoreAll

/-- **From the energy identity to the weighted inequality** (`PartIII-a:T18/3/1/4`; SP 3541-3552).
If `CoreIdentity` holds for every standing datum then `WeightedEnergyIdentity` holds. Proof: first
let `ψ ∈ C¹_c(0,∞)`, `ψ ≥ 0` be replaced by `ψₖ = ψ * ρ_{1/k}` (convolution with a nonnegative
`ContDiffBump.normed` kernel): `ψₖ` is smooth, `≥ 0`, supported in a fixed compact subset of `(0,∞)`
and `ψₖ → ψ`, `ψₖ' → ψ'` uniformly, so both sides of the inequality (integrals over that compact set of
the `L¹` functions `E`, `N`, `J = ∫_cell |F̃||G̃|` against bounded functions) pass to the limit.
For smooth `ψ`, take `w = ψ s^{-1/2} g^{-2}` (`g = gainG γ ν`, smooth with compact support in
`(0,∞)`; `g' = g γ/(1+νs)²`); `vnorm2 (gainConj γ ν b) = g⁻¹ vnorm2 b` so
`E_u = g⁻² E`, `N_u = g⁻² N`, and `tnorm2 F̃ · tnorm2 G̃ = g⁻² tnorm2 F tnorm2 G`;
`w' = g⁻² (ψ' s^{-1/2} - ½ ψ s^{-3/2} - 2 h ψ s^{-1/2})`, `h = γ/(1+νs)² ≥ 0`, so
`∫ w' E = ∫ ψ' s^{-1/2} E_u - ½∫ ψ s^{-3/2} E_u - 2∫ h ψ s^{-1/2} E_u` and `CoreIdentity` rearranges
to the inequality, dropping the term `-2∫ h ψ s^{-1/2} E_u ≤ 0` and using
`-R ≤ ∫ tnorm2 F tnorm2 G` (Cauchy-Schwarz on `ℂ^{2×2} ≅ ℝ^8`). Integrability of every term on
`supp ψ` comes from `energyLoc`, `L2locTensor` and Tonelli (`E`, `N` are measurable in `s`). -/
def CoreImpliesWeighted : Prop := CoreAll → WeightedEnergyIdentity

/-- **The weighted energy identity from four facts** (assembly; SP 3541-3552). -/
theorem weightedEnergyIdentity_of (hD : DivFreeCutoffDensity) (hA : FlatWeakFromDensity)
    (hLM : LionsMagenesCyl) (hAsm : CoreImpliesWeighted) : WeightedEnergyIdentity :=
  hAsm (hLM (hA hD))

end UnforcedLeray.Short.IIIa
