import UnforcedLeray.Short.PartIIIa.StressSpaces
import UnforcedLeray.Short.PartIIIa.FullClock
import UnforcedLeray.Short.PartI.TrainClass

/-!
# Part III-a, module `near/flat-causal.tex` (SP 3405-3581): the polynomial causal inverse

The planar equation `b_s + (μ/s)b - νΔb + 𝒫₀ div(v⊗b + b⊗v) = 𝒫₀ div F` for `b` in the energy class
(`IsCausalEnergySolution`: `b ∈ 𝓗` near zero, `∇b ∈ L²_loc`), tested against divergence-free
space-time tests (`IsFlatTest`); `𝒫₀` is the Leray projection of the cylinder including the
horizontal mean, so testing against all divergence-free tests is the equation. Free case: `v = 0`.
`prop:short-polynomial-causal` (SP 3426-3446) and `cor:short-polynomial-stress` (SP 3560-3581).

The train `v` is "the actual train" of `prop:short-full-clock` (SP 3410), the BUC train of
`sct:train` (SP 270-288): the proof uses its transverse tail `sct:transverse` (SP 3472-3480) and
its late strain `short-bg:train-late` (SP 3528-3531), which `B0140.IsTrain` does not give. So
`PolyCausal` and `PolyStressCorollary` assume `PartI.IsBUCTrain tr`.

Not stated: the "locally continuous in `μ`" clause of the proposition (SP 3445).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-! ## Norms of vector and tensor fields on `(0,∞) × cell` -/

/-- Euclidean norm of a complex 2-vector. -/
def vnorm2 (a : Fin 2 → ℂ) : ℝ := Real.sqrt (∑ i : Fin 2, ‖a i‖ ^ 2)

/-- Frobenius norm of a complex `2×2` tensor. -/
def tnorm2 (T : Fin 2 → Fin 2 → ℂ) : ℝ := Real.sqrt (∑ i : Fin 2, ∑ j : Fin 2, ‖T i j‖ ^ 2)

/-- `‖b‖_𝓗`, `𝓗 = L²(s^{-3/2}ds; L²(dq/c dη))` (SP 3412; divergence-freeness is a separate
clause of the solution class). -/
def hCalNorm (c : ℝ) (b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ) : ℝ≥0∞ :=
  eLpNorm (fun p => vnorm2 (b p)) 2 (ageμ c (-3 / 2))

/-- `‖T‖_𝒯`, `𝒯 = L²(s^{-1/2}ds; L²(dq/c dη))` (SP 3412). -/
def tCalNorm (c : ℝ) (T : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ) : ℝ≥0∞ :=
  eLpNorm (fun p => tnorm2 (T p)) 2 (ageμ c (-1 / 2))

/-- `‖T‖_{𝒵₁}`, `𝒵₁ = L²(s^{-1/2}W²ds dς)` for planar tensors. -/
def z1Norm2 (c mZ : ℝ) (T : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ) : ℝ≥0∞ :=
  eLpNorm (fun p => transWeight mZ p * tnorm2 (T p)) 2 (ageμ c (-1 / 2))

/-- The split stress norm `‖(T₁,T₂)‖_𝒵 = ‖T₁‖_{𝒵₁} + ρ_b^{-1/2}‖T₂‖_𝒯` (SP 2698-2700). -/
def zNorm2 (c mZ ρb : ℝ) (T₁ T₂ : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ) : ℝ≥0∞ :=
  z1Norm2 c mZ T₁ + ENNReal.ofReal (ρb ^ (-1 / 2 : ℝ)) * tCalNorm c T₂

/-! ## The equation in weak form -/

/-- A divergence-free space-time test field: smooth, `c`-periodic in `q`, supported in
`s ∈ [s₁, s₂] ⊂ (0,∞)` and `|η| ≤ R`, with `div Φ(s) = 0` for every `s`. -/
structure IsFlatTest (c : ℝ) (Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ) : Prop where
  smooth : ∀ i, ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => Φ p.1 p.2 i)
  periodic : ∀ s x i, Φ s (x.1 + c, x.2) i = Φ s x i
  support : ∃ s₁ s₂ R : ℝ, 0 < s₁ ∧ ∀ s x i, (s < s₁ ∨ s₂ < s ∨ R < |x.2|) → Φ s x i = 0
  divFree : ∀ s x, B0579.pd 0 (fun y => Φ s y 0) x + B0579.pd 1 (fun y => Φ s y 1) x = 0

/-- `∂_sΦ_i`. -/
def flatDt (Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ) (s : ℝ) (x : ℝ × ℝ) (i : Fin 2) : ℝ :=
  deriv (fun s' => Φ s' x i) s

/-- `∂_jΦ_i`. -/
def flatGrad (Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ) (s : ℝ) (x : ℝ × ℝ) (i j : Fin 2) : ℝ :=
  B0579.pd j (fun y => Φ s y i) x

/-- `ΔΦ_i`. -/
def flatLap (Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ) (s : ℝ) (x : ℝ × ℝ) (i : Fin 2) : ℝ :=
  lapP (fun y => Φ s y i) x

/-- The tested equation: `-⟨b,Φ_s⟩ + (μ/s)⟨b,Φ⟩ - ν⟨b,ΔΦ⟩ - ⟨v⊗b + b⊗v, ∇Φ⟩ + ⟨F,∇Φ⟩` with
`⟨T,∇Φ⟩ = ∑ T_ij ∂_jΦ_i`, so that its space-time integral vanishes iff
`b_s + (μ/s)b - νΔb + 𝒫₀ div(v⊗b + b⊗v) = 𝒫₀ div F` against divergence-free tests. -/
def flatIntegrand (ν : ℝ) (μ : ℂ) (vel : ℝ → ℝ × ℝ → Fin 2 → ℝ)
    (F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ) (b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ)
    (Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ) (p : ℝ × (ℝ × ℝ)) : ℂ :=
  ∑ i : Fin 2,
    (-(b p i * (flatDt Φ p.1 p.2 i : ℂ)) + (μ / (p.1 : ℂ)) * b p i * (Φ p.1 p.2 i : ℂ) -
      (ν : ℂ) * b p i * (flatLap Φ p.1 p.2 i : ℂ) +
      ∑ j : Fin 2, (F p i j - ((vel p.1 p.2 i : ℂ) * b p j + b p i * (vel p.1 p.2 j : ℂ))) *
        (flatGrad Φ p.1 p.2 i j : ℂ))

/-- The causal zero-entrance energy class and equation (SP 3426-3440): `b` has weak gradient `G`
(`G s x i j = ∂_j b_i`) in `L²_loc((0,∞);L²)`, `b(s)` is divergence free, `b ∈ 𝓗` near zero (no
homogeneous `s^{-μ}` entrance), and the weak equation holds. -/
structure IsCausalEnergySolution (c ν : ℝ) (μ : ℂ) (vel : ℝ → ℝ × ℝ → Fin 2 → ℝ)
    (F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ) (b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ)
    (G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ) : Prop where
  measurable : ∀ i, Measurable fun p => b p i
  gradMeasurable : ∀ i j, Measurable fun p => G p i j
  energyLoc : ∀ s₁ s₂ : ℝ, 0 < s₁ → s₁ < s₂ →
    ∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c, ENNReal.ofReal (vnorm2 (b p) ^ 2 + tnorm2 (G p) ^ 2) < ⊤
  zeroEntrance : ∃ δ : ℝ, 0 < δ ∧ ∫⁻ p, ENNReal.ofReal (vnorm2 (b p) ^ 2)
    ∂((ageμ c (-3 / 2)).restrict (Ioo 0 δ ×ˢ univ)) < ⊤
  divFree : ∀ s, 0 < s → ∀ ψ, B0579.IsCylTest c ψ →
    ∫ x in B0579.cell c, (b (s, x) 0 * (B0579.pd 0 ψ x : ℂ) + b (s, x) 1 * (B0579.pd 1 ψ x : ℂ)) = 0
  weakGrad : ∀ s, 0 < s → ∀ i j,
    HasWeakCellDerivC c j (fun x => b (s, x) i) (fun x => G (s, x) i j)
  integrable : ∀ Φ, IsFlatTest c Φ →
    IntegrableOn (flatIntegrand ν μ vel F b Φ) (Ioi (0 : ℝ) ×ˢ B0579.cell c)
  weak : ∀ Φ, IsFlatTest c Φ →
    ∫ p in Ioi (0 : ℝ) ×ˢ B0579.cell c, flatIntegrand ν μ vel F b Φ p = 0

/-- The conjugation by the gain: `g⁻¹ f` for a field on `(0,∞) × cell`. -/
def gainConj {E : Type*} [AddCommGroup E] [Module ℝ E] (γ ν : ℝ) (f : ℝ × (ℝ × ℝ) → E) :
    ℝ × (ℝ × ℝ) → E :=
  fun p => (gainG γ ν p.1)⁻¹ • f p

/-- The actual train velocity as a coefficient field of the flat equation (for ages `s ≥ 0`;
the value `0` for `s < 0`, where the train is not defined and the equation is never evaluated). -/
def trainVel {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) : ℝ → ℝ × ℝ → Fin 2 → ℝ :=
  fun s x i => if 0 ≤ s then tr.v s x i else 0

/-- **Free causal solver** (SP 3427-3440, "start from zero at `s = δ`, let `δ ↓ 0`"; the free
instance of the energy argument): for `K ⋐ {0<Re μ<1/4}`, `k_* = inf_K(Re μ + 1/4)`, small `ν`,
every symmetric `F` with `g⁻¹F ∈ 𝒯` has a UNIQUE causal zero-entrance energy solution of the FREE
equation (`v = 0`), and the free weighted energy bounds
`‖g⁻¹b‖_𝓗 ≤ (2√(k_*ν))⁻¹‖g⁻¹F‖_𝒯`, `‖∇(g⁻¹b)‖_𝒯 ≤ ν⁻¹‖g⁻¹F‖_𝒯` hold when the scalar
coefficient `μ/s + h` (here `g` conjugation absorbed) is used. -/
def FreeCausalExistsUnique : Prop :=
  ∀ P : PlanarData, IsPlanarReference P → ∀ K : Set ℂ, IsAdmissibleK K →
    ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ ν ∈ Ioc 0 ν₀, ∀ μ ∈ K,
      ∀ F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ, (∀ p i j, F p i j = F p j i) →
        (∀ i j, Measurable fun p => F p i j) →
        tCalNorm (ν ^ (-2 : ℝ)) (gainConj P.eigenvalue.re ν F) < ⊤ →
        ∃ b G, IsCausalEnergySolution (ν ^ (-2 : ℝ)) ν μ (fun _ _ _ => 0) F b G ∧
          hCalNorm (ν ^ (-2 : ℝ)) (gainConj P.eigenvalue.re ν b) ≤
            ENNReal.ofReal ((2 * Real.sqrt ((⨅ μ' : K, μ'.1.re + 1 / 4) * ν))⁻¹) *
              tCalNorm (ν ^ (-2 : ℝ)) (gainConj P.eigenvalue.re ν F) ∧
          tCalNorm (ν ^ (-2 : ℝ)) (gainConj P.eigenvalue.re ν G) ≤
            ENNReal.ofReal ν⁻¹ * tCalNorm (ν ^ (-2 : ℝ)) (gainConj P.eigenvalue.re ν F) ∧
          ∀ b' G', IsCausalEnergySolution (ν ^ (-2 : ℝ)) ν μ (fun _ _ _ => 0) F b' G' →
            b' =ᵐ[volume.restrict (Ioi (0 : ℝ) ×ˢ B0579.cell (ν ^ (-2 : ℝ)))] b

/-- **`prop:short-polynomial-causal`** (SP 3426-3446). For every planar reference, `K ⋐
{0 < Re μ < 1/4}` there are `M`, `C`, `ν₀` such that for `ν ≤ ν₀`, the actual train `tr` (BUC class, SP 270-288),
`μ ∈ K` and every symmetric planar tensor `F` with `g⁻¹F ∈ 𝒯`: there is a unique causal
zero-entrance energy solution `b` of `eq:short-causal-equation` and
`‖g⁻¹b‖_𝓗 + √ν‖∇(g⁻¹b)‖_𝒯 ≤ Cν^{-M}‖g⁻¹F‖_𝒯`. -/
def PolyCausal : Prop :=
  ∀ P : PlanarData, IsPlanarReference P → ∀ K : Set ℂ, IsAdmissibleK K →
    ∃ (M : ℕ) (C ν₀ : ℝ), 0 < ν₀ ∧ ∀ ν ∈ Ioc 0 ν₀,
      ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
        UnforcedLeray.Short.PartI.IsBUCTrain tr → ∀ μ ∈ K,
        ∀ F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ, (∀ p i j, F p i j = F p j i) →
          (∀ i j, Measurable fun p => F p i j) →
          tCalNorm (ν ^ (-2 : ℝ)) (gainConj P.eigenvalue.re ν F) < ⊤ →
          ∃ b G, IsCausalEnergySolution (ν ^ (-2 : ℝ)) ν μ (trainVel tr) F b G ∧
            hCalNorm (ν ^ (-2 : ℝ)) (gainConj P.eigenvalue.re ν b) +
                ENNReal.ofReal (Real.sqrt ν) *
                  tCalNorm (ν ^ (-2 : ℝ)) (gainConj P.eigenvalue.re ν G) ≤
              ENNReal.ofReal (C * ν ^ (-(M : ℝ))) *
                tCalNorm (ν ^ (-2 : ℝ)) (gainConj P.eigenvalue.re ν F) ∧
            ∀ b' G', IsCausalEnergySolution (ν ^ (-2 : ℝ)) ν μ (trainVel tr) F b' G' →
              b' =ᵐ[volume.restrict (Ioi (0 : ℝ) ×ˢ B0579.cell (ν ^ (-2 : ℝ)))] b

/-- The flat multiplier `M₀u = (v⊗u + u⊗v, 0)` (first entry), `v` the actual train. -/
def flatMult {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c)
    (u : ℝ × (ℝ × ℝ) → Fin 2 → ℂ) : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ :=
  fun p i j => ((trainVel tr p.1 p.2 i : ℝ) : ℂ) * u p j + u p i * ((trainVel tr p.1 p.2 j : ℝ) : ℂ)

/-- **`cor:short-polynomial-stress`** (SP 3560-3581). Hypothesis: the actual train multiplier
bound `‖M₀u‖_{𝒵₁} ≤ C_V ν^{-p_V}‖u‖_𝓗` (for measurable `u`). Conclusion: there are `M`
(depending on `p_V`, `K`) and, for each `C_V`, `C`, `ν₀`, such that for the actual train `tr`
(BUC class, SP 270-288), `0 < ρ_b ≤ 1`, `μ ∈ K`
and `F = (F₁, F₂)` with finite `‖g⁻¹F‖_𝒵`: `b = S_lin(F₁+F₂)` solves the FREE equation with
tensor `(F₁ - M₀b) + F₂` (so `G = D₀⁻¹F := (F₁ - M₀b, F₂)` has `G + M₀S₀G = F`), and
`‖g⁻¹D₀⁻¹F‖_𝒵 ≤ Cν^{-M}‖g⁻¹F‖_𝒵`. -/
def PolyStressCorollary : Prop :=
  ∀ P : PlanarData, IsPlanarReference P → ∀ K : Set ℂ, IsAdmissibleK K →
    ∀ mZ : ℝ, 3 / 2 < mZ → ∀ pV : ℕ, ∃ M : ℕ, ∀ CV : ℝ, ∃ (C ν₀ : ℝ), 0 < ν₀ ∧
      ∀ ν ∈ Ioc 0 ν₀, ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
        UnforcedLeray.Short.PartI.IsBUCTrain tr →
        ∀ ρb : ℝ, 0 < ρb → ρb ≤ 1 →
        (∀ u : ℝ × (ℝ × ℝ) → Fin 2 → ℂ, (∀ i, Measurable fun p => u p i) →
          z1Norm2 (ν ^ (-2 : ℝ)) mZ (flatMult tr u) ≤
            ENNReal.ofReal (CV * ν ^ (-(pV : ℝ))) * hCalNorm (ν ^ (-2 : ℝ)) u) →
        ∀ μ ∈ K, ∀ F₁ F₂ : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ,
          (∀ p i j, F₁ p i j = F₁ p j i) → (∀ p i j, F₂ p i j = F₂ p j i) →
          (∀ i j, Measurable fun p => F₁ p i j) → (∀ i j, Measurable fun p => F₂ p i j) →
          zNorm2 (ν ^ (-2 : ℝ)) mZ ρb (gainConj P.eigenvalue.re ν F₁)
              (gainConj P.eigenvalue.re ν F₂) < ⊤ →
          ∃ b G, IsCausalEnergySolution (ν ^ (-2 : ℝ)) ν μ (trainVel tr)
              (fun p i j => F₁ p i j + F₂ p i j) b G ∧
            IsCausalEnergySolution (ν ^ (-2 : ℝ)) ν μ (fun _ _ _ => 0)
              (fun p i j => (F₁ p i j - flatMult tr b p i j) + F₂ p i j) b G ∧
            zNorm2 (ν ^ (-2 : ℝ)) mZ ρb
                (gainConj P.eigenvalue.re ν (fun p i j => F₁ p i j - flatMult tr b p i j))
                (gainConj P.eigenvalue.re ν F₂) ≤
              ENNReal.ofReal (C * ν ^ (-(M : ℝ))) *
                zNorm2 (ν ^ (-2 : ℝ)) mZ ρb (gainConj P.eigenvalue.re ν F₁)
                  (gainConj P.eigenvalue.re ν F₂)

end UnforcedLeray.Short.IIIa
