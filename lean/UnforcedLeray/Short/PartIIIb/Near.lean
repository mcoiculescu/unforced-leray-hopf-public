import UnforcedLeray.Short.PartIIIb.Basic
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# The direct zero-entrance near equation (module `near/equation-comparison.tex`, lines 3861-4132)

Concrete statements (no free data):

* `GainRatioSup` : the elementary identity
  `sup_{s>0, s≤t≤Ms} ν(t/(1+νt) - s/(1+νs)) = (√M-1)/(√M+1)` (lines 3993-4001);
* `NearInverseComparison` : the geometric-series step (lines 4056-4062): conjugation by `G`
  (multiplication by the gain `g`), `Q δ_N < 1/2` gives `‖G⁻¹D_N⁻¹G‖ ≤ 2Q` and
  `‖G⁻¹(D_N⁻¹-D_0⁻¹)G‖ ≤ 2Q²δ_N` (`near:inverse-comparison`, 3944-3951);
* `NearParameterChoice` : the parameter choice after the proof (lines 4109-4124): the right side of
  `near:deltaN` is `≤ P_ν e^{-θ d₀/(2ν)}` when `ε = C_* ν^r e^{-d₀/ν}`;
* `ForcedColumnComparison` : the resolvent identity at lines 4128-4132.

Interface statement (the analytic content, over the near operators of the earlier modules):

* `NearDeltaBound` : `near:deltaN` (lines 3931-3942).  The operators `D_0 = I + M_0 S_0`,
  `D_N = I + M_U S_N` on `Z`, and the gain multiplication `G` are the fields of `NearPkg`
  (objects of `near/flat-causal`, `stress-spaces`, `separated-kernels`, areas PartIII-a).
-/

set_option autoImplicit false

noncomputable section

open Filter Topology Set

namespace UnforcedLeray.Short.PartIIIb

/-! ## Elementary statements -/

/-- Lines 3993-4001: for `ν > 0` and `M ≥ 1`,
`sup_{s>0, s≤t≤Ms} ν(t/(1+νt) - s/(1+νs)) = (√M-1)/(√M+1)`, and the supremum is attained
(`x = νs = M^{-1/2}`, `t = Ms`). -/
def GainRatioSup : Prop :=
  ∀ ν M : ℝ, 0 < ν → 1 ≤ M →
    IsGreatest {v : ℝ | ∃ s t : ℝ, 0 < s ∧ s ≤ t ∧ t ≤ M * s ∧
      v = ν * (t / (1 + ν * t) - s / (1 + ν * s))}
      ((Real.sqrt M - 1) / (Real.sqrt M + 1))

/-- `(√M-1)/(√M+1) = tanh(log M / 4)`, so `M = e^{3δ/2}` gives `η_δ = γ tanh(3δ/8)`
(lines 4002-4007). -/
def GainRatioTanh : Prop :=
  ∀ M : ℝ, 1 ≤ M → (Real.sqrt M - 1) / (Real.sqrt M + 1) = Real.tanh (Real.log M / 4)

/-- Conjugation `G⁻¹ X G` of an operator on `Z` by an invertible gain multiplication `G`. -/
def conjG {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z] (G : Z ≃L[ℝ] Z)
    (X : Z →L[ℝ] Z) : Z →L[ℝ] Z :=
  (G.symm : Z →L[ℝ] Z) ∘L X ∘L (G : Z →L[ℝ] Z)

/-- `near:inverse-comparison`, last step of the proof (lines 4056-4062): if `D₀` has the two-sided
inverse `D₀⁻¹` with `‖G⁻¹D₀⁻¹G‖ ≤ Q`, `‖G⁻¹(D_N-D₀)G‖ ≤ δ` and `Qδ < 1/2`, then `D_N` is invertible,
`‖G⁻¹D_N⁻¹G‖ ≤ 2Q` and `‖G⁻¹(D_N⁻¹-D₀⁻¹)G‖ ≤ 2Q²δ`. -/
def NearInverseComparison : Prop :=
  ∀ {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]
    (G : Z ≃L[ℝ] Z) (D₀ D₀inv DN : Z →L[ℝ] Z) (Q δ : ℝ),
    D₀inv ∘L D₀ = 1 → D₀ ∘L D₀inv = 1 →
    ‖conjG G D₀inv‖ ≤ Q → ‖conjG G (DN - D₀)‖ ≤ δ → Q * δ < 1 / 2 →
    ∃ DNinv : Z →L[ℝ] Z, DNinv ∘L DN = 1 ∧ DN ∘L DNinv = 1 ∧
      ‖conjG G DNinv‖ ≤ 2 * Q ∧ ‖conjG G (DNinv - D₀inv)‖ ≤ 2 * Q ^ 2 * δ

/-- The right side of `near:deltaN` (lines 3931-3942) without the polynomial factor `P_ν`:
`ε^{a/2} + ε^{b/2} + ε e^{(m₀+η_δ)/ν} + ε^{1/50-K(a+b)} e^{η_δ/ν}
  + ε^{3/22} e^{(η_δ+m₀/2)/ν} + e^{-(D_⊥-η_δ)/ν}`. -/
def deltaNRhs (a b K ηδ m0 Dp ε ν : ℝ) : ℝ :=
  ε ^ (a / 2) + ε ^ (b / 2) + ε * Real.exp ((m0 + ηδ) / ν)
    + ε ^ (1 / 50 - K * (a + b)) * Real.exp (ηδ / ν)
    + ε ^ (3 / 22 : ℝ) * Real.exp ((ηδ + m0 / 2) / ν)
    + Real.exp (-(Dp - ηδ) / ν)

/-- Parameter choice (lines 4109-4124).  With `K(a+b) < 1/100`, `θ = min{a/2, b/2, 1/100, 3/22}`,
`d₀ = γ/3`, `η_δ, m₀ < θ d₀/8`, `D_⊥ > η_δ + θ d₀` and `ε = C_* ν^r e^{-d₀/ν}`, uniformly for
`C_*` in a compact positive range and bounded `r`:
`deltaNRhs ≤ P_ν e^{-θ d₀/(2ν)}`. -/
def NearParameterChoice : Prop :=
  ∀ (a b γ ηδ m0 Dp K c1 c2 rmax : ℝ), 0 < a → 0 < b → 0 < γ → 0 ≤ ηδ → 0 ≤ m0 → 0 ≤ K →
    K * (a + b) < 1 / 100 →
    ηδ < min (min (a / 2) (b / 2)) (min (1 / 100) (3 / 22)) * (γ / 3) / 8 →
    m0 < min (min (a / 2) (b / 2)) (min (1 / 100) (3 / 22)) * (γ / 3) / 8 →
    ηδ + min (min (a / 2) (b / 2)) (min (1 / 100) (3 / 22)) * (γ / 3) < Dp →
    0 < c1 → c1 ≤ c2 → 0 ≤ rmax →
    ∃ (C : ℝ) (k : ℕ) (ν₀ : ℝ), 0 < ν₀ ∧ ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
      ∀ Cs ∈ Icc c1 c2, ∀ r ∈ Icc (-rmax) rmax,
        deltaNRhs a b K ηδ m0 Dp (Cs * ν ^ r * Real.exp (-(γ / 3) / ν)) ν ≤
          C * ν⁻¹ ^ k * Real.exp (-(min (min (a / 2) (b / 2)) (min (1 / 100) (3 / 22)) *
            (γ / 3)) / (2 * ν))

/-- Resolvent identity step for the forced column (lines 4126-4132): if
`T = D⁻¹u` and `T₀ = D₀⁻¹u₀` with `‖G⁻¹(D⁻¹-D₀⁻¹)G‖ ≤ 2Q²δ` and `‖G⁻¹D⁻¹G‖ ≤ 2Q`, then
`‖G⁻¹(T-T₀)‖ ≤ 2Q‖G⁻¹(u-u₀)‖ + 2Q²δ‖G⁻¹u₀‖`. -/
def ForcedColumnComparison : Prop :=
  ∀ {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]
    (G : Z ≃L[ℝ] Z) (Dinv D₀inv : Z →L[ℝ] Z) (u u₀ : Z) (Q δ : ℝ),
    ‖conjG G Dinv‖ ≤ 2 * Q → ‖conjG G (Dinv - D₀inv)‖ ≤ 2 * Q ^ 2 * δ →
    ‖G.symm (Dinv u - D₀inv u₀)‖ ≤ 2 * Q * ‖G.symm (u - u₀)‖ + 2 * Q ^ 2 * δ * ‖G.symm u₀‖

/-! ## Interface: the near operators -/

/-- Parameters of the near equation (lines 3927-3930): viscosity `ν`, curvature `ε`, Floquet
parameter `μ`, exponents `a, b` (`s₋ = ε^a`, `S = ε^{-b}`), log gap `δ`, background loss `m₀`,
transverse accuracy `D_⊥`. -/
structure NearParams where
  ν : ℝ
  ε : ℝ
  μ : ℝ
  a : ℝ
  b : ℝ
  δ : ℝ
  m0 : ℝ
  Dp : ℝ

/-- The near operators on `Z = Z₁ ⊕ ρ_b^{-1/2} H_T` (lines 3866-3880): `D0 = I + M₀ S₀`,
`DN = I + M_U S_N`, `G` the multiplication by the gain `g`, and the direct causal inverse `D0inv`
(`near:flat-bound`).  Instantiated by the cylinder spaces of `stress-spaces.tex`
and the operators of `near/flat-causal.tex`, `separated-kernels.tex` (area PartIII-a). -/
structure NearPkg where
  Z : Type
  [nz : NormedAddCommGroup Z]
  [nsz : NormedSpace ℝ Z]
  [csz : CompleteSpace Z]
  G : Z ≃L[ℝ] Z
  D0 : Z →L[ℝ] Z
  DN : Z →L[ℝ] Z
  D0inv : Z →L[ℝ] Z
  D0_left : D0inv ∘L D0 = 1
  D0_right : D0 ∘L D0inv = 1

attribute [instance] NearPkg.nz NearPkg.nsz NearPkg.csz

/-- `δ_N = ‖G⁻¹(D_N - D₀)G‖` (line 3931). -/
def NearPkg.deltaN (p : NearPkg) : ℝ := ‖conjG p.G (p.DN - p.D0)‖

/-- `Q`-quantity `‖G⁻¹D₀⁻¹G‖` of `near:flat-bound` (lines 3884-3886). -/
def NearPkg.flatNorm (p : NearPkg) : ℝ := ‖conjG p.G p.D0inv‖

/-- `near:flat-bound` (line 3884): `‖G⁻¹D₀⁻¹G‖_{Z→Z} ≤ Q := P_ν`, with the polynomial fixed before
the parameters of the comparison. -/
def NearFlatBound (pk : NearParams → NearPkg) : Prop :=
  ∃ (C : ℝ) (k : ℕ), ∀ p : NearParams, 0 < p.ν → p.ν ≤ 1 → (pk p).flatNorm ≤ C * p.ν⁻¹ ^ k

/-- `near:deltaN` (lines 3927-3942): there is a fixed integer `K`, chosen before `a, b`, such that
for `μ` in a fixed compact subset of `(0,1/4)` and `0 < b < 1`,
`δ_N ≤ P_ν · deltaNRhs` with `η_δ = γ tanh(3δ/8)`. -/
def NearDeltaBound (γ : ℝ) (pk : NearParams → NearPkg) : Prop :=
  ∃ K : ℕ, ∀ (Kset : Set ℝ), IsCompact Kset → Kset ⊆ Ioo 0 (1 / 4) →
    ∀ a b δ m0 Dp : ℝ, 0 < a → 0 < b → b < 1 → 0 < δ → 0 ≤ m0 → 0 < Dp →
      ∃ (C : ℝ) (k : ℕ), ∀ (ν ε μ : ℝ), 0 < ν → ν ≤ 1 → 0 < ε → ε ≤ 1 → μ ∈ Kset →
        (pk ⟨ν, ε, μ, a, b, δ, m0, Dp⟩).deltaN ≤
          C * ν⁻¹ ^ k * deltaNRhs a b K (γ * Real.tanh (3 * δ / 8)) m0 Dp ε ν

end UnforcedLeray.Short.PartIIIb
