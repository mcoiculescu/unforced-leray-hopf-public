import UnforcedLeray.Units.B0221.TestProfiles

/-!
# B0221: the exact scalar conjugated free generator `A_ε` and its conjugation identity

Blueprint unit B0221 (label `eq:st18-t00114`), `paper/main.tex` lines 3316–3346
(§`sec:st18-2325`), depending on B0220 (`eq:st18-t00113`, the lift `U = a b` and the unitary
`J_ε`, file `Units/B0220.lean`).

The manuscript sets (tex lines 3318–3326, 3335–3338)

  `S = s∂_s`, `K = 2s∂_s + η∂_η`, `Q_ε = ∂_q - ε(K + 1)`,
  `A_ε = -S + ν s [Q_ε² + ∂_η²]`,   `A_0 = -S + ν s Δ_{q,η}`,

and states (tex lines 3341–3347) that `A_ε` is defined by the exact whole-space generator
domain, with no new boundary condition at the axis or at an age endpoint, being the conjugate
of `ν ε² Δ_x + (x·∇)/2 + 1/2 - ∂_τ`.

Formalization map.

* Operators on profiles `b : Profile → ℝ`, `Profile = (s, q, η)` (file `B0221/Generators.lean`):
  `opS`, `opK`, `opQ`, `Aeps` (`A_ε`), `A0` (`A_0`), with `Aeps_zero : Aeps ν 0 = A0 ν`.
  The derivatives are Fréchet derivatives; all claims assume `C²` regularity at the point.
* The outer operator on scalar fields `U : Space × ℝ → ℝ`: `outerGen` (classical coordinate
  derivatives; `spatialLap_eq_laplacian` identifies its Laplacian with Mathlib's).
* **Conjugation identity** (`conjugation_identity`, proof in `B0221/Conjugation.lean`): for the
  lift `U = a b(s,q,η)` (`B0220.liftU`) and `b` of class `C²` at the chart point,
  `outerGen ν ε U (x, τ) = a(x) · A_ε b(s, q, η)` at every `x` off the axis.
* **Operator level** (INF24, `B0221/ScalarLift.lean`): the scalar unitary `J_ε` (`Jsc`, onto the
  axisymmetric scalar fields, `range_Jsc`, `JscEquiv`) and the conjugate `J_ε⁻¹ G J_ε` of an
  operator `G` on `L²(dx dτ)`. `AepsOp G` is the exact scalar conjugated free generator on `H`,
  `G` being the exact whole-space generator. Its domain is exactly the conjugate of the domain
  of `G` (`mem_domain_AepsOp_iff`, given that `G` preserves axisymmetry, `PreservesAxisym`;
  `mem_domain_conjOp_iff` in general): no condition is imposed at the axis or at an age endpoint.
* **Consistency** (`AepsOp_eq_formula`, `B0221/Consistency.lean`): if `G` acts on smooth test
  fields as the classical outer operator (`GeneratorOnTestFields`), then on every `C²`,
  `q`-periodic profile supported in a compact age band and a bounded `η` range, `AepsOp G` acts
  by the formula `A_ε`; `AepsOp_toLp` states it with the `H`-classes of `b` and `A_ε b`
  constructed (`B0221/TestProfiles.lean`), so the statement is not vacuous.

The whole-space generator itself (of the semigroup `S_ε(t)`, tex lines 3348–3352, blueprint
unit B0223) is not formalized; it enters only through the named hypotheses `PreservesAxisym`
and `GeneratorOnTestFields`, which are properties of that generator. The identification of the
domain with a maximal distributional graph (`sec:st18-9487`) is not part of this unit.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open UnforcedLeray.B0220

namespace UnforcedLeray.B0221

/-! ### The profile operators (tex lines 3318–3338) -/

/-- `A_ε = -S + ν s [Q_ε² + ∂_η²]` unfolds as in display `eq:st18-t00114`. -/
theorem Aeps_def (ν ε : ℝ) (b : Profile → ℝ) (p : Profile) :
    Aeps ν ε b p = -(p.1 * dS b p) + ν * p.1 * (opQ ε (opQ ε b) p + dEta (dEta b) p) := rfl

/-- `Q_ε = ∂_q - ε (K + 1)` with `K = 2 s ∂_s + η ∂_η` (tex lines 3320–3321). -/
theorem opQ_def (ε : ℝ) (b : Profile → ℝ) (p : Profile) :
    opQ ε b p = dQ b p - ε * ((2 * p.1 * dS b p + p.2.2 * dEta b p) + b p) := rfl

/-- The limiting generator: `A_ε` at `ε = 0` is `A_0 = -S + ν s Δ_{q,η}` (tex line 3337). -/
theorem limiting_generator (ν : ℝ) : Aeps ν 0 = A0 ν := funext fun b => Aeps_zero ν b

/-! ### The conjugation identity (tex lines 3341–3347) -/

/-- **Conjugation identity** (tex lines 3316–3347, blueprint B0221). For the lift
`U(x, τ) = a b(s, q, η)` of `eq:st18-t00113` (`a = 1/r`, `s = r⁻²`,
`q = ε⁻¹ log r + τ/(2ε)`, `η = z/(εr)`) and a scalar profile `b` of class `C²` at the chart
point, at every `x` off the axis
`(ν ε² Δ_x + (x·∇)/2 + 1/2 - ∂_τ) U (x, τ) = a(x) · (A_ε b)(s, q, η)`. -/
theorem conjugation_identity {ν ε : ℝ} (hε : ε ≠ 0) {b : Profile → ℝ} {x : Space} {τ : ℝ}
    (hx : radius x ≠ 0) (hb : ContDiffAt ℝ 2 b (chart ε (x, τ))) :
    outerGen ν ε (liftU ε b) (x, τ) = liftA x * Aeps ν ε b (chart ε (x, τ)) :=
  outerGen_liftU hε hx hb

/-- The conjugation identity in terms of the unconjugated outer field: with the `C²` profile
`b` defined on the open age half-space `s > 0`, it holds at every point off the axis. -/
theorem conjugation_identity_on {ν ε : ℝ} (hε : ε ≠ 0) {b : Profile → ℝ}
    (hb : ContDiffOn ℝ 2 b {p | 0 < p.1}) {y : Space × ℝ} (hy : radius y.1 ≠ 0) :
    outerGen ν ε (liftU ε b) y = liftA y.1 * Aeps ν ε b (chart ε y) := by
  obtain ⟨x, τ⟩ := y
  exact outerGen_liftU hε hy
    (hb.contDiffAt ((isOpen_lt continuous_const continuous_fst).mem_nhds (chart_fst_pos hy)))

/-! ### `A_ε` as the conjugate of the whole-space generator (tex lines 3341–3347) -/

section Operator

variable {ε c : ℝ} (hε : 0 < ε) (hc : 0 < c)

/-- **The exact scalar conjugated free generator on `H`** (tex lines 3341–3347): the conjugate
`J_ε⁻¹ G J_ε` of the exact whole-space generator `G` on `L²(dx dτ)` by the scalar unitary lift
`J_ε` (`Jsc`). -/
def AepsOp (G : PhysL2sc ε c →ₗ.[ℝ] PhysL2sc ε c) : HSpace c ℝ →ₗ.[ℝ] HSpace c ℝ :=
  conjOp hε hc G

/-- **Named hypothesis (axisymmetry of the whole-space generator).** `G` maps the axisymmetric
scalar fields of its domain to axisymmetric fields. This holds for the generator of the outer
semigroup `S_ε(t)` (tex lines 3348–3352, blueprint unit B0223, not yet formalized), which
commutes with the rotations about the `e₃` axis. -/
def PreservesAxisym (G : PhysL2sc ε c →ₗ.[ℝ] PhysL2sc ε c) : Prop :=
  ∀ V : G.domain, (V : PhysL2sc ε c) ∈ axisymSubspace ε c → G V ∈ axisymSubspace ε c

/-- The domain of `A_ε` in general: `b ∈ dom A_ε` iff `J_ε b ∈ dom G` and `G J_ε b` is the lift
of an element of `H`. -/
theorem mem_domain_AepsOp_iff' (G : PhysL2sc ε c →ₗ.[ℝ] PhysL2sc ε c) (b : HSpace c ℝ) :
    b ∈ (AepsOp hε hc G).domain ↔
      ∃ h : Jsc hε hc b ∈ G.domain,
        G ⟨Jsc hε hc b, h⟩ ∈ LinearMap.range (Jsc hε hc).toLinearMap :=
  mem_domain_conjOp_iff hε hc G b

/-- **The domain of `A_ε` is the conjugate of the whole-space generator domain** (tex lines
3341–3342): `b ∈ dom A_ε ↔ J_ε b ∈ dom G`. No boundary condition is imposed at the axis or at an
age endpoint. -/
theorem mem_domain_AepsOp_iff (G : PhysL2sc ε c →ₗ.[ℝ] PhysL2sc ε c) (hG : PreservesAxisym G)
    (b : HSpace c ℝ) : b ∈ (AepsOp hε hc G).domain ↔ Jsc hε hc b ∈ G.domain := by
  rw [mem_domain_AepsOp_iff']
  constructor
  · rintro ⟨h, -⟩
    exact h
  · intro h
    refine ⟨h, ?_⟩
    rw [range_Jsc]
    refine hG ⟨Jsc hε hc b, h⟩ ?_
    rw [← range_Jsc hε hc]
    exact LinearMap.mem_range_self _ b

/-- **Conjugation on the domain**: `J_ε A_ε b = G J_ε b` (tex lines 3343–3347). -/
theorem Jsc_AepsOp (G : PhysL2sc ε c →ₗ.[ℝ] PhysL2sc ε c) (b : (AepsOp hε hc G).domain)
    (h : Jsc hε hc b ∈ G.domain) :
    Jsc hε hc (AepsOp hε hc G b) = G ⟨Jsc hε hc b, h⟩ :=
  Jsc_conjOp hε hc G b h

/-- **`A_ε` acts on smooth profiles by the formula** `-S + ν s [Q_ε² + ∂_η²]` (tex lines
3316–3347). If the whole-space generator `G` acts on test fields as the classical outer
operator (`GeneratorOnTestFields`), then every `C²`, `c`-periodic profile `b` supported in an
age band `s ∈ [s₀, S₁]` and a bounded range `|η| ≤ Z` lies (through its `H`-class `bL`) in the
domain of `A_ε`, and `A_ε bL` is the `H`-class `Ab` of the function `Aeps ν ε b`. -/
theorem AepsOp_eq_formula {ν : ℝ} (G : PhysL2sc ε c →ₗ.[ℝ] PhysL2sc ε c)
    (hG : GeneratorOnTestFields ν ε c G) {b : Profile → ℝ} {s0 S1 Z : ℝ} (hs0 : 0 < s0)
    (hS1 : s0 ≤ S1) (hb : ContDiffOn ℝ 2 b {p | 0 < p.1}) (hper : QPeriodic c b)
    (hsupp : ∀ p : Profile, 0 < p.1 → b p ≠ 0 → p.1 ∈ Icc s0 S1 ∧ |p.2.2| ≤ Z)
    (bL : HSpace c ℝ) (hbL : (bL : Profile → ℝ) =ᵐ[measureH c] b)
    (Ab : HSpace c ℝ) (hAb : (Ab : Profile → ℝ) =ᵐ[measureH c] Aeps ν ε b) :
    ∃ h : bL ∈ (AepsOp hε hc G).domain, AepsOp hε hc G ⟨bL, h⟩ = Ab :=
  conjOp_eq_Aeps hε hc G hG hs0 hS1 hb hper hsupp bL hbL Ab hAb

/-- **`A_ε` acts on smooth band-supported profiles by the formula**, with the `H`-classes
constructed (tex lines 3316–3347; `B0221/TestProfiles.lean`): every `C²`, `c`-periodic profile
`b` supported in `s ∈ [s₀, S₁]`, `|η| ≤ Z` (`s₀ > 0`) lies in `H`, so does `A_ε b`, the class of
`b` lies in the domain of `A_ε`, and `A_ε` maps it to the class of `A_ε b`. -/
theorem AepsOp_toLp {ν : ℝ} (G : PhysL2sc ε c →ₗ.[ℝ] PhysL2sc ε c)
    (hG : GeneratorOnTestFields ν ε c G) {b : Profile → ℝ} {s0 S1 Z : ℝ} (hs0 : 0 < s0)
    (hS1 : s0 ≤ S1) (hb : ContDiffOn ℝ 2 b {p | 0 < p.1}) (hper : QPeriodic c b)
    (hsupp : ∀ p : Profile, 0 < p.1 → b p ≠ 0 → p.1 ∈ Icc s0 S1 ∧ |p.2.2| ≤ Z) :
    ∃ (hbL : MemLp b 2 (measureH c)) (hAb : MemLp (Aeps ν ε b) 2 (measureH c))
      (h : hbL.toLp b ∈ (AepsOp hε hc G).domain),
        AepsOp hε hc G ⟨hbL.toLp b, h⟩ = hAb.toLp (Aeps ν ε b) := by
  have hbL : MemLp b 2 (measureH c) := memLp_testProfile hs0 hb hsupp
  have hAb : MemLp (Aeps ν ε b) 2 (measureH c) := memLp_Aeps_testProfile ν ε hs0 hb hsupp
  obtain ⟨h, hEq⟩ := AepsOp_eq_formula hε hc G hG hs0 hS1 hb hper hsupp (hbL.toLp b)
    hbL.coeFn_toLp (hAb.toLp _) hAb.coeFn_toLp
  exact ⟨hbL, hAb, h, hEq⟩

/-- The scalar lift `J_ε` is unitary from `H` onto the axisymmetric scalar fields of
`L²(dx dτ)` (the scalar form of B0220's `J_ε`, on which `A_ε` acts). -/
def unitaryLift : HSpace c ℝ ≃ₗᵢ[ℝ] axisymSubspace ε c := JscEquiv hε hc

end Operator

end UnforcedLeray.B0221
