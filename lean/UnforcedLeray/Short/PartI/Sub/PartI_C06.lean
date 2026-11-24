import UnforcedLeray.Short.PartI.StatementsCanonical
import UnforcedLeray.Short.PartI.Sub.PartI_C05
import UnforcedLeray.Short.PartI.Tasks.RfIdentity

/-!
# Part I, task `PartI:C06`: the canonical branch at infinity (design and assembly)

Source of record: `the November 2 reference manuscript`, proof of
Proposition `prop:short-canonical`, lines 1094-1122.

## The reduced system (lines 1095-1111)

Write `W(θ) = e^{λθ}θ^κ V(θ) = A(θ) q + r(θ)` with `A = ℓ(W)` and `r = QW = W - ℓ(W) q`, so that
`ℓ r = 0` (as `ℓ q = 1`).  The equation `-V' = (L + θ⁻¹D)V` becomes (lines 1097-1101)
`-A' = θ⁻¹ ℓ(Dr)`, `-r' = Q{L - λ + θ⁻¹(D - κ)}Q r + θ⁻¹ A QDq`.

* `ℓ(D·)` is the bounded functional `seedLD qd hqd = ⟨Dq†, ·⟩` (`ℓ = ⟨q†, ·⟩`, `q† ∈ 𝒟(D)`, `D`
  self-adjoint: line 1112 "`ℓD` is bounded"), and `QDq = seedQDq l q hq = Dq - κq`.
* The forward complementary evolution `S(θ,s)`, `b ≤ θ ≤ s` (lines 1102-1104), is
  `canonicalS U θ s = U(-θ,-s)`, where `U` is the mild evolution of Lemma
  `short-diffusion-complement` (`IsMildComplementEvolution`; its generator
  `L - λ - P + β(D - κ + R_f)` equals `Q{L - λ + β(D - κ)}Q` on `QX_G` by `seedRf_spec`) in the
  forward time `t = -θ`, with the clock `β(t) = 1/(-t)` for `t ≤ -b`
  (`canonicalClock b t = (max (-t) b)⁻¹`, so `0 < β ≤ 1/b ≤ β_*` once `b ≥ β_*⁻¹`).
* `canonicalRA` and `canonicalTA` are `r_A` and `𝒯A` of lines 1106-1111.
* `IsCanonicalMild lam q l qd hq hqd b V` ("`V` is a mild solution of `-V' = (L + θ⁻¹D)V` on
  `[b,∞)`") is the system of coupled mild initial-value equations of lines 1117-1119
  (`CoupledMild`): for `b ≤ θ ≤ s₀`,
  `r(θ) = S(θ,s₀) r(s₀) + ∫_θ^{s₀} S(θ,s) QDq A(s)/s ds`, `A(θ) = A(s₀) + ∫_θ^{s₀} ℓ(D r(s))/s ds`,
  for `V` continuous on `[b,∞)` (all integrands are then continuous, `MildComplementContStart`).

## The ladder (lines 1112-1122)

* `MildComplementUnique`, `MildComplementContStart`: the mild complementary evolution is unique
  and strongly continuous in its initial time; with `mildComplementCocycle` and
  `SmallDiffusionComplement` this makes `canonicalS U` an `IsComplementPropagator`
  (`isComplementPropagator_canonicalS`).
* `CanonicalRABound`, `CanonicalRAContinuous`, `TailIntegralProps`: the tail bounds
  `‖r_A(θ)‖ + |𝒯A(θ) - 1| ≤ Cθ⁻¹‖A‖_∞` (lines 1112-1114) and continuity; with linearity this gives
  the difference estimate (`canonicalTA_estimates_of`, lines 1114-1116).
* `FixedPointIci`: the contraction has a unique fixed point in `C_b([b,∞))` (line 1115).
* `CanonicalFixedMild`: the fixed point satisfies the coupled mild equations (lines 1117-1118).
* `CanonicalNormalizedUnique`, `CanonicalAsymptoticBounds`: every normalized mild solution
  satisfies the integrals, since `S(θ,s₀)r(s₀) → 0` (lines 1119-1122).
* `canonical_infinity_fixed_point_of`: existence, the asymptotic `e^{-λθ}θ^{-κ}{q + O(θ⁻¹)}`, and
  uniqueness at infinity.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.PartI

/-! ### Objects -/

/-- The clock of the canonical system in the forward time `t = -θ` (lines 1102-1104, eq.
`short-heat-clock`): `β(t) = 1/(-t)` for `t ≤ -b`, frozen at `1/b` for `t ≥ -b`, so that
`0 < β ≤ 1/b`. -/
def canonicalClock (b t : ℝ) : ℝ := (max (-t) b)⁻¹

/-- The forward complementary evolution `S(θ,s) = U(-θ,-s)`, `b ≤ θ ≤ s` (lines 1102-1104): `U` is
the mild evolution of Lemma `short-diffusion-complement` (forward in `t = -θ`). -/
def canonicalS (U : ℝ → ℝ → B0010.XG →L[ℂ] B0010.XG) (θ s : ℝ) : B0010.XG →L[ℂ] B0010.XG :=
  U (-θ) (-s)

/-- `QDq = Dq - κ q`, `κ = ℓ(Dq)` (line 1100). -/
def seedQDq (l : B0010.XG →L[ℂ] ℂ) (q : B0010.XG) (hq : q ∈ B0094.D.domain) : B0010.XG :=
  B0094.D ⟨q, hq⟩ - seedKappa l q hq • q

/-- The bounded functional `f ↦ ℓ(Df) = ⟨Dq†, f⟩` (line 1112, "`ℓD` is bounded"; `ℓ = ⟨q†, ·⟩`,
`D` self-adjoint). -/
def seedLD (qd : B0010.XG) (hqd : qd ∈ B0094.D.domain) : B0010.XG →L[ℂ] ℂ :=
  innerSL ℂ (B0094.D ⟨qd, hqd⟩)

/-- `r_A(θ) = ∫_θ^∞ S(θ,s) y A(s)/s ds` with `y = QDq` (lines 1107-1108). -/
def canonicalRA (S : ℝ → ℝ → B0010.XG →L[ℂ] B0010.XG) (y : B0010.XG) (A : ℝ → ℂ) (θ : ℝ) :
    B0010.XG :=
  ∫ s in Ioi θ, (A s / s) • S θ s y

/-- `(𝒯A)(θ) = 1 + ∫_θ^∞ φ(r_A(s))/s ds` with `φ = ℓ(D·)` (lines 1109-1110). -/
def canonicalTA (S : ℝ → ℝ → B0010.XG →L[ℂ] B0010.XG) (y : B0010.XG) (φ : B0010.XG →L[ℂ] ℂ)
    (A : ℝ → ℂ) (θ : ℝ) : ℂ :=
  1 + ∫ s in Ioi θ, φ (canonicalRA S y A s) / s

/-- The normalized state `W(θ) = e^{λθ}θ^κ V(θ) = A(θ)q + r(θ)` (line 1095). -/
def canonicalW (lam κ : ℂ) (V : ℝ → B0010.XG) (θ : ℝ) : B0010.XG :=
  Complex.exp (lam * θ) • (θ : ℂ) ^ κ • V θ

/-- The coupled mild initial-value equations on `[b,∞)` (lines 1097-1101 and 1117-1119): for
`b ≤ θ ≤ s₀`, `r(θ) = S(θ,s₀) r(s₀) + ∫_θ^{s₀} S(θ,s) y A(s)/s ds` (mild form of
`-r' = Q{L-λ+θ⁻¹(D-κ)}Qr + θ⁻¹A y`) and `A(θ) = A(s₀) + ∫_θ^{s₀} φ(r(s))/s ds` (integrated form of
`-A' = θ⁻¹ ℓ(Dr)`). -/
def CoupledMild (S : ℝ → ℝ → B0010.XG →L[ℂ] B0010.XG) (y : B0010.XG) (φ : B0010.XG →L[ℂ] ℂ)
    (b : ℝ) (A : ℝ → ℂ) (r : ℝ → B0010.XG) : Prop :=
  ∀ θ s₀ : ℝ, b ≤ θ → θ ≤ s₀ →
    r θ = S θ s₀ (r s₀) + ∫ s in θ..s₀, (A s / s) • S θ s y ∧
    A θ = A s₀ + ∫ s in θ..s₀, φ (r s) / s

/-- **`V` is a mild solution of `-V' = (L + θ⁻¹D)V` on `[b,∞)`** (lines 1095-1119): `V` is
continuous on `[b,∞)` and, with `W = e^{λθ}θ^κ V`, `A = ℓ(W)` and `r = W - ℓ(W)q` (so
`V = e^{-λθ}θ^{-κ}(Aq + r)`, `ℓr = 0`), the pair `(A, r)` satisfies the coupled mild
initial-value equations with respect to the forward complementary evolution
`S(θ,s) = U(-θ,-s)` of the clock `canonicalClock b` (`U` the mild evolution of Lemma
`short-diffusion-complement`, unique by `MildComplementUnique`). -/
def IsCanonicalMild (lam : ℂ) (q : B0010.XG) (l : B0010.XG →L[ℂ] ℂ) (qd : B0010.XG)
    (hq : q ∈ B0094.D.domain) (hqd : qd ∈ B0094.D.domain) (b : ℝ) (V : ℝ → B0010.XG) : Prop :=
  ContinuousOn V (Ici b) ∧
    ∃ U : ℝ → ℝ → B0010.XG →L[ℂ] B0010.XG, MildCtx lam q l qd hq hqd (canonicalClock b) U ∧
      CoupledMild (canonicalS U) (seedQDq l q hq) (seedLD qd hqd) b
        (fun θ => l (canonicalW lam (seedKappa l q hq) V θ))
        (fun θ => canonicalW lam (seedKappa l q hq) V θ -
          l (canonicalW lam (seedKappa l q hq) V θ) • q)

/-- The properties of `S(θ,s) = U(-θ,-s)`, `b ≤ θ ≤ s`, used in the fixed-point argument
(lines 1102-1104): cocycle, strong continuity in each variable, invariance of `QX_G = ker ℓ` and
the decay `‖S(θ,s)x‖ ≤ Ce^{-g(s-θ)}‖x‖` on `ker ℓ`. -/
structure IsComplementPropagator (l : B0010.XG →L[ℂ] ℂ) (b C g : ℝ)
    (S : ℝ → ℝ → B0010.XG →L[ℂ] B0010.XG) : Prop where
  cocycle : ∀ θ s s' : ℝ, b ≤ θ → θ ≤ s → s ≤ s' → S θ s' = S θ s * S s s'
  cont_fst : ∀ (s : ℝ) (x : B0010.XG), ContinuousOn (fun θ => S θ s x) (Icc b s)
  cont_snd : ∀ (θ : ℝ) (x : B0010.XG), b ≤ θ → ContinuousOn (fun s => S θ s x) (Ici θ)
  ker : ∀ (θ s : ℝ) (x : B0010.XG), b ≤ θ → θ ≤ s → l x = 0 → l (S θ s x) = 0
  decay : ∀ (θ s : ℝ) (x : B0010.XG), b ≤ θ → θ ≤ s → l x = 0 →
    ‖S θ s x‖ ≤ C * Real.exp (-(g * (s - θ))) * ‖x‖

/-! ### The ladder (open leaves) -/

/-- **Leaf 1** (uniqueness of the mild complementary evolution; lines 1117-1119 "uniqueness
follows from the bounded coupling maps and Gronwall", and line 1052 of
`lem:short-diffusion-complement`): two mild complementary evolutions with the same measurable
coefficient `0 ≤ β ≤ 1` agree for `s ≤ t`.  Sketch: `D(t) = U(t,s)x - U'(t,s)x` satisfies
`D(t) = ∫_s^t e^{D∫_r^tβ} B_β(r) D(r) dr` (subtract the two `duhamel` fields), so
`‖D(t)‖ ≤ M ∫_s^t ‖D‖` with `M = ‖L₀ - λ - P‖ + |κ| + ‖R_f‖` (`mcc_norm_B_le`), and the Gronwall
inequality with zero constant (`NonUniqueEuler.LinODE.int_gronwall`) gives `D = 0`; this is
`mcc_cocycle_core` of `Tasks/SmallDiffusionAssembly/MildCocycle.lean` with `U'(·,s)x` in place
of `U(·,r)U(r,s)x`. -/
def MildComplementUnique : Prop :=
  ∀ (lam : ℂ) (q : B0010.XG) (l : B0010.XG →L[ℂ] ℂ), IsSeedXG lam q l →
    ∀ (qd : B0010.XG), (∀ f, l f = inner ℂ qd f) →
    ∀ (hq : q ∈ B0094.D.domain) (hqd : qd ∈ B0094.D.domain) (β : ℝ → ℝ),
      Measurable β → (∀ t, 0 ≤ β t ∧ β t ≤ 1) →
      ∀ U U' : ℝ → ℝ → B0010.XG →L[ℂ] B0010.XG,
        MildCtx lam q l qd hq hqd β U → MildCtx lam q l qd hq hqd β U' →
          ∀ s t : ℝ, s ≤ t → U t s = U' t s

/-- **Leaf 2** (strong continuity in the initial time; lines 1102-1103, `S(θ,s)` is an evolution
family, needed for the integrands `s ↦ S(θ,s)QDq A(s)/s` of lines 1107-1108): for every mild
complementary evolution, `s ↦ U(t,s)x` is continuous on `(-∞, t]`.  Sketch: cocycle
(`mildComplementCocycle`) and the short-block bound `K` (`mildComplementShortBound`); for
`s₀ ≤ s ≤ t`, `U(t,s₀)x - U(t,s)x = U(t,s)(U(s,s₀)x - x)` (right side, `cont` at `s₀`); for
`s ≤ s₀`, `U(t,s)x - U(t,s₀)x = U(t,s₀)(U(s₀,s)x - x)` and by `duhamel`
`‖U(s₀,s)x - x‖ ≤ ‖e^{D∫_s^{s₀}β}x - x‖ + (s₀ - s) M K ‖x‖ → 0`
(`Cons.G3b.continuous_expD_apply`, `B0123.expD_zero`, `B0123.norm_expD_le`). -/
def MildComplementContStart : Prop :=
  ∀ (lam : ℂ) (q : B0010.XG) (l : B0010.XG →L[ℂ] ℂ), IsSeedXG lam q l →
    ∀ (qd : B0010.XG), (∀ f, l f = inner ℂ qd f) →
    ∀ (hq : q ∈ B0094.D.domain) (hqd : qd ∈ B0094.D.domain) (β : ℝ → ℝ),
      Measurable β → (∀ t, 0 ≤ β t ∧ β t ≤ 1) →
      ∀ U : ℝ → ℝ → B0010.XG →L[ℂ] B0010.XG, MildCtx lam q l qd hq hqd β U →
        ∀ (t : ℝ) (x : B0010.XG), ContinuousOn (fun s => U t s x) (Iic t)

/-- **Leaf 3** (the complement tail bound, lines 1112-1114): for `A` continuous on `[b,∞)` with
`|A| ≤ M` and `y ∈ ker ℓ`, the integrand of `r_A(θ)` is integrable on `(θ,∞)`,
`‖r_A(θ)‖ ≤ C‖y‖M/(gθ)`, and `ℓ(r_A(θ)) = 0`.  Sketch: the integrand is continuous on `[θ,∞)`
(`cont_snd`) and bounded by `(M/θ)C‖y‖e^{-g(s-θ)}` (`decay`, `1/s ≤ 1/θ`), integrable by
`exp_neg_integrableOn_Ioi`; `∫_θ^∞ e^{-g(s-θ)} ds = 1/g`
(`integral_comp_mul_left_Ioi`/`integral_exp_neg_Ioi`); `ℓ` commutes with the Bochner integral
(`ContinuousLinearMap.integral_comp_comm`) and `ℓ(S(θ,s)y) = 0` (`ker`). -/
def CanonicalRABound : Prop :=
  ∀ (l : B0010.XG →L[ℂ] ℂ) (b C g : ℝ) (S : ℝ → ℝ → B0010.XG →L[ℂ] B0010.XG),
    0 < b → 0 ≤ C → 0 < g → IsComplementPropagator l b C g S →
    ∀ (y : B0010.XG), l y = 0 → ∀ (A : ℝ → ℂ) (M : ℝ), ContinuousOn A (Ici b) →
      (∀ θ, b ≤ θ → ‖A θ‖ ≤ M) → ∀ θ, b ≤ θ →
        IntegrableOn (fun s => (A s / s) • S θ s y) (Ioi θ) ∧
        ‖canonicalRA S y A θ‖ ≤ C * ‖y‖ * M / (g * θ) ∧ l (canonicalRA S y A θ) = 0

/-- **Leaf 4** (continuity of `r_A`, needed for `𝒯A ∈ C_b([b,∞))`, line 1115): `θ ↦ r_A(θ)` is
continuous on `[b,∞)`.  Sketch: `r_A(θ) = ∫_{(b,∞)} 1_{s>θ}(A(s)/s) S(θ,s)y ds`
(`setIntegral_indicator`); dominated convergence within `Ici b`
(`MeasureTheory.continuousWithinAt_of_dominated`): for `s ≠ θ₀` the integrand is continuous in
`θ` near `θ₀` (`cont_fst` for `s > θ₀`, zero for `s < θ₀`), and for `θ ≤ θ₀ + 1` it is bounded by
`(M/b)C‖y‖e^{g(θ₀+1)}e^{-gs}`, integrable on `(b,∞)`. -/
def CanonicalRAContinuous : Prop :=
  ∀ (l : B0010.XG →L[ℂ] ℂ) (b C g : ℝ) (S : ℝ → ℝ → B0010.XG →L[ℂ] B0010.XG),
    0 < b → 0 ≤ C → 0 < g → IsComplementPropagator l b C g S →
    ∀ (y : B0010.XG), l y = 0 → ∀ (A : ℝ → ℂ) (M : ℝ), ContinuousOn A (Ici b) →
      (∀ θ, b ≤ θ → ‖A θ‖ ≤ M) → ContinuousOn (canonicalRA S y A) (Ici b)

/-- **Leaf 5** (the amplitude tail, lines 1109-1114): for `r` continuous on `[b,∞)` with
`‖r(θ)‖ ≤ K/θ` and a bounded functional `φ`, the integrand `φ(r(s))/s` is integrable on `(θ,∞)`,
`|∫_θ^∞ φ(r(s))/s ds| ≤ ‖φ‖K/θ`, and `θ ↦ ∫_θ^∞ φ(r(s))/s ds` is continuous on `[b,∞)`.  Sketch:
`|φ(r(s))/s| ≤ ‖φ‖K s⁻²` (`ContinuousLinearMap.le_opNorm`), `integrableOn_Ioi_rpow_of_lt`,
`integral_Ioi_rpow_of_lt` (`∫_θ^∞ s⁻² = θ⁻¹`); continuity: `∫_{(θ,∞)} = ∫_{(b,∞)} - ∫_b^θ`
(`setIntegral_union`, `Set.Ioc_union_Ioi_eq_Ioi`, `intervalIntegral.integral_of_le`) and
`intervalIntegral.continuousOn_primitive_interval`. -/
def TailIntegralProps : Prop :=
  ∀ (φ : B0010.XG →L[ℂ] ℂ) (b K : ℝ) (r : ℝ → B0010.XG), 0 < b → ContinuousOn r (Ici b) →
    (∀ θ, b ≤ θ → ‖r θ‖ ≤ K / θ) →
      ContinuousOn (fun θ => ∫ s in Ioi θ, φ (r s) / s) (Ici b) ∧
      ∀ θ, b ≤ θ → IntegrableOn (fun s => φ (r s) / s) (Ioi θ) ∧
        ‖∫ s in Ioi θ, φ (r s) / s‖ ≤ ‖φ‖ * K / θ

/-- **Leaf 6** (the contraction principle on `C_b([b,∞))`, line 1115): a map `T` of bounded
continuous functions on `[b,∞)` into themselves with `sup|TA - TA'| ≤ ½ sup|A - A'|` has a
fixed point there, unique among bounded continuous functions.  Sketch: Picard iteration
`A₀ = 0`, `A_{n+1} = T A_n` with `sup|A_{n+1} - A_n| ≤ 2^{-n} sup|T 0|`, uniform limit on
`Ici b` (`TendstoUniformlyOn.continuousOn`); or `ContractingWith.fixedPoint` on the complete
space `Ici b →ᵇ ℂ` (`BoundedContinuousFunction.instCompleteSpace`), extending functions by
`θ ↦ A(max θ b)`.  Uniqueness: `sup|A' - A| ≤ δ` implies `≤ δ/2`, iterate. -/
def FixedPointIci : Prop :=
  ∀ (b : ℝ) (T : (ℝ → ℂ) → ℝ → ℂ),
    (∀ A : ℝ → ℂ, ContinuousOn A (Ici b) → (∃ M, ∀ θ, b ≤ θ → ‖A θ‖ ≤ M) →
      ContinuousOn (T A) (Ici b) ∧ ∃ M, ∀ θ, b ≤ θ → ‖T A θ‖ ≤ M) →
    (∀ A A' : ℝ → ℂ, ContinuousOn A (Ici b) → (∃ M, ∀ θ, b ≤ θ → ‖A θ‖ ≤ M) →
      ContinuousOn A' (Ici b) → (∃ M, ∀ θ, b ≤ θ → ‖A' θ‖ ≤ M) →
      ∀ δ : ℝ, (∀ θ, b ≤ θ → ‖A θ - A' θ‖ ≤ δ) → ∀ θ, b ≤ θ → ‖T A θ - T A' θ‖ ≤ δ / 2) →
    ∃ A : ℝ → ℂ, ContinuousOn A (Ici b) ∧ (∃ M, ∀ θ, b ≤ θ → ‖A θ‖ ≤ M) ∧
      (∀ θ, b ≤ θ → T A θ = A θ) ∧
      ∀ A' : ℝ → ℂ, ContinuousOn A' (Ici b) → (∃ M, ∀ θ, b ≤ θ → ‖A' θ‖ ≤ M) →
        (∀ θ, b ≤ θ → T A' θ = A' θ) → ∀ θ, b ≤ θ → A' θ = A θ

/-- **Leaf 7** (the fixed point solves the coupled mild equations, lines 1117-1118: "splitting
both integrals at any finite `s₀` verifies the coupled mild initial-value equations"): if
`𝒯A = A` on `[b,∞)` then `(A, r_A)` satisfies `CoupledMild`.  Sketch: `Ioi θ = Ioc θ s₀ ∪ Ioi s₀`
(`Set.Ioc_union_Ioi_eq_Ioi`, `setIntegral_union`, `intervalIntegral.integral_of_le`); on
`(s₀,∞)` use the cocycle `S(θ,s) = S(θ,s₀)S(s₀,s)` and
`ContinuousLinearMap.integral_comp_comm` to get `S(θ,s₀) r_A(s₀)`; subtract `𝒯A(s₀) = A(s₀)` from
`𝒯A(θ) = A(θ)` for the amplitude. -/
def CanonicalFixedMild : Prop :=
  ∀ (b : ℝ) (S : ℝ → ℝ → B0010.XG →L[ℂ] B0010.XG) (y : B0010.XG) (φ : B0010.XG →L[ℂ] ℂ)
    (A : ℝ → ℂ),
    (∀ θ s s' : ℝ, b ≤ θ → θ ≤ s → s ≤ s' → S θ s' = S θ s * S s s') →
    (∀ θ, b ≤ θ → IntegrableOn (fun s => (A s / s) • S θ s y) (Ioi θ)) →
    (∀ θ, b ≤ θ → IntegrableOn (fun s => φ (canonicalRA S y A s) / s) (Ioi θ)) →
    (∀ θ, b ≤ θ → canonicalTA S y φ A θ = A θ) →
      CoupledMild S y φ b A (canonicalRA S y A)

/-- **Leaf 8** (normalized solutions satisfy the integrals, lines 1119-1122: "the term
`S(θ,s₀)r(s₀)` tends to zero as `s₀ → ∞`"): if `(A, r)` solves the coupled mild equations with
`r ∈ ker ℓ` bounded and `A(θ) → 1`, then `r = r_A` and `A = 𝒯A` on `[b,∞)`.  Sketch: fix `θ`,
let `s₀ → ∞` in the two equations: `‖S(θ,s₀)r(s₀)‖ ≤ Ce^{-g(s₀-θ)}K → 0` (`decay`), and
`∫_θ^{s₀} → ∫_θ^∞` (`MeasureTheory.intervalIntegral_tendsto_integral_Ioi`); conclude by
`tendsto_nhds_unique`; the amplitude integral is rewritten with `r = r_A` on `(θ,∞)`
(`setIntegral_congr_fun`). -/
def CanonicalNormalizedUnique : Prop :=
  ∀ (l : B0010.XG →L[ℂ] ℂ) (b C g : ℝ) (S : ℝ → ℝ → B0010.XG →L[ℂ] B0010.XG),
    0 < g → IsComplementPropagator l b C g S →
    ∀ (y : B0010.XG) (φ : B0010.XG →L[ℂ] ℂ) (A : ℝ → ℂ) (r : ℝ → B0010.XG),
      (∀ θ, b ≤ θ → l (r θ) = 0) → (∃ K, ∀ θ, b ≤ θ → ‖r θ‖ ≤ K) →
      (∀ θ, b ≤ θ → IntegrableOn (fun s => (A s / s) • S θ s y) (Ioi θ)) →
      (∀ θ, b ≤ θ → IntegrableOn (fun s => φ (r s) / s) (Ioi θ)) →
      Tendsto A atTop (𝓝 1) → CoupledMild S y φ b A r →
        ∀ θ, b ≤ θ → r θ = canonicalRA S y A θ ∧ A θ = canonicalTA S y φ A θ

/-- **Leaf 9** (what the normalization at infinity gives, eq. `short-canonical-asymptotic`,
lines 1082-1085 and 1119): if `V` is continuous on `[b,∞)`, `b > 0`, `ℓq = 1` and
`‖W(θ) - q‖ ≤ C₀/θ` for `θ ≥ b₀` (`HasCanonicalAsymptotic`), then `W = e^{λθ}θ^κV` is bounded on
`[b,∞)`, `‖W - ℓ(W)q‖ ≤ K/θ` there, and `ℓ(W(θ)) → 1`.  Sketch: on `[b, max b b₀]` use
`continuousOn_canonicalW` and `IsCompact.exists_bound_of_continuousOn`; beyond, `‖W‖ ≤ ‖q‖ + |C₀|/b₀`;
`W - ℓ(W)q = (W - q) - ℓ(W - q)q` (as `ℓq = 1`) has norm `≤ (1 + ‖ℓ‖‖q‖)C₀/θ`;
`|ℓ(W) - 1| = |ℓ(W - q)| ≤ ‖ℓ‖C₀/θ`. -/
def CanonicalAsymptoticBounds : Prop :=
  ∀ (lam κ : ℂ) (q : B0010.XG) (l : B0010.XG →L[ℂ] ℂ), l q = 1 →
    ∀ (b : ℝ) (V : ℝ → B0010.XG), 0 < b → ContinuousOn V (Ici b) →
      HasCanonicalAsymptotic lam κ q V →
        (∃ M, ∀ θ, b ≤ θ → ‖canonicalW lam κ V θ‖ ≤ M) ∧
        (∃ K, ∀ θ, b ≤ θ → ‖canonicalW lam κ V θ - l (canonicalW lam κ V θ) • q‖ ≤ K / θ) ∧
        Tendsto (fun θ => l (canonicalW lam κ V θ)) atTop (𝓝 1)

/-! ### Elementary facts -/

theorem canonicalClock_pos {b : ℝ} (hb : 0 < b) (t : ℝ) : 0 < canonicalClock b t :=
  inv_pos.2 (lt_of_lt_of_le hb (le_max_right _ _))

theorem canonicalClock_le {b : ℝ} (hb : 0 < b) (t : ℝ) : canonicalClock b t ≤ b⁻¹ :=
  inv_anti₀ hb (le_max_right _ _)

/-- On `t ≤ -b` the clock is `1/(-t) = θ⁻¹`, `θ = -t` (eq. `short-heat-clock`). -/
theorem canonicalClock_eq {b t : ℝ} (ht : t ≤ -b) : canonicalClock b t = (-t)⁻¹ := by
  unfold canonicalClock
  rw [max_eq_left (by linarith)]

theorem measurable_canonicalClock {b : ℝ} (hb : 0 < b) : Measurable (canonicalClock b) := by
  have hc : Continuous (fun t : ℝ => max (-t) b) := continuous_neg.max continuous_const
  have h := (hc.inv₀ fun t => (lt_of_lt_of_le hb (le_max_right (-t) b)).ne').measurable
  exact h

theorem canonicalClock_mem {b : ℝ} (hb : 1 ≤ b) (t : ℝ) :
    0 ≤ canonicalClock b t ∧ canonicalClock b t ≤ 1 :=
  ⟨(canonicalClock_pos (lt_of_lt_of_le one_pos hb) t).le,
    (canonicalClock_le (lt_of_lt_of_le one_pos hb) t).trans (inv_le_one_of_one_le₀ hb)⟩

/-- `QDq ∈ ker ℓ`. -/
theorem seedQDq_ker {l : B0010.XG →L[ℂ] ℂ} {q : B0010.XG} (hlq : l q = 1)
    (hq : q ∈ B0094.D.domain) : l (seedQDq l q hq) = 0 := by
  simp [seedQDq, seedKappa, hlq]

theorem CoupledMild.congr {S : ℝ → ℝ → B0010.XG →L[ℂ] B0010.XG} {y : B0010.XG}
    {φ : B0010.XG →L[ℂ] ℂ} {b : ℝ} {A A' : ℝ → ℂ} {r r' : ℝ → B0010.XG}
    (h : CoupledMild S y φ b A r) (hA : ∀ θ, b ≤ θ → A' θ = A θ)
    (hr : ∀ θ, b ≤ θ → r' θ = r θ) : CoupledMild S y φ b A' r' := by
  intro θ s₀ hθ hθs
  obtain ⟨h1, h2⟩ := h θ s₀ hθ hθs
  have hs₀ : b ≤ s₀ := hθ.trans hθs
  have hI1 : ∫ s in θ..s₀, (A' s / s) • S θ s y = ∫ s in θ..s₀, (A s / s) • S θ s y := by
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le hθs] at hs
    simp only [hA s (hθ.trans hs.1)]
  have hI2 : ∫ s in θ..s₀, φ (r' s) / s = ∫ s in θ..s₀, φ (r s) / s := by
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le hθs] at hs
    simp only [hr s (hθ.trans hs.1)]
  refine ⟨?_, ?_⟩
  · rw [hr θ hθ, hr s₀ hs₀, hI1]
    exact h1
  · rw [hA θ hθ, hA s₀ hs₀, hI2]
    exact h2

theorem CoupledMild.congr_S {S S' : ℝ → ℝ → B0010.XG →L[ℂ] B0010.XG} {y : B0010.XG}
    {φ : B0010.XG →L[ℂ] ℂ} {b : ℝ} {A : ℝ → ℂ} {r : ℝ → B0010.XG}
    (h : CoupledMild S' y φ b A r) (hS : ∀ θ s, b ≤ θ → θ ≤ s → S' θ s = S θ s) :
    CoupledMild S y φ b A r := by
  intro θ s₀ hθ hθs
  obtain ⟨h1, h2⟩ := h θ s₀ hθ hθs
  refine ⟨?_, h2⟩
  have hI : ∫ s in θ..s₀, (A s / s) • S' θ s y = ∫ s in θ..s₀, (A s / s) • S θ s y := by
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le hθs] at hs
    simp only [hS θ s hθ hs.1]
  rw [h1, hS θ s₀ hθ hθs, hI]

theorem ofReal_cpow_mul_cpow_neg {θ : ℝ} (hθ : 0 < θ) (κ : ℂ) :
    (θ : ℂ) ^ κ * (θ : ℂ) ^ (-κ) = 1 := by
  rw [Complex.cpow_neg, mul_inv_cancel₀]
  exact Complex.cpow_ne_zero_iff.2 (Or.inl (Complex.ofReal_ne_zero.2 hθ.ne'))

theorem gauge_mul_gaugeInv (lam κ : ℂ) {θ : ℝ} (hθ : 0 < θ) :
    Complex.exp (lam * θ) * (θ : ℂ) ^ κ * Complex.exp (-(lam * θ)) * (θ : ℂ) ^ (-κ) = 1 := by
  have h1 : Complex.exp (lam * θ) * Complex.exp (-(lam * θ)) = 1 := by
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  calc _ = (Complex.exp (lam * θ) * Complex.exp (-(lam * θ))) *
        ((θ : ℂ) ^ κ * (θ : ℂ) ^ (-κ)) := by ring
    _ = 1 := by rw [h1, ofReal_cpow_mul_cpow_neg hθ κ, one_mul]

/-- `W` of `e^{-λθ}θ^{-κ}w` is `w` (line 1095). -/
theorem canonicalW_gaugeInv (lam κ : ℂ) (w : ℝ → B0010.XG) {θ : ℝ} (hθ : 0 < θ) :
    canonicalW lam κ (fun t => Complex.exp (-(lam * t)) • (t : ℂ) ^ (-κ) • w t) θ = w θ := by
  show Complex.exp (lam * θ) • (θ : ℂ) ^ κ •
      (Complex.exp (-(lam * θ)) • (θ : ℂ) ^ (-κ) • w θ) = w θ
  rw [smul_smul, smul_smul, smul_smul, gauge_mul_gaugeInv lam κ hθ, one_smul]

/-- `V = e^{-λθ}θ^{-κ}W` (line 1095). -/
theorem gaugeInv_canonicalW (lam κ : ℂ) (V : ℝ → B0010.XG) {θ : ℝ} (hθ : 0 < θ) :
    Complex.exp (-(lam * θ)) • (θ : ℂ) ^ (-κ) • canonicalW lam κ V θ = V θ := by
  show Complex.exp (-(lam * θ)) • (θ : ℂ) ^ (-κ) •
      (Complex.exp (lam * θ) • (θ : ℂ) ^ κ • V θ) = V θ
  have h : Complex.exp (-(lam * θ)) * (θ : ℂ) ^ (-κ) * Complex.exp (lam * θ) * (θ : ℂ) ^ κ = 1 := by
    rw [← gauge_mul_gaugeInv lam κ hθ]
    ring
  rw [smul_smul, smul_smul, smul_smul, h, one_smul]

theorem continuousOn_ofReal_cpow_Ici {b : ℝ} (hb : 0 < b) (κ : ℂ) :
    ContinuousOn (fun θ : ℝ => (θ : ℂ) ^ κ) (Ici b) := fun θ hθ =>
  (Complex.continuousAt_ofReal_cpow_const θ κ
    (Or.inr (lt_of_lt_of_le hb hθ).ne')).continuousWithinAt

theorem continuousOn_canonicalW {b : ℝ} (hb : 0 < b) (lam κ : ℂ) {V : ℝ → B0010.XG}
    (hV : ContinuousOn V (Ici b)) : ContinuousOn (canonicalW lam κ V) (Ici b) := by
  have h1 : Continuous (fun θ : ℝ => Complex.exp (lam * θ)) := by fun_prop
  show ContinuousOn (fun θ : ℝ => Complex.exp (lam * θ) • (θ : ℂ) ^ κ • V θ) (Ici b)
  exact h1.continuousOn.smul ((continuousOn_ofReal_cpow_Ici hb κ).smul hV)

theorem continuousOn_gaugeInv {b : ℝ} (hb : 0 < b) (lam κ : ℂ) {w : ℝ → B0010.XG}
    (hw : ContinuousOn w (Ici b)) :
    ContinuousOn (fun θ : ℝ => Complex.exp (-(lam * θ)) • (θ : ℂ) ^ (-κ) • w θ) (Ici b) := by
  have h1 : Continuous (fun θ : ℝ => Complex.exp (-(lam * θ))) := by fun_prop
  exact h1.continuousOn.smul ((continuousOn_ofReal_cpow_Ici hb (-κ)).smul hw)

/-- `S(θ,s) = U(-θ,-s)` is a complementary propagator on `[b,∞)` (lines 1102-1104), given the
cocycle, the continuity in the initial time, and the invariance and decay on `ker ℓ` from
`SmallDiffusionComplement`. -/
theorem isComplementPropagator_canonicalS (hC : MildComplementCocycle)
    (hCS : MildComplementContStart) {lam : ℂ} {q : B0010.XG} {l : B0010.XG →L[ℂ] ℂ}
    (hI : IsSeedXG lam q l) {qd : B0010.XG} (hl : ∀ f, l f = inner ℂ qd f)
    (hq : q ∈ B0094.D.domain) (hqd : qd ∈ B0094.D.domain) {b C g : ℝ} (hb : 1 ≤ b)
    {U : ℝ → ℝ → B0010.XG →L[ℂ] B0010.XG}
    (hU : MildCtx lam q l qd hq hqd (canonicalClock b) U)
    (hdec : ∀ s t : ℝ, s ≤ t → ∀ x : B0010.XG, l x = 0 →
      l (U t s x) = 0 ∧ ‖U t s x‖ ≤ C * Real.exp (-(g * (t - s))) * ‖x‖) :
    IsComplementPropagator l b C g (canonicalS U) := by
  have hb0 : 0 < b := lt_of_lt_of_le one_pos hb
  have hβm := measurable_canonicalClock hb0
  have hβ1 := canonicalClock_mem hb
  have hU' : IsMildComplementEvolution lam (seedKappa l q hq) l q (seedRf l q qd hq hqd)
      (canonicalClock b) U := hU
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro θ s s' _ hθs hss'
    exact hC lam q l hI qd hl hq hqd _ hβm hβ1 U hU (-s') (-s) (-θ) (neg_le_neg hss')
      (neg_le_neg hθs)
  · intro s x
    show ContinuousOn (fun θ => U (-θ) (-s) x) (Icc b s)
    exact (hU'.cont (-s) x).comp continuous_neg.continuousOn
      (fun θ hθ => neg_le_neg hθ.2)
  · intro θ x _
    show ContinuousOn (fun s => U (-θ) (-s) x) (Ici θ)
    exact (hCS lam q l hI qd hl hq hqd _ hβm hβ1 U hU (-θ) x).comp
      continuous_neg.continuousOn (fun s hs => Set.mem_Iic.2 (neg_le_neg (Set.mem_Ici.1 hs)))
  · intro θ s x _ hθs hx
    exact (hdec (-s) (-θ) (neg_le_neg hθs) x hx).1
  · intro θ s x _ hθs hx
    have h := (hdec (-s) (-θ) (neg_le_neg hθs) x hx).2
    have e : -θ - -s = s - θ := by ring
    rw [e] at h
    exact h

/-! ### The contraction (lines 1112-1116) -/

/-- `𝒯` maps `C_b([b,∞))` into itself, and the difference estimate
`|𝒯A(θ) - 𝒯A'(θ)| ≤ ‖φ‖ C‖y‖ δ/(gθ)` when `|A - A'| ≤ δ` on `[b,∞)` (lines 1112-1116). -/
theorem canonicalTA_estimates_of (hR1 : CanonicalRABound) (hR2 : CanonicalRAContinuous)
    (hT : TailIntegralProps) {l : B0010.XG →L[ℂ] ℂ} {b C g : ℝ}
    {S : ℝ → ℝ → B0010.XG →L[ℂ] B0010.XG} (hb : 0 < b) (hC : 0 ≤ C) (hg : 0 < g)
    (hS : IsComplementPropagator l b C g S) {y : B0010.XG} (hy : l y = 0)
    (φ : B0010.XG →L[ℂ] ℂ) :
    (∀ A : ℝ → ℂ, ContinuousOn A (Ici b) → (∃ M, ∀ θ, b ≤ θ → ‖A θ‖ ≤ M) →
      ContinuousOn (canonicalTA S y φ A) (Ici b) ∧
        ∃ M, ∀ θ, b ≤ θ → ‖canonicalTA S y φ A θ‖ ≤ M) ∧
    (∀ A A' : ℝ → ℂ, ContinuousOn A (Ici b) → (∃ M, ∀ θ, b ≤ θ → ‖A θ‖ ≤ M) →
      ContinuousOn A' (Ici b) → (∃ M, ∀ θ, b ≤ θ → ‖A' θ‖ ≤ M) →
      ∀ δ : ℝ, (∀ θ, b ≤ θ → ‖A θ - A' θ‖ ≤ δ) → ∀ θ, b ≤ θ →
        ‖canonicalTA S y φ A θ - canonicalTA S y φ A' θ‖ ≤ ‖φ‖ * (C * ‖y‖ * δ / g) / θ) := by
  have hone : ∀ (A : ℝ → ℂ) (M : ℝ), ContinuousOn A (Ici b) → (∀ θ, b ≤ θ → ‖A θ‖ ≤ M) →
      ContinuousOn (fun θ => ∫ s in Ioi θ, φ (canonicalRA S y A s) / s) (Ici b) ∧
      ∀ θ, b ≤ θ → IntegrableOn (fun s => φ (canonicalRA S y A s) / s) (Ioi θ) ∧
        ‖∫ s in Ioi θ, φ (canonicalRA S y A s) / s‖ ≤ ‖φ‖ * (C * ‖y‖ * M / g) / θ := by
    intro A M hA hM
    refine hT φ b (C * ‖y‖ * M / g) (canonicalRA S y A) hb
      (hR2 l b C g S hb hC hg hS y hy A M hA hM) ?_
    intro θ hθ
    rw [div_div]
    exact (hR1 l b C g S hb hC hg hS y hy A M hA hM θ hθ).2.1
  refine ⟨?_, ?_⟩
  · rintro A hA ⟨M, hM⟩
    obtain ⟨hc, hb'⟩ := hone A M hA hM
    have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM b le_rfl)
    have hK : 0 ≤ ‖φ‖ * (C * ‖y‖ * M / g) := by positivity
    refine ⟨?_, 1 + ‖φ‖ * (C * ‖y‖ * M / g) / b, fun θ hθ => ?_⟩
    · show ContinuousOn (fun θ => (1 : ℂ) + ∫ s in Ioi θ, φ (canonicalRA S y A s) / s) (Ici b)
      exact continuousOn_const.add hc
    · show ‖(1 : ℂ) + ∫ s in Ioi θ, φ (canonicalRA S y A s) / s‖ ≤ _
      have h := (hb' θ hθ).2
      have h3 : ‖φ‖ * (C * ‖y‖ * M / g) / θ ≤ ‖φ‖ * (C * ‖y‖ * M / g) / b :=
        div_le_div_of_nonneg_left hK hb hθ
      calc _ ≤ ‖(1 : ℂ)‖ + ‖∫ s in Ioi θ, φ (canonicalRA S y A s) / s‖ := norm_add_le _ _
        _ ≤ _ := by rw [norm_one]; linarith
  · rintro A A' hA ⟨M, hM⟩ hA' ⟨M', hM'⟩ δ hδ θ hθ
    have hDc : ContinuousOn (fun s => A s - A' s) (Ici b) := hA.sub hA'
    have hlin : ∀ s, b ≤ s →
        canonicalRA S y A s - canonicalRA S y A' s = canonicalRA S y (fun u => A u - A' u) s := by
      intro s hs
      have i1 := (hR1 l b C g S hb hC hg hS y hy A M hA hM s hs).1
      have i2 := (hR1 l b C g S hb hC hg hS y hy A' M' hA' hM' s hs).1
      unfold canonicalRA
      rw [← integral_sub i1 i2]
      refine setIntegral_congr_fun measurableSet_Ioi (fun u _ => ?_)
      simp only [sub_div, sub_smul]
    obtain ⟨_, hTA⟩ := hone A M hA hM
    obtain ⟨_, hTA'⟩ := hone A' M' hA' hM'
    obtain ⟨_, hTD⟩ := hone (fun u => A u - A' u) δ hDc hδ
    have e : canonicalTA S y φ A θ - canonicalTA S y φ A' θ =
        ∫ s in Ioi θ, φ (canonicalRA S y (fun u => A u - A' u) s) / s := by
      unfold canonicalTA
      rw [add_sub_add_left_eq_sub, ← integral_sub (hTA θ hθ).1 (hTA' θ hθ).1]
      refine setIntegral_congr_fun measurableSet_Ioi (fun s hs => ?_)
      have hs' : b ≤ s := hθ.trans (le_of_lt hs)
      rw [← sub_div, ← map_sub, hlin s hs']
    rw [e]
    exact (hTD θ hθ).2

/-! ### Assembly -/

/-- **`PartI:C06` from the leaves** (lines 1094-1122): there is `b > 0` and a mild solution `V`
of `-V' = (L + θ⁻¹D)V` on `[b,∞)` with `V(θ) = e^{-λθ}θ^{-κ}{q + O(θ⁻¹)}`, and it is the only
mild solution on `[b,∞)` with this asymptotic. -/
theorem canonical_infinity_fixed_point_of (hSD : SmallDiffusionComplement)
    (hC : MildComplementCocycle) (hU1 : MildComplementUnique) (hCS : MildComplementContStart)
    (hR1 : CanonicalRABound) (hR2 : CanonicalRAContinuous) (hT : TailIntegralProps)
    (hFP : FixedPointIci) (hM : CanonicalFixedMild) (hN : CanonicalNormalizedUnique)
    (hAs : CanonicalAsymptoticBounds)
    {lam : ℂ} {q : B0010.XG} {l : B0010.XG →L[ℂ] ℂ} (hI : IsSeedXG lam q l) {qd : B0010.XG}
    (hl : ∀ f, l f = inner ℂ qd f) (hq : q ∈ B0094.D.domain) (hqd : qd ∈ B0094.D.domain) :
    ∃ b > 0, ∃ V : ℝ → B0010.XG, IsCanonicalMild lam q l qd hq hqd b V ∧
      HasCanonicalAsymptotic lam (seedKappa l q hq) q V ∧
      ∀ V' : ℝ → B0010.XG, IsCanonicalMild lam q l qd hq hqd b V' →
        HasCanonicalAsymptotic lam (seedKappa l q hq) q V' → ∀ θ : ℝ, b ≤ θ → V' θ = V θ := by
  obtain ⟨βs, g, C, hβs, hg, hCpos, hSDU⟩ := hSD lam q l hI qd hl hq hqd
  have hy : l (seedQDq l q hq) = 0 := seedQDq_ker hI.ell_q hq
  -- the threshold `b` (lines 1102, 1115: `b ≥ β_*⁻¹`, then enlarged for the contraction)
  obtain ⟨b, hbdef⟩ : ∃ b : ℝ, b = max (max 1 βs⁻¹)
      (2 * (‖seedLD qd hqd‖ * (C * ‖seedQDq l q hq‖) / g)) := ⟨_, rfl⟩
  have hb1 : 1 ≤ b := hbdef ▸ (le_max_left _ _).trans (le_max_left _ _)
  have hb0 : 0 < b := lt_of_lt_of_le one_pos hb1
  have hbβ : βs⁻¹ ≤ b := hbdef ▸ (le_max_right _ _).trans (le_max_left _ _)
  have hbK : 2 * (‖seedLD qd hqd‖ * (C * ‖seedQDq l q hq‖) / g) ≤ b := hbdef ▸ le_max_right _ _
  -- the clock and the complementary evolution
  have hβm : Measurable (canonicalClock b) := measurable_canonicalClock hb0
  have hβ1 : ∀ t, 0 ≤ canonicalClock b t ∧ canonicalClock b t ≤ 1 := canonicalClock_mem hb1
  have hββs : ∀ t, 0 ≤ canonicalClock b t ∧ canonicalClock b t ≤ βs := fun t =>
    ⟨(hβ1 t).1, (canonicalClock_le hb0 t).trans ((inv_le_comm₀ hb0 hβs).2 hbβ)⟩
  obtain ⟨U, hU, hUdec⟩ := hSDU (canonicalClock b) hβm hββs
  have hS : IsComplementPropagator l b C g (canonicalS U) :=
    isComplementPropagator_canonicalS hC hCS hI hl hq hqd hb1 hU hUdec
  -- the contraction and its fixed point (lines 1112-1116)
  obtain ⟨hmap, hdiff⟩ := canonicalTA_estimates_of hR1 hR2 hT hb0 hCpos.le hg hS hy
    (seedLD qd hqd)
  have hcontr : ∀ A A' : ℝ → ℂ, ContinuousOn A (Ici b) → (∃ M, ∀ θ, b ≤ θ → ‖A θ‖ ≤ M) →
      ContinuousOn A' (Ici b) → (∃ M, ∀ θ, b ≤ θ → ‖A' θ‖ ≤ M) →
      ∀ δ : ℝ, (∀ θ, b ≤ θ → ‖A θ - A' θ‖ ≤ δ) → ∀ θ, b ≤ θ →
        ‖canonicalTA (canonicalS U) (seedQDq l q hq) (seedLD qd hqd) A θ -
          canonicalTA (canonicalS U) (seedQDq l q hq) (seedLD qd hqd) A' θ‖ ≤ δ / 2 := by
    intro A A' hA hAb hA' hA'b δ hδ θ hθ
    have hδ0 : 0 ≤ δ := (norm_nonneg _).trans (hδ b le_rfl)
    have hθ0 : 0 < θ := lt_of_lt_of_le hb0 hθ
    refine (hdiff A A' hA hAb hA' hA'b δ hδ θ hθ).trans ?_
    rw [div_le_iff₀ hθ0]
    have e : ‖seedLD qd hqd‖ * (C * ‖seedQDq l q hq‖ * δ / g) =
        (‖seedLD qd hqd‖ * (C * ‖seedQDq l q hq‖) / g) * δ := by ring
    rw [e]
    have h2 := mul_le_mul_of_nonneg_right (hbK.trans hθ) hδ0
    linarith
  obtain ⟨A, hAc, ⟨MA, hMA⟩, hAfix, hAuniq⟩ :=
    hFP b (canonicalTA (canonicalS U) (seedQDq l q hq) (seedLD qd hqd)) hmap hcontr
  -- the tail bounds for the fixed point
  have hR1A := hR1 l b C g (canonicalS U) hb0 hCpos.le hg hS (seedQDq l q hq) hy A MA hAc hMA
  have hR2A := hR2 l b C g (canonicalS U) hb0 hCpos.le hg hS (seedQDq l q hq) hy A MA hAc hMA
  have hTA := hT (seedLD qd hqd) b (C * ‖seedQDq l q hq‖ * MA / g)
    (canonicalRA (canonicalS U) (seedQDq l q hq) A) hb0 hR2A (fun θ hθ => by
      rw [div_div]; exact (hR1A θ hθ).2.1)
  have hmild := hM b (canonicalS U) (seedQDq l q hq) (seedLD qd hqd) A hS.cocycle
    (fun θ hθ => (hR1A θ hθ).1) (fun θ hθ => (hTA.2 θ hθ).1) hAfix
  -- the solution `V = e^{-λθ}θ^{-κ}(Aq + r_A)` (line 1095)
  let w : ℝ → B0010.XG := fun θ => A θ • q + canonicalRA (canonicalS U) (seedQDq l q hq) A θ
  let V : ℝ → B0010.XG := fun θ =>
    Complex.exp (-(lam * θ)) • (θ : ℂ) ^ (-(seedKappa l q hq)) • w θ
  have hWV : ∀ θ, b ≤ θ → canonicalW lam (seedKappa l q hq) V θ = w θ := fun θ hθ =>
    canonicalW_gaugeInv lam (seedKappa l q hq) w (lt_of_lt_of_le hb0 hθ)
  have hlW : ∀ θ, b ≤ θ → l (canonicalW lam (seedKappa l q hq) V θ) = A θ := by
    intro θ hθ
    rw [hWV θ hθ]
    show l (A θ • q + canonicalRA (canonicalS U) (seedQDq l q hq) A θ) = A θ
    rw [map_add, map_smul, hI.ell_q, (hR1A θ hθ).2.2, smul_eq_mul, mul_one, add_zero]
  have hrW : ∀ θ, b ≤ θ → canonicalW lam (seedKappa l q hq) V θ -
      l (canonicalW lam (seedKappa l q hq) V θ) • q =
        canonicalRA (canonicalS U) (seedQDq l q hq) A θ := by
    intro θ hθ
    rw [hlW θ hθ, hWV θ hθ]
    show A θ • q + canonicalRA (canonicalS U) (seedQDq l q hq) A θ - A θ • q = _
    abel
  have hwc : ContinuousOn w (Ici b) := (hAc.smul continuousOn_const).add hR2A
  have hVc : ContinuousOn V (Ici b) := continuousOn_gaugeInv hb0 lam (seedKappa l q hq) hwc
  refine ⟨b, hb0, V, ⟨hVc, U, hU, hmild.congr hlW hrW⟩, ?_, ?_⟩
  · -- the asymptotic (line 1116)
    refine ⟨‖seedLD qd hqd‖ * (C * ‖seedQDq l q hq‖ * MA / g) * ‖q‖ +
      C * ‖seedQDq l q hq‖ * MA / g, b, hb0, fun θ hθ => ?_⟩
    have hθ0 : 0 < θ := lt_of_lt_of_le hb0 hθ
    have e1 : Complex.exp (lam * θ) • (θ : ℂ) ^ (seedKappa l q hq) • V θ - q =
        (A θ - 1) • q + canonicalRA (canonicalS U) (seedQDq l q hq) A θ := by
      have h := hWV θ hθ
      unfold canonicalW at h
      rw [h]
      show A θ • q + canonicalRA (canonicalS U) (seedQDq l q hq) A θ - q = _
      rw [sub_smul, one_smul]
      abel
    have e2 : A θ - 1 = ∫ s in Ioi θ,
        seedLD qd hqd (canonicalRA (canonicalS U) (seedQDq l q hq) A s) / s := by
      rw [← hAfix θ hθ]
      unfold canonicalTA
      ring
    rw [e1]
    have h1 : ‖(A θ - 1) • q‖ ≤
        ‖seedLD qd hqd‖ * (C * ‖seedQDq l q hq‖ * MA / g) / θ * ‖q‖ := by
      rw [norm_smul, e2]
      exact mul_le_mul_of_nonneg_right (hTA.2 θ hθ).2 (norm_nonneg _)
    have h2 : ‖canonicalRA (canonicalS U) (seedQDq l q hq) A θ‖ ≤
        C * ‖seedQDq l q hq‖ * MA / g / θ := by
      rw [div_div]
      exact (hR1A θ hθ).2.1
    calc ‖(A θ - 1) • q + canonicalRA (canonicalS U) (seedQDq l q hq) A θ‖
        ≤ ‖(A θ - 1) • q‖ + ‖canonicalRA (canonicalS U) (seedQDq l q hq) A θ‖ :=
          norm_add_le _ _
      _ ≤ ‖seedLD qd hqd‖ * (C * ‖seedQDq l q hq‖ * MA / g) / θ * ‖q‖ +
          C * ‖seedQDq l q hq‖ * MA / g / θ := add_le_add h1 h2
      _ = (‖seedLD qd hqd‖ * (C * ‖seedQDq l q hq‖ * MA / g) * ‖q‖ +
          C * ‖seedQDq l q hq‖ * MA / g) / θ := by ring
  · -- uniqueness at infinity (lines 1117-1122)
    rintro V' ⟨hV'c, U', hU', hcm'⟩ hasy' θ hθ
    have hθ0 : 0 < θ := lt_of_lt_of_le hb0 hθ
    have hUU' : ∀ s t : ℝ, s ≤ t → U' t s = U t s := fun s t hst =>
      hU1 lam q l hI qd hl hq hqd _ hβm hβ1 U' U hU' hU s t hst
    have hcm := hcm'.congr_S (S := canonicalS U)
      (fun θ s _ hθs => hUU' (-s) (-θ) (neg_le_neg hθs))
    obtain ⟨⟨MW, hMW⟩, ⟨K, hK⟩, hlim⟩ :=
      hAs lam (seedKappa l q hq) q l hI.ell_q b V' hb0 hV'c hasy'
    have hW'c := continuousOn_canonicalW hb0 lam (seedKappa l q hq) hV'c
    let A' : ℝ → ℂ := fun θ => l (canonicalW lam (seedKappa l q hq) V' θ)
    let r' : ℝ → B0010.XG := fun θ => canonicalW lam (seedKappa l q hq) V' θ -
      l (canonicalW lam (seedKappa l q hq) V' θ) • q
    have hA'c : ContinuousOn A' (Ici b) := l.continuous.comp_continuousOn hW'c
    have hr'c : ContinuousOn r' (Ici b) :=
      hW'c.sub ((l.continuous.comp_continuousOn hW'c).smul continuousOn_const)
    have hA'b : ∀ θ, b ≤ θ → ‖A' θ‖ ≤ ‖l‖ * MW := fun θ hθ =>
      (l.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hMW θ hθ) (norm_nonneg _))
    have hr'l : ∀ θ, b ≤ θ → l (r' θ) = 0 := by
      intro θ _
      show l (canonicalW lam (seedKappa l q hq) V' θ -
        l (canonicalW lam (seedKappa l q hq) V' θ) • q) = 0
      rw [map_sub, map_smul, hI.ell_q, smul_eq_mul, mul_one, sub_self]
    have hK0 : 0 ≤ K := by
      have h0 : 0 ≤ K / b := (norm_nonneg _).trans (hK b le_rfl)
      have h1 := mul_nonneg h0 hb0.le
      rwa [div_mul_cancel₀ K hb0.ne'] at h1
    have hr'b : ∃ K', ∀ θ, b ≤ θ → ‖r' θ‖ ≤ K' :=
      ⟨K / b, fun θ hθ => (hK θ hθ).trans (div_le_div_of_nonneg_left hK0 hb0 hθ)⟩
    have hR1A' := hR1 l b C g (canonicalS U) hb0 hCpos.le hg hS (seedQDq l q hq) hy A'
      (‖l‖ * MW) hA'c hA'b
    have hTr' := hT (seedLD qd hqd) b K r' hb0 hr'c hK
    have hN' := hN l b C g (canonicalS U) hg hS (seedQDq l q hq) (seedLD qd hqd) A' r' hr'l hr'b
      (fun θ hθ => (hR1A' θ hθ).1) (fun θ hθ => (hTr'.2 θ hθ).1) hlim hcm
    have hfix' : ∀ θ, b ≤ θ →
        canonicalTA (canonicalS U) (seedQDq l q hq) (seedLD qd hqd) A' θ = A' θ :=
      fun θ hθ => ((hN' θ hθ).2).symm
    have hAA : ∀ θ, b ≤ θ → A' θ = A θ := hAuniq A' hA'c ⟨_, hA'b⟩ hfix'
    have hRR : canonicalRA (canonicalS U) (seedQDq l q hq) A' θ =
        canonicalRA (canonicalS U) (seedQDq l q hq) A θ := by
      unfold canonicalRA
      refine setIntegral_congr_fun measurableSet_Ioi (fun s hs => ?_)
      rw [hAA s (hθ.trans (le_of_lt hs))]
    have hWW : canonicalW lam (seedKappa l q hq) V' θ = canonicalW lam (seedKappa l q hq) V θ := by
      have e : canonicalW lam (seedKappa l q hq) V' θ = A' θ • q + r' θ := by
        show _ = l (canonicalW lam (seedKappa l q hq) V' θ) • q +
          (canonicalW lam (seedKappa l q hq) V' θ - l (canonicalW lam (seedKappa l q hq) V' θ) • q)
        abel
      rw [e, hAA θ hθ, (hN' θ hθ).1, hRR]
      exact (hWV θ hθ).symm
    rw [← gaugeInv_canonicalW lam (seedKappa l q hq) V' hθ0, hWW,
      gaugeInv_canonicalW lam (seedKappa l q hq) V hθ0]

end UnforcedLeray.Short.PartI
