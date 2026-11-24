import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6.VtvFubini
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6.VtvStreamFlat
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# Decomposition of `VtvFlux`, the flux cutoff (source 3511-3514)

Source of record: `the November 2 reference manuscript` (73 pages), lines 3511-3514
("The velocity equation follows from its curl and divergence equations ... This retains the
horizontal mean"), 3426-3440 (the energy class; the force lies in `𝒯`).

Let `Φ` be a flat test vanishing off `[s₁,s₂] × {|η| ≤ R₀}` (`VtvFlatSupp`).

* `Z(s,q,η) = -∫_{-(R₀+1)}^{η} Φ_q(s,q,t) dt` (`vtvZp`) is jointly smooth (`VtvZpSmooth`),
  `∂_η Z = -Φ_q`, `∂_q Z = Φ_η` (`VtvZpPdEta`, `VtvZpPdQ`: FTC and `div Φ = 0`), periodic in `q`,
  zero off the age band and below the support (`VtvZpVanish`), and equal to the flux
  `F(s) = Z(s,0,R₀+1)` above the support (`VtvZpFlux`).  So `∇^⊥Z = Φ`, but `Z` is not compactly
  supported: it tends to the flux `F(s)` as `η → ∞` (the horizontal mean).
* With the one-sided cutoff `θ = smoothTransition(2 - ·)` (`VtvThetaFacts`), `ζ_R = Zθ(η/R)` is a
  stream test (`VtvZetaStream`) and, for `R > R₀`, `Φ = ∇^⊥ζ_R + E_R` with the explicit flat test
  `E_R = (F(s)θ'(η/R)/R, 0)` (`VtvErrFlat`, `VtvSplit`), supported in `R ≤ η ≤ 2R`.
* `forcedIntegrand` is additive in the test (`VtvForcedAdd`), so the weak equation against the
  stream test gives `∫ forcedIntegrand Φ = ∫ forcedIntegrand E_R` for every `R > R₀`.
* Tail (`VtvErrTail`): `E_R` and `∂_sE_R`, `∇E_R`, `ΔE_R` are `O(1/R)` (`VtvErrDerivs`,
  `VtvFluxFBound`, `VtvErrBound`), the tested integrand is bounded by the coefficient size times
  `|b| + |f|` (`VtvIntegrandLe`), `b` and `f` are `L²` on age bands (`VtvEnergyBand`, the force
  hypothesis), and Cauchy-Schwarz on the slab `{|η| ≤ 2R}` of measure `O(R)` (`VtvBandCS`) gives
  `|∫ forcedIntegrand E_R| = O(R^{-1/2}) → 0`.

`vtvFlux_of` assembles `VtvFlux` (compiled here).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ComplexConjugate

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.Short.IIIa (IsFlatTest flatIntegrand trainVel flatDt flatGrad flatLap fibK1)

/-! ## Definitions -/

/-- The one-sided cutoff profile `θ(t) = smoothTransition(2 - t)`: smooth, `θ = 1` for `t ≤ 1`,
`θ = 0` for `t ≥ 2`. -/
def vtvTheta (t : ℝ) : ℝ := Real.smoothTransition (2 - t)

/-- The stream function of a flat test from below (source 3511-3514):
`Z(s,q,η) = -∫_{-(R₀+1)}^{η} Φ_q(s,q,t) dt`, so that `∇^⊥Z = (-∂_ηZ, ∂_qZ) = Φ`. -/
def vtvZp (Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ) (R₀ s : ℝ) (x : ℝ × ℝ) : ℝ :=
  -∫ t in (-(R₀ + 1))..x.2, Φ s (x.1, t) 0

/-- The flux of `Φ` through a horizontal line above its support, `F(s) = Z(s, 0, R₀ + 1)` (the
horizontal mean retained by the velocity equation, source 3511-3514). -/
def vtvFluxF (Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ) (R₀ s : ℝ) : ℝ := vtvZp Φ R₀ s (0, R₀ + 1)

/-- The cut-off stream test `ζ_R(s,x) = Z(s,x) θ(η/R)`. -/
def vtvZeta (Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ) (R₀ R s : ℝ) (x : ℝ × ℝ) : ℝ :=
  vtvZp Φ R₀ s x * vtvTheta (x.2 / R)

/-- The flux remainder `E_R = (F(s) θ'(η/R)/R, 0)`; for `R > R₀`, `Φ = ∇^⊥ζ_R + E_R`
(`VtvSplit`). -/
def vtvErr (Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ) (R₀ R s : ℝ) (x : ℝ × ℝ) (i : Fin 2) : ℝ :=
  if i = 0 then vtvFluxF Φ R₀ s * deriv vtvTheta (x.2 / R) / R else 0

/-- `Φ` is a flat test vanishing off `[s₁, s₂] × {|η| ≤ R₀}`, with `s₁ > 0`, `R₀ ≥ 0` (the data of
`IsFlatTest.support`, with `R₀` made nonnegative). -/
def VtvFlatSupp (c : ℝ) (Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ) (s₁ s₂ R₀ : ℝ) : Prop :=
  IsFlatTest c Φ ∧ 0 < s₁ ∧ 0 ≤ R₀ ∧
    ∀ s x i, (s < s₁ ∨ s₂ < s ∨ R₀ < |x.2|) → Φ s x i = 0

/-! ## The lemmas -/

/-- **(1) The cutoff profile.**  `θ = smoothTransition(2 - ·)` is smooth, `1` on `t ≤ 1`, `0` on
`t ≥ 2`; `θ' = 0` for `t ≤ 1` or `t ≥ 2`; `θ', θ'', θ'''` are bounded.  Route:
`Real.smoothTransition.contDiff`, `.one_of_one_le`, `.zero_of_nonpos`; `θ` is locally constant on
`t < 1` and `t > 2` (`Filter.EventuallyEq.deriv_eq`), and at `t = 1, 2` use continuity of `θ'`
(closure of `Iio 1`, `Ioi 2`); the derivatives are continuous with support in `[1,2]`
(`HasCompactSupport.intro isCompact_Icc`, `Continuous.bounded_above_of_compact_support`). -/
def VtvThetaFacts : Prop :=
  ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) vtvTheta ∧ (∀ t, t ≤ 1 → vtvTheta t = 1) ∧ (∀ t, 2 ≤ t → vtvTheta t = 0) ∧
    (∀ t, (t ≤ 1 ∨ 2 ≤ t) → deriv vtvTheta t = 0) ∧
    ∃ C : ℝ, ∀ t, |deriv vtvTheta t| ≤ C ∧ |deriv (deriv vtvTheta) t| ≤ C ∧
      |deriv (deriv (deriv vtvTheta)) t| ≤ C

/-- **(2) Joint smoothness of the stream function** (differentiation under the integral over a
compact interval).  Route: substitute `t = a + u(η - a)`, `a = -(R₀+1)`
(`intervalIntegral.smul_integral_comp_mul_add`, as in `IIIa.dfcQPrim_eq_mul`):
`Z(s,q,η) = -(η - a) ∫₀¹ Φ_q(s, q, a + u(η - a)) du`; the integrand is smooth in
`((s,(q,η)), u)` (`IsFlatTest.smooth`), and `IIIa.DfcQPrimSmoothAux.ipsContDiff` (with
`P = ℝ × (ℝ × ℝ)`, every finite order, `contDiff_infty`) gives smoothness of the parametric
integral, exactly as in `IIIa.paramIntegral_contDiff`
(`PartIII-a/T18_FreeCausal/EnergyBound/WeightedEnergy/DivFreeCutoffDensity/QPrimSmooth.lean`). -/
def VtvZpSmooth : Prop :=
  ∀ (c : ℝ) (Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ), IsFlatTest c Φ → ∀ R₀ : ℝ,
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × (ℝ × ℝ) => vtvZp Φ R₀ p.1 p.2)

/-- **(3) `∂_η Z = -Φ_q`** (fundamental theorem of calculus).  Route: `IIIa.DfcQPrimDerivAux.pd1_eq`
(differentiability from `VtvZpSmooth`) turns `pd 1` into the derivative of
`η ↦ -∫_{a}^{η} Φ_q(s,q,t) dt`, and `intervalIntegral.integral_hasDerivAt_right` (the integrand is
continuous in `t`). -/
def VtvZpPdEta : Prop :=
  ∀ (c : ℝ) (Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ) (s₁ s₂ R₀ : ℝ), VtvFlatSupp c Φ s₁ s₂ R₀ →
    ∀ s x, B0579.pd 1 (vtvZp Φ R₀ s) x = -Φ s x 0

/-- **(4) `∂_q Z = Φ_η`** (`div Φ = 0` and vanishing of `Φ` at `η = -(R₀+1)`).  Route:
`IIIa.DfcQPrimDerivAux.pd0_eq` turns `pd 0` into the derivative of `q ↦ -∫_a^η Φ_q(s,q,t) dt`;
differentiate under the integral (`IIIa.DfcQPrimDerivAux.hasDerivAt_param` applied to
`(t, q) ↦ Φ s (q, t) 0`): the derivative is `-∫_a^η ∂_qΦ_q(s,q,t) dt = ∫_a^η ∂_ηΦ_η(s,q,t) dt`
(`IsFlatTest.divFree`) `= Φ_η(s,q,η) - Φ_η(s,q,a)` (`intervalIntegral.integral_eq_sub_of_hasDerivAt`
with `pd1_eq`), and `Φ_η(s,q,a) = 0` since `|a| = R₀ + 1 > R₀`. -/
def VtvZpPdQ : Prop :=
  ∀ (c : ℝ) (Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ) (s₁ s₂ R₀ : ℝ), VtvFlatSupp c Φ s₁ s₂ R₀ →
    ∀ s x, B0579.pd 0 (vtvZp Φ R₀ s) x = Φ s x 1

/-- **(5) Periodicity and vanishing of `Z`.**  `Z` is `c`-periodic in `q` (periodicity of `Φ`,
`intervalIntegral.integral_congr`), vanishes off the age band (the integrand is `0`), and vanishes
for `η < -R₀` (on `uIcc (-(R₀+1)) η` every `t < -R₀`, so `|t| > R₀` and the integrand is `0`). -/
def VtvZpVanish : Prop :=
  ∀ (c : ℝ) (Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ) (s₁ s₂ R₀ : ℝ), VtvFlatSupp c Φ s₁ s₂ R₀ →
    (∀ s x, vtvZp Φ R₀ s (x.1 + c, x.2) = vtvZp Φ R₀ s x) ∧
    (∀ s x, (s < s₁ ∨ s₂ < s) → vtvZp Φ R₀ s x = 0) ∧
    (∀ s x, x.2 < -R₀ → vtvZp Φ R₀ s x = 0)

/-- **(6) Above the support `Z` is the flux** `F(s)` (source 3511-3514, the horizontal mean).
Route: `η`-independence for `η > R₀`: `intervalIntegral.integral_add_adjacent_intervals` and the
integrand vanishes on `uIcc (R₀+1) η ⊂ (R₀, ∞)`; `q`-independence on the line `η = R₀ + 1`: the
derivative of `q ↦ Z(s,q,R₀+1)` is `Φ_η(s,q,R₀+1) = 0` (`VtvZpPdQ`, `IIIa.DfcQPrimDerivAux.pd0_eq`,
differentiability from `VtvZpSmooth`), so it is constant (`is_const_of_deriv_eq_zero`). -/
def VtvZpFlux : Prop :=
  ∀ (c : ℝ) (Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ) (s₁ s₂ R₀ : ℝ), VtvFlatSupp c Φ s₁ s₂ R₀ →
    ∀ s x, R₀ < x.2 → vtvZp Φ R₀ s x = vtvFluxF Φ R₀ s

/-- **(7) `ζ_R` is a stream test** (`R > 0`).  Route: joint smoothness from `VtvZpSmooth` and
`VtvThetaFacts` (product, `θ(η/R)` smooth); each slice is a cylinder test (smooth by composing with
`y ↦ (s, y)`, periodic by `VtvZpVanish`, band `max R₀ (2R)`: `θ(η/R) = 0` for `η ≥ 2R`, `Z = 0` for
`η < -R₀`); uniform support `[s₁, s₂] × {|η| ≤ max R₀ (2R)}` (`VtvZpVanish`). -/
def VtvZetaStream : Prop :=
  ∀ (c : ℝ) (Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ) (s₁ s₂ R₀ : ℝ), VtvFlatSupp c Φ s₁ s₂ R₀ →
    ∀ R : ℝ, 0 < R → IsStreamTest c (vtvZeta Φ R₀ R)

/-- **(8) `E_R` is a flat test supported in `[s₁,s₂] × {|η| ≤ 2R}`** (`R > 0`).  Route: `F` is
smooth (`VtvZpSmooth` composed with `s ↦ (s, (0, R₀+1))`), `θ'` is smooth (`VtvThetaFacts`,
`ContDiff.iterate_deriv`); no `q`-dependence gives periodicity and `∂_q E_q = 0`, and `E_η = 0`,
so `div E_R = 0`; `F(s) = 0` off `[s₁,s₂]` (`VtvZpVanish`), `θ'(η/R) = 0` for `|η| > 2R`
(`VtvThetaFacts`: `η/R > 2` or `η/R < -2 ≤ 1`). -/
def VtvErrFlat : Prop :=
  ∀ (c : ℝ) (Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ) (s₁ s₂ R₀ : ℝ), VtvFlatSupp c Φ s₁ s₂ R₀ →
    ∀ R : ℝ, 0 < R → IsFlatTest c (vtvErr Φ R₀ R) ∧
      ∀ s x i, (s < s₁ ∨ s₂ < s ∨ 2 * R < |x.2|) → vtvErr Φ R₀ R s x i = 0

/-- **(9) The split `Φ = ∇^⊥ζ_R + E_R`** for `R > R₀` (source 3511-3514).  Route: product rule
`IIIa.DfcCutPdAux.pdSndMul` with `ψ = θ(·/R)` (`deriv ψ t = θ'(t/R)/R`):
`∂_η ζ_R = (∂_ηZ)θ_R + Zθ'(η/R)/R = -Φ_qθ_R + Zθ'(η/R)/R`, `∂_q ζ_R = Φ_ηθ_R` (`VtvZpPdEta`,
`VtvZpPdQ`).  If `η ≤ R`: `θ_R = 1`, `θ'(η/R) = 0`, `E_R = 0`.  If `η > R > R₀`: `Φ = 0` and
`Z = F(s)` (`VtvZpFlux`), so `∇^⊥ζ_R = (-F θ'(η/R)/R, 0) = -E_R`. -/
def VtvSplit : Prop :=
  ∀ (c : ℝ) (Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ) (s₁ s₂ R₀ : ℝ), VtvFlatSupp c Φ s₁ s₂ R₀ →
    ∀ R : ℝ, R₀ < R → ∀ s x i,
      Φ s x i = streamField (vtvZeta Φ R₀ R) s x i + vtvErr Φ R₀ R s x i

/-- **(10) The forced integrand is additive in the test field** (for smooth tests: `flatDt`,
`flatGrad`, `flatLap` of a sum are the sums, `deriv_add`, `IIIa.DfcCutPdAux.pdAddAux` twice for the
Laplacian; then `forcedIntegrand`, `IIIa.flatIntegrand` are linear; compare
`forcedIntegrand_sub` in `Concrete/FlatSettingInst/Column.lean`). -/
def VtvForcedAdd : Prop :=
  ∀ (c ν : ℝ) (μ : ℂ) (vel : ℝ → ℝ × ℝ → Fin 2 → ℝ) (f b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ)
    (Φ Ψ : ℝ → ℝ × ℝ → Fin 2 → ℝ), IsFlatTest c Φ → IsFlatTest c Ψ → ∀ p : ℝ × (ℝ × ℝ),
      forcedIntegrand ν μ vel f b (fun s x i => Φ s x i + Ψ s x i) p =
        forcedIntegrand ν μ vel f b Φ p + forcedIntegrand ν μ vel f b Ψ p

/-- **(11) Derivatives of `E_R`** (`R ≠ 0`).  `E_R(s,x) = (F(s)θ'(x₂/R)/R, 0)`:
`∂_sE_q = F'(s)θ'(η/R)/R` (`deriv_mul_const`, `F` differentiable by `VtvZpSmooth`),
`∂_qE_q = 0`, `∂_ηE_q = F(s)θ''(η/R)/R²` (chain rule through `y ↦ y.2/R`), `ΔE_q = F(s)θ'''(η/R)/R³`
(`IIIa.lapP`: `pd 0 (pd 0 ·) = 0`), and every derivative of `E_η = 0` vanishes. -/
def VtvErrDerivs : Prop :=
  ∀ (c : ℝ) (Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ) (s₁ s₂ R₀ : ℝ), VtvFlatSupp c Φ s₁ s₂ R₀ →
    ∀ R : ℝ, R ≠ 0 → ∀ s x,
      flatDt (vtvErr Φ R₀ R) s x 0 = deriv (vtvFluxF Φ R₀) s * deriv vtvTheta (x.2 / R) / R ∧
      flatGrad (vtvErr Φ R₀ R) s x 0 0 = 0 ∧
      flatGrad (vtvErr Φ R₀ R) s x 0 1 =
        vtvFluxF Φ R₀ s * deriv (deriv vtvTheta) (x.2 / R) / R ^ 2 ∧
      flatLap (vtvErr Φ R₀ R) s x 0 =
        vtvFluxF Φ R₀ s * deriv (deriv (deriv vtvTheta)) (x.2 / R) / R ^ 3 ∧
      flatDt (vtvErr Φ R₀ R) s x 1 = 0 ∧ (∀ j, flatGrad (vtvErr Φ R₀ R) s x 1 j = 0) ∧
      flatLap (vtvErr Φ R₀ R) s x 1 = 0

/-- **(12) The flux and its age derivative are bounded.**  `F` is smooth (`VtvZpSmooth`) and
vanishes off `[s₁, s₂]` (`VtvZpVanish`), so `F` and `F'` vanish on the open sets `s < s₁`,
`s > s₂` (`Filter.EventuallyEq.deriv_eq`) and are bounded by their maxima on the compact
`[s₁, s₂]` (`IsCompact.exists_bound_of_continuousOn`). -/
def VtvFluxFBound : Prop :=
  ∀ (c : ℝ) (Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ) (s₁ s₂ R₀ : ℝ), VtvFlatSupp c Φ s₁ s₂ R₀ →
    ∃ C : ℝ, ∀ s, |vtvFluxF Φ R₀ s| ≤ C ∧ |deriv (vtvFluxF Φ R₀) s| ≤ C

/-- **(13) `E_R` and its derivatives are `O(1/R)`** (`R ≥ 1`).  Route: `VtvErrDerivs`,
`VtvFluxFBound` (`C`), `VtvThetaFacts` (`Cθ`); `K = C·Cθ ≥ 0`, `1/R², 1/R³ ≤ 1/R`. -/
def VtvErrBound : Prop :=
  ∀ (c : ℝ) (Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ) (s₁ s₂ R₀ : ℝ), VtvFlatSupp c Φ s₁ s₂ R₀ →
    ∃ K : ℝ, ∀ R : ℝ, 1 ≤ R → ∀ s x i,
      |vtvErr Φ R₀ R s x i| ≤ K / R ∧ |flatDt (vtvErr Φ R₀ R) s x i| ≤ K / R ∧
        |flatLap (vtvErr Φ R₀ R) s x i| ≤ K / R ∧ ∀ j, |flatGrad (vtvErr Φ R₀ R) s x i j| ≤ K / R

/-- **(14) Pointwise bound of the tested integrand** by the size `δ` of the test and its
derivatives: unfold `forcedIntegrand`, `IIIa.flatIntegrand` (with `F = 0`), triangle inequality;
`‖μ/s‖ ≤ ‖μ‖/s₁` for `s ≥ s₁ > 0`; the stress term contributes `4Vδ ∑ ‖b_i‖`. -/
def VtvIntegrandLe : Prop :=
  ∀ (ν : ℝ) (μ : ℂ) (vel : ℝ → ℝ × ℝ → Fin 2 → ℝ) (f b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ)
    (Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ) (p : ℝ × (ℝ × ℝ)) (s₁ δ V : ℝ), 0 < s₁ → s₁ ≤ p.1 →
    (∀ i, |Φ p.1 p.2 i| ≤ δ ∧ |flatDt Φ p.1 p.2 i| ≤ δ ∧ |flatLap Φ p.1 p.2 i| ≤ δ ∧
      ∀ j, |flatGrad Φ p.1 p.2 i j| ≤ δ) →
    (∀ i, |vel p.1 p.2 i| ≤ V) →
    ‖forcedIntegrand ν μ vel f b Φ p‖ ≤
      δ * (1 + ‖μ‖ / s₁ + |ν| + 4 * V) * ∑ i : Fin 2, (‖b p i‖ + ‖f p i‖)

/-- **(15) Cauchy-Schwarz on the slab** `fibK1 c s₁ s₂ (2R) = [s₁,s₂] × [-c/2,c/2) × [-2R,2R]`
(measure `≤ 4R·c·(s₂ - s₁)` up to signs): for `h ∈ L²` of the band,
`∫_slab ‖h‖ ≤ (∫_band ‖h‖²)^{1/2} · vol(slab)^{1/2} ≤ C √R`.  Route: `MemLp.mono_measure`
(`Measure.restrict_mono`, `fibK1 ⊆ Icc s₁ s₂ ×ˢ cell`), finite measure of the slab,
`integral_mul_le_Lp_mul_Lq_of_nonneg` with `p = q = 2` and the constant `1` (or
`eLpNorm_le_eLpNorm_mul_rpow_measure_univ`). -/
def VtvBandCS : Prop :=
  ∀ (c s₁ s₂ : ℝ) (h : ℝ × (ℝ × ℝ) → ℂ),
    MemLp h 2 (volume.restrict (Icc s₁ s₂ ×ˢ B0579.cell c)) →
    ∃ C : ℝ, ∀ R : ℝ, 1 ≤ R →
      IntegrableOn (fun p => ‖h p‖) (fibK1 c s₁ s₂ (2 * R)) ∧
        ∫ p in fibK1 c s₁ s₂ (2 * R), ‖h p‖ ≤ C * Real.sqrt R

/-- **(16) Energy fields are `L²` on age bands** (source 3426-3430, `energyLoc`): measurability
(`IsEnergyField.measurable`) and `‖b_i‖² ≤ vnorm2(b)² ≤ vnorm2(b)² + tnorm2(G)²`
(`IIIa.fib_norm_le_vnorm2`), whose integral over `Icc s₁ s₂' ×ˢ cell`, `s₂' = max s₂ (s₁ + 1)`, is
finite (`memLp_two_iff_integrable_sq` / `MemLp` via `eLpNorm` and `lintegral_mono`). -/
def VtvEnergyBand : Prop :=
  ∀ (c : ℝ) (b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ) (G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ),
    IsEnergyField c b G → ∀ s₁ s₂ : ℝ, 0 < s₁ → ∀ i,
      MemLp (fun p => b p i) 2 (volume.restrict (Icc s₁ s₂ ×ˢ B0579.cell c))

/-- **(17) The flux remainder is negligible** (source 3511-3514; the cutoff error is
`O(R^{-1/2})`).  Route, for `R ≥ 1`: `E_R` is a flat test supported in `[s₁,s₂] × {|η| ≤ 2R}`
(`VtvErrFlat`), so its tested integrand vanishes on `Ioi 0 ×ˢ cell` off `fibK1 c s₁ s₂ (2R)`
(`vtv_zero_outside`, `IIIa.fib_outside`) and the integral is over the slab
(`setIntegral_eq_of_subset_of_forall_diff_eq_zero`); on the slab `s ≥ s₁`, the train velocity is
bounded by `V` (`PartI.IsBUCTrain.sup_bound` with `S = max s₂ 0`, `trainVel = tr.v` for `s ≥ 0`),
and `VtvErrBound`, `VtvIntegrandLe` give `‖integrand‖ ≤ (K/R)·A·∑_i(‖b_i‖ + ‖f_i‖)`; by
`VtvEnergyBand` and the force clause of `VtvHyps`, `VtvBandCS` bounds each slab integral by
`C √R`; so `|∫| ≤ K A C'/√R → 0` (`squeeze_zero_norm'`, `tendsto_inv_atTop_zero`,
`Real.sqrt` tends to `∞`). -/
def VtvErrTail : Prop :=
  ∀ (ν c μ : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c) (ω g : ℝ → ℝ × ℝ → ℂ)
    (b : Chart → Fin 2 → ℂ) (G : Chart → Fin 2 → Fin 2 → ℂ) (f : Chart → Fin 2 → ℂ),
    VtvHyps ν c μ tr ω g b G f →
    ∀ (Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ) (s₁ s₂ R₀ : ℝ), VtvFlatSupp c Φ s₁ s₂ R₀ →
      Tendsto (fun R => ∫ p in Ioi (0 : ℝ) ×ˢ B0579.cell c,
        forcedIntegrand ν (μ : ℂ) (trainVel tr) f b (vtvErr Φ R₀ R) p) atTop (𝓝 0)

/-! ## Assembly -/

theorem vtvFlux_of (h1 : VtvZetaStream) (h2 : VtvErrFlat) (h3 : VtvSplit) (h4 : VtvForcedAdd)
    (h5 : VtvErrTail) : VtvFlux := by
  intro ν c μ tr ω g b G f H hstream Φ hΦ
  obtain ⟨hint, -⟩ := vtvFubini ν c μ tr ω g b G f H Φ hΦ
  refine ⟨hint, ?_⟩
  obtain ⟨s₁, s₂, R', hs₁, hsupp'⟩ := hΦ.support
  set R₀ : ℝ := max R' 0 with hR₀
  have hsupp : ∀ s x i, (s < s₁ ∨ s₂ < s ∨ R₀ < |x.2|) → Φ s x i = 0 := by
    intro s x i h
    refine hsupp' s x i ?_
    rcases h with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (lt_of_le_of_lt (le_max_left _ _) h))
  have hS : VtvFlatSupp c Φ s₁ s₂ R₀ := ⟨hΦ, hs₁, le_max_right _ _, hsupp⟩
  have key : ∀ R : ℝ, R₀ < R →
      ∫ p in Ioi (0 : ℝ) ×ˢ B0579.cell c,
          forcedIntegrand ν (μ : ℂ) (trainVel tr) f b (vtvErr Φ R₀ R) p =
        ∫ p in Ioi (0 : ℝ) ×ˢ B0579.cell c, forcedIntegrand ν (μ : ℂ) (trainVel tr) f b Φ p := by
    intro R hR
    have hRpos : 0 < R := lt_of_le_of_lt (le_max_right _ _) hR
    have hz := h1 c Φ s₁ s₂ R₀ hS R hRpos
    have hE := (h2 c Φ s₁ s₂ R₀ hS R hRpos).1
    have hzf := vtvStreamFlat c _ hz
    have hΦeq : Φ = fun s x i => streamField (vtvZeta Φ R₀ R) s x i + vtvErr Φ R₀ R s x i := by
      funext s x i
      exact h3 c Φ s₁ s₂ R₀ hS R hR s x i
    have hpt : ∀ p, forcedIntegrand ν (μ : ℂ) (trainVel tr) f b Φ p =
        forcedIntegrand ν (μ : ℂ) (trainVel tr) f b (streamField (vtvZeta Φ R₀ R)) p +
          forcedIntegrand ν (μ : ℂ) (trainVel tr) f b (vtvErr Φ R₀ R) p := fun p =>
      (congrArg (fun Ψ => forcedIntegrand ν (μ : ℂ) (trainVel tr) f b Ψ p) hΦeq).trans
        (h4 c ν (μ : ℂ) (trainVel tr) f b _ _ hzf hE p)
    obtain ⟨hzI, hz0⟩ := hstream _ hz
    have hEI := (vtvFubini ν c μ tr ω g b G f H _ hE).1
    rw [integral_congr_ae (Eventually.of_forall hpt), integral_add hzI hEI, hz0, zero_add]
  have hT := h5 ν c μ tr ω g b G f H Φ s₁ s₂ R₀ hS
  have hev : (fun _ : ℝ => ∫ p in Ioi (0 : ℝ) ×ˢ B0579.cell c,
        forcedIntegrand ν (μ : ℂ) (trainVel tr) f b Φ p) =ᶠ[atTop]
      fun R => ∫ p in Ioi (0 : ℝ) ×ˢ B0579.cell c,
        forcedIntegrand ν (μ : ℂ) (trainVel tr) f b (vtvErr Φ R₀ R) p := by
    filter_upwards [eventually_gt_atTop R₀] with R hR
    exact (key R hR).symm
  exact tendsto_nhds_unique (tendsto_const_nhds.congr' hev) hT

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
