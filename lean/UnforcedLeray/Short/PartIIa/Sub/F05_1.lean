import UnforcedLeray.Short.PartIIa.Sub.F05
import UnforcedLeray.Analysis.Heat.Averaging
import UnforcedLeray.Lib.HeatR3.FTC
import Mathlib.MeasureTheory.Integral.ExpDecay

/-!
# Part II-a, task `PartII-a:F05/1`: the adjoint resolvent of a phase test, decomposed

Source of record: `the November 2 reference manuscript`, lines 1403-1413
(adjoint semigroup `S(t)*h = e^{-t}[e^{ν(1-e^{-t})Δ}h](e^{-t/2}y)`; the adjoint resolvent of a smooth
compact spatial test has itself and two spatial derivatives in `Y_{r'}` "by the gap and the extra
factor `e^{-t/2}` per derivative").

The resolvent is `Ψ(τ, y) = ∫₀^∞ F(t, τ, y) dt` with
`F(t, τ, y) = e^{-(μ+1)t} · H(w(t); τ + t, e^{-t/2} y)`, `w(t) = √(ν(1 - e^{-t}))`, where
`H(w; τ, z) = ∫ γ(ξ) Φ₀(τ, z - wξ) dξ` (`γ = Heat.kernel 1`) is the heat flow `e^{w²Δ}` of the slice
`Φ₀(τ, ·)`, written with the *scaled* Gaussian average so that `H` is `C^∞` jointly in `(w, τ, z)`
including `w = 0` (`H(0) = Φ₀`), with all `(τ, z)`-derivatives bounded uniformly in `w`
(a translate-average of `D^kΦ₀`), and `∂_w H = 2w Δ_z H` for `w > 0` (the library heat equation
`Heat.hasDerivAt_average_time` with `w² = s`).

Everything below is a `Prop` (a lemma to be proved by a separate task) except `heatGauss`,
`adjIntegrand`, `adjPsi` (definitions) and the conditional theorem `adjResolventSolution_of`, which
derives `AdjResolventSolution` from the seven Ψ-level / abstract Props. The four `HeatGauss*` Props
are the inputs of the Ψ-level Props (they are not used by the conditional theorem itself).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.RieszLp

/-! ### Definitions -/

/-- The scaled Gaussian average of the slices of `Φ₀`:
`H(w; τ, z) = ∫ γ(ξ) Φ₀(τ, z - w ξ) dξ`, `γ = Heat.kernel 1`. For `w ≠ 0` this is
`e^{w²Δ}Φ₀(τ, ·)(z)` (`Heat.average (w^2) (Φ₀(τ, ·)) z`, substituting `y = wξ`); at `w = 0` it is
`Φ₀(τ, z)`. -/
def heatGauss (Φ₀ : ℝ × Space → CVec3) (w : ℝ) (p : ℝ × Space) : CVec3 :=
  ∫ ξ : Space, UnforcedLeray.Heat.kernel 1 ξ • Φ₀ (p.1, p.2 - w • ξ)

/-- The heat-flow parameter `w(t) = √(ν (1 - e^{-t}))` of the adjoint semigroup. -/
def adjW (ν t : ℝ) : ℝ := Real.sqrt (ν * (1 - Real.exp (-t)))

/-- The integrand `F(t, ·)` of the adjoint resolvent:
`F(t, τ, y) = e^{-(μ+1)t} H(w(t); τ + t, e^{-t/2} y)`. -/
def adjIntegrand (ν : ℝ) (μ : ℂ) (Φ₀ : ℝ × Space → CVec3) (t : ℝ) (p : ℝ × Space) : CVec3 :=
  Complex.exp (-((μ + 1) * (t : ℂ))) • heatGauss Φ₀ (adjW ν t) (p.1 + t, Real.exp (-t / 2) • p.2)

/-- The adjoint resolvent `Ψ = ∫₀^∞ F(t, ·) dt`. -/
def adjPsi (ν : ℝ) (μ : ℂ) (Φ₀ : ℝ × Space → CVec3) (p : ℝ × Space) : CVec3 :=
  ∫ t in Ioi (0 : ℝ), adjIntegrand ν μ Φ₀ t p

/-- The bound `C e^{-a t} (1 + e^{-t/2} x)^{-N}` used for the decay of `F` and its derivatives. -/
def adjDecayBound (C a N t x : ℝ) : ℝ :=
  C * Real.exp (-a * t) * (1 + Real.exp (-t / 2) * x) ^ (-N)

/-- Hypotheses on a family `G : X → (ℝ × ℝ³ → ℂ³)` for differentiation under the integral sign in
the phase-space variable: a.e. smooth, a.e.-measurable derivatives, and for each order `k` an
integrable bound of `‖D^k G_x‖` uniform in the phase-space point. -/
def ParamFamilyHyp {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {X : Type} [MeasurableSpace X] (m : Measure X) (G : X → E → CVec3) : Prop :=
  (∀ᵐ x ∂m, ContDiff ℝ ∞ (G x)) ∧
  (∀ (k : ℕ) (p : E), AEStronglyMeasurable (fun x => iteratedFDeriv ℝ k (G x) p) m) ∧
  (∀ k : ℕ, ∃ b : X → ℝ, Integrable b m ∧
    ∀ᵐ x ∂m, ∀ p : E, ‖iteratedFDeriv ℝ k (G x) p‖ ≤ b x)

/-! ### Abstract lemma Props -/

/-- **Smoothness of parameter integrals** (pure analysis; Mathlib has only the first-order
`hasFDerivAt_integral_of_dominated_of_fderiv_le`, iterate it): under `ParamFamilyHyp`, the integral
`Ψ(p) = ∫ G_x(p) dm(x)` is `C^∞` and `D^kΨ = ∫ D^kG_x dm`. -/
def ParamIntegralSmooth : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : Type) [MeasurableSpace X] (m : Measure X) (G : X → E → CVec3),
    ParamFamilyHyp m G →
      ContDiff ℝ ∞ (fun p => ∫ x, G x p ∂m) ∧
      ∀ (k : ℕ) (p : E),
        iteratedFDeriv ℝ k (fun q => ∫ x, G x q ∂m) p = ∫ x, iteratedFDeriv ℝ k (G x) p ∂m

/-- **Phase-space operators pass under the integral** (consequence of `ParamIntegralSmooth` for
`k ≤ 2`, via `iteratedFDeriv_one_apply`, `iteratedFDeriv_two_apply` and
`ContinuousMultilinearMap.integral_apply`-type commutation): under `ParamFamilyHyp`, the pointwise
values `G_x(p)`, `∂_τ G_x(p)`, `∂_{y_j} G_x(p)`, `(y·∇)G_x(p)`, `ΔG_x(p)` are integrable in `x` and
the operators `∂_τ`, `∂_{y_j}`, `y·∇`, `Δ` of `Ψ = ∫ G_x dm` are the integrals of those values. -/
def OpsUnderIntegral : Prop :=
  ∀ (X : Type) [MeasurableSpace X] (m : Measure X) (G : X → ℝ × Space → CVec3),
    ParamFamilyHyp m G → ∀ p : ℝ × Space,
      Integrable (fun x => G x p) m ∧ Integrable (fun x => dτ (G x) p) m ∧
      (∀ j, Integrable (fun x => dy j (G x) p) m) ∧
      Integrable (fun x => radialT (G x) p) m ∧ Integrable (fun x => lapT (G x) p) m ∧
      dτ (fun q => ∫ x, G x q ∂m) p = ∫ x, dτ (G x) p ∂m ∧
      (∀ j, dy j (fun q => ∫ x, G x q ∂m) p = ∫ x, dy j (G x) p ∂m) ∧
      radialT (fun q => ∫ x, G x q ∂m) p = ∫ x, radialT (G x) p ∂m ∧
      lapT (fun q => ∫ x, G x q ∂m) p = ∫ x, lapT (G x) p ∂m

/-- **The `t`-integral decay** (pure real analysis): for `a > 0`, `N > 2a`,
`∫₀^∞ e^{-at} (1 + e^{-t/2} x)^{-N} dt ≤ C (1 + x)^{-2a}` for all `x ≥ 0`. Split at
`t₀ = 2 log(1 + x)`: for `t ≥ t₀` use `e^{-at} ≤ e^{-a t₀}`-integration, for `t ≤ t₀` use
`(1 + u)^{-N} ≤ u^{-N}` with `u = e^{-t/2}x`. -/
def TIntegralDecay : Prop :=
  ∀ a N : ℝ, 0 < a → 2 * a < N →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 0 ≤ x →
      ∫ t in Ioi (0 : ℝ), Real.exp (-a * t) * (1 + Real.exp (-t / 2) * x) ^ (-N) ≤
        C * (1 + x) ^ (-(2 * a))

/-- **Derivatives of a phase test are bounded** (`P > 0`): `D^kΦ₀` is continuous, `P`-periodic in `τ`
and vanishes for `‖y‖ > R` (it vanishes on the open set where `Φ₀` vanishes), so it is bounded by its
sup over the compact set `[0, P] × closedBall 0 R`. (`P > 0` is essential: with `P = 0` the
periodicity condition is vacuous and `Φ₀(τ, y) = τ χ(y)` is a "phase test".) -/
def PhaseTestDerivBounded : Prop :=
  ∀ (P : ℝ), 0 < P → ∀ (Φ₀ : ℝ × Space → CVec3), IsPhaseTest P Φ₀ →
    ∀ k : ℕ, ∃ M : ℝ, 0 ≤ M ∧ ∀ p : ℝ × Space, ‖iteratedFDeriv ℝ k Φ₀ p‖ ≤ M

/-! ### Heat-flow Props (for `heatGauss Φ₀`, `Φ₀` a phase test) -/

/-- **Smoothness and uniform derivative bounds of `heatGauss`**: jointly `C^∞` in `(w, τ, z)`
(differentiate under the integral: `(w, τ, z) ↦ (τ, z - wξ)` is linear of norm `≤ 1 + ‖ξ‖`, so
`‖D^k‖ ≤ M_k (1 + ‖ξ‖)^k`, integrable against `γ`), and for each `k` the `(τ, z)`-derivatives are
bounded by `M_k = sup ‖D^kΦ₀‖` uniformly in `w` (translate average of `D^kΦ₀`; `∫ γ = 1`). -/
def HeatGaussSmooth : Prop :=
  ∀ (P : ℝ), 0 < P → ∀ (Φ₀ : ℝ × Space → CVec3), IsPhaseTest P Φ₀ →
    ContDiff ℝ ∞ (fun q : ℝ × (ℝ × Space) => heatGauss Φ₀ q.1 q.2) ∧
    (∀ w, ContDiff ℝ ∞ (heatGauss Φ₀ w)) ∧
    ∀ k : ℕ, ∃ M : ℝ, 0 ≤ M ∧ ∀ (w : ℝ) (q : ℝ × Space),
      ‖iteratedFDeriv ℝ k (heatGauss Φ₀ w) q‖ ≤ M

/-- **Initial value and periodicity of `heatGauss`**: `H(0) = Φ₀` (`∫ γ = 1`,
`Heat.integral_kernel`) and `H(w)` is `P`-periodic in `τ`. -/
def HeatGaussInitial : Prop :=
  ∀ (P : ℝ), 0 < P → ∀ (Φ₀ : ℝ × Space → CVec3), IsPhaseTest P Φ₀ →
    (∀ p, heatGauss Φ₀ 0 p = Φ₀ p) ∧
    ∀ (w τ : ℝ) (y : Space), heatGauss Φ₀ w (τ + P, y) = heatGauss Φ₀ w (τ, y)

/-- **Heat equation for `heatGauss`**: for `w > 0`, `∂_w H(w) = 2w Δ_z H(w)` (change of variables
`y = wξ` identifies `H(w; τ, ·) = Heat.average (w^2) (Φ₀(τ, ·))`; then
`Heat.hasDerivAt_average_time` (`C²_b` data) and `Heat.vlap_average` with the chain rule `s = w²`;
`lapT` of the phase-space function is the `vlap` of the slice). -/
def HeatGaussEquation : Prop :=
  ∀ (P : ℝ), 0 < P → ∀ (Φ₀ : ℝ × Space → CVec3), IsPhaseTest P Φ₀ →
    ∀ w : ℝ, 0 < w → ∀ q : ℝ × Space,
      HasDerivAt (fun w' => heatGauss Φ₀ w' q) ((2 * w) • lapT (heatGauss Φ₀ w) q) w

/-- **Polynomial (Gaussian-tail) decay of `heatGauss`, locally uniformly in `w`**: since `D^kΦ₀`
vanishes for `‖y‖ > R`, the translate average `∫ γ(ξ) D^kΦ₀(τ, z - wξ) dξ` only sees
`‖ξ‖ ≥ (‖z‖ - R)/W` for `|w| ≤ W`, and `γ` has Gaussian tails. -/
def HeatGaussDecay : Prop :=
  ∀ (P : ℝ), 0 < P → ∀ (Φ₀ : ℝ × Space → CVec3), IsPhaseTest P Φ₀ →
    ∀ (W : ℝ) (k N : ℕ), ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℝ, |w| ≤ W → ∀ q : ℝ × Space,
      ‖iteratedFDeriv ℝ k (heatGauss Φ₀ w) q‖ ≤ C * (1 + ‖q.2‖) ^ (-(N : ℝ))

/-! ### Ψ-level Props (consumed by the conditional theorem) -/

/-- **Regularity of the integrand** `F(t, ·) = adjIntegrand ν μ Φ₀ t` (inputs: `HeatGaussSmooth`,
`HeatGaussInitial`): for `t > 0` it is `C^∞` (composition of `heatGauss Φ₀ (adjW ν t)` with the affine
map `(τ, y) ↦ (τ + t, e^{-t/2} y)`); it is `P`-periodic in `τ`; `t ↦ D^kF(t)(p)` is a.e.-measurable
on `(0, ∞)` (continuous in `t` there: `adjW ν` is continuous, `heatGauss` jointly smooth); and
`‖D^kF(t)(p)‖ ≤ C e^{-(Re μ + 1)t}` (the linear part of the affine map has norm `≤ 1` for `t ≥ 0`,
`‖e^{-(μ+1)t}‖ = e^{-(Re μ+1)t}`, uniform bound `M_k` of `HeatGaussSmooth`). -/
def AdjIntegrandRegular : Prop :=
  ∀ (P ν : ℝ), 0 < P → 0 < ν → ∀ μ : ℂ, 0 < μ.re + 1 → ∀ Φ₀ : ℝ × Space → CVec3, IsPhaseTest P Φ₀ →
    (∀ t : ℝ, 0 < t → ContDiff ℝ ∞ (adjIntegrand ν μ Φ₀ t)) ∧
    (∀ (t τ : ℝ) (y : Space), adjIntegrand ν μ Φ₀ t (τ + P, y) = adjIntegrand ν μ Φ₀ t (τ, y)) ∧
    (∀ (k : ℕ) (p : ℝ × Space),
      AEStronglyMeasurable (fun t => iteratedFDeriv ℝ k (adjIntegrand ν μ Φ₀ t) p)
        (volume.restrict (Ioi (0 : ℝ)))) ∧
    ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 < t → ∀ p : ℝ × Space,
      ‖iteratedFDeriv ℝ k (adjIntegrand ν μ Φ₀ t) p‖ ≤ C * Real.exp (-(μ.re + 1) * t)

/-- **The `t`-derivative of the integrand** (chain rule, inputs: `HeatGaussSmooth`,
`HeatGaussEquation`): for `t > 0`,
`∂_t F = -(μ+1) F + ∂_τ F - ½ (y·∇)F + ν ΔF`. With `w(t) = √(ν(1 - e^{-t}))`,
`w'(t) = ν e^{-t}/(2w)`, so `∂_w H · w' = ν e^{-t} Δ_z H`, while `ΔF = e^{-(μ+1)t} e^{-t} (Δ_zH)`,
`(y·∇)F = e^{-(μ+1)t} e^{-t/2} (y·∇_zH)` and `∂_τF = e^{-(μ+1)t} ∂_τH`. -/
def AdjIntegrandDeriv : Prop :=
  ∀ (P ν : ℝ), 0 < P → 0 < ν → ∀ (μ : ℂ) (Φ₀ : ℝ × Space → CVec3), IsPhaseTest P Φ₀ →
    ∀ t : ℝ, 0 < t → ∀ p : ℝ × Space,
      HasDerivAt (fun s => adjIntegrand ν μ Φ₀ s p)
        (-(μ + 1) • adjIntegrand ν μ Φ₀ t p + dτ (adjIntegrand ν μ Φ₀ t) p
          - (1 / 2 : ℝ) • radialT (adjIntegrand ν μ Φ₀ t) p
          + ν • lapT (adjIntegrand ν μ Φ₀ t) p) t

/-- **Limits of the integrand** (inputs: `AdjIntegrandRegular` for the `t → ∞` bound
`‖F(t)(p)‖ ≤ C e^{-(Re μ+1)t}`; `HeatGaussSmooth` (continuity of `heatGauss` at `(0, ·)`) and
`HeatGaussInitial` (`H(0) = Φ₀`) for `t → 0⁺`, where `w(t) → 0` and `e^{-(μ+1)t} → 1`). -/
def AdjIntegrandLimits : Prop :=
  ∀ (P ν : ℝ), 0 < P → 0 < ν → ∀ μ : ℂ, 0 < μ.re + 1 → ∀ Φ₀ : ℝ × Space → CVec3, IsPhaseTest P Φ₀ →
    ∀ p : ℝ × Space,
      Tendsto (fun t => adjIntegrand ν μ Φ₀ t p) atTop (𝓝 0) ∧
      Tendsto (fun t => adjIntegrand ν μ Φ₀ t p) (𝓝[>] 0) (𝓝 (Φ₀ p))

/-- **Decay of the integrand and its operators** (inputs: `HeatGaussSmooth`, `HeatGaussDecay` with
`W = √ν`, since `w(t) ≤ √ν`): for each `N` there is `C` with
`‖F(t)(τ, y)‖, ‖∂_{y_j}F(t)(τ, y)‖, ‖ΔF(t)(τ, y)‖ ≤ C e^{-(Re μ+1)t} (1 + e^{-t/2}‖y‖)^{-N}`
(`∂_{y_j}F = e^{-(μ+1)t} e^{-t/2} (∂_jH)`, `ΔF = e^{-(μ+1)t} e^{-t} (ΔH)`, evaluated at
`(τ + t, e^{-t/2}y)` with `‖e^{-t/2}y‖ = e^{-t/2}‖y‖`). -/
def AdjIntegrandDecay : Prop :=
  ∀ (P ν : ℝ), 0 < P → 0 < ν → ∀ μ : ℂ, 0 < μ.re + 1 → ∀ Φ₀ : ℝ × Space → CVec3, IsPhaseTest P Φ₀ →
    ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 < t → ∀ (τ : ℝ) (y : Space),
      ‖adjIntegrand ν μ Φ₀ t (τ, y)‖ ≤ adjDecayBound C (μ.re + 1) N t ‖y‖ ∧
      (∀ j, ‖dy j (adjIntegrand ν μ Φ₀ t) (τ, y)‖ ≤ adjDecayBound C (μ.re + 1) N t ‖y‖) ∧
      ‖lapT (adjIntegrand ν μ Φ₀ t) (τ, y)‖ ≤ adjDecayBound C (μ.re + 1) N t ‖y‖

/-! ### The conditional theorem -/

/-- `AdjResolventSolution` follows from the seven Props above (the abstract smoothness /
operator-under-integral / `t`-integral Props and the four Ψ-level Props). -/
theorem adjResolventSolution_of
    (hA : ParamIntegralSmooth) (hO : OpsUnderIntegral) (hT : TIntegralDecay)
    (hR : AdjIntegrandRegular) (hD : AdjIntegrandDeriv) (hL : AdjIntegrandLimits)
    (hY : AdjIntegrandDecay) : AdjResolventSolution := by
  intro P hPf ν hν μ hμ Φ₀ hΦ
  have hP : 0 < P := hPf.out
  obtain ⟨hFs, hFp, hFm, hFb⟩ := hR P ν hP hν μ hμ Φ₀ hΦ
  have hia : IntegrableOn (fun t : ℝ => Real.exp (-(μ.re + 1) * t)) (Ioi 0) :=
    exp_neg_integrableOn_Ioi 0 hμ
  have hfam : ParamFamilyHyp (volume.restrict (Ioi (0 : ℝ))) (adjIntegrand ν μ Φ₀) := by
    refine ⟨?_, hFm, ?_⟩
    · rw [ae_restrict_iff' measurableSet_Ioi]
      exact Eventually.of_forall fun t ht => hFs t ht
    · intro k
      obtain ⟨C, hC, hb⟩ := hFb k
      refine ⟨fun t => C * Real.exp (-(μ.re + 1) * t), hia.const_mul C, ?_⟩
      rw [ae_restrict_iff' measurableSet_Ioi]
      exact Eventually.of_forall fun t ht p => hb t ht p
  obtain ⟨hΨs, -⟩ := hA (ℝ × Space) ℝ (volume.restrict (Ioi (0 : ℝ))) (adjIntegrand ν μ Φ₀) hfam
  have hops := hO ℝ (volume.restrict (Ioi (0 : ℝ))) (adjIntegrand ν μ Φ₀) hfam
  refine ⟨adjPsi ν μ Φ₀, hΨs, ?_, ?_, ?_⟩
  · intro τ y
    simp only [adjPsi, hFp]
  · intro p
    obtain ⟨iF, iτ, iy, ir, il, eτ, ey, er, el⟩ := hops p
    have i1 : Integrable (fun t => -(μ + 1) • adjIntegrand ν μ Φ₀ t p)
        (volume.restrict (Ioi (0 : ℝ))) := iF.smul (-(μ + 1) : ℂ)
    have i3 : Integrable (fun t => (1 / 2 : ℝ) • radialT (adjIntegrand ν μ Φ₀ t) p)
        (volume.restrict (Ioi (0 : ℝ))) := ir.smul (1 / 2 : ℝ)
    have i4 : Integrable (fun t => ν • lapT (adjIntegrand ν μ Φ₀ t) p)
        (volume.restrict (Ioi (0 : ℝ))) := il.smul ν
    have i12 : Integrable (fun t => -(μ + 1) • adjIntegrand ν μ Φ₀ t p
        + dτ (adjIntegrand ν μ Φ₀ t) p) (volume.restrict (Ioi (0 : ℝ))) := i1.add iτ
    have i123 : Integrable (fun t => -(μ + 1) • adjIntegrand ν μ Φ₀ t p
        + dτ (adjIntegrand ν μ Φ₀ t) p - (1 / 2 : ℝ) • radialT (adjIntegrand ν μ Φ₀ t) p)
        (volume.restrict (Ioi (0 : ℝ))) := i12.sub i3
    have hftc : ∫ t in Ioi (0 : ℝ), (-(μ + 1) • adjIntegrand ν μ Φ₀ t p
        + dτ (adjIntegrand ν μ Φ₀ t) p - (1 / 2 : ℝ) • radialT (adjIntegrand ν μ Φ₀ t) p
        + ν • lapT (adjIntegrand ν μ Φ₀ t) p) = -Φ₀ p := by
      let f : ℝ → CVec3 := fun t => if t = 0 then Φ₀ p else adjIntegrand ν μ Φ₀ t p
      have hfeq : ∀ t : ℝ, 0 < t → f t = adjIntegrand ν μ Φ₀ t p :=
        fun t ht => ite_eq_right_iff.mpr (fun h => absurd h ht.ne')
      obtain ⟨hlimTop, hlim0⟩ := hL P ν hP hν μ hμ Φ₀ hΦ p
      have h1 : ContinuousWithinAt f (Ici 0) 0 := by
        rw [← continuousWithinAt_Ioi_iff_Ici]
        have h0 : f 0 = Φ₀ p := ite_eq_left_iff.mpr (fun h => absurd rfl h)
        rw [ContinuousWithinAt, h0]
        refine hlim0.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with t ht
        exact (hfeq t ht).symm
      have h2 : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt f
          (-(μ + 1) • adjIntegrand ν μ Φ₀ x p + dτ (adjIntegrand ν μ Φ₀ x) p
            - (1 / 2 : ℝ) • radialT (adjIntegrand ν μ Φ₀ x) p
            + ν • lapT (adjIntegrand ν μ Φ₀ x) p) x := by
        intro x hx
        refine (hD P ν hP hν μ Φ₀ hΦ x hx p).congr_of_eventuallyEq ?_
        filter_upwards [Ioi_mem_nhds hx] with s hs using hfeq s hs
      have h3 : IntegrableOn (fun t => -(μ + 1) • adjIntegrand ν μ Φ₀ t p
          + dτ (adjIntegrand ν μ Φ₀ t) p - (1 / 2 : ℝ) • radialT (adjIntegrand ν μ Φ₀ t) p
          + ν • lapT (adjIntegrand ν μ Φ₀ t) p) (Ioi 0) := i123.add i4
      have h4 : Tendsto f atTop (𝓝 0) := by
        refine hlimTop.congr' ?_
        filter_upwards [eventually_gt_atTop 0] with t ht
        exact (hfeq t ht).symm
      have h5 := integral_Ioi_of_hasDerivAt_of_tendsto h1 h2 h3 h4
      have h0 : f 0 = Φ₀ p := ite_eq_left_iff.mpr (fun h => absurd rfl h)
      rw [h5, h0, zero_sub]
    rw [integral_add i123 i4, integral_sub i12 i3, integral_add i1 iτ, integral_smul,
      integral_smul, integral_smul] at hftc
    have eτ' : dτ (adjPsi ν μ Φ₀) p = ∫ t in Ioi (0 : ℝ), dτ (adjIntegrand ν μ Φ₀ t) p := eτ
    have er' : radialT (adjPsi ν μ Φ₀) p
        = ∫ t in Ioi (0 : ℝ), radialT (adjIntegrand ν μ Φ₀ t) p := er
    have el' : lapT (adjPsi ν μ Φ₀) p
        = ∫ t in Ioi (0 : ℝ), lapT (adjIntegrand ν μ Φ₀ t) p := el
    have hΨp : adjPsi ν μ Φ₀ p = ∫ t in Ioi (0 : ℝ), adjIntegrand ν μ Φ₀ t p := rfl
    rw [← hΨp, ← eτ', ← er', ← el'] at hftc
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, L0T, driftT, nuLapT]
    simp only [← Complex.coe_smul] at hftc ⊢
    push_cast at hftc ⊢
    linear_combination (norm := module) (-1 : ℂ) • hftc
  · obtain ⟨N, hN⟩ : ∃ N : ℕ, 2 * (μ.re + 1) < (N : ℝ) := exists_nat_gt _
    obtain ⟨C₁, hC₁, hC₁b⟩ := hY P ν hP hν μ hμ Φ₀ hΦ N
    obtain ⟨C₂, hC₂, hC₂b⟩ := hT (μ.re + 1) N hμ hN
    refine ⟨C₁ * C₂, fun τ y => ?_⟩
    have key : ∀ X : ℝ → CVec3,
        (∀ t : ℝ, 0 < t → ‖X t‖ ≤ adjDecayBound C₁ (μ.re + 1) N t ‖y‖) →
        ‖∫ t in Ioi (0 : ℝ), X t‖ ≤ C₁ * C₂ * (1 + ‖y‖) ^ (-(2 * (μ.re + 1))) := by
      intro X hX
      have hg : IntegrableOn (fun t => adjDecayBound C₁ (μ.re + 1) N t ‖y‖) (Ioi 0) := by
        refine Integrable.mono' (hia.const_mul C₁) ?_ ?_
        · unfold adjDecayBound
          have hc : Continuous (fun t : ℝ => C₁ * Real.exp (-(μ.re + 1) * t) *
              (1 + Real.exp (-t / 2) * ‖y‖) ^ (-(N : ℝ))) := by
            refine (continuous_const.mul (by fun_prop)).mul ?_
            refine Continuous.rpow_const (by fun_prop) (fun t => Or.inl ?_)
            positivity
          exact hc.aestronglyMeasurable
        · rw [ae_restrict_iff' measurableSet_Ioi]
          refine Eventually.of_forall fun t ht => ?_
          unfold adjDecayBound
          have hb : (1 : ℝ) ≤ 1 + Real.exp (-t / 2) * ‖y‖ := by
            have := mul_nonneg (Real.exp_pos (-t / 2)).le (norm_nonneg y)
            linarith
          have h1 : (1 + Real.exp (-t / 2) * ‖y‖) ^ (-(N : ℝ)) ≤ 1 :=
            Real.rpow_le_one_of_one_le_of_nonpos hb (by simp)
          rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
          exact mul_le_of_le_one_right (by positivity) h1
      calc ‖∫ t in Ioi (0 : ℝ), X t‖
          ≤ ∫ t in Ioi (0 : ℝ), adjDecayBound C₁ (μ.re + 1) N t ‖y‖ :=
            norm_integral_le_of_norm_le hg
              ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => hX t ht))
        _ = C₁ * ∫ t in Ioi (0 : ℝ), Real.exp (-(μ.re + 1) * t) *
              (1 + Real.exp (-t / 2) * ‖y‖) ^ (-(N : ℝ)) := by
            rw [← integral_const_mul]
            refine integral_congr_ae (Eventually.of_forall fun t => ?_)
            simp only [adjDecayBound]
            ring
        _ ≤ C₁ * (C₂ * (1 + ‖y‖) ^ (-(2 * (μ.re + 1)))) :=
            mul_le_mul_of_nonneg_left (hC₂b ‖y‖ (norm_nonneg _)) hC₁
        _ = C₁ * C₂ * (1 + ‖y‖) ^ (-(2 * (μ.re + 1))) := by ring
    obtain ⟨-, -, -, -, -, -, ey, -, el⟩ := hops (τ, y)
    refine ⟨key (fun t => adjIntegrand ν μ Φ₀ t (τ, y)) (fun t ht => (hC₁b t ht τ y).1),
      fun j => ?_, ?_⟩
    · have e : dy j (adjPsi ν μ Φ₀) (τ, y)
          = ∫ t in Ioi (0 : ℝ), dy j (adjIntegrand ν μ Φ₀ t) (τ, y) := ey j
      rw [e]
      exact key (fun t => dy j (adjIntegrand ν μ Φ₀ t) (τ, y)) (fun t ht => (hC₁b t ht τ y).2.1 j)
    · have e : lapT (adjPsi ν μ Φ₀) (τ, y)
          = ∫ t in Ioi (0 : ℝ), lapT (adjIntegrand ν μ Φ₀ t) (τ, y) := el
      rw [e]
      exact key (fun t => lapT (adjIntegrand ν μ Φ₀ t) (τ, y)) (fun t ht => (hC₁b t ht τ y).2.2)

end UnforcedLeray.Short.PartIIa
