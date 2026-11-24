import UnforcedLeray.Short.PartI.Sub.T01

/-!
# Part I, tasks `PartI:T01/1`, `PartI:T01/2`: the stream of a BUC train (leaves)

Source of record: `the November 2 reference manuscript`, lines 397-404
(eq. `sct:mean`: `S_s - ν S_ηη = g := \overline{v₁v₂}`, `\bar v₁ = -S_η`, `\bar v₂ = 0` for the
mean stream `S = \bar ψ`; "the last equality follows from divergence and finite energy") and
lines 261-288 (the train is the Gallay-Slijepcevic solution in `BUC`).

For a train of the BUC class (`IsBUCTrain`, `TrainClass.lean`) the time regularity of the stream
`ψ` is *derived* here, by an elementary route that needs neither a decay of `∂_sψ` nor the energy
of `\bar v₁`.  Notation: `u(s,η) = \bar v₁ = meanVel1 tr s η`, `g = meanStress tr s η`,
`S = meanStream tr s η`.

1. `ψ - S` is explicit: `∂_qψ = v₂`, so `ψ(s,q,η) - S(s,η)` is an average of `q`-integrals of
   `v₂` and is jointly smooth (`FluctStreamSmooth`).
2. `S_η = -u` (`TrainMeanV1`), so `S(s,η) = S(s,0) - ∫₀^η u(s,t) dt`.
3. `S(s,0)` is the improper integral `∫₀^∞ u(s,t) dt` (`MeanStreamDecay`: `S → 0`).  Its increment in
   `s` is computed from the averaged momentum equation `u_s = ν u_ηη - g_η`
   (`TrainMeanMomentumU`, `MeanVelIntegralDeriv`) and the decay at `+∞` of `g` and `u_η`
   (`BUCMeanStressDecay`, `BUCMeanVelDecay`, consequences of the decay of `ψ`, the bounded
   derivatives and the one-dimensional interpolation inequality `LkOneSided`), by dominated
   convergence (`MeanStreamIncrement`): `S(s₂,0) - S(s₁,0) = ∫_{s₁}^{s₂} (g(r,0) - ν u_η(r,0)) dr`.
4. Hence `S` is jointly smooth (`BUCMeanStreamSmooth`), `ψ = (ψ - S) + S` is jointly smooth
   (`trainStreamSmooth_of`, task `PartI:T01/1`), and `S_s = g - ν u_η` (`TrainMeanStreamDeriv`,
   task `PartI:T01/2`), i.e. `S_s - ν S_ηη = g`.

Each `Prop` below is the target of one task `PartI:TC/<k>` (`Short/PartI/Tasks/TrainClass/*.lean`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)

/-- The horizontal mean of the first velocity component, `u(s,η) = \bar v₁(s,η)`. -/
def meanVel1 {ν c : ℝ} (tr : B0140.TrainSol ν c) (s η : ℝ) : ℝ :=
  hmean c (fun z => tr.v s z 0) η

/-! ### Leaves -/

/-- **`PartI:TC/1`. One-sided interpolation** (Landau-Kolmogorov, by Taylor's formula): if `f` is
`C²` with `|f''| ≤ B` everywhere and `|f(t)| ≤ m` for all `t ≥ x`, then for every `h > 0`,
`|f'(x)| ≤ 2m/h + B h/2`.  (Taylor: `f(x+h) = f(x) + h f'(x) + ∫_x^{x+h} (x+h-t) f''(t) dt`, so
`h|f'(x)| ≤ |f(x+h)| + |f(x)| + B h²/2 ≤ 2m + B h²/2`.) -/
def LkOneSided : Prop :=
  ∀ (f : ℝ → ℝ) (x B m h : ℝ), ContDiff ℝ 2 f → 0 ≤ B → 0 ≤ m → 0 < h →
    (∀ t, |iteratedDeriv 2 f t| ≤ B) → (∀ t, x ≤ t → |f t| ≤ m) →
    |deriv f x| ≤ 2 * m / h + B * h / 2

/-- **`PartI:TC/2`. The mean stream decays** (lines 397-404; uses only `stream_decay`): for a
train and every age `s ≥ 0`, `S(s,η) = c⁻¹∫ ψ(s,q,η) dq → 0` as `η → +∞` (the average over one
period of a function that tends to `0` uniformly in `q`). -/
def MeanStreamDecay : Prop :=
  ∀ ν c : ℝ, 0 < ν → 0 < c → ∀ tr : B0140.TrainSol ν c, ∀ s : ℝ, 0 ≤ s →
    Tendsto (fun η : ℝ => meanStream tr s η) atTop (𝓝 0)

/-- **`PartI:TC/3`. Decay of the mean velocity and its derivative** (BUC train, `s ≥ 0`):
`u(s,η) → 0` and `∂_η u(s,η) → 0` as `η → +∞`.  Proof: `S(s,·)` is `C^∞` with `S' = -u`
(`TrainMeanV1`), `S'' = -u'` and `S''' = -u''` bounded because `u' = \overline{∂_ηv₁}`,
`u'' = \overline{∂_η²v₁}` and the orders `1, 2` of `IsBUCTrain` are bounded on `[0,s]`; `S → 0`
(`MeanStreamDecay`); apply `LkOneSided` to `f = S(s,·)` (giving `S' = -u → 0`) and to `f = S'`
(giving `S'' = -u' → 0`), with `h = 2√(m/B)`-type choices, `m` the tail sup of `|f|`. -/
def BUCMeanVelDecay : Prop :=
  ∀ ν c : ℝ, 0 < ν → 0 < c → ∀ tr : B0140.TrainSol ν c, IsBUCTrain tr → ∀ s : ℝ, 0 ≤ s →
    Tendsto (meanVel1 tr s) atTop (𝓝 0) ∧
      Tendsto (fun η : ℝ => deriv (meanVel1 tr s) η) atTop (𝓝 0)

/-- **`PartI:TC/4`. Decay of the mean stress** (BUC train, `s ≥ 0`): `g(s,η) = \overline{v₁v₂}(s,η)
→ 0` as `η → +∞`.  Proof: `v₂ = ∂_qψ`; for fixed `η` the function `q ↦ ψ(s,q,η)` is `C²` with
`|∂_q²ψ| = |∂_qv₂| ≤ M₁` (order `1` of `IsBUCTrain`) and `sup_q|ψ(s,q,η)| =: m(η) → 0` (`stream_decay`);
`LkOneSided` gives `sup_q|v₂(s,q,η)| ≤ 2m(η)/h + M₁h/2 → 0`; and `|v₁| ≤ M₀` (order `0`), so
`|g| ≤ M₀ sup_q|v₂| → 0`. -/
def BUCMeanStressDecay : Prop :=
  ∀ ν c : ℝ, 0 < ν → 0 < c → ∀ tr : B0140.TrainSol ν c, IsBUCTrain tr → ∀ s : ℝ, 0 ≤ s →
    Tendsto (meanStress tr s) atTop (𝓝 0)

/-- **`PartI:TC/5`. Age derivative of the integral of the mean velocity** (any train; lines
397-404): for `s > 0` and every `R`, the function `r ↦ ∫₀^R u(r,t) dt` has at `r = s` the derivative
`ν (∂_η u(s,R) - ∂_η u(s,0)) - (g(s,R) - g(s,0))`.  Proof: `u` and `g` are jointly `C^∞` on
`(0,∞) × ℝ` (`hmeanContDiff` with `v₁`, `v₁v₂`, smooth by `smooth_v`), so the derivative passes
under the integral over the compact `[0,R]`: `d/ds ∫₀^R u = ∫₀^R u_s`; then
`u_s = ν u_ηη - g_η` (`TrainMeanMomentumU`, theorem `trainMeanMomentumU`) and the fundamental
theorem of calculus in `t`. -/
def MeanVelIntegralDeriv : Prop :=
  ∀ ν c : ℝ, 0 < ν → 0 < c → ∀ tr : B0140.TrainSol ν c, ∀ s : ℝ, 0 < s → ∀ R : ℝ,
    HasDerivAt (fun r : ℝ => ∫ t in (0 : ℝ)..R, meanVel1 tr r t)
      (ν * (deriv (meanVel1 tr s) R - deriv (meanVel1 tr s) 0) -
        (meanStress tr s R - meanStress tr s 0)) s

/-- **`PartI:TC/6`. Increment of the mean stream at the origin** (BUC train; lines 397-404): for
`s₁, s₂ > 0`, `S(s₂,0) - S(s₁,0) = ∫_{s₁}^{s₂} (g(r,0) - ν ∂_η u(r,0)) dr`.  Proof: by `TrainMeanV1`
(`S' = -u`), `S(s,0) = S(s,R) + ∫₀^R u(s,t) dt` for every `R`; hence
`S(s₂,0) - S(s₁,0) = (S(s₂,R) - S(s₁,R)) + ∫₀^R (u(s₂,t) - u(s₁,t)) dt`.  The first bracket
tends to `0` as `R → ∞` (`MeanStreamDecay`).  By `MeanVelIntegralDeriv` and the fundamental theorem
of calculus in `r` (the derivative is continuous in `r`), the second term equals
`∫_{s₁}^{s₂} [ν(∂_η u(r,R) - ∂_η u(r,0)) - (g(r,R) - g(r,0))] dr`, which tends to
`∫_{s₁}^{s₂} [g(r,0) - ν ∂_η u(r,0)] dr` by dominated convergence: pointwise limits by
`BUCMeanVelDecay`, `BUCMeanStressDecay`, domination by `ν M₁ + M₀²` (orders `0, 1` of
`IsBUCTrain` on `[0, max s₁ s₂]`). -/
def MeanStreamIncrement : Prop :=
  ∀ ν c : ℝ, 0 < ν → 0 < c → ∀ tr : B0140.TrainSol ν c, IsBUCTrain tr → ∀ s₁ s₂ : ℝ, 0 < s₁ →
    0 < s₂ →
    meanStream tr s₂ 0 - meanStream tr s₁ 0 =
      ∫ r in s₁..s₂, (meanStress tr r 0 - ν * deriv (meanVel1 tr r) 0)

/-- **`PartI:TC/7`. The fluctuation of the stream is jointly smooth** (any train; lines
397-404): `(s,q,η) ↦ ψ(s,q,η) - S(s,η)` is `C^∞` on `(0,∞) × ℝ²`.  Proof: `∂_qψ = v₂`
(`stream`: `v s z = toVec (perpendicularGradient (ψ s) z)`), so `ψ(s,q,η) = ψ(s,0,η) + f(s,q,η)`
with `f(s,q,η) = ∫₀^q v₂(s,t,η) dt` jointly `C^∞` (parametric integral over a compact interval,
e.g. `f = q ∫₀^1 v₂(s,qτ,η) dτ`, `v₂` smooth by `smooth_v`); averaging in `q` (linear),
`S(s,η) = ψ(s,0,η) + \bar f(s,η)`, so `ψ - S = f - \bar f`, where `\bar f` is smooth by
`hmeanContDiff`. -/
def FluctStreamSmooth : Prop :=
  ∀ ν c : ℝ, 0 < ν → 0 < c → ∀ tr : B0140.TrainSol ν c,
    ContDiffOn ℝ ∞ (fun x : ℝ × Plane => tr.ψ x.1 x.2 - meanStream tr x.1 x.2.2)
      (Ioi 0 ×ˢ univ)

/-- **`PartI:TC/8`. The mean stream is jointly smooth** (BUC train; lines 397-404): `S` is `C^∞`
on `(0,∞) × ℝ`.  Proof: `S(s,η) = a(s) - ∫₀^η u(s,t) dt` with `a(s) = S(s,0)`
(`TrainMeanV1` and the fundamental theorem of calculus).  By `MeanStreamIncrement` and the
fundamental theorem of calculus, `a` has derivative `G(s) = g(s,0) - ν ∂_η u(s,0)` at every `s > 0`,
and `G` is `C^∞` on `(0,∞)` (`hmeanContDiff`), so `a` is `C^∞`.  The integral
`(s,η) ↦ ∫₀^η u(s,t) dt = η ∫₀^1 u(s,ητ) dτ` is jointly `C^∞` as a parametric integral over the
compact `[0,1]`, with the `log s` reparametrization and `Kernels.contDiffOn_integral` exactly as
in `Tasks/TrainMeanEquations/HmeanContDiff.lean`. -/
def BUCMeanStreamSmooth : Prop :=
  ∀ ν c : ℝ, 0 < ν → 0 < c → ∀ tr : B0140.TrainSol ν c, IsBUCTrain tr →
    ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => meanStream tr x.1 x.2) (Ioi 0 ×ˢ univ)

/-! ### `PartI:T01/1`: the stream of a BUC train is smooth -/

/-- **`PartI:T01/1`, conditional form**: `TrainStreamSmooth` from the smoothness of the
fluctuation `ψ - S` and of the mean stream `S`; `ψ = (ψ - S) + S ∘ (s,q,η) ↦ (s,η)`. -/
theorem trainStreamSmooth_of (hF : FluctStreamSmooth) (hS : BUCMeanStreamSmooth) :
    TrainStreamSmooth := by
  intro ν c hν hc tr hb
  have h1 := hF ν c hν hc tr
  have h2 : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => meanStream tr x.1 x.2.2)
      (Ioi 0 ×ˢ univ) := by
    have hproj : ContDiff ℝ ∞ (fun x : ℝ × Plane => ((x.1, x.2.2) : ℝ × ℝ)) := by fun_prop
    exact (hS ν c hν hc tr hb).comp hproj.contDiffOn
      (fun x hx => ⟨hx.1, mem_univ _⟩)
  have h3 := h1.add h2
  refine h3.congr (fun x _ => ?_)
  simp

end UnforcedLeray.Short.PartI
