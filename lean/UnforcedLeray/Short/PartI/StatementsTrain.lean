import UnforcedLeray.Short.PartI.TrainClass
import UnforcedLeray.Units.B0140
import UnforcedLeray.Units.B0277
import UnforcedLeray.Units.B0278
import UnforcedLeray.Lib.Train.VortexBounds
import UnforcedLeray.Lib.Train.Datum
import UnforcedLeray.Lib.Train.Params
import UnforcedLeray.Lib.Train.PeriodizedVortex

/-!
# Part I, module `seed-train/train.tex`: the exact periodic planar train (statements)

Source of record: `the November 2 reference manuscript`, lines 241-552
(Section "The exact periodic planar train", Lemma `sct:train` lines 289-325 / proof 326-436,
Lemma `sct:heat` lines 437-481 / proof 482-551).  Everything below is a `Prop`-valued definition stating a
numbered result of the source about the concrete train `v = ∇^⊥ψ` of the cylinder
`C_c = (ℝ/cℤ) × ℝ`; there are no `sorry`s and no axioms.

## The BUC class

The train of the source is the Gallay-Slijepcevic solution in `BUC` (lines 270-288).  The bare
`B0140.IsTrain` is not strong enough to make Lemmas `sct:train`, `sct:heat` or the uniqueness of the
train true or derivable (it is pointwise in the age `s`), so *every* statement below about a train
`tr : B0140.TrainSol ν c` carries the hypothesis `IsBUCTrain tr` (`TrainClass.lean`: all spatial
derivatives of `v` bounded on `[0, S] × ℝ²` for every `S`).  `TrainGlobalExistence` says that the class
is non-empty (for `c ≥ 1`); `TrainUniqueness` that it has at most one member for `s ≥ 0`.

## Reused Lean objects (existing names)

* `UnforcedLeray.B0140.TrainSol ν c` / `IsTrain`: the global smooth finite-energy train with
  decaying stream `ψ`, decaying pressure `p`, central oddness (source lines 261-288);
  `IsBUCTrain` (`TrainClass.lean`) is the class wrapping it.
* `UnforcedLeray.Train.Vc ν c s`: the periodized isolated heat vortex `V_c^p`;
  `Train.pc ν c s` the sum of isolated radial pressures `p_c^p` in the decaying gauge;
  `Train.width ν s = 1 + νs = a(s)`; `Train.jet j f = D^j f`; `Train.cellL2` and `Train.wCellL2`
  the unnormalized one-cell (weighted) `L²` norms, valued in `[0,∞]`;
  `B0277.supNormD j f = ‖D^j f‖_∞ ∈ [0,∞]`; `B0146.overlapAge ν c = s_c = (c²-1)/ν`;
  `B0278.TrainStrainEstimate`.
* `Train.Vc_bounds` (Lib/Train/VortexBounds.lean) is the first paragraph of the proof of
  Lemma `sct:train` (isolated-vortex bounds, lines 327-336).

## Conventions

* `c = ν^{-ρ}` (`Real.rpow`), `ρ > 1/2`; `e_c = (νc²)^{-1}`; "decreasing `e_c`" is the existence
  of `ν₀ > 0` with all statements for `0 < ν ≤ ν₀`.  The source's polynomials `P` in `c, ν^{-1}`
  are represented by their majorant `C (1 + c + ν⁻¹)^N` (`polyP`); `P_S` by `polyPS`.
* Norms valued in `ℝ≥0∞` (`eLpNorm`, `supNormD`) so that no junk value of a divergent integral
  or an unbounded supremum can enter a statement.
* Age derivatives `∂_s^ℓ` are `iteratedDeriv ℓ` in the age variable, taken at `s > 0` (interior
  points, so no one-sided junk); `D^j` is `iteratedFDeriv ℝ j` in `(q, η)`.
* `hmean c f η` is the normalized horizontal average `c⁻¹ ∫_{cell} f(q,η) dq` (the source's bar),
  `hfluct` its complement (the source's tilde).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Real
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec jet cellL2 wCellL2 jap Vc pc width)

/-! ### Notation -/

/-- The period `c = ν^{-ρ}` of Section `sct:section` (line 253). -/
def trainPeriod (ρ ν : ℝ) : ℝ := ν ^ (-ρ)

/-- `e_c = (ν c²)^{-1}` (line 253). -/
def eC (ν c : ℝ) : ℝ := (ν * c ^ 2)⁻¹

/-- The normalized horizontal average `\bar f(η) = c⁻¹ ∫_{(-c/2,c/2]} f(q,η) dq`. -/
def hmean {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (c : ℝ) (f : Plane → E)
    (η : ℝ) : E :=
  c⁻¹ • ∫ q in Ioc (-c / 2) (c / 2), f (q, η)

/-- The complement `\tilde f = f - \bar f` of the horizontal average. -/
def hfluct {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (c : ℝ) (f : Plane → E)
    (z : Plane) : E :=
  f z - hmean c f z.2

/-- The mixed age/spatial jet `∂_s^ℓ D^j F (s)`, of a time-dependent field `F`. -/
def ageJet {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (ℓ j : ℕ)
    (F : ℝ → Plane → E) (s : ℝ) : Plane → ContinuousMultilinearMap ℝ (fun _ : Fin j => Plane) E :=
  jet j (fun z => iteratedDeriv ℓ (fun r => F r z) s)

/-- The mixed slow-age/spatial jet `∂_σ^ℓ D^j F`, `σ = ν s`, evaluated at age `s`. -/
def sigmaJet {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (ν : ℝ) (ℓ j : ℕ)
    (F : ℝ → Plane → E) (s : ℝ) : Plane → ContinuousMultilinearMap ℝ (fun _ : Fin j => Plane) E :=
  jet j (fun z => iteratedDeriv ℓ (fun σ => F (σ / ν) z) (ν * s))

/-- The weighted sup norm `‖⟨η⟩^m f‖_∞ ∈ [0,∞]`, `⟨η⟩^m = (1+η²)^{m/2}`. -/
def wSupNorm {E : Type*} [NormedAddCommGroup E] (m : ℕ) (f : Plane → E) : ℝ≥0∞ :=
  ⨆ z : Plane, ENNReal.ofReal (Real.sqrt (jap m z)) * ‖f z‖ₑ

/-- The source's polynomial `P` in `c, ν⁻¹` (line 257), as the majorant `C (1+c+ν⁻¹)^N`. -/
def polyP (C : ℝ) (N : ℕ) (ν c : ℝ) : ℝ := C * (1 + c + ν⁻¹) ^ N

/-- `P_S`: additionally polynomial in `1+S` (line 248). -/
def polyPS (C : ℝ) (N : ℕ) (ν c S : ℝ) : ℝ := C * ((1 + c + ν⁻¹) * (1 + S)) ^ N

/-- The one-dimensional heat kernel `G_t(η) = (4πt)^{-1/2} e^{-η²/(4t)}`, `∂_t G = ∂_η² G`. -/
def heatKernel1 (t η : ℝ) : ℝ := (Real.sqrt (4 * π * t))⁻¹ * Real.exp (-(η ^ 2) / (4 * t))

/-- The overlap-rescaled field `U(T,y) = c³ v(s_c + c²T/ν, c y)`, `y = (X,Y) = (q/c, η/c)`
(line 305: `X = q/c`, `Y = η/c`, `T = ν(s-s_c)/c²`, `c³ v = b e₁ + W`). -/
def overlapField (ν c : ℝ) (v : ℝ → Plane → Vec) (T : ℝ) (y : Plane) : Vec :=
  c ^ 3 • v (B0146.overlapAge ν c + c ^ 2 * T / ν) (c • y)

/-- The mean stream `S = \bar ψ` of the train (line 397). -/
def meanStream {ν c : ℝ} (tr : B0140.TrainSol ν c) (s η : ℝ) : ℝ := hmean c (tr.ψ s) η

/-- The mean Reynolds stress `g = \overline{v₁ v₂}` (line 399, eq. `sct:mean`). -/
def meanStress {ν c : ℝ} (tr : B0140.TrainSol ν c) (s η : ℝ) : ℝ :=
  hmean c (fun z => tr.v s z 0 * tr.v s z 1) η

/-- The coefficient `a_{2j}` of the mean-stream expansion (second display of `sct:expansion`,
lines 450-453). -/
def meanCoeff {ν c : ℝ} (tr : B0140.TrainSol ν c) (j : ℕ) : ℝ :=
  (∫ η : ℝ, η ^ (2 * j) * meanStream tr 0 η) / ((2 * j).factorial : ℝ) +
    ∫ t in Ioi (0 : ℝ), ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal j,
      ((-(ν * t)) ^ kl.2 / ((kl.2.factorial : ℝ) * ((2 * kl.1).factorial : ℝ))) *
        ∫ η : ℝ, η ^ (2 * kl.1) * meanStress tr t η

/-- The remainder `R_N(η,s) = S(η,s) - ∑_{j≤N} a_{2j} ∂_η^{2j} G_{νs}(η)` (first display of
`sct:expansion`, lines 448-449). -/
def meanRemainder {ν c : ℝ} (tr : B0140.TrainSol ν c) (N : ℕ) (s η : ℝ) : ℝ :=
  meanStream tr s η -
    ∑ j ∈ Finset.range (N + 1), meanCoeff tr j * iteratedDeriv (2 * j) (heatKernel1 (ν * s)) η

/-! ### Existence and uniqueness of the train (lines 256-272) -/

/-- **Global existence of the train in the BUC class** (Gallay-Slijepcevic, Thm 1.1 and
Rem. 1.3(2), applied as in lines 261-282): for every viscosity `ν > 0` and period `c ≥ 1` (the
periods of the paper are `c = ν^{-ρ} ≥ 1`; the library's datum estimates and the local existence
route assume `c ≥ 1`) there is the global smooth finite-energy solution `v = ∇^⊥ψ` on `C_c` with
the periodized Gaussian datum, decaying stream, decaying (bounded periodic) pressure gauge,
central oddness (`B0140.IsTrain`, lines 261-288), in the Gallay-Slijepcevic class `BUC`: all spatial
derivatives of `v` are bounded on `[0, S] × ℝ²` for every `S` (`IsBUCTrain`, `TrainClass.lean`). -/
def TrainGlobalExistence : Prop :=
  ∀ ν c : ℝ, 0 < ν → 1 ≤ c → TrainBUCSolvable ν c

/-- **Uniqueness of the train in the BUC class** (lines 276-288: "unique global mild solution in
`BUC`", "the finite-energy solution", "Uniqueness gives `v(-q,-η,s) = -v(q,η,s)`"): two trains of
the class `IsBUCTrain` with the same period have the same velocity at every age `s ≥ 0`.  (Equality
of `v` on negative ages is not a property of `B0140.IsTrain`, and for the bare `IsTrain` the
statement is not derivable: see `TrainClass.lean`.) -/
def TrainUniqueness : Prop :=
  ∀ ν c : ℝ, 0 < ν → 1 ≤ c → ∀ tr tr' : B0140.TrainSol ν c, IsBUCTrain tr → IsBUCTrain tr' →
    ∀ s : ℝ, 0 ≤ s → tr.v s = tr'.v s

/-! ### Lemma `sct:train` -/

/-- **`sct:comparison`** (lines 291-303): one estimate before overlap.  For every fixed `j`, with
constants independent of `c, ν`, and for `ν` small (`e_c` small), `1 ≤ a ≤ c²`:
`‖D^j (v - V_c^p)(s)‖₂ ≤ C_j ν⁻¹ a^{-2-j/2} e^{-b_j c²/a}` and
`‖D^j (v - V_c^p)(s)‖_∞ ≤ C_j ν⁻¹ a^{-(5+j)/2} e^{-b_j c²/a}`. -/
def TrainComparison : Prop :=
  ∀ ρ : ℝ, 1 / 2 < ρ → ∀ j : ℕ, ∃ C b ν₀ : ℝ, 0 < C ∧ 0 < b ∧ 0 < ν₀ ∧
    ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ → ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr → ∀ s : ℝ, 0 ≤ s →
      width ν s ≤ trainPeriod ρ ν ^ 2 →
        cellL2 (trainPeriod ρ ν) (jet j (fun z => tr.v s z - Vc ν (trainPeriod ρ ν) s z)) ≤
            ENNReal.ofReal (C * ν⁻¹ * width ν s ^ (-(2 + (j : ℝ) / 2)) *
              Real.exp (-(b * trainPeriod ρ ν ^ 2 / width ν s))) ∧
        B0277.supNormD j (fun z => tr.v s z - Vc ν (trainPeriod ρ ν) s z) ≤
            ENNReal.ofReal (C * ν⁻¹ * width ν s ^ (-((5 + (j : ℝ)) / 2)) *
              Real.exp (-(b * trainPeriod ρ ν ^ 2 / width ν s)))

/-- **`sct:overlap`** (lines 304-313): the decomposition after overlap.  With `U = c³ v` in the
overlap variables, `U(T) = b(Y,T) e₁ + W(X,Y,T)`, `\bar W = 0` (here `b e₁ = \bar U`, the
second component of `\bar U` vanishing by `sct:mean`), and for all `T ≥ 0`:
`‖∂_Y^j b(T)‖_p ≤ C_{j,p} (1+T)^{-1-j/2+1/(2p)}` for `p = 2, ∞` and
`‖D^j W(T)‖_{2∩∞} ≤ C_j e^{-λ_j T}` (norms on the unit cylinder). -/
def TrainOverlap : Prop :=
  ∀ ρ : ℝ, 1 / 2 < ρ → ∀ j : ℕ, ∃ C lam ν₀ : ℝ, 0 < C ∧ 0 < lam ∧ 0 < ν₀ ∧
    ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ → ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr → ∀ T : ℝ, 0 ≤ T →
      let U := overlapField ν (trainPeriod ρ ν) tr.v T
      let b : ℝ → ℝ := fun Y => hmean 1 U Y 0
      (∀ Y : ℝ, hmean 1 U Y 1 = 0) ∧ ContDiff ℝ ∞ b ∧
      eLpNorm (iteratedDeriv j b) 2 volume ≤
          ENNReal.ofReal (C * (1 + T) ^ (-1 - (j : ℝ) / 2 + 1 / 4)) ∧
      eLpNorm (iteratedDeriv j b) ⊤ volume ≤
          ENNReal.ofReal (C * (1 + T) ^ (-1 - (j : ℝ) / 2)) ∧
      cellL2 1 (jet j (hfluct 1 U)) ≤ ENNReal.ofReal (C * Real.exp (-(lam * T))) ∧
      B0277.supNormD j (hfluct 1 U) ≤ ENNReal.ofReal (C * Real.exp (-(lam * T)))

/-- **`sct:integrated`, first two lines** (lines 314-317): the `L²` decay of the train, on one
unnormalized cell: `‖v(s)‖₂ ≤ C a(s)⁻¹` for `s ≤ s_c` and `‖v(s)‖₂ ≤ C c⁻² (s/s_c)^{-3/4}`
for `s ≥ s_c`. -/
def TrainL2Decay : Prop :=
  ∀ ρ : ℝ, 1 / 2 < ρ → ∃ C ν₀ : ℝ, 0 < C ∧ 0 < ν₀ ∧
    ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ → ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr → ∀ s : ℝ, 0 ≤ s →
      (s ≤ B0146.overlapAge ν (trainPeriod ρ ν) →
        cellL2 (trainPeriod ρ ν) (tr.v s) ≤ ENNReal.ofReal (C * (width ν s)⁻¹)) ∧
      (B0146.overlapAge ν (trainPeriod ρ ν) ≤ s →
        cellL2 (trainPeriod ρ ν) (tr.v s) ≤
          ENNReal.ofReal (C * (trainPeriod ρ ν) ^ (-2 : ℝ) *
            (s / B0146.overlapAge ν (trainPeriod ρ ν)) ^ (-(3 / 4 : ℝ))))

/-- **`sct:integrated`, third line** (lines 318-319): whenever `a(s₀) ≤ c²`,
`∫_{s₀}^∞ ∑_{j=1}^{k+1} ‖D^j v(s)‖_∞ ds ≤ C_k/(ν a(s₀)) + C_k e_c` (`s₀ = σ₀/ν`,
`a(s₀) = 1+σ₀`); `B0278.TrainStrainEstimate k Ck ν c σ₀ v` is exactly this inequality. -/
def TrainStrainIntegral : Prop :=
  ∀ ρ : ℝ, 1 / 2 < ρ → ∀ k : ℕ, ∃ Ck ν₀ : ℝ, 0 < Ck ∧ 0 < ν₀ ∧
    ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ → ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr → ∀ σ₀ : ℝ, 0 ≤ σ₀ →
      1 + σ₀ ≤ trainPeriod ρ ν ^ 2 →
        B0278.TrainStrainEstimate k Ck ν (trainPeriod ρ ν) σ₀ tr.v

/-- **`sct:integrated`, fourth line** (lines 320-322): `∫_{s₀}^∞ ‖\tilde v(s)‖₂ ds ≤
(C/ν)(1 + log(c²/a(s₀)))` whenever `a(s₀) ≤ c²`. -/
def TrainFluctuationIntegral : Prop :=
  ∀ ρ : ℝ, 1 / 2 < ρ → ∃ C ν₀ : ℝ, 0 < C ∧ 0 < ν₀ ∧
    ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ → ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr → ∀ σ₀ : ℝ, 0 ≤ σ₀ →
      1 + σ₀ ≤ trainPeriod ρ ν ^ 2 →
        ∫⁻ s in Ioi (σ₀ / ν), cellL2 (trainPeriod ρ ν) (hfluct (trainPeriod ρ ν) (tr.v s)) ≤
          ENNReal.ofReal (C / ν * (1 + Real.log (trainPeriod ρ ν ^ 2 / (1 + σ₀))))

/-- **The mean equations `sct:mean`** (lines 397-404): `S_s - ν S_{ηη} = g := \overline{v₁v₂}`,
`\bar v₁ = -S_η`, `\bar v₂ = 0` for the mean stream `S = \bar ψ`, with `S` smooth for `s > 0`. -/
def TrainMeanEquations : Prop :=
  ∀ ν c : ℝ, 0 < ν → 0 < c → ∀ tr : B0140.TrainSol ν c, IsBUCTrain tr →
    ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => meanStream tr x.1 x.2) (Ioi 0 ×ˢ univ) ∧
    ∀ s : ℝ, 0 < s → ∀ η : ℝ,
      deriv (fun r => meanStream tr r η) s -
          ν * deriv (deriv (fun e => meanStream tr s e)) η = meanStress tr s η ∧
      hmean c (fun z => tr.v s z 0) η = -deriv (fun e => meanStream tr s e) η ∧
      hmean c (fun z => tr.v s z 1) η = 0

/-! ### Lemma `sct:heat` -/

/-- **`sct:fluctuation`** (lines 439-446): for every fixed `m, ℓ, j` there are a polynomial
`P` (majorant `C(1+c+ν⁻¹)^N`) and `κ > 0` with
`‖⟨η⟩^m ∂_s^ℓ D^j (\tilde ψ, \tilde v, p)(s)‖_{2∩∞} ≤ P e^{-κ ν s/c²}` at every age `s > 0`
(the fluctuation of the stream and velocity, and the decaying-gauge pressure itself). -/
def TrainFluctuationDecay : Prop :=
  ∀ ρ : ℝ, 1 / 2 < ρ → ∀ m ℓ j : ℕ, ∃ C : ℝ, ∃ N : ℕ, ∃ κ ν₀ : ℝ, 0 < C ∧ 0 < κ ∧ 0 < ν₀ ∧
    ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ → ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr → ∀ s : ℝ, 0 < s →
      let c := trainPeriod ρ ν
      let K : ℝ≥0∞ := ENNReal.ofReal (polyP C N ν c * Real.exp (-(κ * ν * s / c ^ 2)))
      (wCellL2 c m (ageJet ℓ j (fun r z => tr.ψ r z - hmean c (tr.ψ r) z.2) s) ≤ K ∧
        wSupNorm m (ageJet ℓ j (fun r z => tr.ψ r z - hmean c (tr.ψ r) z.2) s) ≤ K) ∧
      (wCellL2 c m (ageJet ℓ j (fun r => hfluct c (tr.v r)) s) ≤ K ∧
        wSupNorm m (ageJet ℓ j (fun r => hfluct c (tr.v r)) s) ≤ K) ∧
      (wCellL2 c m (ageJet ℓ j tr.p s) ≤ K ∧ wSupNorm m (ageJet ℓ j tr.p s) ≤ K)

/-- **`sct:expansion`** (lines 447-459): the mean stream `S` is even at every age `s ≥ 0` (the
ages of the train, lines 261-288; `B0140.IsTrain` constrains `ψ` only for `s ≥ 0`) and has the heat-kernel
expansion `S = ∑_{j≤N} a_{2j} ∂_η^{2j} G_{νs} + R_N` with the stated moments finite and the
remainder bound `‖η^m ∂_η^b ∂_s^ℓ R_N(s)‖_p ≤ P s^{(m-b-2N-3)/2-ℓ+1/(2p)}` for `s ≥ 1`,
`1 ≤ p ≤ ∞`; and, with `s` replaced by `1+s` and the power `(m-b-1)/2-ℓ+1/(2p)`, the same
bound for `S` itself (all `s ≥ 0`).  The exponent `1/(2p)` is `p.toReal⁻¹/2` (it is `0` for
`p = ∞`). -/
def TrainMeanExpansion : Prop :=
  ∀ ρ : ℝ, 1 / 2 < ρ → ∀ (N m b ℓ : ℕ) (p : ℝ≥0∞), 1 ≤ p → ∃ C : ℝ, ∃ M : ℕ, ∃ ν₀ : ℝ,
    0 < C ∧ 0 < ν₀ ∧
    ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ → ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr →
      let c := trainPeriod ρ ν
      (∀ s : ℝ, 0 ≤ s → ∀ η : ℝ, meanStream tr s (-η) = meanStream tr s η) ∧
      (∀ j : ℕ, Integrable (fun η : ℝ => η ^ (2 * j) * meanStream tr 0 η) volume ∧
        ∀ k : ℕ, (∀ t : ℝ, 0 < t → Integrable (fun η : ℝ => η ^ (2 * k) * meanStress tr t η) volume) ∧
          IntegrableOn (fun t : ℝ => ∫ η : ℝ, η ^ (2 * k) * meanStress tr t η)
            (Ioi 0) volume) ∧
      (∀ s : ℝ, 1 ≤ s →
        eLpNorm (fun η : ℝ => η ^ m * iteratedDeriv b
            (fun e => iteratedDeriv ℓ (fun r => meanRemainder tr N r e) s) η) p volume ≤
          ENNReal.ofReal (polyP C M ν c *
            s ^ (((m : ℝ) - b - 2 * N - 3) / 2 - ℓ + p.toReal⁻¹ / 2))) ∧
      (∀ s : ℝ, 0 ≤ s →
        eLpNorm (fun η : ℝ => η ^ m * iteratedDeriv b
            (fun e => iteratedDeriv ℓ (fun r => meanStream tr r e) s) η) p volume ≤
          ENNReal.ofReal (polyP C M ν c *
            (1 + s) ^ (((m : ℝ) - b - 1) / 2 - ℓ + p.toReal⁻¹ / 2)))

/-- **`sct:transverse`** (lines 460-467): on each `0 < s ≤ S_*` the train fields `ψ, v, ω, p`
and their fixed derivatives have transverse tails
`P_{S_*}{e^{-b l/c} + e^{-b l²/(C₀+νS_*)}}` for `|η| ≥ C/ν + 2 + l`, `l ≥ 0`.
`P_{S_*} = polyPS C N ν c S_* = C((1+c+ν⁻¹)(1+S_*))^N` is polynomial in `c, ν⁻¹` and `1+S_*`, with
`C, N` and the smallness threshold `ν₀` fixed before `S_*` (lines 255-258: "`P_S` may also depend
polynomially on `1+S`. All the smallness conditions below are satisfied by first fixing that
collection and then decreasing `e_c`"). -/
def TrainTransverseTails : Prop :=
  ∀ ρ : ℝ, 1 / 2 < ρ → ∀ ℓ j : ℕ, ∃ b C₀ C' : ℝ, 0 < b ∧ 0 < C₀ ∧ 0 < C' ∧
    ∃ C : ℝ, ∃ N : ℕ, ∃ ν₀ : ℝ, 0 < C ∧ 0 < ν₀ ∧ ∀ S_ : ℝ, 0 ≤ S_ →
      ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ → ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr →
        ∀ l : ℝ, 0 ≤ l → ∀ s : ℝ, 0 < s → s ≤ S_ → ∀ z : Plane, C' / ν + 2 + l ≤ |z.2| →
          let c := trainPeriod ρ ν
          let K : ℝ := polyPS C N ν c S_ *
            (Real.exp (-(b * l / c)) + Real.exp (-(b * l ^ 2 / (C₀ + ν * S_))))
          ‖ageJet ℓ j tr.ψ s z‖ ≤ K ∧ ‖ageJet ℓ j tr.v s z‖ ≤ K ∧
          ‖ageJet ℓ j (fun r w => Cyl.curl (tr.v r) w) s z‖ ≤ K ∧ ‖ageJet ℓ j tr.p s z‖ ≤ K

/-- **`sct:fixed-band`** (lines 468-478): on every fixed slow-age interval `0 < s ≤ Sg/ν` (`Sg` is the source's `Σ`), for
`d = (v - V_c^p, ω - curl V_c^p, ∇(p - p_c^p))` and fixed `m, L, k`,
`∑_{ℓ≤L, j≤k} (‖⟨η⟩^m ∂_σ^ℓ D^j d‖₂ + ‖∂_σ^ℓ D^j d‖_∞) ≤ P e^{C_Σ/ν - b_Σ c²}`,
`σ = ν s`. -/
def TrainFixedBand : Prop :=
  ∀ ρ : ℝ, 1 / 2 < ρ → ∀ Sg : ℝ, 0 < Sg → ∀ m L k : ℕ, ∃ C : ℝ, ∃ N : ℕ, ∃ CS bS ν₀ : ℝ,
    0 < C ∧ 0 < bS ∧ 0 < ν₀ ∧
    ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ → ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr →
      ∀ s : ℝ, 0 < s → s ≤ Sg / ν →
        let c := trainPeriod ρ ν
        let dv : ℝ → Plane → Vec := fun r z => tr.v r z - Vc ν c r z
        let dω : ℝ → Plane → ℝ := fun r z => Cyl.curl (tr.v r) z - Cyl.curl (Vc ν c r) z
        let dp : ℝ → Plane → Vec := fun r z =>
          Train.gradS (fun w => tr.p r w - pc ν c r w) z
        ∑ ℓ ∈ Finset.range (L + 1), ∑ j ∈ Finset.range (k + 1),
          (wCellL2 c m (sigmaJet ν ℓ j dv s) + wSupNorm 0 (sigmaJet ν ℓ j dv s) +
           wCellL2 c m (sigmaJet ν ℓ j dω s) + wSupNorm 0 (sigmaJet ν ℓ j dω s) +
           wCellL2 c m (sigmaJet ν ℓ j dp s) + wSupNorm 0 (sigmaJet ν ℓ j dp s)) ≤
          ENNReal.ofReal (polyP C N ν c * Real.exp (CS / ν - bS * c ^ 2))

end UnforcedLeray.Short.PartI
