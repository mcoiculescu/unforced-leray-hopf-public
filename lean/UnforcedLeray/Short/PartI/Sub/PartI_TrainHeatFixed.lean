import UnforcedLeray.Short.PartI.StatementsTrain
import UnforcedLeray.Short.PartI.Sub.T01

/-!
# Part I: the heat description of `sct:heat` at fixed parameters (statements)

Source of record: `the November 2 reference manuscript` (SP).

The quantitative statements `TrainFluctuationDecay` (SP 439-446) and `TrainMeanExpansion`
(SP 447-459) of `Short/PartI/StatementsTrain.lean` have the threshold `ν₀` depending on the orders
(`∀ m ℓ j, ∃ ν₀` / `∀ N m b ℓ p, ∃ ν₀`), as in SP 247-258 (constants and smallness conditions are
fixed after the finite collection of orders).  The smoothness of the train through the axis
(PartII-a:R06 `RingAxisSmooth` for all `ρ > 1/2`, PartII-b:R1/6, PartII-b:G1/4, and
PartII-b:G4/4/1/1/2/1 `RawParityForm` through `TrainHeatExpansion`,
`Short/PartII-b/Sub/PartII-b_G4_4_1_1_2_org.lean`) needs *all* orders `C^∞` at the *same* train, so
it needs the fixed-parameter all-order form: SP 427-435: "For smoothness statements at fixed
parameters there is no restriction to this quantitative derivative budget. The resulting integrable
strain and the tame higher-order inequality `d‖U‖_{H^k}/dT ≤ C_k e_c ‖∇U‖_∞ ‖U‖_{H^k}` propagate
every higher norm from its finite smooth overlap datum. All higher-order versions of the argument
therefore hold at fixed parameters, without requiring a new smallness condition for each order."

So: for `ρ > 1/2` there is ONE `ν₀` (fixed by the base order, SP 255-258 "first fixing that collection
and then decreasing `e_c`"), and for every train with `ν ≤ ν₀` every order has finite constants
(depending on `ν, c`, the train and the order).  Everything below is stated in this form.

Tree of the leaves (each a `Prop` below; the pool tasks prove them; `trainHeatFixed_of` assembles):

* `TrainStreamSmooth` (existing, `Sub/T01.lean`, task PartI:T01/1): the stream of a BUC train is
  jointly `C^∞` for `s > 0` (SP 261-288).
* `TrainJetsBoundedFixed` (A1, SP 427-435): every mixed age/spatial jet of `v` is bounded on `s ≥ 0`.
* `TrainFluctAgeJetFixed` (A2, SP 439-446 with 516-526, at fixed parameters): every mixed jet of
  `ψ̃ = ψ − \bar ψ` is `≤ C e^{-κ s}`.
* `JointFromAgeJets` (A3, generic calculus): the full `i`-th derivative in `(s, q, η)` of a function
  that is `C^∞` for `s > 0` is bounded by the mixed jets `∂_s^ℓ D^{i-ℓ}`.
* `TrainFluctFixed` (A): the joint-derivative form of A2, from A2 + A3 + `TrainStreamSmooth` +
  `TrainMeanEquations`.
* `TrainMeanMomentsFixed` (B0, SP 447-459 with 527-551): evenness of `S` and finiteness of the moments
  of `S(0)` and `g` (fixed parameters).
* `TrainMeanRemMixedFixed` (B1, SP 455-458 at `m = 0`, `p = ∞`, fixed parameters): the mixed
  `(s, η)` derivatives of `R_N` are `≤ C s^{(-b-2N-3)/2-ℓ}`.
* `JointFromMixed1D` (B2, generic calculus): the full `i`-th derivative in `(s, η)` from the mixed ones.
* `TrainMeanRemFixed` (B): the joint-derivative form of B1, from B1 + B2 + `TrainMeanEquations` +
  `HeatTermSmooth` (`Short/PartII-b/Sub/PartII-b_G4_4_1_1_2_org.lean`; the heat kernel is smooth for
  `s > 0`).
* `TrainHeatFixed` = A and B with one `ν₀`; `trainHeatFixed_of`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Real
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)

/-- **A1: all mixed jets of the velocity are bounded, at fixed parameters** (SP 427-435: "For
smoothness statements at fixed parameters there is no restriction to this quantitative derivative
budget. The resulting integrable strain and the tame higher-order inequality
`d‖U‖_{H^k}/dT ≤ C_k e_c ‖∇U‖_∞ ‖U‖_{H^k}` propagate every higher norm from its finite smooth
overlap datum"; the base order fixes `ν₀`).  For `ρ > 1/2` there is `ν₀` such that for every BUC
train with `ν ≤ ν₀` and all `ℓ, j` there is `M` with `‖∂_s^ℓ D^j v(s, z)‖ ≤ M` for all `s ≥ 0`,
`z`. (`ageJet` at `s = 0` is two-sided in the age; use `s > 0`.) -/
def TrainJetsBoundedFixed : Prop :=
  ∀ ρ : ℝ, 1 / 2 < ρ → ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
    ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr → ∀ ℓ j : ℕ, ∃ M : ℝ,
      ∀ s : ℝ, 0 < s → ∀ z : Plane, ‖ageJet ℓ j tr.v s z‖ ≤ M

/-- **A2: exponential decay of every mixed jet of the stream fluctuation, at fixed parameters**
(`sct:fluctuation`, SP 439-446, proof SP 516-526 — interpolate a doubled polynomial weight with the
unweighted exponential fluctuation bounds, for `s ≥ s_c` and the pre-overlap bounds for `s ≤ s_c`;
age derivatives by finite induction — run at fixed parameters as SP 429-435).  With `ν₀` fixed
before the orders: for every train with `ν ≤ ν₀` and all `ℓ, j` there are `C` and `κ > 0` with
`‖∂_s^ℓ D^j (ψ − \bar ψ)(s, z)‖ ≤ C e^{-κ s}` for `s > 0`. (At fixed `ν, c` the source's
`e^{-κνs/c²}` is `e^{-κ' s}`.) -/
def TrainFluctAgeJetFixed : Prop :=
  ∀ ρ : ℝ, 1 / 2 < ρ → ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
    ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr → ∀ ℓ j : ℕ, ∃ C κ : ℝ, 0 < κ ∧
      ∀ s : ℝ, 0 < s → ∀ z : Plane,
        ‖ageJet ℓ j (fun r w => tr.ψ r w - hmean (trainPeriod ρ ν) (tr.ψ r) w.2) s z‖ ≤
          C * Real.exp (-(κ * s))

/-- **A3: the full derivative from the mixed jets** (generic calculus; the full `i`-th derivative
of `(s, z) ↦ F s z` is the symmetric sum of the mixed derivatives `∂_s^ℓ D^{i-ℓ}`).  For every
`i` there is `K` such that for every `F` jointly `C^∞` on `s > 0`, at every `y` with `y.1 > 0`,
`‖D^i (s, z) ↦ F s z (y)‖ ≤ K ∑_{ℓ ≤ i} ‖ageJet ℓ (i-ℓ) F y.1 y.2‖`. -/
def JointFromAgeJets : Prop :=
  ∀ i : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ F : ℝ → Plane → ℝ,
    ContDiffOn ℝ ∞ (fun x : ℝ × Plane => F x.1 x.2) (Ioi 0 ×ˢ univ) →
    ∀ y : ℝ × Plane, 0 < y.1 →
      ‖iteratedFDeriv ℝ i (fun x : ℝ × Plane => F x.1 x.2) y‖ ≤
        K * ∑ ℓ ∈ Finset.range (i + 1), ‖ageJet ℓ (i - ℓ) F y.1 y.2‖

/-- **A: the stream fluctuation in the joint derivative form, at fixed parameters** (the statement
of `sct:fluctuation` for `ψ̃`, SP 440-445, with `D^i` the full derivative in `(s, q, η)`): for
`ρ > 1/2` there is `ν₀` such that for every BUC train with `ν ≤ ν₀` and every `i` there are `C`,
`κ > 0` with `‖D^i(ψ − \bar ψ)(s, q, η)‖ ≤ C e^{-κ s}` for `s ≥ 1`. -/
def TrainFluctFixed : Prop :=
  ∀ ρ : ℝ, 1 / 2 < ρ → ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
    ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr → ∀ i : ℕ, ∃ C κ : ℝ, 0 < κ ∧
      ∀ y : ℝ × Plane, 1 ≤ y.1 →
        ‖iteratedFDeriv ℝ i
            (fun x : ℝ × Plane => tr.ψ x.1 x.2 - meanStream tr x.1 x.2.2) y‖ ≤
          C * Real.exp (-(κ * y.1))

/-- **B0: evenness and moments of the mean stream, at fixed parameters** (the first two conjuncts of
`sct:expansion`, SP 447-459, proof SP 527-551, at fixed parameters as SP 429-435): `S` is even at
every age `s ≥ 0`, and all moments of `S(0)` and of the mean stress `g` are finite and integrable
in time. -/
def TrainMeanMomentsFixed : Prop :=
  ∀ ρ : ℝ, 1 / 2 < ρ → ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
    ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr →
      (∀ s : ℝ, 0 ≤ s → ∀ η : ℝ, meanStream tr s (-η) = meanStream tr s η) ∧
      (∀ j : ℕ, Integrable (fun η : ℝ => η ^ (2 * j) * meanStream tr 0 η) volume ∧
        ∀ k : ℕ, (∀ t : ℝ, 0 < t →
              Integrable (fun η : ℝ => η ^ (2 * k) * meanStress tr t η) volume) ∧
          IntegrableOn (fun t : ℝ => ∫ η : ℝ, η ^ (2 * k) * meanStress tr t η) (Ioi 0) volume)

/-- **B1: the remainder of the mean stream expansion, at fixed parameters, `m = 0`, `p = ∞`**
(`sct:expansion`, SP 455-458: `‖∂_η^b ∂_s^ℓ R_N(s)‖_∞ ≤ P s^{(-b-2N-3)/2-ℓ}`, `s ≥ 1`; proof
SP 527-551 — Taylor expansion of `G_{νs}` through order `2N+1`, evenness, the identity
`∂_s G = ν ∂_η² G`, integral remainders by the next even derivative and a fixed higher moment — at
fixed parameters as SP 429-435).  With `ν₀` fixed before `N, b, ℓ`. -/
def TrainMeanRemMixedFixed : Prop :=
  ∀ ρ : ℝ, 1 / 2 < ρ → ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
    ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr → ∀ N b ℓ : ℕ, ∃ C : ℝ,
      ∀ s : ℝ, 1 ≤ s → ∀ η : ℝ,
        ‖iteratedDeriv b (fun e => iteratedDeriv ℓ (fun r => meanRemainder tr N r e) s) η‖ ≤
          C * s ^ (((-(b : ℝ)) - 2 * N - 3) / 2 - ℓ)

/-- **B2: the full derivative in `(s, η)` from the mixed ones** (generic calculus, as
`JointFromAgeJets`).  For every `i` there is `K` such that for every `f : ℝ × ℝ → ℝ` that is `C^∞`
on `s > 0`, at every `y` with `y.1 > 0`,
`‖D^i f(y)‖ ≤ K ∑_{ℓ ≤ i} |∂_η^{i-ℓ} ∂_s^ℓ f(y)|` (`∂_s^ℓ` first, as in `TrainMeanRemMixedFixed`). -/
def JointFromMixed1D : Prop :=
  ∀ i : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ f : ℝ → ℝ → ℝ,
    ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => f x.1 x.2) (Ioi 0 ×ˢ univ) →
    ∀ y : ℝ × ℝ, 0 < y.1 →
      ‖iteratedFDeriv ℝ i (fun x : ℝ × ℝ => f x.1 x.2) y‖ ≤
        K * ∑ ℓ ∈ Finset.range (i + 1),
          ‖iteratedDeriv (i - ℓ) (fun e => iteratedDeriv ℓ (fun r => f r e) y.1) y.2‖

/-- **B: the mean remainder in the joint derivative form, at fixed parameters**: for `ρ > 1/2`
there is `ν₀` such that for every BUC train with `ν ≤ ν₀` and all `N, i` there is `C` with
`‖D^i_{(s,η)} R_N(s, η)‖ ≤ C s^{-N-3/2}` for `s ≥ 1` (`R_N = meanRemainder`; the total order `i`
is `b + ℓ`, and `s^{(-b-2N-3)/2-ℓ} ≤ s^{-N-3/2}` for `s ≥ 1`). -/
def TrainMeanRemFixed : Prop :=
  ∀ ρ : ℝ, 1 / 2 < ρ → ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
    ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr → ∀ N i : ℕ, ∃ C : ℝ,
      ∀ y : ℝ × ℝ, 1 ≤ y.1 →
        ‖iteratedFDeriv ℝ i (fun x : ℝ × ℝ => meanRemainder tr N x.1 x.2) y‖ ≤
          C * y.1 ^ (-(N : ℝ) - 3 / 2)

/-- **The all-order heat description of the train at fixed parameters** (`sct:heat`, SP 438-459,
at fixed parameters as SP 429-435): one `ν₀` for `ρ > 1/2`, and for every BUC train with
`ν ≤ ν₀` and all orders the fluctuation `ψ̃` decays like `e^{-κ s}` and the mean remainder `R_N`
like `s^{-N-3/2}`, in the full derivatives in the variables of the train.  This is what
PartII-b:G4/4/1/1/2/1/1 (`TrainHeatExpansion`), and through it PartII-a:R06 (`RingAxisSmooth`, all
`ρ > 1/2`), PartII-b:R1/6 and PartII-b:G1/4 (`C^∞` through the axis) need. -/
def TrainHeatFixed : Prop :=
  ∀ ρ : ℝ, 1 / 2 < ρ → ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
    ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr →
      (∀ i : ℕ, ∃ C κ : ℝ, 0 < κ ∧ ∀ y : ℝ × Plane, 1 ≤ y.1 →
        ‖iteratedFDeriv ℝ i
            (fun x : ℝ × Plane => tr.ψ x.1 x.2 - meanStream tr x.1 x.2.2) y‖ ≤
          C * Real.exp (-(κ * y.1))) ∧
      (∀ N i : ℕ, ∃ C : ℝ, ∀ y : ℝ × ℝ, 1 ≤ y.1 →
        ‖iteratedFDeriv ℝ i (fun x : ℝ × ℝ => meanRemainder tr N x.1 x.2) y‖ ≤
          C * y.1 ^ (-(N : ℝ) - 3 / 2))

/-- **Assembly of `TrainHeatFixed`**: one threshold, the minimum of the two. -/
theorem trainHeatFixed_of (hA : TrainFluctFixed) (hB : TrainMeanRemFixed) : TrainHeatFixed := by
  intro ρ hρ
  obtain ⟨νA, hνA, hA'⟩ := hA ρ hρ
  obtain ⟨νB, hνB, hB'⟩ := hB ρ hρ
  refine ⟨min νA νB, lt_min hνA hνB, fun ν hν hle tr htr => ?_⟩
  exact ⟨hA' ν hν (hle.trans (min_le_left _ _)) tr htr,
    hB' ν hν (hle.trans (min_le_right _ _)) tr htr⟩

end UnforcedLeray.Short.PartI
