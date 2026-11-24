import UnforcedLeray.Short.PartI.StatementsTrain
import UnforcedLeray.Short.PartI.Sub.T08Statement
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# Part I, task `PartI:T09`: `TrainComparison` from the differentiated energy inequality

Source of record: `the November 2 reference manuscript`,
lines 337-355 (the end of the proof of Lemma `sct:train`):

> Time-ordered Gronwall yields `E_N²(a) ≤ C_N ν⁻² ∫_1^a r^{-5} e^{-b_N c²/r + C_N/(ν r)} dr ≤
> C_N ν⁻² a^{-4} e^{-b'_N c²/a}`, because `e_c` is small. In the last integral use `u = c²/r`.
> The cylinder interpolation inequality ... proves the second estimate in (`sct:comparison`),
> since `a^{1/4} c^{-1/2} ≤ 1`. Consequently `‖∇e‖_∞ ≤ C e_c (c²/a) e^{-b c²/a} a^{-2} ≤ a^{-2}/2`.

(and "choose an integer `N ≥ 3` at least two above the required supremum order", line 341).
The continuity (bootstrap) argument closes `‖∇e‖_∞ ≤ a^{-2}` up to `a = c²` from the smooth datum
`e(0) = 0`.

## Decomposition

`train_comparison_of` proves `TrainComparison` from `DifferentiatedEnergyInequality` (`PartI:T08`,
proved), `TrainErrBasic` (proved leaf of `PartI:T08`) and the following leaves, each a true
source fact:

1. `ComparisonGronwall`: the time-ordered Gronwall bound with exponent absorption (pure analysis).
2. `BootstrapContinuity`: the abstract continuity argument (pure analysis).
3. `JetL2Bridge`, `JetSupBridge`: Hilbert jet energies versus the operator-norm jets / sup norms
   (`PartI:T07`, `CylJetWord`, `CylSupInterp`).
4. `TrainErrInitial`, `TrainErrGradSup`: the train facts `e(0) = 0`, continuity of `E_N` at `0`,
   finiteness and continuity of `‖∇e(s)‖_∞`.
5. `TrainPeriodAsymptotics`: `νc² → ∞` for `c = ν^{-ρ}`, `ρ > 1/2`.
6. `JetArithmetic`, `GradClosing`: the exponent arithmetic of the interpolation and of the
   closure `C e_c (c²/a) e^{-bc²/a} ≤ 1/2`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec Vc width)

/-- `‖∇e(s)‖_∞`: the supremum of all first partials of all components of the comparison error. -/
def gradErrSup {ν c : ℝ} (tr : B0140.TrainSol ν c) (s : ℝ) : ℝ :=
  sSup {x : ℝ | ∃ (β : Bool) (k : Fin 2) (z : Plane), x = |wordComp [β] (trainErr tr s) k z|}

/-- The right side of the cylinder interpolation inequality (line 366-374), in terms of
`J_i = ‖D^i f‖₂²`: `C ((√J_j √J_{j+2})^{1/2} + c^{-1/2} (√J_j √J_{j+1})^{1/2})`. -/
def supRhs (C c Jj Jj1 Jj2 : ℝ) : ℝ :=
  C * ((Real.sqrt Jj * Real.sqrt Jj2) ^ (1 / 2 : ℝ) +
    c ^ (-(1 / 2 : ℝ)) * (Real.sqrt Jj * Real.sqrt Jj1) ^ (1 / 2 : ℝ))

/-- **Leaf 1: time-ordered Gronwall with exponent absorption** (lines 346-349). If a continuous
`E` on `[0,S]` (`a(S) ≤ c²`) with `E(0) = 0` satisfies, in slow time, `ν⁻¹E' ≤ C/(νa²) E +
C/(ν²a⁵) e^{-bc²/a}` on `(0,S)`, and `νc² ≥ R` (`e_c` small), then
`E ≤ K ν⁻² a⁻⁴ e^{-b'c²/a}` on `[0,S]`. (Integrating factor `exp(C/ν (1/r - 1/a))`, absorb
`C/(νr) ≤ (b/2)c²/r` for `νc² ≥ 2C/b`, substitute `u = c²/r`; `b' = b/2`.) -/
def ComparisonGronwall : Prop :=
  ∀ C b : ℝ, 0 < C → 0 < b → ∃ K b' R : ℝ, 0 < K ∧ 0 < b' ∧ 0 < R ∧
    ∀ ν c S : ℝ, 0 < ν → 1 ≤ c → R ≤ ν * c ^ 2 → 0 ≤ S → width ν S ≤ c ^ 2 →
    ∀ E : ℝ → ℝ, ContinuousOn E (Icc 0 S) → E 0 = 0 →
      (∀ s ∈ Ioo 0 S, ∃ D : ℝ, HasDerivAt E D s ∧
        ν⁻¹ * D ≤ C / (ν * width ν s ^ 2) * E s +
          C / (ν ^ 2 * width ν s ^ 5) * Real.exp (-(b * c ^ 2 / width ν s))) →
      ∀ s ∈ Icc 0 S, E s ≤ K / (ν ^ 2 * width ν s ^ 4) * Real.exp (-(b' * c ^ 2 / width ν s))

/-- **Leaf 2: the continuity (bootstrap) argument** (line 355: "Consequently ... `≤ a^{-2}/2`",
closed by continuity from the datum). If `g, h` are continuous on `[0,S]`, `h > 0`, `g(0) ≤ h(0)`, and
`g ≤ h` on `[0,s]` implies `g(s) ≤ h(s)/2`, then `g ≤ h/2` on `[0,S]`. -/
def BootstrapContinuity : Prop :=
  ∀ S : ℝ, 0 ≤ S → ∀ g h : ℝ → ℝ, ContinuousOn g (Icc 0 S) → ContinuousOn h (Icc 0 S) →
    (∀ s ∈ Icc 0 S, 0 < h s) → g 0 ≤ h 0 →
    (∀ s ∈ Icc 0 S, (∀ r ∈ Icc 0 s, g r ≤ h r) → g s ≤ h s / 2) →
    ∀ s ∈ Icc 0 S, g s ≤ h s / 2

/-- **Leaf 3a: `L²` bridge** (`CylJetWord`, `Sub/T07.lean`): the operator-norm jet is bounded in
cell `L²` by the Hilbert jet energy. -/
def JetL2Bridge : Prop :=
  ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ c : ℝ, 1 ≤ c → ∀ f : Plane → Vec, CellSmoothL2 c f →
    Train.cellL2 c (Train.jet j f) ≤ ENNReal.ofReal (C * Real.sqrt (jetEnergy c j f))

/-- **Leaf 3b: sup bridge** (`cylinder_interpolation_uniform`, conjunct 1, lines 366-374, applied
to each `∂_w f_k`, `|w| = j`, with `CylJetWord`): the coordinate derivatives of order `j` and
`‖D^j f‖_∞` are bounded by `supRhs`. -/
def JetSupBridge : Prop :=
  ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ c : ℝ, 1 ≤ c → ∀ f : Plane → Vec, CellSmoothL2 c f →
    (∀ w : List Bool, w.length = j → ∀ (k : Fin 2) (z : Plane),
      |wordComp w f k z| ≤
        supRhs C c (jetEnergy c j f) (jetEnergy c (j + 1) f) (jetEnergy c (j + 2) f)) ∧
    B0277.supNormD j f ≤
      ENNReal.ofReal (supRhs C c (jetEnergy c j f) (jetEnergy c (j + 1) f) (jetEnergy c (j + 2) f))

/-- **Leaf 4a: the datum and the start of the energy** (lines 261-288, 294: `v(0)` is the
periodized Gaussian `= V_c^p(0)`): `e(0) = 0`, so `e(0)` is smooth `L²` with all jet energies
`0`, and `E_N` is continuous at `s = 0` from the right. -/
def TrainErrInitial : Prop :=
  ∀ ν c : ℝ, 0 < ν → 1 ≤ c → ∀ tr : B0140.TrainSol ν c, IsBUCTrain tr →
    (∀ j : ℕ, jetEnergy c j (trainErr tr 0) = 0) ∧
    (∀ (N : ℕ) (δ : ℝ), ContinuousWithinAt
      (fun s => weightedEnergy c δ (width ν s) N (trainErr tr s)) (Ici 0) 0) ∧
    CellSmoothL2 c (trainErr tr 0)

/-- **Leaf 4b: the gradient of the error** (BUC class, lines 270-288; line 355): `∇e(s)` is
bounded for every `s ≥ 0`, `‖∇e(0)‖_∞ = 0`, and `s ↦ ‖∇e(s)‖_∞` is continuous on `[0,∞)`. -/
def TrainErrGradSup : Prop :=
  ∀ ν c : ℝ, 0 < ν → 1 ≤ c → ∀ tr : B0140.TrainSol ν c, IsBUCTrain tr →
    (∀ s : ℝ, 0 ≤ s →
      BddAbove {x : ℝ | ∃ (β : Bool) (k : Fin 2) (z : Plane),
        x = |wordComp [β] (trainErr tr s) k z|}) ∧
    gradErrSup tr 0 = 0 ∧ ContinuousOn (gradErrSup tr) (Ici 0)

/-- **Leaf 5: the period** (line 253: `c = ν^{-ρ}`, `ρ > 1/2`, `e_c = (νc²)⁻¹ → 0`): for every
`R` there is `ν₁ ∈ (0,1]` with `c ≥ 1` and `νc² ≥ R` for all `0 < ν ≤ ν₁`. -/
def TrainPeriodAsymptotics : Prop :=
  ∀ ρ : ℝ, 1 / 2 < ρ → ∀ R : ℝ, 0 < R → ∃ ν₁ : ℝ, 0 < ν₁ ∧ ν₁ ≤ 1 ∧
    ∀ ν : ℝ, 0 < ν → ν ≤ ν₁ → 1 ≤ trainPeriod ρ ν ∧ R ≤ ν * trainPeriod ρ ν ^ 2

/-- **Leaf 6a: exponent arithmetic of the interpolation** (lines 349-355). With `δ = 1/(4N)`,
`N ≥ j+2`, `N ≥ 3`: if `(δa)^i J_i ≤ E` for `i ≤ N` and `E ≤ K ν⁻² a⁻⁴ e^{-b'c²/a}`, `1 ≤ a ≤ c²`,
then `√J_j ≤ C ν⁻¹ a^{-(2+j/2)} e^{-(b'/2)c²/a}` and the interpolation expression is at most
`C ν⁻¹ a^{-(5+j)/2} e^{-(b'/2)c²/a}` (uses `a^{1/4} c^{-1/2} ≤ 1`). -/
def JetArithmetic : Prop :=
  ∀ (N j : ℕ) (K b' : ℝ), 3 ≤ N → j + 2 ≤ N → 0 < K → 0 < b' → ∃ Cj : ℝ, 0 < Cj ∧
    ∀ ν c a E : ℝ, 0 < ν → 1 ≤ c → 1 ≤ a → a ≤ c ^ 2 → ∀ J : ℕ → ℝ, (∀ i, 0 ≤ J i) →
      E ≤ K / (ν ^ 2 * a ^ 4) * Real.exp (-(b' * c ^ 2 / a)) →
      (∀ i ≤ N, (1 / (4 * (N : ℝ)) * a) ^ i * J i ≤ E) →
      Real.sqrt (J j) ≤
          Cj * ν⁻¹ * a ^ (-(2 + (j : ℝ) / 2)) * Real.exp (-(b' / 2 * c ^ 2 / a)) ∧
      ((Real.sqrt (J j) * Real.sqrt (J (j + 2))) ^ (1 / 2 : ℝ) +
          c ^ (-(1 / 2 : ℝ)) * (Real.sqrt (J j) * Real.sqrt (J (j + 1))) ^ (1 / 2 : ℝ)) ≤
        Cj * ν⁻¹ * a ^ (-((5 + (j : ℝ)) / 2)) * Real.exp (-(b' / 2 * c ^ 2 / a))

/-- **Leaf 6b: closing the bootstrap** (line 355): `C ν⁻¹ a⁻³ e^{-βc²/a} ≤ a⁻²/2` when
`νc² ≥ R` and `1 ≤ a ≤ c²` (`a⁻¹ = (c²/a)/c²` and `u e^{-βu} ≤ 1/(eβ)`). -/
def GradClosing : Prop :=
  ∀ C β : ℝ, 0 < C → 0 < β → ∃ R : ℝ, 0 < R ∧ ∀ ν c a : ℝ, 0 < ν → 1 ≤ a → a ≤ c ^ 2 →
    R ≤ ν * c ^ 2 →
      C * ν⁻¹ * a ^ (-(3 : ℝ)) * Real.exp (-(β * c ^ 2 / a)) ≤ (a ^ 2)⁻¹ / 2

end UnforcedLeray.Short.PartI
