import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T09_6
import UnforcedLeray.Short.PartIIb.Tasks.DriftNvC.Approx.SCut

/-!
# Part II-b, task `PartII-b:T09/6/1`: the fixed `s`-cutoff of Laplacian graph data

Source: `the November 2 reference manuscript` lines 1639-1668, 1902-1921.
For `χ = sBump k (s)` (depends on `s` only) the chart derivation `D = vQ · ∇ = -2 ε s ∂_s` gives
`D χ = -2 ε E1`, `D² χ = 4 ε² E2` with `E1 = s χ'`, `E2 = s (s χ')'`, and
`Q_ε(χ b) = χ Q_ε b + (Dχ) b`, `Q_ε²(χ b) = χ Q_ε² b + 2 (Dχ) Q_ε b + (D²χ) b`,
`∂_η(χ b) = χ ∂_η b`.  The cut data below are exactly these.  For each fixed `k` the cut data are
graph data in a compact window (`LapCutWeak`, `LapCutInHr`, `LapCutSupport`); they are used with
`k` so large that `χ = 1` near the chart window of a test supported away from the axis
(`Sub/PartIIb_T09_6a.lean`).  The limit `k → ∞` in the graph norm (the former `LapCutTendsto`)
is false for `r > 2` (axis trace) and was retired (task `PartII-b:T09/6/redesign/org`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb
open DriftSCutHelp

/-- `s χ'(s)` for `χ = sBump k`. -/
def cutE1 (k : ℝ) (x : Coord) : ℝ := x.1 * deriv (sBump k) x.1

/-- `s (s χ')'(s)` for `χ = sBump k`. -/
def cutE2 (k : ℝ) (x : Coord) : ℝ := x.1 * deriv (fun s => s * deriv (sBump k) s) x.1

def cutB (k : ℝ) (b : CProf) : CProf := fun x => ((sBump k x.1 : ℝ) : ℂ) • b x

def cutQ (k ε : ℝ) (b Qb : CProf) : CProf := fun x =>
  ((sBump k x.1 : ℝ) : ℂ) • Qb x + ((-2 * ε * cutE1 k x : ℝ) : ℂ) • b x

def cutEb (k : ℝ) (Eb : CProf) : CProf := fun x => ((sBump k x.1 : ℝ) : ℂ) • Eb x

def cutQ2 (k ε : ℝ) (b Qb Q2b : CProf) : CProf := fun x =>
  ((sBump k x.1 : ℝ) : ℂ) • Q2b x + ((2 * (-2 * ε * cutE1 k x) : ℝ) : ℂ) • Qb x +
    ((4 * ε ^ 2 * cutE2 k x : ℝ) : ℂ) • b x

def cutE2b (k : ℝ) (E2b : CProf) : CProf := fun x => ((sBump k x.1 : ℝ) : ℂ) • E2b x

/-- **Leaf `/1`** (weak identities; first-order analogue `cut_hasWeakVec` in
`Tasks/DriftNvC/Approx/SCut.lean`; `hasWeakFO_leib` there is the scalar Leibniz rule for `vS`, here
for `vQ ε`, `dQ ε` and `vEta`). -/
def LapCutWeak : Prop :=
  ∀ (c r ε ν k : ℝ) (b Qb Eb Q2b E2b : CProf), 0 < k → 0 < c → 0 < ε → 2 < r →
    LapData c r ε ν b Qb Eb Q2b E2b →
    HasWeakVec (vQ ε) (dQ ε) (cutB k b) (cutQ k ε b Qb) ∧
    HasWeakVec vEta dZero (cutB k b) (cutEb k Eb) ∧
    HasWeakVec (vQ ε) (dQ ε) (cutQ k ε b Qb) (cutQ2 k ε b Qb Q2b) ∧
    HasWeakVec vEta dZero (cutEb k Eb) (cutE2b k E2b)

/-- **Leaf `/2`** (membership in `H_r`: `cutE1, cutE2` are bounded continuous; `√s` weights and
`lapProf` are linear in the cut data). -/
def LapCutInHr : Prop :=
  ∀ (c r ε ν k : ℝ) (b Qb Eb Q2b E2b : CProf), 0 < k → 0 < c → 0 < ε → 2 < r →
    LapData c r ε ν b Qb Eb Q2b E2b →
    InHr c r (cutB k b) ∧ InHr c r (sqrtS (cutQ k ε b Qb)) ∧ InHr c r (sqrtS (cutEb k Eb)) ∧
    InHr c r (lapProf ν ε (cutB k b) (cutQ2 k ε b Qb Q2b) (cutE2b k E2b))

/-- **Leaf `/4`** (compact `s`-support in `[exp(-2k), exp(2k)]`: `sBump_zero_of_lt/gt` and
`sBump_deriv_zero_of_lt/gt`, also for `(s χ')'` since `s χ'` vanishes on an open set). -/
def LapCutSupport : Prop :=
  ∀ (k ε : ℝ) (b Qb Eb Q2b E2b : CProf), 0 < k →
    SCut (Real.exp (-2 * k)) (Real.exp (2 * k)) (cutB k b) ∧
    SCut (Real.exp (-2 * k)) (Real.exp (2 * k)) (cutQ k ε b Qb) ∧
    SCut (Real.exp (-2 * k)) (Real.exp (2 * k)) (cutEb k Eb) ∧
    SCut (Real.exp (-2 * k)) (Real.exp (2 * k)) (cutQ2 k ε b Qb Q2b) ∧
    SCut (Real.exp (-2 * k)) (Real.exp (2 * k)) (cutE2b k E2b)

end UnforcedLeray.Short.IIb
