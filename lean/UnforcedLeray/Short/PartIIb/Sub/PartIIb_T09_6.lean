import UnforcedLeray.Short.PartIIb.Sub.T09
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T08_2

/-!
# Part II-b, task `PartII-b:T09/6` (Laplacian graph data): window classes and approximation stages

Source of record: `the November 2 reference manuscript`, lines 1639-1668, 1902-1921.
Graph data `LapData` supported in a compact `s`-window (`LapDataS`) and, in addition, in a bounded
`η`-range (`LapDataSE`), and the two approximation stages that are true inside the window:

1. `LapEtaCutApprox`: cut off in `η` (multiply by `χ(η/L)`);
2. `LapMollApprox`: mollify in `(log s, q, η)`.

Closeness is measured by `b` and `lapProf ν ε b Q2b E2b` in `H_r` (`LapClose`).  They are used
with a *fixed* `s`-cutoff (`Sub/PartIIb_T09_6_1.lean`) for the identity against phase tests
supported away from the axis (`LapAwayAxis`, `Sub/PartIIb_T09_6a.lean`).  A global `s`-cutoff
stage (density of nice profiles in all of `LapData`) is false for `r > 2`: the axis trace of
`∇(N_v b)` is continuous for the graph norm and vanishes on nice profiles; it was retired with
the former leaf `LapApprox` (task `PartII-b:T09/6/redesign/org`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-- Graph-norm `δ`-closeness of `(b', lapProf b')` to `(b, lapProf b)` in `H_r`. -/
def LapClose (c r ε ν : ℝ) (b Q2b E2b b' Q2b' E2b' : CProf) (δ : ℝ) : Prop :=
  DriftClose c r b (lapProf ν ε b Q2b E2b) b' (lapProf ν ε b' Q2b' E2b') δ

/-- Laplacian graph data supported in a compact `s`-window inside `s > 0`. -/
def LapDataS (c r ε ν : ℝ) (b Qb Eb Q2b E2b : CProf) : Prop :=
  LapData c r ε ν b Qb Eb Q2b E2b ∧ ∃ s₀ s₁ : ℝ, 0 < s₀ ∧ SCut s₀ s₁ b ∧ SCut s₀ s₁ Qb ∧
    SCut s₀ s₁ Eb ∧ SCut s₀ s₁ Q2b ∧ SCut s₀ s₁ E2b

/-- Laplacian graph data supported in a compact `s`-window and a bounded `η`-range. -/
def LapDataSE (c r ε ν : ℝ) (b Qb Eb Q2b E2b : CProf) : Prop :=
  LapDataS c r ε ν b Qb Eb Q2b E2b ∧ ∃ L : ℝ, EtaCut L b ∧ EtaCut L Qb ∧ EtaCut L Eb ∧
    EtaCut L Q2b ∧ EtaCut L E2b

/-- **Stage `η`-cutoff** (SP 1912-1916): multiply by `χ(η/L)`; `∂_η χ` and `Q_ε χ = -εη ∂_η χ`
are bounded and supported in `L ≤ |η| ≤ 2L`; commutator terms tend to `0` as `L → ∞`. -/
def LapEtaCutApprox : Prop :=
  ∀ (c r ε ν : ℝ) (b Qb Eb Q2b E2b : CProf), 0 < c → 0 < ε → 2 < r →
    LapDataS c r ε ν b Qb Eb Q2b E2b → ∀ δ : ℝ, 0 < δ →
    ∃ b' Qb' Eb' Q2b' E2b' : CProf, LapDataSE c r ε ν b' Qb' Eb' Q2b' E2b' ∧
      LapClose c r ε ν b Q2b E2b b' Q2b' E2b' δ

/-- **Stage mollification** (SP 1912-1916): convolve in `(log s, q, η)` with a product
mollifier; on the compact window `Q_ε` has coefficients `-2ε`, `1`, `-εη` in `(log s, q, η)`, so it
commutes with the convolution up to a zeroth-order bounded commutator, as do `∂_η` and the factor
`s` inside `lapProf`; periodicity in `q` is preserved. -/
def LapMollApprox : Prop :=
  ∀ (c r ε ν : ℝ) (b Qb Eb Q2b E2b : CProf), 0 < c → 0 < ε → 2 < r →
    LapDataSE c r ε ν b Qb Eb Q2b E2b → ∀ δ : ℝ, 0 < δ →
    ∃ b' Qb' Eb' Q2b' E2b' : CProf, NiceProf c b' ∧ LapData c r ε ν b' Qb' Eb' Q2b' E2b' ∧
      LapClose c r ε ν b Q2b E2b b' Q2b' E2b' δ

end UnforcedLeray.Short.IIb
