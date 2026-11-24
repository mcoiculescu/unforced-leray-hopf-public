import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Fubini.Defs
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Hardy-Littlewood-Sobolev `L² → L⁶` for the Biot-Savart kernel: the route

Source `the November 2 reference manuscript` (stream potential of the solenoidal
cutoff, `L² * |w|⁻² → L⁶`; the Biot-Savart kernel has `|K(w)| = 1/(4π|w|²)`).
Mathlib has no Hardy-Littlewood maximal function, so we follow Hedberg's route, with all scalar
statements in `ℝ≥0∞` (no integrability junk values):

* `hlMax G y = sup_{r>0} (1/|B(y,r)|) ∫_{B(y,r)} G` (uncentred-free, centred maximal function);
* `rieszT G y = ∫ G(z) k(y-z) dz`, `k(w) = (4π)⁻¹ |w|⁻²`;
* near/far split of `rieszT` at radius `R` (near: `≤ R · M G(y)`; far: Cauchy-Schwarz);
* optimising `R` gives `T G ≤ 2 (M G)^{1/3} ‖G‖₂^{2/3}`;
* `M` is of weak type `(1,1)` (Vitali `5r`-covering) hence strong `(2,2)` (layer cake);
* hence `∫ (T G)⁶ ≤ C (∫ G²)³`, and the vector statement follows from `‖a × b‖ ≤ 2‖a‖‖b‖`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- Scalar Biot-Savart kernel modulus `k(w) = (4π)⁻¹ ‖w‖⁻²` (`= ‖bsKernel w‖`), in `ℝ≥0∞`. -/
def bsK2 (w : Space) : ℝ≥0∞ := ENNReal.ofReal ((4 * Real.pi)⁻¹ * (‖w‖ ^ 2)⁻¹)

/-- Hardy-Littlewood (centred, open-ball) maximal function of `G : ℝ³ → ℝ≥0∞`. -/
def hlMax (G : Space → ℝ≥0∞) (y : Space) : ℝ≥0∞ :=
  ⨆ r : {r : ℝ // 0 < r}, (volume (ball y r.1))⁻¹ * ∫⁻ z in ball y r.1, G z

/-- The positive Biot-Savart potential `T G (y) = ∫ G(z) k(y-z) dz`. -/
def rieszT (G : Space → ℝ≥0∞) (y : Space) : ℝ≥0∞ := ∫⁻ z, G z * bsK2 (y - z)

/-- `‖bsKernel w‖ = k(w)` as extended reals (from `BSKernelNorm`, source: `|K| = 1/(4π|w|²)`). -/
def BsK2Norm : Prop := ∀ w : Space, ENNReal.ofReal ‖bsKernel w‖ = bsK2 w

/-- Measurability of the maximal function (it is lower semicontinuous). -/
def HLMaxMeasurable : Prop := ∀ G : Space → ℝ≥0∞, Measurable G → Measurable (hlMax G)

/-- Weak type `(1,1)` of the maximal function: Vitali `5r`-covering, `|B(x,5r)| = 125 |B(x,r)|`
(`volume (ball x (5 r)) = 125 * volume (ball x r)` in `ℝ³`). -/
def HLMaxWeakL1 : Prop :=
  ∀ G : Space → ℝ≥0∞, Measurable G → ∀ t : ℝ≥0∞, 0 < t → t ≠ ⊤ →
    t * volume {y | t < hlMax G y} ≤ 125 * ∫⁻ z, G z

/-- Strong type `(2,2)` of the maximal function: Marcinkiewicz by the layer cake formula,
`∫ M² = ∫ 2t |{M>t}| dt = 8 ∫ λ |{M>2λ}| dλ ≤ 8·125 ∫ G ∫_{G>λ} ... = 1000 ∫ G²`. -/
def HLMaxL2 : Prop :=
  ∀ G : Space → ℝ≥0∞, Measurable G → ∫⁻ y, (hlMax G y) ^ 2 ≤ 1000 * ∫⁻ z, (G z) ^ 2

/-- Near part: `∫_{|w|<R} G(y-w) (4π)⁻¹|w|⁻² dw ≤ R · M G(y)`.  Proof: for `|w|<R`,
`|w|⁻² = R⁻² + ∫_{|w|}^R 2 s⁻³ ds`, Tonelli, `∫_{B_s} G(y-·) ≤ |B_s| M G(y)`, `|B_s| = (4π/3)s³`:
`R⁻²|B_R| + ∫_0^R 2 s⁻³ |B_s| ds = (4π/3 + 8π/3) R = 4πR`. -/
def HedbergNear : Prop :=
  ∀ G : Space → ℝ≥0∞, Measurable G → ∀ (y : Space) (R : ℝ), 0 < R →
    ∫⁻ z in ball y R, G z * bsK2 (y - z) ≤ ENNReal.ofReal R * hlMax G y

/-- Far part: Cauchy-Schwarz and `∫_{|w|≥R} k² = (4π)⁻² · 4π/R = 1/(4πR)` (polar coordinates). -/
def HedbergFar : Prop :=
  ∀ G : Space → ℝ≥0∞, Measurable G → ∀ (y : Space) (R : ℝ), 0 < R →
    ∫⁻ z in (ball y R)ᶜ, G z * bsK2 (y - z)
      ≤ (∫⁻ z, (G z) ^ 2) ^ (1 / 2 : ℝ) * ENNReal.ofReal ((4 * Real.pi * R) ^ (-(1 / 2 : ℝ)))

/-- Hedberg's pointwise bound (optimise `R = A^{2/3} M^{-2/3}`, `A = ‖G‖₂`; `1 + (4π)^{-1/2} ≤ 2`). -/
def HedbergPtwise : Prop :=
  ∀ G : Space → ℝ≥0∞, Measurable G → ∀ y : Space,
    rieszT G y ≤ 2 * (hlMax G y) ^ (1 / 3 : ℝ) * (∫⁻ z, (G z) ^ 2) ^ (1 / 3 : ℝ)

/-- Scalar HLS: `∫ (T G)⁶ ≤ 64 · 1000 · (∫ G²)³` from `T G ≤ 2 M^{1/3} A^{2/3}`
(`(T G)⁶ ≤ 64 M² A⁴`, `A⁴ = (∫G²)²`). -/
def RieszL6 : Prop :=
  ∀ G : Space → ℝ≥0∞, Measurable G →
    ∫⁻ y, (rieszT G y) ^ 6 ≤ 64000 * (∫⁻ z, (G z) ^ 2) ^ 3

/-- Vector reduction (source: `|a × b| ≤ 2|a||b|`, `‖F‖ ∈ L²`): for `F ∈ L²` the integral defining
`bsSlice F y` is absolutely convergent a.e., and `y ↦ bsSlice F y` is a.e. strongly measurable
(Fubini, `AEStronglyMeasurable.integral_prod_right'`, as in `bsDefined`). -/
def BsSliceMeasConv : Prop :=
  ∀ F : Space → CVec3, MemLp F 2 volume →
    AEStronglyMeasurable (bsSlice F) volume ∧
      ∀ᵐ y : Space, Integrable (fun z : Space => crossC (F z) (bsKernel (y - z))) volume

/-- Pointwise bound `‖bsSlice F y‖ ≤ 2 · T(‖F‖)(y)` (for all `y`). -/
def BsSlicePtwise : Prop :=
  ∀ F : Space → CVec3, ∀ y : Space,
    ENNReal.ofReal ‖bsSlice F y‖ ≤ 2 * rieszT (fun z => ENNReal.ofReal ‖F z‖) y

end UnforcedLeray.Short.PartIIIb.Concrete
