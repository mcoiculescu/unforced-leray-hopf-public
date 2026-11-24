import UnforcedLeray.Lib.Cylinder.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Decomposition of `l2Sq_hasDerivAt` (source 341-348: derivative of the cell energy)

Source: `the November 2 reference manuscript`.

Three analytic facts, all true for an arbitrary measure `μ` on the plane (hypotheses of the target):
* `L2SqMeas`: the slices `F r`, `|r - s| < ε`, are a.e. strongly measurable (`F r z = F s z +
  ∫_s^r ∂_t F`, a limit of Riemann sums of a.e.-measurable slices; null sets are a countable union);
* `L2SqDiff`: `F r - F s ∈ L²` with `∫ (F r - F s)² ≤ (r-s)² K` (pointwise FTC, Cauchy–Schwarz in
  `t`, Tonelli);
* `L2SqWeak`: the difference quotients `q_r` are bounded in `L²` by `√K` and converge pointwise
  to `∂_t F s`, hence converge weakly: `∫ q_r g → ∫ ∂_t F s · g` for every `g ∈ L²`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology
open UnforcedLeray.Cyl

namespace UnforcedLeray.Short.PartI.L2SqDeriv

/-- The hypotheses of `l2Sq_hasDerivAt`. -/
def Hyp {μ : Measure Plane} (F : ℝ → Plane → ℝ) (s ε K : ℝ) : Prop :=
  0 < ε ∧ (∀ z, ContDiff ℝ 1 (fun t => F t z)) ∧ MemLp (F s) 2 μ ∧
    ∀ r, |r - s| < ε → MemLp (fun z => deriv (fun t => F t z) r) 2 μ ∧
      ∫ z, (deriv (fun t => F t z) r) ^ 2 ∂μ ≤ K

/-- Slices near `s` are a.e. strongly measurable (source 341-348). -/
def L2SqMeas : Prop :=
  ∀ {μ : Measure Plane} (F : ℝ → Plane → ℝ) (s ε K : ℝ), Hyp (μ := μ) F s ε K →
    ∀ r, |r - s| < ε → AEStronglyMeasurable (F r) μ

/-- `F r - F s ∈ L²` with `∫ (F r - F s)² ≤ (r-s)² K` (source 341-348). -/
def L2SqDiff : Prop :=
  ∀ {μ : Measure Plane} (F : ℝ → Plane → ℝ) (s ε K : ℝ), Hyp (μ := μ) F s ε K →
    (∀ r, |r - s| < ε → AEStronglyMeasurable (F r) μ) →
    ∀ r, |r - s| < ε → MemLp (fun z => F r z - F s z) 2 μ ∧
      ∫ z, (F r z - F s z) ^ 2 ∂μ ≤ (r - s) ^ 2 * K

/-- Weak convergence of the difference quotients (source 341-348). -/
def L2SqWeak : Prop :=
  ∀ {μ : Measure Plane} (F : ℝ → Plane → ℝ) (s ε K : ℝ), Hyp (μ := μ) F s ε K →
    (∀ r, |r - s| < ε → AEStronglyMeasurable (F r) μ) →
    ∀ g : Plane → ℝ, MemLp g 2 μ →
      Tendsto (fun r => ∫ z, (F r z - F s z) / (r - s) * g z ∂μ) (𝓝[≠] s)
        (𝓝 (∫ z, deriv (fun t => F t z) s * g z ∂μ))

theorem l2Sq_hasDerivAt_of (h1 : L2SqMeas) (h2 : L2SqDiff) (h3 : L2SqWeak)
    {μ : MeasureTheory.Measure Plane} (F : ℝ → Plane → ℝ) (s ε K : ℝ) (hε : 0 < ε)
    (hC : ∀ z, ContDiff ℝ 1 (fun t => F t z)) (hF : MeasureTheory.MemLp (F s) 2 μ)
    (hD : ∀ r, |r - s| < ε → MeasureTheory.MemLp (fun z => deriv (fun t => F t z) r) 2 μ ∧
      ∫ z, (deriv (fun t => F t z) r) ^ 2 ∂μ ≤ K) :
    (∀ᶠ r in nhds s, MeasureTheory.MemLp (F r) 2 μ) ∧
      HasDerivAt (fun r => ∫ z, (F r z) ^ 2 ∂μ)
        (2 * ∫ z, F s z * deriv (fun t => F t z) s ∂μ) s := by
  have hH : Hyp (μ := μ) F s ε K := ⟨hε, hC, hF, hD⟩
  have hm := h1 F s ε K hH
  have hdiff := h2 F s ε K hH hm
  have hev : ∀ᶠ r in 𝓝 s, |r - s| < ε := by
    have : Metric.ball s ε ∈ 𝓝 s := Metric.ball_mem_nhds s hε
    filter_upwards [this] with r hr
    simpa [Metric.mem_ball, Real.dist_eq] using hr
  have hMem : ∀ r, |r - s| < ε → MemLp (F r) 2 μ := fun r hr => by
    have := (hdiff r hr).1.add hF
    convert this using 1
    funext z; simp
  refine ⟨hev.mono hMem, ?_⟩
  rw [hasDerivAt_iff_tendsto_slope]
  have hw := h3 F s ε K hH hm (F s) hF
  -- the quadratic remainder
  have hE : Tendsto (fun r => (∫ z, (F r z - F s z) ^ 2 ∂μ) / (r - s)) (𝓝[≠] s) (𝓝 0) := by
    have hev' : ∀ᶠ r in 𝓝[≠] s, |r - s| < ε := nhdsWithin_le_nhds hev
    have hK : Tendsto (fun r : ℝ => |r - s| * |K|) (𝓝[≠] s) (𝓝 0) := by
      have : Tendsto (fun r : ℝ => |r - s| * |K|) (𝓝 s) (𝓝 (|s - s| * |K|)) := by
        exact ((continuous_abs.comp (continuous_id.sub continuous_const)).mul
          continuous_const).tendsto s
      simpa using this.mono_left nhdsWithin_le_nhds
    refine squeeze_zero_norm' ?_ hK
    filter_upwards [hev', self_mem_nhdsWithin] with r hr hne
    have hne' : r - s ≠ 0 := sub_ne_zero.mpr hne
    have hb := (hdiff r hr).2
    have h0 : 0 ≤ ∫ z, (F r z - F s z) ^ 2 ∂μ := integral_nonneg fun z => sq_nonneg _
    rw [Real.norm_eq_abs, abs_div, abs_of_nonneg h0, div_le_iff₀ (abs_pos.mpr hne')]
    calc ∫ z, (F r z - F s z) ^ 2 ∂μ ≤ (r - s) ^ 2 * K := hb
      _ ≤ (r - s) ^ 2 * |K| := by gcongr; exact le_abs_self K
      _ = |r - s| * |K| * |r - s| := by rw [← sq_abs]; ring
  have hlim := hE.add (hw.const_mul 2)
  have heq : (∫ z, F s z * deriv (fun t => F t z) s ∂μ) =
      ∫ z, deriv (fun t => F t z) s * F s z ∂μ := by
    simp_rw [mul_comm]
  rw [heq, ← zero_add (2 * ∫ z, deriv (fun t => F t z) s * F s z ∂μ)]
  refine hlim.congr' ?_
  have hev' : ∀ᶠ r in 𝓝[≠] s, |r - s| < ε := nhdsWithin_le_nhds hev
  filter_upwards [hev', self_mem_nhdsWithin] with r hr hne
  have hne' : r - s ≠ 0 := sub_ne_zero.mpr hne
  have hr2 := hMem r hr
  have hd2 := (hdiff r hr).1
  have i1 : Integrable (fun z => (F r z) ^ 2) μ := hr2.integrable_sq
  have i2 : Integrable (fun z => (F s z) ^ 2) μ := hF.integrable_sq
  have i3 : Integrable (fun z => (F r z - F s z) ^ 2) μ := hd2.integrable_sq
  have i4 : Integrable (fun z => (F r z - F s z) * F s z) μ := hd2.integrable_mul hF
  have hsplit : ∫ z, (F r z) ^ 2 ∂μ - ∫ z, (F s z) ^ 2 ∂μ =
      ∫ z, (F r z - F s z) ^ 2 ∂μ + 2 * ∫ z, (F r z - F s z) * F s z ∂μ := by
    rw [← integral_sub i1 i2, ← integral_const_mul, ← integral_add i3 (i4.const_mul 2)]
    congr 1; funext z; ring
  have hq : ∫ z, (F r z - F s z) / (r - s) * F s z ∂μ =
      (r - s)⁻¹ * ∫ z, (F r z - F s z) * F s z ∂μ := by
    rw [← integral_const_mul]
    congr 1; funext z; field_simp
  show (∫ z, (F r z - F s z) ^ 2 ∂μ) / (r - s) + 2 * ∫ z, (F r z - F s z) / (r - s) * F s z ∂μ =
    slope (fun r => ∫ z, (F r z) ^ 2 ∂μ) s r
  rw [slope_def_field, hq, div_eq_mul_inv]
  have : (r - s)⁻¹ = (r - s)⁻¹ := rfl
  rw [show (∫ z, (F r z) ^ 2 ∂μ - ∫ z, (F s z) ^ 2 ∂μ) / (r - s) =
    (∫ z, (F r z) ^ 2 ∂μ - ∫ z, (F s z) ^ 2 ∂μ) * (r - s)⁻¹ from div_eq_mul_inv _ _, hsplit]
  ring

end UnforcedLeray.Short.PartI.L2SqDeriv
