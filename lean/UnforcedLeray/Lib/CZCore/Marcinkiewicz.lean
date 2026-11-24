import UnforcedLeray.Lib.CZCore.WeakType
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Marcinkiewicz interpolation between weak `(1,1)` and strong `(2,2)` (INF01 T7)


target T7 (dependencies `Layercake.lean:445`, `ChebyshevMarkov.lean:33`).

For `1 < p < 2`, an `L²`-bounded operator `T` of weak type `(1,1)` with constant `A` satisfies
`‖T f‖_p ≤ C(p, A, ‖T‖) ‖f‖_p` for every `f ∈ L² ∩ L^p`, with the explicit constant
`marcConst p A ‖T‖₊ = (p (2A/(p-1) + 4‖T‖²/(2-p)))^{1/p}`.

Proof (standard): layer cake for `|T f|^p`; at height `t` split `f = f 1_{|f| ≥ t} + f 1_{|f|<t}`,
use the weak bound at `t/2` on the first piece and Chebyshev in `L²` at `t/2` on the second;
Tonelli; `∫_0^b t^{p-2} dt = b^{p-1}/(p-1)` and `∫_b^∞ t^{p-3} dt = b^{p-2}/(2-p)`.
All estimates are in `ℝ≥0∞`.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

namespace UnforcedLeray.CZ

set_option autoImplicit false

/-! ### One-dimensional integrals -/

/-- `∫_{(0,b]} t^r dt = b^{r+1}/(r+1)` for `r > -1`, `b ≥ 0`, in `ℝ≥0∞`. -/
theorem lintegral_Ioc_rpow {r : ℝ} (hr : -1 < r) {b : ℝ} (hb : 0 ≤ b) :
    ∫⁻ t in Ioc 0 b, ENNReal.ofReal (t ^ r) = ENNReal.ofReal (b ^ (r + 1) / (r + 1)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (intervalIntegral.intervalIntegrable_rpow' hr).1
    (ae_restrict_of_forall_mem measurableSet_Ioc fun t ht => Real.rpow_nonneg ht.1.le _)]
  rw [← intervalIntegral.integral_of_le hb, integral_rpow (Or.inl hr),
    Real.zero_rpow (by linarith), sub_zero]

/-- `∫_{(b,∞)} t^r dt = -b^{r+1}/(r+1)` for `r < -1`, `b > 0`, in `ℝ≥0∞`. -/
theorem lintegral_Ioi_rpow {r : ℝ} (hr : r < -1) {b : ℝ} (hb : 0 < b) :
    ∫⁻ t in Ioi b, ENNReal.ofReal (t ^ r) = ENNReal.ofReal (-b ^ (r + 1) / (r + 1)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_Ioi_rpow_of_lt hr hb)
    (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht =>
      Real.rpow_nonneg (hb.trans ht).le _), integral_Ioi_rpow_of_lt hr hb]

/-- Inner integral of the low part. -/
theorem lintegral_Ioi_rpow_mul_ite_le {r : ℝ} (hr : -1 < r) {b : ℝ} (hb : 0 ≤ b) (d : ℝ≥0∞) :
    ∫⁻ t in Ioi 0, ENNReal.ofReal (t ^ r) * (if t ≤ b then d else 0) =
      d * ENNReal.ofReal (b ^ (r + 1) / (r + 1)) := by
  have h : (fun t : ℝ => ENNReal.ofReal (t ^ r) * (if t ≤ b then d else 0)) =
      (Iic b).indicator (fun t => d * ENNReal.ofReal (t ^ r)) := by
    funext t
    by_cases ht : t ≤ b
    · simp [ht, mul_comm]
    · simp [ht]
  rw [h, lintegral_indicator measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic,
    Iic_inter_Ioi, lintegral_const_mul _ (by fun_prop), lintegral_Ioc_rpow hr hb]

/-- Inner integral of the high part. -/
theorem lintegral_Ioi_rpow_mul_ite_lt {r : ℝ} (hr : r < -1) {b : ℝ} (hb : 0 < b) (d : ℝ≥0∞) :
    ∫⁻ t in Ioi 0, ENNReal.ofReal (t ^ r) * (if b < t then d else 0) =
      d * ENNReal.ofReal (-b ^ (r + 1) / (r + 1)) := by
  have h : (fun t : ℝ => ENNReal.ofReal (t ^ r) * (if b < t then d else 0)) =
      (Ioi b).indicator (fun t => d * ENNReal.ofReal (t ^ r)) := by
    funext t
    by_cases ht : b < t
    · simp [ht, mul_comm]
    · simp [ht]
  rw [h, lintegral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
    Ioi_inter_Ioi, max_eq_left hb.le, lintegral_const_mul _ (by fun_prop),
    lintegral_Ioi_rpow hr hb]

/-! ### The constant -/

/-- The Marcinkiewicz constant in `ℝ≥0∞`: `(p (2A/(p-1) + 4M²/(2-p)))^{1/p}`. -/
def marcConstE (p : ℝ) (A M : ℝ≥0) : ℝ≥0∞ :=
  (ENNReal.ofReal p * (2 * A * ENNReal.ofReal (1 / (p - 1)) +
    4 * (M : ℝ≥0∞) ^ 2 * ENNReal.ofReal (1 / (2 - p)))) ^ (1 / p)

theorem marcConstE_ne_top {p : ℝ} (hp : 0 ≤ p) (A M : ℝ≥0) : marcConstE p A M ≠ ⊤ := by
  unfold marcConstE
  refine ENNReal.rpow_ne_top_of_nonneg (by positivity) ?_
  refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.add_ne_top.2 ⟨?_, ?_⟩)
  · exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num) ENNReal.coe_ne_top)
      ENNReal.ofReal_ne_top
  · exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num)
      (ENNReal.pow_ne_top ENNReal.coe_ne_top)) ENNReal.ofReal_ne_top

/-- **The Marcinkiewicz constant** `marcConst p A M = (p (2A/(p-1) + 4M²/(2-p)))^{1/p}` (in
`ℝ≥0`; meaningful for `1 < p < 2`). -/
def marcConst (p : ℝ) (A M : ℝ≥0) : ℝ≥0 := (marcConstE p A M).toNNReal

theorem coe_marcConst {p : ℝ} (hp : 0 ≤ p) (A M : ℝ≥0) :
    (marcConst p A M : ℝ≥0∞) = marcConstE p A M :=
  ENNReal.coe_toNNReal (marcConstE_ne_top hp A M)

/-! ### The level-set estimate -/

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- `∫ ofReal |g|^p = ‖g‖_p^p`. -/
theorem lintegral_ofReal_abs_rpow (g : α → ℝ) {p : ℝ} (hp : 0 < p) :
    ∫⁻ x, ENNReal.ofReal (|g x| ^ p) ∂μ = eLpNorm g (ENNReal.ofReal p) μ ^ p := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simp [hp]) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hp.le, ← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hp.ne',
    ENNReal.rpow_one]
  congr 1; funext x
  rw [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hp.le]

/-- **Level-set estimate.** For `t > 0`, splitting `f` at height `t`:
`μ{|Tf| > t} t^{p-1} ≤ ∫ 2A t^{p-2} |f| 1_{|f| ≥ t} + ∫ 4‖T‖² t^{p-3} |f|² 1_{|f| < t}`. -/
theorem meas_lt_mul_le {T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ} {A : ℝ≥0} (h1 : HasWeakType11 μ T A)
    (f : Lp ℝ 2 μ) {t : ℝ} (ht : 0 < t) (p : ℝ) :
    μ {x | t < |T f x|} * ENNReal.ofReal (t ^ (p - 1)) ≤
      ∫⁻ x, 2 * A * ENNReal.ofReal (t ^ (p - 2)) *
          (if t ≤ |f x| then ENNReal.ofReal |f x| else 0) ∂μ +
      ∫⁻ x, 4 * (‖T‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (t ^ (p - 3)) *
          (if |f x| < t then ENNReal.ofReal |f x| ^ (2 : ℝ) else 0) ∂μ := by
  have hfm : StronglyMeasurable (f : α → ℝ) := Lp.stronglyMeasurable f
  have hf2 : MemLp (f : α → ℝ) 2 μ := Lp.memLp f
  set S₁ : Set α := {x | t ≤ |f x|}
  set S₂ : Set α := {x | |f x| < t}
  have hS₁ : MeasurableSet S₁ :=
    measurableSet_le measurable_const (continuous_abs.measurable.comp hfm.measurable)
  have hS₂ : MeasurableSet S₂ :=
    measurableSet_lt (continuous_abs.measurable.comp hfm.measurable) measurable_const
  set f₁ : α → ℝ := S₁.indicator f
  set f₂ : α → ℝ := S₂.indicator f
  have hf₁2 : MemLp f₁ 2 μ := hf2.indicator hS₁
  have hf₂2 : MemLp f₂ 2 μ := hf2.indicator hS₂
  set F₁ : Lp ℝ 2 μ := hf₁2.toLp f₁
  set F₂ : Lp ℝ 2 μ := hf₂2.toLp f₂
  have hsum : f = F₁ + F₂ := by
    refine Lp.ext ?_
    filter_upwards [Lp.coeFn_add F₁ F₂, hf₁2.coeFn_toLp, hf₂2.coeFn_toLp] with x hx h1x h2x
    rw [hx, Pi.add_apply, h1x, h2x]
    by_cases hx1 : t ≤ |f x|
    · have hx2 : ¬ |f x| < t := not_lt.2 hx1
      simp [f₁, f₂, S₁, S₂, indicator_of_mem (show x ∈ S₁ from hx1),
        indicator_of_notMem (show x ∉ S₂ from hx2)]
    · have hx2 : |f x| < t := lt_of_not_ge hx1
      simp [f₁, f₂, S₁, S₂, indicator_of_notMem (show x ∉ S₁ from hx1),
        indicator_of_mem (show x ∈ S₂ from hx2)]
  -- the a.e. splitting of `T f`
  have hTsplit : ∀ᵐ x ∂μ, |T f x| ≤ |T F₁ x| + |T F₂ x| := by
    have : (T f : α → ℝ) =ᵐ[μ] (T F₁ : α → ℝ) + T F₂ := by
      rw [hsum, map_add]; exact Lp.coeFn_add _ _
    filter_upwards [this] with x hx
    rw [hx, Pi.add_apply]; exact abs_add_le _ _
  have hmeas : μ {x | t < |T f x|} ≤ μ {x | t / 2 < |T F₁ x|} + μ {x | t / 2 ≤ |T F₂ x|} := by
    refine (measure_mono_ae ?_).trans (measure_union_le _ _)
    filter_upwards [hTsplit] with x hx hxs
    have hxs' : t / 2 + t / 2 < |T f x| := by rw [add_halves]; exact hxs
    exact lt_abs_or_le_abs_of_le hx hxs'
  -- `F₁ ∈ L¹`
  have hf₁1 : MemLp f₁ 1 μ := by
    refine MemLp.mono (g := fun x => t⁻¹ * f x ^ 2) ?_ (hf₁2.1) (Eventually.of_forall fun x => ?_)
    · exact memLp_one_iff_integrable.2 (hf2.integrable_sq.const_mul _)
    · by_cases hx : x ∈ S₁
      · simp only [f₁, indicator_of_mem hx, Real.norm_eq_abs]
        have hx' : t ≤ |f x| := hx
        rw [abs_of_nonneg (by positivity : 0 ≤ t⁻¹ * f x ^ 2), ← sq_abs, le_inv_mul_iff₀ ht, sq]
        exact mul_le_mul_of_nonneg_right hx' (abs_nonneg _)
      · simp only [f₁, indicator_of_notMem hx, norm_zero]; exact norm_nonneg _
  have hF₁1 : MemLp F₁ 1 μ := hf₁1.ae_eq hf₁2.coeFn_toLp.symm
  -- the weak-type piece
  have hI₁ : eLpNorm F₁ 1 μ = ∫⁻ x, (if t ≤ |f x| then ENNReal.ofReal |f x| else 0) ∂μ := by
    rw [eLpNorm_congr_ae hf₁2.coeFn_toLp, eLpNorm_one_eq_lintegral_enorm]
    congr 1; funext x
    by_cases hx : t ≤ |f x|
    · simp [f₁, S₁, hx, Real.enorm_eq_ofReal_abs]
    · simp [f₁, S₁, hx]
  have hweak := h1 F₁ hF₁1 (t / 2) (by positivity)
  rw [hI₁] at hweak
  -- the `L²` piece
  have hI₂ : eLpNorm F₂ 2 μ ^ (2 : ℝ) =
      ∫⁻ x, (if |f x| < t then ENNReal.ofReal |f x| ^ (2 : ℝ) else 0) ∂μ := by
    rw [eLpNorm_congr_ae hf₂2.coeFn_toLp, eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num)
      (by norm_num), ← ENNReal.rpow_mul]
    norm_num
    congr 1; funext x
    by_cases hx : |f x| < t
    · simp [f₂, S₂, hx, Real.enorm_eq_ofReal_abs]
    · simp [f₂, S₂, hx]
  have hcheb := ofReal_rpow_two_mul_meas_le (μ := μ) (Lp.aestronglyMeasurable (T F₂)) (t / 2)
  have hL2 : eLpNorm (T F₂) 2 μ ^ (2 : ℝ) ≤ (‖T‖₊ : ℝ≥0∞) ^ (2 : ℝ) * eLpNorm F₂ 2 μ ^ (2 : ℝ) := by
    rw [← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
    gcongr
    exact eLpNorm_apply_le T F₂
  rw [hI₂] at hL2
  -- cancel the factors `t/2`
  set τ : ℝ≥0∞ := ENNReal.ofReal (t / 2)
  have hτ0 : τ ≠ 0 := by simp [τ, ht]
  have hτt : τ ≠ ⊤ := ENNReal.ofReal_ne_top
  have hτ2 : τ ^ (2 : ℝ) ≠ 0 := (ENNReal.rpow_pos (pos_iff_ne_zero.2 hτ0) hτt).ne'
  have hτ2t : τ ^ (2 : ℝ) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) hτt
  have hid1 : τ * (2 * ENNReal.ofReal (t ^ (p - 2))) = ENNReal.ofReal (t ^ (p - 1)) := by
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num),
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [show p - 1 = 1 + (p - 2) by ring, Real.rpow_add ht, Real.rpow_one]; ring
  have hid2 : τ ^ (2 : ℝ) * (4 * ENNReal.ofReal (t ^ (p - 3))) = ENNReal.ofReal (t ^ (p - 1)) := by
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
      show (4 : ℝ≥0∞) = ENNReal.ofReal 4 by simp, ← ENNReal.ofReal_mul (by norm_num),
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [show p - 1 = 2 + (p - 3) by ring, Real.rpow_add ht, Real.div_rpow ht.le (by norm_num)]
    norm_num
    ring
  have hpart1 : μ {x | t / 2 < |T F₁ x|} * ENNReal.ofReal (t ^ (p - 1)) ≤
      ∫⁻ x, 2 * A * ENNReal.ofReal (t ^ (p - 2)) *
          (if t ≤ |f x| then ENNReal.ofReal |f x| else 0) ∂μ := by
    rw [lintegral_const_mul' _ _ (by
      exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num) ENNReal.coe_ne_top)
        ENNReal.ofReal_ne_top)]
    rw [← ENNReal.mul_le_mul_iff_right hτ0 hτt]
    calc τ * (μ {x | t / 2 < |T F₁ x|} * ENNReal.ofReal (t ^ (p - 1)))
        = (τ * μ {x | t / 2 < |T F₁ x|}) * ENNReal.ofReal (t ^ (p - 1)) := by ring
      _ ≤ (A * ∫⁻ x, (if t ≤ |f x| then ENNReal.ofReal |f x| else 0) ∂μ) *
            ENNReal.ofReal (t ^ (p - 1)) := by gcongr
      _ = τ * (2 * A * ENNReal.ofReal (t ^ (p - 2)) *
            ∫⁻ x, (if t ≤ |f x| then ENNReal.ofReal |f x| else 0) ∂μ) := by
          rw [← hid1]; ring
  have hpart2 : μ {x | t / 2 ≤ |T F₂ x|} * ENNReal.ofReal (t ^ (p - 1)) ≤
      ∫⁻ x, 4 * (‖T‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (t ^ (p - 3)) *
          (if |f x| < t then ENNReal.ofReal |f x| ^ (2 : ℝ) else 0) ∂μ := by
    rw [lintegral_const_mul' _ _ (by
      exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num)
        (ENNReal.pow_ne_top ENNReal.coe_ne_top)) ENNReal.ofReal_ne_top)]
    rw [← ENNReal.mul_le_mul_iff_right hτ2 hτ2t]
    have hM : (‖T‖₊ : ℝ≥0∞) ^ (2 : ℝ) = (‖T‖₊ : ℝ≥0∞) ^ (2 : ℕ) := by
      rw [← ENNReal.rpow_natCast]; norm_num
    rw [hM] at hL2
    calc τ ^ (2 : ℝ) * (μ {x | t / 2 ≤ |T F₂ x|} * ENNReal.ofReal (t ^ (p - 1)))
        = (τ ^ (2 : ℝ) * μ {x | t / 2 ≤ |T F₂ x|}) * ENNReal.ofReal (t ^ (p - 1)) := by ring
      _ ≤ ((‖T‖₊ : ℝ≥0∞) ^ 2 *
            ∫⁻ x, (if |f x| < t then ENNReal.ofReal |f x| ^ (2 : ℝ) else 0) ∂μ) *
            ENNReal.ofReal (t ^ (p - 1)) := mul_le_mul_left (hcheb.trans hL2) _
      _ = τ ^ (2 : ℝ) * (4 * (‖T‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (t ^ (p - 3)) *
            ∫⁻ x, (if |f x| < t then ENNReal.ofReal |f x| ^ (2 : ℝ) else 0) ∂μ) := by
          rw [← hid2]; ring
  calc μ {x | t < |T f x|} * ENNReal.ofReal (t ^ (p - 1))
      ≤ (μ {x | t / 2 < |T F₁ x|} + μ {x | t / 2 ≤ |T F₂ x|}) * ENNReal.ofReal (t ^ (p - 1)) := by
        gcongr
    _ = μ {x | t / 2 < |T F₁ x|} * ENNReal.ofReal (t ^ (p - 1)) +
        μ {x | t / 2 ≤ |T F₂ x|} * ENNReal.ofReal (t ^ (p - 1)) := add_mul _ _ _
    _ ≤ _ := add_le_add hpart1 hpart2

/-! ### Marcinkiewicz -/

/-- `b · b^{p-1} = b^p` for `b ≥ 0`, `p > 0`. -/
private theorem mul_rpow_sub_one' {b p : ℝ} (hb : 0 ≤ b) (hp : 0 < p) :
    b * b ^ (p - 1) = b ^ p := by
  rcases hb.eq_or_lt with rfl | hb
  · simp [Real.zero_rpow hp.ne']
  · rw [show p = 1 + (p - 1) by ring, Real.rpow_add hb, Real.rpow_one]; ring_nf

/-- **T7 (INF01 §5, Level 1): Marcinkiewicz interpolation.** If `T` is bounded on `L²(μ)` and
of weak type `(1,1)` with constant `A`, then for `1 < p < 2` and every `f ∈ L² ∩ L^p`,
`‖T f‖_p ≤ marcConst p A ‖T‖₊ · ‖f‖_p`. -/
theorem marcinkiewicz [SigmaFinite μ] {T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ} {A : ℝ≥0}
    (h1 : HasWeakType11 μ T A) {p : ℝ} (hp : 1 < p) (hp2 : p < 2) :
    ∀ f : Lp ℝ 2 μ, MemLp f (ENNReal.ofReal p) μ →
      eLpNorm (T f) (ENNReal.ofReal p) μ ≤ marcConst p A ‖T‖₊ * eLpNorm f (ENNReal.ofReal p) μ := by
  intro f _hfp
  have hp0 : 0 < p := by linarith
  set M : ℝ≥0∞ := (‖T‖₊ : ℝ≥0∞)
  have hfm : Measurable (f : α → ℝ) := (Lp.stronglyMeasurable f).measurable
  have hafm : Measurable fun x => |f x| := continuous_abs.measurable.comp hfm
  -- the two integrands on `ℝ × α`
  set G₁ : ℝ → α → ℝ≥0∞ := fun t x => 2 * A * ENNReal.ofReal (t ^ (p - 2)) *
    (if t ≤ |f x| then ENNReal.ofReal |f x| else 0)
  set G₂ : ℝ → α → ℝ≥0∞ := fun t x => 4 * M ^ 2 * ENNReal.ofReal (t ^ (p - 3)) *
    (if |f x| < t then ENNReal.ofReal |f x| ^ (2 : ℝ) else 0)
  have hG₁ : Measurable (Function.uncurry G₁) := by
    refine (measurable_const.mul (ENNReal.measurable_ofReal.comp
      (measurable_fst.pow_const _))).mul (Measurable.ite ?_ ?_ measurable_const)
    · exact measurableSet_le measurable_fst (hafm.comp measurable_snd)
    · exact ENNReal.measurable_ofReal.comp (hafm.comp measurable_snd)
  have hG₂ : Measurable (Function.uncurry G₂) := by
    refine (measurable_const.mul (ENNReal.measurable_ofReal.comp
      (measurable_fst.pow_const _))).mul (Measurable.ite ?_ ?_ measurable_const)
    · exact measurableSet_lt (hafm.comp measurable_snd) measurable_fst
    · exact (ENNReal.measurable_ofReal.comp (hafm.comp measurable_snd)).pow_const _
  -- inner integrals in `t`
  have hin₁ : ∀ x, ∫⁻ t in Ioi 0, G₁ t x =
      2 * A * (ENNReal.ofReal (1 / (p - 1)) * ENNReal.ofReal (|f x| ^ p)) := by
    intro x
    simp only [G₁]
    simp_rw [mul_assoc (2 * (A : ℝ≥0∞))]
    rw [lintegral_const_mul' _ _ (ENNReal.mul_ne_top (by norm_num) ENNReal.coe_ne_top),
      lintegral_Ioi_rpow_mul_ite_le (by linarith) (abs_nonneg _)]
    congr 1
    rw [← ENNReal.ofReal_mul (abs_nonneg _), ← ENNReal.ofReal_mul (by
      have : 0 < p - 1 := by linarith
      positivity)]
    congr 1
    rw [show p - 2 + 1 = p - 1 by ring, ← mul_rpow_sub_one' (abs_nonneg (f x)) hp0]; ring
  have hin₂ : ∀ x, ∫⁻ t in Ioi 0, G₂ t x =
      4 * M ^ 2 * (ENNReal.ofReal (1 / (2 - p)) * ENNReal.ofReal (|f x| ^ p)) := by
    intro x
    simp only [G₂]
    simp_rw [mul_assoc (4 * M ^ 2)]
    rw [lintegral_const_mul' _ _ (ENNReal.mul_ne_top (by norm_num)
      (ENNReal.pow_ne_top ENNReal.coe_ne_top))]
    congr 1
    rcases (abs_nonneg (f x)).eq_or_lt with h0 | hpos
    · rw [← h0]
      simp [Real.zero_rpow hp0.ne']
    · rw [lintegral_Ioi_rpow_mul_ite_lt (by linarith) hpos,
        ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num),
        ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by
          have : 0 < 2 - p := by linarith
          positivity)]
      congr 1
      have key : |f x| ^ p = |f x| ^ (2 : ℝ) * |f x| ^ (p - 2) := by
        rw [← Real.rpow_add hpos]; ring_nf
      rw [key, show p - 3 + 1 = p - 2 by ring, neg_div, ← div_neg, neg_sub]
      ring
  -- assemble
  have hlayer := lintegral_rpow_eq_lintegral_meas_lt_mul μ
    (f := fun x => |T f x|) (Eventually.of_forall fun x => abs_nonneg _)
    (continuous_abs.measurable.comp (Lp.stronglyMeasurable (T f)).measurable).aemeasurable hp0
  have hmain : ∫⁻ x, ENNReal.ofReal (|T f x| ^ p) ∂μ ≤
      ENNReal.ofReal p * ((2 * A * ENNReal.ofReal (1 / (p - 1)) +
        4 * M ^ 2 * ENNReal.ofReal (1 / (2 - p))) * ∫⁻ x, ENNReal.ofReal (|f x| ^ p) ∂μ) := by
    rw [hlayer]
    gcongr
    calc ∫⁻ t in Ioi 0, μ {a | t < |T f a|} * ENNReal.ofReal (t ^ (p - 1))
        ≤ ∫⁻ t in Ioi (0 : ℝ), ((∫⁻ x, G₁ t x ∂μ) + ∫⁻ x, G₂ t x ∂μ) := by
          refine setLIntegral_mono' measurableSet_Ioi fun t ht => ?_
          exact meas_lt_mul_le h1 f ht p
      _ = (∫⁻ t in Ioi (0 : ℝ), (∫⁻ x, G₁ t x ∂μ)) + ∫⁻ t in Ioi (0 : ℝ), (∫⁻ x, G₂ t x ∂μ) :=
          lintegral_add_left (hG₁.lintegral_prod_right') _
      _ = (∫⁻ x, (∫⁻ t in Ioi (0 : ℝ), G₁ t x) ∂μ) + ∫⁻ x, (∫⁻ t in Ioi (0 : ℝ), G₂ t x) ∂μ := by
          rw [lintegral_lintegral_swap hG₁.aemeasurable,
            lintegral_lintegral_swap hG₂.aemeasurable]
      _ = _ := by
          simp_rw [hin₁, hin₂, ← mul_assoc]
          rw [lintegral_const_mul _ (hafm.pow_const p).ennreal_ofReal,
            lintegral_const_mul _ (hafm.pow_const p).ennreal_ofReal]
          ring
  rw [lintegral_ofReal_abs_rpow _ hp0, lintegral_ofReal_abs_rpow _ hp0] at hmain
  -- take `p`-th roots
  rw [coe_marcConst hp0.le, marcConstE]
  have hroot := ENNReal.rpow_le_rpow hmain (by positivity : (0 : ℝ) ≤ 1 / p)
  rw [← ENNReal.rpow_mul, mul_one_div_cancel hp0.ne', ENNReal.rpow_one, ← mul_assoc,
    ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
    mul_one_div_cancel hp0.ne', ENNReal.rpow_one] at hroot
  exact hroot

end UnforcedLeray.CZ
