import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

/-!
# Strong continuity of bounded multipliers on `L²` (dominated convergence)

If `h ∈ L²(μ)` and `g_i → g₀` a.e. with `|g_i| ≤ C`, then `g_i h → g₀ h` in `L²(μ)`; the statement
is over a countably generated filter, so it applies to `𝓝[Icc 0 T] s₀`.  Used for SP 2819-2836
(`B(t)ω = vω + E K_cω` strongly continuous).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa.Exist

theorem enorm_rpow_two_eq (a : ℝ) : ‖a‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (a ^ 2) := by
  rw [Real.enorm_eq_ofReal_abs, ENNReal.rpow_two, ← ENNReal.ofReal_pow (abs_nonneg a), sq_abs]

theorem lintegral_sq_lt_top {α : Type*} [MeasurableSpace α] {μ : Measure α} {h : α → ℝ}
    (hh : MemLp h 2 μ) : ∫⁻ x, ‖h x‖ₑ ^ (2 : ℝ) ∂μ < ⊤ := by
  have h1 := hh.eLpNorm_lt_top
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)] at h1
  simp only [ENNReal.toReal_ofNat] at h1
  by_contra hcon
  have : ∫⁻ x, ‖h x‖ₑ ^ (2 : ℝ) ∂μ = ⊤ := not_lt_top_iff.mp hcon
  rw [this, ENNReal.top_rpow_of_pos (by norm_num)] at h1
  exact lt_irrefl _ h1

theorem tendsto_eLpNorm_mul_sub {α : Type*} [MeasurableSpace α] {μ : Measure α} {ι : Type*}
    {l : Filter ι} [l.IsCountablyGenerated] {h : α → ℝ} (hh : MemLp h 2 μ)
    (g : ι → α → ℝ) (g0 : α → ℝ) {C : ℝ}
    (hg : ∀ i, AEStronglyMeasurable (g i) μ) (hg0 : AEStronglyMeasurable g0 μ)
    (hb : ∀ᶠ i in l, ∀ᵐ x ∂μ, |g i x| ≤ C) (hb0 : ∀ᵐ x ∂μ, |g0 x| ≤ C)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun i => g i x) l (𝓝 (g0 x))) :
    Tendsto (fun i => eLpNorm ((fun x => g i x * h x) - fun x => g0 x * h x) 2 μ) l (𝓝 0) := by
  have key : Tendsto (fun i => ∫⁻ x, ‖g i x * h x - g0 x * h x‖ₑ ^ (2 : ℝ) ∂μ) l (𝓝 0) := by
    have hD := tendsto_lintegral_filter_of_dominated_convergence'
      (μ := μ) (l := l) (F := fun i x => ‖g i x * h x - g0 x * h x‖ₑ ^ (2 : ℝ))
      (f := fun _ => 0) (fun x => ENNReal.ofReal ((2 * C) ^ 2) * ‖h x‖ₑ ^ (2 : ℝ)) ?_ ?_ ?_ ?_
    · simpa using hD
    · refine Eventually.of_forall fun i => ?_
      have hm : AEStronglyMeasurable (fun x => g i x * h x - g0 x * h x) μ :=
        ((hg i).mul hh.1).sub (hg0.mul hh.1)
      exact AEMeasurable.pow_const hm.enorm _
    · filter_upwards [hb] with i hi
      filter_upwards [hi, hb0] with x hx hx0
      rw [enorm_rpow_two_eq, enorm_rpow_two_eq, ← ENNReal.ofReal_mul (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      have hC : 0 ≤ C := (abs_nonneg _).trans hx
      have : |g i x * h x - g0 x * h x| ≤ 2 * C * |h x| := by
        rw [← sub_mul, abs_mul]
        refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
        calc |g i x - g0 x| ≤ |g i x| + |g0 x| := abs_sub _ _
          _ ≤ C + C := add_le_add hx hx0
          _ = 2 * C := by ring
      calc (g i x * h x - g0 x * h x) ^ 2 = |g i x * h x - g0 x * h x| ^ 2 := (sq_abs _).symm
        _ ≤ (2 * C * |h x|) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) this 2
        _ = (2 * C) ^ 2 * h x ^ 2 := by rw [mul_pow, sq_abs]
    · rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (lintegral_sq_lt_top hh).ne
    · filter_upwards [hlim] with x hx
      have h1 : Tendsto (fun i => g i x * h x - g0 x * h x) l (𝓝 (g0 x * h x - g0 x * h x)) :=
        (hx.mul_const _).sub_const _
      rw [sub_self] at h1
      have h2 : Tendsto (fun i => ENNReal.ofReal ((g i x * h x - g0 x * h x) ^ 2)) l
          (𝓝 (ENNReal.ofReal (0 ^ 2))) :=
        (ENNReal.continuous_ofReal.tendsto _).comp ((continuous_pow 2).tendsto _ |>.comp h1)
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, ENNReal.ofReal_zero] at h2
      simpa only [enorm_rpow_two_eq] using h2
  have hev : (fun i => eLpNorm ((fun x => g i x * h x) - fun x => g0 x * h x) 2 μ) =
      fun i => (∫⁻ x, ‖g i x * h x - g0 x * h x‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := by
    funext i
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
    simp only [ENNReal.toReal_ofNat, Pi.sub_apply]
  rw [hev]
  have := (ENNReal.continuous_rpow_const (y := 1 / (2 : ℝ))).tendsto 0 |>.comp key
  rw [Function.comp_def, ENNReal.zero_rpow_of_pos (by norm_num)] at this
  exact this

end UnforcedLeray.Short.IIIa.Exist
