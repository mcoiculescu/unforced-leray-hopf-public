import UnforcedLeray.Lib.Gaussian.Kernel

/-!
# The causal kernel `1_{t>0} e^{-t} G_t` in space-time `L^r` (INF22 G3, second part)


row B0448–B0450 and §5 target G3: "the causal kernel `1_{t>0}e^{-t}G_t ∈ L^{q'}(ℝ×ℝ³)` iff
`q' < 5/3`".

Manuscript: `paper/main.tex` lines 7671–7681 (B0448–B0450): the causal inverse kernel
`K(t,z) = 1_{t>0} e^{-t} H_t(z)` "belongs to `L^{q'}` precisely when `q > 5/2`, because
`‖K‖_{L^{q'}}^{q'} = C ∫_0^∞ e^{-q't} t^{-3(q'-1)/2} dt`" (eq:free-stress-22).

Main results (any dimension `d`, any exponent `r > 0`):
* `integral_causalKernel_rpow_slice`: the slice identity behind eq:free-stress-22,
  `∫ |K(t,·)|^r = e^{-rt} c_{d,r} t^{-(d/2)(r-1)}` for `t > 0`;
* `memLp_causalKernel_iff`: `K ∈ L^r(ℝ × ℝ^d) ↔ (d/2)(r-1) < 1`;
* `memLp_causalKernel_three_iff`: for `d = 3` and `r > 0`, `K ∈ L^r ↔ r < 5/3`
  (that is `q > 5/2` for `r = q' = q/(q-1)`).
-/

noncomputable section

set_option autoImplicit false

namespace UnforcedLeray.Gaussian

open MeasureTheory Real Set
open scoped ENNReal

variable {d : ℕ}

/-- The causal kernel `K(t, z) = 1_{t>0} e^{-t} G_t(z)` on `ℝ × ℝ^d` (tex 7671–7673). -/
def causalKernel (d : ℕ) (X : ℝ × Euc d) : ℝ :=
  if 0 < X.1 then Real.exp (-X.1) * gaussKernel d X.1 X.2 else 0

theorem causalKernel_nonneg (X : ℝ × Euc d) : 0 ≤ causalKernel d X := by
  unfold causalKernel
  split_ifs with h
  · exact mul_nonneg (Real.exp_pos _).le (gaussKernel_nonneg h _)
  · exact le_rfl

theorem measurable_causalKernel : Measurable (causalKernel d) := by
  unfold causalKernel gaussKernel
  refine Measurable.ite (measurableSet_lt measurable_const measurable_fst) ?_ measurable_const
  fun_prop

/-- The constant `c_{d,r} = (4π)^{-dr/2} (4π/r)^{d/2}` of the slice identity. -/
def causalConst (d : ℕ) (r : ℝ) : ℝ := (4 * π) ^ (-(d : ℝ) * r / 2) * (4 * π / r) ^ ((d : ℝ) / 2)

theorem causalConst_pos {r : ℝ} (hr : 0 < r) : 0 < causalConst d r := by
  unfold causalConst; positivity

/-- **Slice identity (eq:free-stress-22, inner integral).** For `t > 0`, `r > 0`:
`∫_{ℝ^d} |K(t,y)|^r dy = c_{d,r} t^{-(d/2)(r-1)} e^{-rt}`. -/
theorem integral_causalKernel_rpow_slice {r t : ℝ} (hr : 0 < r) (ht : 0 < t) :
    ∫ y : Euc d, ‖causalKernel d (t, y)‖ ^ r =
      causalConst d r * t ^ (-((d : ℝ) / 2 * (r - 1))) * Real.exp (-r * t) := by
  have hK : ∀ y : Euc d, ‖causalKernel d (t, y)‖ ^ r =
      Real.exp (-r * t) * (((4 * π * t) ^ (-(d : ℝ) / 2)) ^ r *
        Real.exp (-(r / (4 * t)) * ‖y‖ ^ 2)) := by
    intro y
    simp only [causalKernel, ht, ↓reduceIte]
    rw [Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le (gaussKernel_nonneg ht _)),
      Real.mul_rpow (Real.exp_pos _).le (gaussKernel_nonneg ht _), gaussKernel_rpow ht,
      ← Real.exp_mul]
    congr 2; ring
  simp_rw [hK]
  rw [integral_const_mul, integral_const_mul, integral_exp_neg_mul_sq_norm (by positivity),
    show π / (r / (4 * t)) = (4 * π / r) * t by field_simp,
    ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ 4 * π * t),
    Real.mul_rpow (by positivity : (0 : ℝ) ≤ 4 * π) ht.le,
    Real.mul_rpow (by positivity : (0 : ℝ) ≤ 4 * π / r) ht.le, causalConst]
  have e1 : t ^ (-(d : ℝ) / 2 * r) * t ^ ((d : ℝ) / 2) = t ^ (-((d : ℝ) / 2 * (r - 1))) := by
    rw [← Real.rpow_add ht]; congr 1; ring
  have e2 : (4 * π) ^ (-(d : ℝ) / 2 * r) = (4 * π) ^ (-(d : ℝ) * r / 2) := by
    congr 1; ring
  calc Real.exp (-r * t) * ((4 * π) ^ (-(d : ℝ) / 2 * r) * t ^ (-(d : ℝ) / 2 * r) *
        ((4 * π / r) ^ ((d : ℝ) / 2) * t ^ ((d : ℝ) / 2)))
      = (4 * π) ^ (-(d : ℝ) / 2 * r) * (4 * π / r) ^ ((d : ℝ) / 2) *
          (t ^ (-(d : ℝ) / 2 * r) * t ^ ((d : ℝ) / 2)) * Real.exp (-r * t) := by ring
    _ = _ := by rw [e1, e2]

theorem integrable_causalKernel_rpow_slice {r : ℝ} (hr : 0 < r) (t : ℝ) :
    Integrable (fun y : Euc d => ‖causalKernel d (t, y)‖ ^ r) := by
  by_cases ht : 0 < t
  · have : (fun y : Euc d => ‖causalKernel d (t, y)‖ ^ r) = fun y =>
        Real.exp (-r * t) * (((4 * π * t) ^ (-(d : ℝ) / 2)) ^ r *
          Real.exp (-(r / (4 * t)) * ‖y‖ ^ 2)) := by
      funext y
      simp only [causalKernel, ht, ↓reduceIte]
      rw [Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le (gaussKernel_nonneg ht _)),
        Real.mul_rpow (Real.exp_pos _).le (gaussKernel_nonneg ht _), gaussKernel_rpow ht,
        ← Real.exp_mul]
      congr 2; ring
    rw [this]
    exact ((integrable_exp_neg_mul_sq_norm (by positivity)).const_mul _).const_mul _
  · have : (fun y : Euc d => ‖causalKernel d (t, y)‖ ^ r) = fun _ => 0 := by
      funext y; simp [causalKernel, ht, Real.zero_rpow hr.ne']
    rw [this]; exact integrable_zero _ _ _

/-- `t^{-a} e^{-rt}` is integrable on `(0, ∞)` iff `a < 1` (`r > 0`). -/
theorem integrableOn_rpow_neg_mul_exp_iff {a r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun t : ℝ => t ^ (-a) * Real.exp (-r * t)) (Ioi 0) ↔ a < 1 := by
  constructor
  · intro h
    have h1 : IntegrableOn (fun t : ℝ => t ^ (-a)) (Ioo 0 1) := by
      have h' : IntegrableOn (fun t : ℝ => Real.exp r * (t ^ (-a) * Real.exp (-r * t)))
          (Ioo 0 1) := (h.mono_set Ioo_subset_Ioi_self).const_mul _
      refine h'.mono' (Measurable.aestronglyMeasurable (by fun_prop)) ?_
      refine (ae_restrict_iff' measurableSet_Ioo).2 (Filter.Eventually.of_forall fun t ht => ?_)
      have ht0 : 0 < t := ht.1
      rw [Real.norm_of_nonneg (Real.rpow_pos_of_pos ht0 _).le]
      have hexp : 1 ≤ Real.exp r * Real.exp (-r * t) := by
        rw [← Real.exp_add, Real.one_le_exp_iff]; nlinarith [ht.2]
      have hp : 0 < t ^ (-a) := Real.rpow_pos_of_pos ht0 _
      nlinarith
    have := (intervalIntegral.integrableOn_Ioo_rpow_iff one_pos).1 h1
    linarith
  · intro ha
    have := integrableOn_rpow_mul_exp_neg_mul_rpow (s := -a) (p := 1) (b := r) (by linarith)
      one_pos hr
    refine this.congr_fun (fun t ht => ?_) measurableSet_Ioi
    simp [Real.rpow_one]

/-- **INF22 G3, space-time part.** For every dimension `d` and `r > 0`:
`1_{t>0} e^{-t} G_t ∈ L^r(ℝ × ℝ^d)` iff `(d/2)(r-1) < 1`. -/
theorem memLp_causalKernel_iff {r : ℝ} (hr : 0 < r) :
    MemLp (causalKernel d) (ENNReal.ofReal r) volume ↔ (d : ℝ) / 2 * (r - 1) < 1 := by
  have hmeas : AEStronglyMeasurable (causalKernel d) volume :=
    measurable_causalKernel.aestronglyMeasurable
  rw [← integrable_norm_rpow_iff hmeas (by simpa using hr) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hr.le, Measure.volume_eq_prod,
    integrable_prod_iff (by
      rw [← Measure.volume_eq_prod]
      exact (measurable_causalKernel.norm.pow_const r).aestronglyMeasurable)]
  have hslice : ∀ t : ℝ, (∫ y : Euc d, ‖‖causalKernel d (t, y)‖ ^ r‖) =
      (Ioi (0 : ℝ)).indicator (fun t => causalConst d r *
        (t ^ (-((d : ℝ) / 2 * (r - 1))) * Real.exp (-r * t))) t := by
    intro t
    have hn : ∀ y : Euc d, ‖‖causalKernel d (t, y)‖ ^ r‖ = ‖causalKernel d (t, y)‖ ^ r :=
      fun y => Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)
    simp_rw [hn]
    by_cases ht : 0 < t
    · rw [Set.indicator_of_mem (show t ∈ Ioi (0 : ℝ) from ht),
        integral_causalKernel_rpow_slice hr ht, mul_assoc]
    · rw [Set.indicator_of_notMem (show t ∉ Ioi (0 : ℝ) from ht)]
      have : (fun y : Euc d => ‖causalKernel d (t, y)‖ ^ r) = fun _ => 0 := by
        funext y; simp [causalKernel, ht, Real.zero_rpow hr.ne']
      rw [this, integral_zero]
  simp_rw [hslice]
  rw [integrable_indicator_iff measurableSet_Ioi]
  constructor
  · rintro ⟨-, h⟩
    have h' := h.const_mul (causalConst d r)⁻¹
    have hc := (causalConst_pos (d := d) hr).ne'
    simp_rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul] at h'
    exact (integrableOn_rpow_neg_mul_exp_iff hr).1 h'
  · intro h
    exact ⟨Filter.Eventually.of_forall fun t => integrable_causalKernel_rpow_slice hr t,
      ((integrableOn_rpow_neg_mul_exp_iff hr).2 h).const_mul _⟩

/-- **B0448–B0450 (tex 7671–7681).** In `ℝ × ℝ³`, for `r > 0`:
`1_{t>0} e^{-t} G_t ∈ L^r` iff `r < 5/3` (with `r = q'`, iff `q > 5/2`). -/
theorem memLp_causalKernel_three_iff {r : ℝ} (hr : 0 < r) :
    MemLp (causalKernel 3) (ENNReal.ofReal r) volume ↔ r < 5 / 3 := by
  rw [memLp_causalKernel_iff hr]
  constructor <;> intro h <;> push_cast at h ⊢ <;> linarith

end UnforcedLeray.Gaussian
