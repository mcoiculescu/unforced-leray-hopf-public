import UnforcedLeray.Short.PartIIa.Sub.F05_1

/-!
# Part II-a, task `PartII-a:F05a`: the `t`-integral decay

Target: `TIntegralDecay` (defined in `Short/PartII-a/Sub/F05_1.lean`).

Source of record: `the November 2 reference manuscript`, lines 1411-1413
("by the gap"; the substitution `u = e^{-t/2}|y|`).

Proof. Write `g(t) = e^{-at}(1 + e^{-t/2} x)^{-N}`, `A = (1 + x)^{-2a}`.
* `0 ≤ g(t) ≤ e^{-at}` for all `t`, since the base `1 + e^{-t/2} x` is at least `1`.
* For `x > 0`, `g(t) ≤ x^{-N} e^{(N/2 - a) t}`, from `(1 + u)^{-N} ≤ u^{-N}` with `u = e^{-t/2} x`.
* For `x ≤ 1`: `∫ g ≤ ∫ e^{-at} = 1/a ≤ (2^{2a}/a) A`.
* For `x ≥ 1`: split `(0, ∞)` at `T = 2 log(1 + x)`. On `(0, T]` use the second bound and
  `x^{-N} e^{(N-2a) log(1+x)} ≤ 2^N A` (since `1 + x ≤ 2x`). On `(T, ∞)` use the first bound and
  `∫_T^∞ e^{-at} = A / a`.
-/

set_option autoImplicit false

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

namespace TIntegralDecayAux

/-- The integrand is bounded by `e^{-at}` for every real `t` when `x ≥ 0`. -/
lemma g_le_exp (a N x t : ℝ) (hN : 0 ≤ N) (hx : 0 ≤ x) :
    Real.exp (-a * t) * (1 + Real.exp (-t / 2) * x) ^ (-N) ≤ Real.exp (-a * t) := by
  have h1 : (1 : ℝ) ≤ 1 + Real.exp (-t / 2) * x := by
    have := mul_nonneg (Real.exp_pos (-t / 2)).le hx
    linarith
  have h2 : (1 + Real.exp (-t / 2) * x) ^ (-N) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos h1 (by linarith)
  calc Real.exp (-a * t) * (1 + Real.exp (-t / 2) * x) ^ (-N)
      ≤ Real.exp (-a * t) * 1 := mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
    _ = Real.exp (-a * t) := mul_one _

/-- For `x > 0`: `e^{-at}(1 + e^{-t/2} x)^{-N} ≤ x^{-N} e^{(N/2 - a) t}`. -/
lemma g_le_k (a N x t : ℝ) (hN : 0 ≤ N) (hx : 0 < x) :
    Real.exp (-a * t) * (1 + Real.exp (-t / 2) * x) ^ (-N)
      ≤ x ^ (-N) * Real.exp ((N / 2 - a) * t) := by
  have hu : 0 < Real.exp (-t / 2) * x := mul_pos (Real.exp_pos _) hx
  have h1 : (1 + Real.exp (-t / 2) * x) ^ (-N) ≤ (Real.exp (-t / 2) * x) ^ (-N) :=
    Real.rpow_le_rpow_of_nonpos hu (by linarith) (by linarith)
  have h2 : (Real.exp (-t / 2) * x) ^ (-N) = Real.exp (-t / 2 * -N) * x ^ (-N) := by
    rw [Real.mul_rpow (Real.exp_pos _).le hx.le, ← Real.exp_mul]
  have h3 : Real.exp (-a * t) * Real.exp (-t / 2 * -N) = Real.exp ((N / 2 - a) * t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc Real.exp (-a * t) * (1 + Real.exp (-t / 2) * x) ^ (-N)
      ≤ Real.exp (-a * t) * (Real.exp (-t / 2) * x) ^ (-N) :=
        mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
    _ = Real.exp (-a * t) * (Real.exp (-t / 2 * -N) * x ^ (-N)) := by rw [h2]
    _ = (Real.exp (-a * t) * Real.exp (-t / 2 * -N)) * x ^ (-N) := by ring
    _ = Real.exp ((N / 2 - a) * t) * x ^ (-N) := by rw [h3]
    _ = x ^ (-N) * Real.exp ((N / 2 - a) * t) := by ring

lemma base_pos (t x : ℝ) (hx : 0 ≤ x) : 0 < 1 + Real.exp (-t / 2) * x := by
  have := mul_nonneg (Real.exp_pos (-t / 2)).le hx
  linarith

/-- The integrand is integrable on `(0, ∞)`. -/
lemma g_integrableOn (a N x : ℝ) (ha : 0 < a) (hN : 0 ≤ N) (hx : 0 ≤ x) :
    IntegrableOn (fun t : ℝ => Real.exp (-a * t) * (1 + Real.exp (-t / 2) * x) ^ (-N))
      (Ioi 0) := by
  have hr : Continuous (fun t : ℝ => (1 + Real.exp (-t / 2) * x) ^ (-N)) :=
    Continuous.rpow_const (by fun_prop) (fun t => Or.inl (base_pos t x hx).ne')
  have hg : Continuous (fun t : ℝ => Real.exp (-a * t) * (1 + Real.exp (-t / 2) * x) ^ (-N)) :=
    (by fun_prop : Continuous (fun t : ℝ => Real.exp (-a * t))).mul hr
  have hbound : ∀ t : ℝ, ‖Real.exp (-a * t) * (1 + Real.exp (-t / 2) * x) ^ (-N)‖
      ≤ Real.exp (-a * t) := by
    intro t
    have hnn : 0 ≤ Real.exp (-a * t) * (1 + Real.exp (-t / 2) * x) ^ (-N) :=
      mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg (base_pos t x hx).le _)
    rw [Real.norm_of_nonneg hnn]
    exact g_le_exp a N x t hN hx
  exact Integrable.mono' (exp_neg_integrableOn_Ioi 0 ha) hg.aestronglyMeasurable
    (ae_of_all _ hbound)

/-- `∫_{(0,T]} p e^{c t} dt ≤ p e^{cT} / c` for `p ≥ 0`, `c > 0`, `T ≥ 0`. -/
lemma Ioc_exp_le (p c T : ℝ) (hp : 0 ≤ p) (hc : 0 < c) (hT : 0 ≤ T) :
    ∫ t in Ioc (0 : ℝ) T, p * Real.exp (c * t) ≤ p * Real.exp (c * T) / c := by
  have hc0 : c ≠ 0 := hc.ne'
  have hd : ∀ t ∈ uIcc (0 : ℝ) T,
      HasDerivAt (fun s : ℝ => p * Real.exp (c * s) / c) (p * Real.exp (c * t)) t := by
    intro t _
    have h1 : HasDerivAt (fun s : ℝ => c * s) c t := by
      simpa using (hasDerivAt_id t).const_mul c
    have h2 := ((h1.exp).const_mul p).div_const c
    exact h2.congr_deriv (by rw [div_eq_iff hc0]; ring)
  have hint : IntervalIntegrable (fun t : ℝ => p * Real.exp (c * t)) volume 0 T :=
    (by fun_prop : Continuous (fun t : ℝ => p * Real.exp (c * t))).intervalIntegrable 0 T
  rw [← intervalIntegral.integral_of_le hT,
    intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint]
  have h3 : 0 ≤ p / c := div_nonneg hp hc.le
  simp only [mul_zero, Real.exp_zero, mul_one]
  linarith

/-- `∫_{(T,∞)} e^{-at} dt = e^{-aT} / a`. -/
lemma tail_int (a T : ℝ) (ha : 0 < a) :
    ∫ t in Ioi T, Real.exp (-a * t) = Real.exp (-a * T) / a := by
  rw [integral_exp_mul_Ioi (by linarith : -a < 0) T, neg_div_neg_eq]

end TIntegralDecayAux

/-- **The `t`-integral decay** (pure real analysis): for `a > 0`, `N > 2a`,
`∫₀^∞ e^{-at} (1 + e^{-t/2} x)^{-N} dt ≤ C (1 + x)^{-2a}` for all `x ≥ 0`. -/
theorem tIntegralDecay_proof : UnforcedLeray.Short.PartIIa.TIntegralDecay := by
  unfold UnforcedLeray.Short.PartIIa.TIntegralDecay
  intro a N ha hN
  have hN0 : 0 < N := by linarith
  have hc : 0 < N / 2 - a := by linarith
  have hX : 0 ≤ (2 : ℝ) ^ N / (N / 2 - a) :=
    div_nonneg (Real.rpow_nonneg (by norm_num) _) hc.le
  have hY : 0 ≤ (2 : ℝ) ^ (2 * a) / a :=
    div_nonneg (Real.rpow_nonneg (by norm_num) _) ha.le
  have h2a : (1 : ℝ) ≤ (2 : ℝ) ^ (2 * a) := Real.one_le_rpow (by norm_num) (by linarith)
  refine ⟨(2 : ℝ) ^ N / (N / 2 - a) + (2 : ℝ) ^ (2 * a) / a, add_nonneg hX hY, ?_⟩
  intro x hx
  have h1x : (0 : ℝ) < 1 + x := by linarith
  have hA0 : 0 ≤ (1 + x) ^ (-(2 * a)) := Real.rpow_nonneg h1x.le _
  have hint : IntegrableOn
      (fun t : ℝ => Real.exp (-a * t) * (1 + Real.exp (-t / 2) * x) ^ (-N)) (Ioi 0) :=
    TIntegralDecayAux.g_integrableOn a N x ha hN0.le hx
  rcases le_total x 1 with hx1 | hx1
  · -- Case `0 ≤ x ≤ 1`: only the bound `g ≤ e^{-at}` is used.
    have hlog : Real.log (1 + x) ≤ Real.log 2 := Real.log_le_log h1x (by linarith)
    have hpow : (1 : ℝ) ≤ (2 : ℝ) ^ (2 * a) * (1 + x) ^ (-(2 * a)) := by
      rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), Real.rpow_def_of_pos h1x,
        ← Real.exp_add]
      apply Real.one_le_exp
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * a) (sub_nonneg.mpr hlog)]
    calc ∫ t in Ioi (0 : ℝ), Real.exp (-a * t) * (1 + Real.exp (-t / 2) * x) ^ (-N)
        ≤ ∫ t in Ioi (0 : ℝ), Real.exp (-a * t) :=
          setIntegral_mono_on hint (exp_neg_integrableOn_Ioi 0 ha) measurableSet_Ioi
            (fun t _ => TIntegralDecayAux.g_le_exp a N x t hN0.le hx)
      _ = Real.exp (-a * 0) / a := TIntegralDecayAux.tail_int a 0 ha
      _ = 1 / a := by simp
      _ ≤ (2 : ℝ) ^ (2 * a) * (1 + x) ^ (-(2 * a)) / a := div_le_div_of_nonneg_right hpow ha.le
      _ = (2 : ℝ) ^ (2 * a) / a * (1 + x) ^ (-(2 * a)) := by ring
      _ ≤ ((2 : ℝ) ^ N / (N / 2 - a) + (2 : ℝ) ^ (2 * a) / a) * (1 + x) ^ (-(2 * a)) := by
          rw [add_mul]
          have := mul_nonneg hX hA0
          linarith
  · -- Case `x ≥ 1`: split at `T = 2 log(1 + x)`.
    have hx0 : 0 < x := by linarith
    have hT : 0 ≤ 2 * Real.log (1 + x) := by
      have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ 1 + x)
      linarith
    have hlogxx : Real.log (1 + x) ≤ Real.log 2 + Real.log x := by
      rw [← Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hx0.ne']
      exact Real.log_le_log h1x (by linarith)
    have hsplit : Ioi (0 : ℝ) = Ioc 0 (2 * Real.log (1 + x)) ∪ Ioi (2 * Real.log (1 + x)) :=
      (Set.Ioc_union_Ioi_eq_Ioi hT).symm
    have hdisj : Disjoint (Ioc (0 : ℝ) (2 * Real.log (1 + x))) (Ioi (2 * Real.log (1 + x))) :=
      Set.Ioc_disjoint_Ioi_same
    have hI1 : IntegrableOn
        (fun t : ℝ => Real.exp (-a * t) * (1 + Real.exp (-t / 2) * x) ^ (-N))
        (Ioc (0 : ℝ) (2 * Real.log (1 + x))) :=
      hint.mono_set Set.Ioc_subset_Ioi_self
    have hI2 : IntegrableOn
        (fun t : ℝ => Real.exp (-a * t) * (1 + Real.exp (-t / 2) * x) ^ (-N))
        (Ioi (2 * Real.log (1 + x))) :=
      hint.mono_set (Set.Ioi_subset_Ioi hT)
    have hcont : Continuous (fun t : ℝ => x ^ (-N) * Real.exp ((N / 2 - a) * t)) := by
      fun_prop
    have hk : IntegrableOn (fun t : ℝ => x ^ (-N) * Real.exp ((N / 2 - a) * t))
        (Ioc (0 : ℝ) (2 * Real.log (1 + x))) :=
      hcont.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
    rw [hsplit, setIntegral_union hdisj measurableSet_Ioi hI1 hI2]
    have hkey : x ^ (-N) * Real.exp ((N / 2 - a) * (2 * Real.log (1 + x)))
        ≤ (2 : ℝ) ^ N * (1 + x) ^ (-(2 * a)) := by
      rw [Real.rpow_def_of_pos hx0, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2),
        Real.rpow_def_of_pos h1x, ← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg hN0.le (sub_nonneg.mpr hlogxx)]
    have hPA : ∫ t in Ioc (0 : ℝ) (2 * Real.log (1 + x)),
        Real.exp (-a * t) * (1 + Real.exp (-t / 2) * x) ^ (-N)
        ≤ x ^ (-N) * Real.exp ((N / 2 - a) * (2 * Real.log (1 + x))) / (N / 2 - a) := by
      calc ∫ t in Ioc (0 : ℝ) (2 * Real.log (1 + x)),
            Real.exp (-a * t) * (1 + Real.exp (-t / 2) * x) ^ (-N)
          ≤ ∫ t in Ioc (0 : ℝ) (2 * Real.log (1 + x)),
              x ^ (-N) * Real.exp ((N / 2 - a) * t) :=
            setIntegral_mono_on hI1 hk measurableSet_Ioc
              (fun t _ => TIntegralDecayAux.g_le_k a N x t hN0.le hx0)
        _ ≤ x ^ (-N) * Real.exp ((N / 2 - a) * (2 * Real.log (1 + x))) / (N / 2 - a) :=
            TIntegralDecayAux.Ioc_exp_le (x ^ (-N)) (N / 2 - a) (2 * Real.log (1 + x))
              (Real.rpow_nonneg hx0.le _) hc hT
    have hB : ∫ t in Ioi (2 * Real.log (1 + x)),
        Real.exp (-a * t) * (1 + Real.exp (-t / 2) * x) ^ (-N)
        ≤ (1 + x) ^ (-(2 * a)) / a := by
      have hA_eq : (1 + x) ^ (-(2 * a)) = Real.exp (-a * (2 * Real.log (1 + x))) := by
        rw [Real.rpow_def_of_pos h1x]
        congr 1
        ring
      calc ∫ t in Ioi (2 * Real.log (1 + x)),
            Real.exp (-a * t) * (1 + Real.exp (-t / 2) * x) ^ (-N)
          ≤ ∫ t in Ioi (2 * Real.log (1 + x)), Real.exp (-a * t) :=
            setIntegral_mono_on hI2 (exp_neg_integrableOn_Ioi _ ha) measurableSet_Ioi
              (fun t _ => TIntegralDecayAux.g_le_exp a N x t hN0.le hx)
        _ = Real.exp (-a * (2 * Real.log (1 + x))) / a :=
            TIntegralDecayAux.tail_int a _ ha
        _ = (1 + x) ^ (-(2 * a)) / a := by rw [hA_eq]
    calc _ ≤ x ^ (-N) * Real.exp ((N / 2 - a) * (2 * Real.log (1 + x))) / (N / 2 - a)
            + (1 + x) ^ (-(2 * a)) / a := add_le_add hPA hB
      _ ≤ (2 : ℝ) ^ N * (1 + x) ^ (-(2 * a)) / (N / 2 - a) + (1 + x) ^ (-(2 * a)) / a :=
            add_le_add (div_le_div_of_nonneg_right hkey hc.le) le_rfl
      _ = (2 : ℝ) ^ N / (N / 2 - a) * (1 + x) ^ (-(2 * a))
            + 1 / a * (1 + x) ^ (-(2 * a)) := by ring
      _ ≤ (2 : ℝ) ^ N / (N / 2 - a) * (1 + x) ^ (-(2 * a))
            + (2 : ℝ) ^ (2 * a) / a * (1 + x) ^ (-(2 * a)) :=
            add_le_add le_rfl (mul_le_mul_of_nonneg_right
              (div_le_div_of_nonneg_right h2a ha.le) hA0)
      _ = ((2 : ℝ) ^ N / (N / 2 - a) + (2 : ℝ) ^ (2 * a) / a) * (1 + x) ^ (-(2 * a)) := by
            ring

end UnforcedLeray.Short.PartIIa
