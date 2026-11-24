import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T16_1_1.Defs

/-!
# `PartIII-a:T16/1/1/1` : `HeatLerayKSmoothAll` (`K_t` is `C^∞` for `t > 0`)

Source `the November 2 reference manuscript` lines 3597-3603.
`∫_t^∞ G_a(x) da = Ψ(|x|²/4)` with `Ψ(r) = ∫_t^∞ (4πa)^{-3/2}e^{-r/a} da`; every `r`-derivative
of `Ψ` is again such an integral (differentiation under the integral sign), so `Ψ ∈ C^∞(ℝ)`.
The C^3 argument of `PartIII-b` (`L2.lean`) is copied under the prefix `l1_`, with the
`C^∞` conclusion obtained from `contDiff_of_differentiable_iteratedDeriv` with `n = ∞`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.IIIa

/-- The `k`-th `r`-derivative integrand of `Ψ`. -/
def l1_hkG (k : ℕ) (a r : ℝ) : ℝ :=
  (-1 / a) ^ k * (4 * Real.pi * a) ^ (-3 / 2 : ℝ) * Real.exp (-r / a)

/-- `Ψ_k(r) = ∫_t^∞ l1_hkG k a r da`. -/
def l1_hkPsi (t : ℝ) (k : ℕ) (r : ℝ) : ℝ := ∫ a in Ioi t, l1_hkG k a r

lemma l1_intPow (t : ℝ) (ht : 0 < t) (c : ℝ) :
    IntegrableOn (fun a : ℝ => c * (4 * Real.pi * a) ^ (-3 / 2 : ℝ)) (Ioi t) := by
  have h1 : IntegrableOn (fun a : ℝ => a ^ (-3 / 2 : ℝ)) (Ioi t) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) ht
  have h2 : IntegrableOn
      (fun a : ℝ => c * ((4 * Real.pi) ^ (-3 / 2 : ℝ) * a ^ (-3 / 2 : ℝ))) (Ioi t) :=
    (h1.const_mul ((4 * Real.pi) ^ (-3 / 2 : ℝ))).const_mul c
  refine h2.congr_fun (fun a ha => ?_) measurableSet_Ioi
  have ha0 : 0 < a := lt_trans ht ha
  simp only
  rw [Real.mul_rpow (by positivity) ha0.le]

lemma l1_bound (t : ℝ) (ht : 0 < t) (k : ℕ) (R a r : ℝ) (ha : t ≤ a) (hr : |r| ≤ R) :
    ‖l1_hkG k a r‖ ≤ ((1 / t) ^ k * Real.exp (R / t)) * (4 * Real.pi * a) ^ (-3 / 2 : ℝ) := by
  have ha0 : 0 < a := lt_of_lt_of_le ht ha
  have hR0 : 0 ≤ R := le_trans (abs_nonneg r) hr
  have hA : (1 / a) ^ k ≤ (1 / t) ^ k :=
    pow_le_pow_left₀ (by positivity) (one_div_le_one_div_of_le ht ha) k
  have h1 : -r / a ≤ R / t := by
    have hr' : -r ≤ R := by
      have := (abs_le.mp hr).1
      linarith
    calc -r / a ≤ R / a := div_le_div_of_nonneg_right hr' ha0.le
      _ ≤ R / t := div_le_div_of_nonneg_left hR0 ht ha
  have hB : Real.exp (-r / a) ≤ Real.exp (R / t) := Real.exp_le_exp.mpr h1
  have hP : 0 ≤ (4 * Real.pi * a) ^ (-3 / 2 : ℝ) := Real.rpow_nonneg (by positivity) _
  have hq : ‖(-1 / a) ^ k‖ = (1 / a) ^ k := by
    rw [norm_pow, norm_div, norm_neg, norm_one, Real.norm_of_nonneg ha0.le]
  have hnorm : ‖l1_hkG k a r‖ =
      (1 / a) ^ k * Real.exp (-r / a) * (4 * Real.pi * a) ^ (-3 / 2 : ℝ) := by
    unfold l1_hkG
    rw [norm_mul, norm_mul, hq, Real.norm_of_nonneg hP, Real.norm_of_nonneg (Real.exp_pos _).le]
    ring
  rw [hnorm]
  gcongr

lemma l1_hasDeriv (t : ℝ) (ht : 0 < t) (k : ℕ) (a x : ℝ) (ha : t ≤ a) :
    HasDerivAt (fun y => l1_hkG k a y) (l1_hkG (k + 1) a x) x := by
  have ha0 : 0 < a := lt_of_lt_of_le ht ha
  have h1 : HasDerivAt (fun y : ℝ => -y / a) (-1 / a) x :=
    ((hasDerivAt_id' x).neg).div_const a
  have h2 := (h1.exp).const_mul ((-1 / a) ^ k * (4 * Real.pi * a) ^ (-3 / 2 : ℝ))
  have e : l1_hkG (k + 1) a x =
      (-1 / a) ^ k * (4 * Real.pi * a) ^ (-3 / 2 : ℝ) * (Real.exp (-x / a) * (-1 / a)) := by
    unfold l1_hkG
    rw [pow_succ]
    ring
  rw [e]
  exact h2

lemma l1_psi_hasDeriv (t : ℝ) (ht : 0 < t) (k : ℕ) (r : ℝ) :
    HasDerivAt (l1_hkPsi t k) (l1_hkPsi t (k + 1) r) r := by
  have hmeas : ∀ (j : ℕ) (x : ℝ),
      AEStronglyMeasurable (fun a => l1_hkG j a x) (volume.restrict (Ioi t)) := by
    intro j x
    refine Measurable.aestronglyMeasurable ?_
    unfold l1_hkG
    fun_prop
  have hdom : ∀ (j : ℕ) (R : ℝ), ∀ᵐ a ∂(volume.restrict (Ioi t)), ∀ x : ℝ, |x| ≤ R →
      ‖l1_hkG j a x‖ ≤ ((1 / t) ^ j * Real.exp (R / t)) * (4 * Real.pi * a) ^ (-3 / 2 : ℝ) := by
    intro j R
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha x hx
    exact l1_bound t ht j R a x (le_of_lt (Set.mem_Ioi.mp ha)) hx
  have hint : ∀ (j : ℕ) (x : ℝ), Integrable (fun a => l1_hkG j a x) (volume.restrict (Ioi t)) := by
    intro j x
    refine Integrable.mono' (l1_intPow t ht ((1 / t) ^ j * Real.exp (|x| / t)))
      (hmeas j x) ?_
    exact (hdom j |x|).mono fun a ha => ha x le_rfl
  have hbound_r : ∀ᵐ a ∂(volume.restrict (Ioi t)), ∀ x ∈ Metric.ball r 1,
      ‖l1_hkG (k + 1) a x‖ ≤
        ((1 / t) ^ (k + 1) * Real.exp ((|r| + 1) / t)) * (4 * Real.pi * a) ^ (-3 / 2 : ℝ) := by
    filter_upwards [hdom (k + 1) (|r| + 1)] with a ha x hx
    apply ha x
    rw [Metric.mem_ball, Real.dist_eq] at hx
    have h2 := abs_sub_abs_le_abs_sub x r
    linarith
  have hd : ∀ᵐ a ∂(volume.restrict (Ioi t)), ∀ x ∈ Metric.ball r 1,
      HasDerivAt (fun y => l1_hkG k a y) (l1_hkG (k + 1) a x) x := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha x _
    exact l1_hasDeriv t ht k a x (le_of_lt (Set.mem_Ioi.mp ha))
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi t))
    (F := fun y a => l1_hkG k a y) (F' := fun y a => l1_hkG (k + 1) a y) (x₀ := r)
    (bound := fun a => ((1 / t) ^ (k + 1) * Real.exp ((|r| + 1) / t)) * (4 * Real.pi * a) ^ (-3 / 2 : ℝ))
    (Metric.ball_mem_nhds r one_pos)
    (Filter.Eventually.of_forall fun x => hmeas k x)
    (hint k r)
    (hmeas (k + 1) r)
    hbound_r
    (l1_intPow t ht _)
    hd
  unfold l1_hkPsi
  exact key.2

/-- `Ψ = l1_hkPsi t 0` is `C^∞` on `ℝ` (all `r`-derivatives are `l1_hkPsi t k`). -/
lemma l1_psi_contDiff (t : ℝ) (ht : 0 < t) : ContDiff ℝ ∞ (l1_hkPsi t 0) := by
  have hIter : ∀ m : ℕ, iteratedDeriv m (l1_hkPsi t 0) = l1_hkPsi t m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [iteratedDeriv_succ, ih]
      funext r
      exact (l1_psi_hasDeriv t ht m r).deriv
  apply contDiff_of_differentiable_iteratedDeriv
  intro m _
  rw [hIter m]
  intro r
  exact (l1_psi_hasDeriv t ht m r).differentiableAt

/-- **`PartIII-a:T16/1/1/1`**: `K_t` is `C^∞` on `ℝ³` for every `t > 0` and all `i, j`. -/
theorem heatLerayKSmoothAll : UnforcedLeray.Short.IIIa.HeatLerayKSmoothAll := by
  intro t ht i j
  have hT : ContDiff ℝ ∞ (heatTail t) := by
    have hfun : heatTail t = fun x => l1_hkPsi t 0 (‖x‖ ^ 2 / 4) := by
      funext x
      unfold heatTail l1_hkPsi
      congr 1
      funext a
      unfold heatG l1_hkG
      have e : -‖x‖ ^ 2 / (4 * a) = -(‖x‖ ^ 2 / 4) / a := by ring
      simp only [pow_zero, one_mul]
      rw [e]
    rw [hfun]
    exact (l1_psi_contDiff t ht).comp (ContDiff.div_const (contDiff_norm_sq ℝ) 4)
  have hG : ContDiff ℝ ∞ (fun x => heatG t x) := by
    unfold heatG
    exact contDiff_const.mul (Real.contDiff_exp.comp (ContDiff.div_const (ContDiff.neg (contDiff_norm_sq ℝ)) _))
  have hf1 : ContDiff ℝ ∞ (fun y => fderiv ℝ (heatTail t) y (coordinateVector j)) :=
    (contDiff_infty_iff_fderiv.1 hT).2.clm_apply contDiff_const
  have hp : ContDiff ℝ ∞ (fun x => part2 (heatTail t) i j x) := by
    unfold part2
    exact (contDiff_infty_iff_fderiv.1 hf1).2.clm_apply contDiff_const
  unfold heatLerayK
  refine ContDiff.add ?_ hp
  by_cases h : i = j
  · simp only [if_pos h]
    exact hG
  · simp only [if_neg h]
    exact contDiff_const

end UnforcedLeray.Short.IIIa
