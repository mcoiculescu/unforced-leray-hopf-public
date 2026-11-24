import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_2

/-!
# `HeatLerayKSmooth` (`PartIII-b:IIIb-D2/3/1/1/2/2`)

`∫_t^∞ G_a(x) da = Ψ(|x|²/4)` with `Ψ(r) = ∫_t^∞ (4πa)^{-3/2} e^{-r/a} da`, defined for all
real `r`. Differentiation under the integral (dominated by `C a^{-3/2}` on `a ≥ t`) gives
`Ψ ∈ C^∞(ℝ)`, and the second partials of `heatTail` are then `C^3`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The `k`-th `r`-derivative integrand of `Ψ`. -/
def L2hkG (k : ℕ) (a r : ℝ) : ℝ :=
  (-1 / a) ^ k * (4 * Real.pi * a) ^ (-3 / 2 : ℝ) * Real.exp (-r / a)

/-- `Ψ_k(r) = ∫_t^∞ L2hkG k a r da`. -/
def L2hkPsi (t : ℝ) (k : ℕ) (r : ℝ) : ℝ := ∫ a in Ioi t, L2hkG k a r

lemma L2_intPow (t : ℝ) (ht : 0 < t) (c : ℝ) :
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

lemma L2_bound (t : ℝ) (ht : 0 < t) (k : ℕ) (R a r : ℝ) (ha : t ≤ a) (hr : |r| ≤ R) :
    ‖L2hkG k a r‖ ≤ ((1 / t) ^ k * Real.exp (R / t)) * (4 * Real.pi * a) ^ (-3 / 2 : ℝ) := by
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
  have hnorm : ‖L2hkG k a r‖ =
      (1 / a) ^ k * Real.exp (-r / a) * (4 * Real.pi * a) ^ (-3 / 2 : ℝ) := by
    unfold L2hkG
    rw [norm_mul, norm_mul, hq, Real.norm_of_nonneg hP, Real.norm_of_nonneg (Real.exp_pos _).le]
    ring
  rw [hnorm]
  gcongr

lemma L2_hasDeriv (t : ℝ) (ht : 0 < t) (k : ℕ) (a x : ℝ) (ha : t ≤ a) :
    HasDerivAt (fun y => L2hkG k a y) (L2hkG (k + 1) a x) x := by
  have ha0 : 0 < a := lt_of_lt_of_le ht ha
  have h1 : HasDerivAt (fun y : ℝ => -y / a) (-1 / a) x :=
    ((hasDerivAt_id' x).neg).div_const a
  have h2 := (h1.exp).const_mul ((-1 / a) ^ k * (4 * Real.pi * a) ^ (-3 / 2 : ℝ))
  have e : L2hkG (k + 1) a x =
      (-1 / a) ^ k * (4 * Real.pi * a) ^ (-3 / 2 : ℝ) * (Real.exp (-x / a) * (-1 / a)) := by
    unfold L2hkG
    rw [pow_succ]
    ring
  rw [e]
  exact h2

lemma L2_psi_hasDeriv (t : ℝ) (ht : 0 < t) (k : ℕ) (r : ℝ) :
    HasDerivAt (L2hkPsi t k) (L2hkPsi t (k + 1) r) r := by
  have hmeas : ∀ (j : ℕ) (x : ℝ),
      AEStronglyMeasurable (fun a => L2hkG j a x) (volume.restrict (Ioi t)) := by
    intro j x
    refine Measurable.aestronglyMeasurable ?_
    unfold L2hkG
    fun_prop
  have hdom : ∀ (j : ℕ) (R : ℝ), ∀ᵐ a ∂(volume.restrict (Ioi t)), ∀ x : ℝ, |x| ≤ R →
      ‖L2hkG j a x‖ ≤ ((1 / t) ^ j * Real.exp (R / t)) * (4 * Real.pi * a) ^ (-3 / 2 : ℝ) := by
    intro j R
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha x hx
    exact L2_bound t ht j R a x (le_of_lt (Set.mem_Ioi.mp ha)) hx
  have hint : ∀ (j : ℕ) (x : ℝ), Integrable (fun a => L2hkG j a x) (volume.restrict (Ioi t)) := by
    intro j x
    refine Integrable.mono' (L2_intPow t ht ((1 / t) ^ j * Real.exp (|x| / t)))
      (hmeas j x) ?_
    exact (hdom j |x|).mono fun a ha => ha x le_rfl
  have hbound_r : ∀ᵐ a ∂(volume.restrict (Ioi t)), ∀ x ∈ Metric.ball r 1,
      ‖L2hkG (k + 1) a x‖ ≤
        ((1 / t) ^ (k + 1) * Real.exp ((|r| + 1) / t)) * (4 * Real.pi * a) ^ (-3 / 2 : ℝ) := by
    filter_upwards [hdom (k + 1) (|r| + 1)] with a ha x hx
    apply ha x
    rw [Metric.mem_ball, Real.dist_eq] at hx
    have h2 := abs_sub_abs_le_abs_sub x r
    linarith
  have hd : ∀ᵐ a ∂(volume.restrict (Ioi t)), ∀ x ∈ Metric.ball r 1,
      HasDerivAt (fun y => L2hkG k a y) (L2hkG (k + 1) a x) x := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha x _
    exact L2_hasDeriv t ht k a x (le_of_lt (Set.mem_Ioi.mp ha))
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi t))
    (F := fun y a => L2hkG k a y) (F' := fun y a => L2hkG (k + 1) a y) (x₀ := r)
    (bound := fun a => ((1 / t) ^ (k + 1) * Real.exp ((|r| + 1) / t)) * (4 * Real.pi * a) ^ (-3 / 2 : ℝ))
    (Metric.ball_mem_nhds r one_pos)
    (Filter.Eventually.of_forall fun x => hmeas k x)
    (hint k r)
    (hmeas (k + 1) r)
    hbound_r
    (L2_intPow t ht _)
    hd
  unfold L2hkPsi
  exact key.2

lemma L2_psi_contDiff (t : ℝ) (ht : 0 < t) : ContDiff ℝ 5 (L2hkPsi t 0) := by
  have hIter : ∀ m : ℕ, iteratedDeriv m (L2hkPsi t 0) = L2hkPsi t m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [iteratedDeriv_succ, ih]
      funext r
      exact (L2_psi_hasDeriv t ht m r).deriv
  have h : ContDiff ℝ ((5 : ℕ∞) : WithTop ℕ∞) (L2hkPsi t 0) := by
    apply contDiff_of_differentiable_iteratedDeriv
    intro m _
    rw [hIter m]
    intro r
    exact (L2_psi_hasDeriv t ht m r).differentiableAt
  exact_mod_cast h

/-- **`HeatLerayKSmooth`**: `K_t` is `C³` (indeed smooth) on `ℝ³` for `t > 0`. -/
theorem heatLerayKSmooth : HeatLerayKSmooth := by
  intro t ht i j
  have hT : ContDiff ℝ 5 (UnforcedLeray.Short.IIIa.heatTail t) := by
    have hfun : UnforcedLeray.Short.IIIa.heatTail t =
        fun x => L2hkPsi t 0 (‖x‖ ^ 2 / 4) := by
      funext x
      unfold UnforcedLeray.Short.IIIa.heatTail L2hkPsi
      congr 1
      funext a
      unfold UnforcedLeray.Short.IIIa.heatG L2hkG
      have e : -‖x‖ ^ 2 / (4 * a) = -(‖x‖ ^ 2 / 4) / a := by ring
      simp only [pow_zero, one_mul]
      rw [e]
    rw [hfun]
    exact (L2_psi_contDiff t ht).comp (ContDiff.div_const (contDiff_norm_sq ℝ) 4)
  have hG : ContDiff ℝ 3 (fun x => UnforcedLeray.Short.IIIa.heatG t x) := by
    unfold UnforcedLeray.Short.IIIa.heatG
    exact contDiff_const.mul (Real.contDiff_exp.comp (ContDiff.div_const (ContDiff.neg (contDiff_norm_sq ℝ)) _))
  have hg : ContDiff ℝ 4
      (fun y => fderiv ℝ (UnforcedLeray.Short.IIIa.heatTail t) y (coordinateVector j)) :=
    (hT.fderiv_right (m := 4) (by norm_num)).clm_apply contDiff_const
  have hp : ContDiff ℝ 3 (fun x => UnforcedLeray.Short.IIIa.part2
      (UnforcedLeray.Short.IIIa.heatTail t) i j x) := by
    unfold UnforcedLeray.Short.IIIa.part2
    exact (hg.fderiv_right (m := 3) (by norm_num)).clm_apply contDiff_const
  unfold UnforcedLeray.Short.IIIa.heatLerayK
  refine ContDiff.add ?_ hp
  by_cases h : i = j
  · simp only [if_pos h]
    exact hG
  · simp only [if_neg h]
    exact contDiff_const

end UnforcedLeray.Short.PartIIIb.Concrete
