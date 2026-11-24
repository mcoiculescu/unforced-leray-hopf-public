import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Sub.PartIIIb_C_srcL_9_5_1

/-!
# Local `t^{-3}` domination for the jets of `psiF` (source 4178-4186, 4917-4937)

Proves `SCPsiF_dom`.  For `t ≥ 1` the map `L_t y = (t y₀, t y₁, y₂)` has operator norm `≤ t`,
and `psiF Z t = (t • proj₂ ∘ Z) ∘ L_t`.  Around `x₀ ∈ psiU ν` take `ε = cylR x₀ / 4`; on the ball
`cylR ≥ cylR x₀ / 4`, and `|L_t x| ≥ t · cylR x`, so every `k`-th jet (`k ≤ 7`) of `psiF Z t` is
bounded by `B r₀^{-4-k} t^{-3}` with `r₀ = cylR x₀ / 4`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Metric UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The linear map `y ↦ (t y₀, t y₁, y₂)` as a continuous linear map. -/
def psiFdomL (t : ℝ) : Vec3 →L[ℝ] Vec3 :=
  ContinuousLinearMap.pi fun i : Fin 3 =>
    (![t, t, (1 : ℝ)] i) • (ContinuousLinearMap.proj i : Vec3 →L[ℝ] ℝ)

theorem psiFdomL_apply (t : ℝ) (y : Vec3) :
    psiFdomL t y = ![t * y 0, t * y 1, y 2] := by
  funext i
  fin_cases i <;> simp [psiFdomL]

theorem psiFdomL_norm_le {t : ℝ} (ht : 1 ≤ t) : ‖psiFdomL t‖ ≤ t := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by linarith) (fun y => ?_)
  rw [pi_norm_le_iff_of_nonneg (mul_nonneg (by linarith) (norm_nonneg y))]
  have h0 : ‖y 0‖ ≤ ‖y‖ := norm_le_pi_norm (f := y) 0
  have h1 : ‖y 1‖ ≤ ‖y‖ := norm_le_pi_norm (f := y) 1
  have h2 : ‖y 2‖ ≤ ‖y‖ := norm_le_pi_norm (f := y) 2
  intro i
  rw [psiFdomL_apply]
  fin_cases i
  · show ‖t * y 0‖ ≤ t * ‖y‖
    rw [norm_mul, Real.norm_of_nonneg (by linarith : (0:ℝ) ≤ t)]
    exact mul_le_mul_of_nonneg_left h0 (by linarith)
  · show ‖t * y 1‖ ≤ t * ‖y‖
    rw [norm_mul, Real.norm_of_nonneg (by linarith : (0:ℝ) ≤ t)]
    exact mul_le_mul_of_nonneg_left h1 (by linarith)
  · show ‖y 2‖ ≤ t * ‖y‖
    nlinarith [norm_nonneg y]

theorem psiFdom_proj_norm_le :
    ‖(ContinuousLinearMap.proj (2 : Fin 3) : Vec3 →L[ℝ] ℝ)‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun y => ?_)
  rw [one_mul]
  exact norm_le_pi_norm (f := y) 2

theorem psiFdom_eucSq (w : Vec3) : eucSq w = w 0 ^ 2 + w 1 ^ 2 + w 2 ^ 2 := by
  simp [eucSq, Fin.sum_univ_three]

theorem psiFdom_cylR_ball {x₀ x : Vec3} (hx : x ∈ ball x₀ (cylR x₀ / 4)) :
    cylR x₀ / 4 ≤ cylR x := by
  have hd : ‖x - x₀‖ < cylR x₀ / 4 := by
    rw [mem_ball, dist_eq_norm] at hx
    exact hx
  have h0 : |x 0 - x₀ 0| < cylR x₀ / 4 := by
    have := norm_le_pi_norm (f := x - x₀) 0
    rw [Pi.sub_apply, Real.norm_eq_abs] at this
    linarith
  have h1 : |x 1 - x₀ 1| < cylR x₀ / 4 := by
    have := norm_le_pi_norm (f := x - x₀) 1
    rw [Pi.sub_apply, Real.norm_eq_abs] at this
    linarith
  have hA : |x 0| ≤ cylR x := by
    unfold cylR
    exact Real.abs_le_sqrt (by nlinarith [sq_nonneg (x 1)])
  have hB : |x 1| ≤ cylR x := by
    unfold cylR
    exact Real.abs_le_sqrt (by nlinarith [sq_nonneg (x 0)])
  have hC : cylR x₀ ≤ |x₀ 0| + |x₀ 1| := by
    unfold cylR
    calc Real.sqrt (x₀ 0 ^ 2 + x₀ 1 ^ 2)
        ≤ Real.sqrt ((|x₀ 0| + |x₀ 1|) ^ 2) :=
          Real.sqrt_le_sqrt (by
            nlinarith [sq_abs (x₀ 0), sq_abs (x₀ 1),
              mul_nonneg (abs_nonneg (x₀ 0)) (abs_nonneg (x₀ 1))])
      _ = |x₀ 0| + |x₀ 1| := Real.sqrt_sq (by positivity)
  have hi0 : |x₀ 0| - |x 0| ≤ |x 0 - x₀ 0| := by
    have := abs_sub_abs_le_abs_sub (x₀ 0) (x 0)
    rwa [abs_sub_comm] at this
  have hi1 : |x₀ 1| - |x 1| ≤ |x 1 - x₀ 1| := by
    have := abs_sub_abs_le_abs_sub (x₀ 1) (x 1)
    rwa [abs_sub_comm] at this
  linarith

theorem psiFdom_iteratedFDeriv_comp {W : Vec3 → ℝ} {S : Set Vec3} (hS : IsOpen S)
    {N : WithTop ℕ∞} (hW : ContDiffOn ℝ N W S) (g : Vec3 →L[ℝ] Vec3) {x : Vec3}
    (hx : g x ∈ S) {i : ℕ} (hi : (i : WithTop ℕ∞) ≤ N) :
    ‖iteratedFDeriv ℝ i (W ∘ g) x‖ ≤ ‖iteratedFDeriv ℝ i W (g x)‖ * ‖g‖ ^ i := by
  have hpre : IsOpen (g ⁻¹' S) := hS.preimage g.continuous
  have hxp : x ∈ g ⁻¹' S := hx
  have h1 := g.iteratedFDerivWithin_comp_right hW hS.uniqueDiffOn hpre.uniqueDiffOn hx hi
  have e1 : iteratedFDeriv ℝ i (W ∘ g) x = iteratedFDerivWithin ℝ i (W ∘ g) (g ⁻¹' S) x :=
    ((iteratedFDerivWithin_of_isOpen i hpre) hxp).symm
  have e2 : iteratedFDeriv ℝ i W (g x) = iteratedFDerivWithin ℝ i W S (g x) :=
    ((iteratedFDerivWithin_of_isOpen i hS) hx).symm
  rw [e1, h1, e2]
  have h2 := ContinuousMultilinearMap.norm_compContinuousLinearMap_le
    (iteratedFDerivWithin ℝ i W S (g x)) (fun _ : Fin i => g)
  simpa [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using h2

theorem psiFdom_key {t r B : ℝ} (ht : 0 < t) (hr : 0 < r) (k : ℕ) :
    t * (B * (t * r) ^ (-(4:ℝ) - (k:ℝ))) * t ^ k
      = B * r ^ (-(4:ℝ) - (k:ℝ)) * t ^ (-3:ℝ) := by
  have e1 : (t * r) ^ (-(4:ℝ) - (k:ℝ))
      = t ^ (-(4:ℝ) - (k:ℝ)) * r ^ (-(4:ℝ) - (k:ℝ)) := Real.mul_rpow ht.le hr.le
  have e2 : t ^ (-3:ℝ) = t ^ (1:ℝ) * t ^ (-(4:ℝ) - (k:ℝ)) * t ^ (k:ℝ) := by
    rw [← Real.rpow_add ht, ← Real.rpow_add ht]
    congr 1
    ring
  have e3 : t ^ (k:ℝ) = t ^ k := Real.rpow_natCast t k
  rw [e1, e2, e3, Real.rpow_one]
  ring

theorem scPsiF_dom : SCPsiF_dom := by
  intro ν B Z hν hB hZ x₀ hx₀
  obtain ⟨hZ1, hZ2⟩ := hZ
  have hx₀' : ν * (11 / 12) < eucSq x₀ ∧ 0 < cylR x₀ := hx₀
  have hr₀ : 0 < cylR x₀ / 4 := div_pos hx₀'.2 (by norm_num)
  have hS : IsOpen {w : Vec3 | ν * (11 / 12) < eucSq w} :=
    isOpen_lt continuous_const (by unfold eucSq; fun_prop)
  refine ⟨cylR x₀ / 4, hr₀,
    fun t => (∑ j ∈ Finset.range 8, B * (cylR x₀ / 4) ^ (-(4:ℝ) - (j:ℝ))) * t ^ (-3:ℝ),
    ?_, ?_⟩
  · exact Integrable.const_mul
      (integrableOn_Ioi_rpow_of_lt (a := -3) (c := 1) (by norm_num) one_pos) _
  · intro k hk t ht x hx
    obtain ⟨hxU, hxB⟩ := hx
    have hxU' : ν * (11 / 12) < eucSq x ∧ 0 < cylR x := hxU
    have hcyl : cylR x₀ / 4 ≤ cylR x := psiFdom_cylR_ball hxB
    have ht1 : (1:ℝ) ≤ t := ht.le
    have ht0 : (0:ℝ) < t := by linarith
    have hLx0 : psiFdomL t x 0 = t * x 0 := by rw [psiFdomL_apply]; rfl
    have hLx1 : psiFdomL t x 1 = t * x 1 := by rw [psiFdomL_apply]; rfl
    have hLx2 : psiFdomL t x 2 = x 2 := by rw [psiFdomL_apply]; rfl
    have hsq : eucSq x ≤ eucSq (psiFdomL t x) := by
      rw [psiFdom_eucSq, psiFdom_eucSq, hLx0, hLx1, hLx2]
      nlinarith [mul_nonneg (by nlinarith : (0:ℝ) ≤ t ^ 2 - 1)
        (add_nonneg (sq_nonneg (x 0)) (sq_nonneg (x 1)))]
    have hLmem : ν * (11 / 12) < eucSq (psiFdomL t x) := lt_of_lt_of_le hxU'.1 hsq
    have hcx : cylR x ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by
      unfold cylR
      exact Real.sq_sqrt (by positivity)
    have h3 : (cylR x₀ / 4) ^ 2 ≤ x 0 ^ 2 + x 1 ^ 2 := by
      rw [← hcx]
      nlinarith
    have hsq2 : (t * (cylR x₀ / 4)) ^ 2 ≤ eucSq (psiFdomL t x) := by
      rw [psiFdom_eucSq, hLx0, hLx1, hLx2, mul_pow]
      have h4 : t ^ 2 * (cylR x₀ / 4) ^ 2 ≤ t ^ 2 * (x 0 ^ 2 + x 1 ^ 2) :=
        mul_le_mul_of_nonneg_left h3 (sq_nonneg t)
      nlinarith [sq_nonneg (x 2)]
    have hsqrt : t * (cylR x₀ / 4) ≤ Real.sqrt (eucSq (psiFdomL t x)) :=
      (Real.le_sqrt (mul_pos ht0 hr₀).le
        (by rw [psiFdom_eucSq]; positivity)).mpr hsq2
    have hZb := hZ2 k hk (psiFdomL t x) hLmem
    have hpow : (Real.sqrt (eucSq (psiFdomL t x))) ^ (-(4:ℝ) - (k:ℝ))
        ≤ (t * (cylR x₀ / 4)) ^ (-(4:ℝ) - (k:ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (mul_pos ht0 hr₀) hsqrt
        (by have : (0:ℝ) ≤ k := Nat.cast_nonneg k; linarith)
    have hZbound : ‖iteratedFDeriv ℝ k Z (psiFdomL t x)‖
        ≤ B * (t * (cylR x₀ / 4)) ^ (-(4:ℝ) - (k:ℝ)) :=
      hZb.trans (mul_le_mul_of_nonneg_left hpow hB)
    have hZat : ContDiffAt ℝ 7 Z (psiFdomL t x) :=
      hZ1.contDiffAt (hS.mem_nhds hLmem)
    have hQ : ‖iteratedFDeriv ℝ k ((t • (ContinuousLinearMap.proj (2 : Fin 3) :
          Vec3 →L[ℝ] ℝ)) ∘ Z) (psiFdomL t x)‖
        ≤ ‖t • (ContinuousLinearMap.proj (2 : Fin 3) : Vec3 →L[ℝ] ℝ)‖
          * ‖iteratedFDeriv ℝ k Z (psiFdomL t x)‖ :=
      ContinuousLinearMap.norm_iteratedFDeriv_comp_left _ hZat (by exact_mod_cast hk)
    have hQn : ‖t • (ContinuousLinearMap.proj (2 : Fin 3) : Vec3 →L[ℝ] ℝ)‖ ≤ t := by
      rw [norm_smul, Real.norm_of_nonneg ht0.le]
      have := mul_le_mul_of_nonneg_left psiFdom_proj_norm_le ht0.le
      linarith
    have hW : ContDiffOn ℝ 7 ((t • (ContinuousLinearMap.proj (2 : Fin 3) :
          Vec3 →L[ℝ] ℝ)) ∘ Z) {w : Vec3 | ν * (11 / 12) < eucSq w} :=
      (ContinuousLinearMap.contDiff (t • (ContinuousLinearMap.proj (2 : Fin 3) :
          Vec3 →L[ℝ] ℝ))).comp_contDiffOn hZ1
    have hcomp := psiFdom_iteratedFDeriv_comp (i := k) hS hW (psiFdomL t) hLmem
      (by exact_mod_cast hk)
    have hfun : psiF Z t = ((t • (ContinuousLinearMap.proj (2 : Fin 3) :
          Vec3 →L[ℝ] ℝ)) ∘ Z) ∘ psiFdomL t := by
      funext y
      simp [psiF, psiFdomL_apply]
    have hsum : B * (cylR x₀ / 4) ^ (-(4:ℝ) - (k:ℝ))
        ≤ ∑ j ∈ Finset.range 8, B * (cylR x₀ / 4) ^ (-(4:ℝ) - (j:ℝ)) :=
      Finset.single_le_sum
        (f := fun j : ℕ => B * (cylR x₀ / 4) ^ (-(4:ℝ) - (j:ℝ)))
        (fun j _ => mul_nonneg hB (Real.rpow_nonneg hr₀.le _))
        (Finset.mem_range.mpr (by omega))
    show ‖iteratedFDeriv ℝ k (psiF Z t) x‖
      ≤ (∑ j ∈ Finset.range 8, B * (cylR x₀ / 4) ^ (-(4:ℝ) - (j:ℝ))) * t ^ (-3:ℝ)
    rw [hfun]
    calc ‖iteratedFDeriv ℝ k (((t • (ContinuousLinearMap.proj (2 : Fin 3) :
            Vec3 →L[ℝ] ℝ)) ∘ Z) ∘ psiFdomL t) x‖
        ≤ ‖iteratedFDeriv ℝ k ((t • (ContinuousLinearMap.proj (2 : Fin 3) :
            Vec3 →L[ℝ] ℝ)) ∘ Z) (psiFdomL t x)‖ * ‖psiFdomL t‖ ^ k := hcomp
      _ ≤ (‖t • (ContinuousLinearMap.proj (2 : Fin 3) : Vec3 →L[ℝ] ℝ)‖
            * ‖iteratedFDeriv ℝ k Z (psiFdomL t x)‖) * ‖psiFdomL t‖ ^ k :=
          mul_le_mul_of_nonneg_right hQ (by positivity)
      _ ≤ (t * (B * (t * (cylR x₀ / 4)) ^ (-(4:ℝ) - (k:ℝ)))) * t ^ k :=
          mul_le_mul
            (mul_le_mul hQn hZbound (norm_nonneg _) ht0.le)
            (pow_le_pow_left₀ (norm_nonneg _) (psiFdomL_norm_le ht1) k)
            (by positivity)
            (mul_nonneg ht0.le (mul_nonneg hB (Real.rpow_nonneg (mul_pos ht0 hr₀).le _)))
      _ = B * (cylR x₀ / 4) ^ (-(4:ℝ) - (k:ℝ)) * t ^ (-3:ℝ) :=
          psiFdom_key ht0 hr₀ k
      _ ≤ (∑ j ∈ Finset.range 8, B * (cylR x₀ / 4) ^ (-(4:ℝ) - (j:ℝ))) * t ^ (-3:ℝ) :=
          mul_le_mul_of_nonneg_right hsum (Real.rpow_nonneg ht0.le _)

end UnforcedLeray.Short.PartIIIb.Concrete
