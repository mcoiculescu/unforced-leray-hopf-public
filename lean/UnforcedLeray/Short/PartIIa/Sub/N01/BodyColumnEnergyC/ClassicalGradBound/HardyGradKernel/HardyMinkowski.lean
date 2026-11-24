import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N01_9_1_3_3_2_1_3

/-!
# `PartII-a:N01/9/1/3/3/2/1/3/3`: `HardyMinkowski`

Source `the November 2 reference manuscript`
lines 3541-3552.  Cauchy-Schwarz with the weight `t^{1/4}` (split `w Φ(ts) = √(w t^{1/4}) √(w t^{-1/4} Φ(ts)²)`),
Tonelli in `(s,t)`, and the dilation identity
`∫_{s>0} s^{-3/2} Φ(ts)² ds = t^{1/2} ∫_{σ>0} σ^{-3/2} Φ(σ)² dσ`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIa.N01

lemma hm_half_sq (x : ℝ≥0∞) : (x ^ (1 / 2 : ℝ)) ^ (2:ℕ) = x := by
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num

lemma hm_sq_rpow_half (x : ℝ≥0∞) : (x ^ (2:ℕ)) ^ (1 / 2 : ℝ) = x := by
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num

/-- Cauchy-Schwarz in the form `(∫ F)² ≤ (∫ P)(∫ Q)` when `F = √P √Q` almost everywhere. -/
lemma hm_cs {α : Type*} [MeasurableSpace α] (μ : Measure α) (P Q F : α → ℝ≥0∞)
    (hP : Measurable P) (hQ : Measurable Q)
    (hF : ∀ᵐ x ∂μ, F x = P x ^ (1 / 2 : ℝ) * Q x ^ (1 / 2 : ℝ)) :
    (∫⁻ x, F x ∂μ) ^ (2:ℕ) ≤ (∫⁻ x, P x ∂μ) * ∫⁻ x, Q x ∂μ := by
  have hf : AEMeasurable (fun x => P x ^ (1 / 2 : ℝ)) μ := (hP.pow_const _).aemeasurable
  have hg : AEMeasurable (fun x => Q x ^ (1 / 2 : ℝ)) μ := (hQ.pow_const _).aemeasurable
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two hf hg
  have hP2 : ∀ x, (P x ^ (1 / 2 : ℝ)) ^ (2:ℝ) = P x := fun x => by
    rw [← ENNReal.rpow_mul]; norm_num
  have hQ2 : ∀ x, (Q x ^ (1 / 2 : ℝ)) ^ (2:ℝ) = Q x := fun x => by
    rw [← ENNReal.rpow_mul]; norm_num
  have h' : ∫⁻ x, F x ∂μ ≤ (∫⁻ x, P x ∂μ) ^ (1 / 2 : ℝ) * (∫⁻ x, Q x ∂μ) ^ (1 / 2 : ℝ) := by
    calc ∫⁻ x, F x ∂μ = ∫⁻ x, P x ^ (1 / 2 : ℝ) * Q x ^ (1 / 2 : ℝ) ∂μ := lintegral_congr_ae hF
      _ ≤ (∫⁻ x, (P x ^ (1 / 2 : ℝ)) ^ (2:ℝ) ∂μ) ^ (1 / (2:ℝ)) *
            (∫⁻ x, (Q x ^ (1 / 2 : ℝ)) ^ (2:ℝ) ∂μ) ^ (1 / (2:ℝ)) := h
      _ = (∫⁻ x, P x ∂μ) ^ (1 / 2 : ℝ) * (∫⁻ x, Q x ∂μ) ^ (1 / 2 : ℝ) := by
          simp only [hP2, hQ2]
  calc (∫⁻ x, F x ∂μ) ^ (2:ℕ)
      ≤ ((∫⁻ x, P x ∂μ) ^ (1 / 2 : ℝ) * (∫⁻ x, Q x ∂μ) ^ (1 / 2 : ℝ)) ^ (2:ℕ) := by gcongr
    _ = (∫⁻ x, P x ∂μ) * ∫⁻ x, Q x ∂μ := by rw [mul_pow, hm_half_sq, hm_half_sq]

/-- Dilation: `∫_{s>0} s^{-3/2} Φ(ts)² ds = t^{1/2} ∫_{σ>0} σ^{-3/2} Φ(σ)² dσ` for `t > 0`. -/
lemma hm_dil (t : ℝ) (ht : 0 < t) (Φ : ℝ → ℝ≥0∞) :
    ∫⁻ s in Ioi (0:ℝ), ENNReal.ofReal (s ^ (-(3 / 2 : ℝ))) * Φ (t * s) ^ (2:ℕ) =
      ENNReal.ofReal (t ^ (1 / 2 : ℝ)) *
        ∫⁻ σ in Ioi (0:ℝ), ENNReal.ofReal (σ ^ (-(3 / 2 : ℝ))) * Φ σ ^ (2:ℕ) := by
  have himg : (fun x : ℝ => t * x) '' Ioi (0:ℝ) = Ioi 0 := by
    rw [Set.image_mul_left_Ioi ht]; simp
  have hcov := lintegral_image_eq_lintegral_abs_deriv_mul (f := fun x : ℝ => t * x)
    (f' := fun _ => t) (s := Ioi (0:ℝ))
    (g := fun σ => ENNReal.ofReal (σ ^ (-(3 / 2 : ℝ))) * Φ σ ^ (2:ℕ)) measurableSet_Ioi
    (fun x _ => by simpa using ((hasDerivAt_id' x).const_mul t).hasDerivWithinAt)
    (fun x _ y _ hxy => mul_left_cancel₀ ht.ne' hxy)
  rw [himg, abs_of_pos ht] at hcov
  have h2 : ∫⁻ x in Ioi (0:ℝ), ENNReal.ofReal t *
      (ENNReal.ofReal ((t * x) ^ (-(3 / 2 : ℝ))) * Φ (t * x) ^ (2:ℕ)) =
      ENNReal.ofReal (t ^ (-(1 / 2 : ℝ))) *
        ∫⁻ s in Ioi (0:ℝ), ENNReal.ofReal (s ^ (-(3 / 2 : ℝ))) * Φ (t * s) ^ (2:ℕ) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine setLIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
    have hx0 : 0 < x := hx
    rw [Real.mul_rpow ht.le hx0.le, ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _)]
    have hpow : t ^ (-(1 / 2 : ℝ)) = t * t ^ (-(3 / 2 : ℝ)) := by
      rw [show (-(1 / 2 : ℝ)) = 1 + (-(3 / 2 : ℝ)) by norm_num, Real.rpow_add ht, Real.rpow_one]
    have hc : ENNReal.ofReal t * ENNReal.ofReal (t ^ (-(3 / 2 : ℝ))) =
        ENNReal.ofReal (t ^ (-(1 / 2 : ℝ))) := by
      rw [← ENNReal.ofReal_mul ht.le, hpow]
    rw [← hc]
    ring
  have hCJ : ∫⁻ σ in Ioi (0:ℝ), ENNReal.ofReal (σ ^ (-(3 / 2 : ℝ))) * Φ σ ^ (2:ℕ) =
      ENNReal.ofReal (t ^ (-(1 / 2 : ℝ))) *
        ∫⁻ s in Ioi (0:ℝ), ENNReal.ofReal (s ^ (-(3 / 2 : ℝ))) * Φ (t * s) ^ (2:ℕ) :=
    hcov.trans h2
  have hprod : t ^ (1 / 2 : ℝ) * t ^ (-(1 / 2 : ℝ)) = 1 := by
    rw [← Real.rpow_add ht]; norm_num
  rw [hCJ, ← mul_assoc, ← ENNReal.ofReal_mul (Real.rpow_nonneg ht.le (1 / 2)), hprod,
    ENNReal.ofReal_one, one_mul]

theorem hardyMinkowski : UnforcedLeray.Short.PartIIa.N01.HardyMinkowski := by
  intro w hw Φ hΦ
  -- Cauchy-Schwarz for each `s`.
  have hcs : ∀ s : ℝ, (∫⁻ t in Ioo (0:ℝ) 1, w t * Φ (t * s)) ^ (2:ℕ) ≤
      (∫⁻ t in Ioo (0:ℝ) 1, w t * ENNReal.ofReal (t ^ (1 / 4 : ℝ))) *
        ∫⁻ t in Ioo (0:ℝ) 1, w t * ENNReal.ofReal (t ^ (-(1 / 4 : ℝ))) * Φ (t * s) ^ (2:ℕ) := by
    intro s
    refine hm_cs (volume.restrict (Ioo (0:ℝ) 1))
      (fun t => w t * ENNReal.ofReal (t ^ (1 / 4 : ℝ)))
      (fun t => w t * ENNReal.ofReal (t ^ (-(1 / 4 : ℝ))) * Φ (t * s) ^ (2:ℕ))
      (fun t => w t * Φ (t * s)) ?_ ?_ ?_
    · fun_prop
    · fun_prop
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      have h0 : 0 < t := ht.1
      have hm : ENNReal.ofReal (t ^ (1 / 4 : ℝ)) * ENNReal.ofReal (t ^ (-(1 / 4 : ℝ))) = 1 := by
        rw [← ENNReal.ofReal_mul (Real.rpow_nonneg h0.le _), ← Real.rpow_add h0]; norm_num
      have hPQ : (w t * ENNReal.ofReal (t ^ (1 / 4 : ℝ))) *
          (w t * ENNReal.ofReal (t ^ (-(1 / 4 : ℝ))) * Φ (t * s) ^ (2:ℕ)) =
          (w t * Φ (t * s)) ^ (2:ℕ) := by
        calc _ = w t ^ (2:ℕ) * (ENNReal.ofReal (t ^ (1 / 4 : ℝ)) *
                ENNReal.ofReal (t ^ (-(1 / 4 : ℝ)))) * Φ (t * s) ^ (2:ℕ) := by ring
          _ = _ := by rw [hm]; ring
      show w t * Φ (t * s) = (w t * ENNReal.ofReal (t ^ (1 / 4 : ℝ))) ^ (1 / 2 : ℝ) *
        (w t * ENNReal.ofReal (t ^ (-(1 / 4 : ℝ))) * Φ (t * s) ^ (2:ℕ)) ^ (1 / 2 : ℝ)
      rw [← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 1 / 2), hPQ, hm_sq_rpow_half]
  -- Measurability of the joint integrand.
  have hF : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal (p.1 ^ (-(3 / 2 : ℝ))) *
      (w p.2 * ENNReal.ofReal (p.2 ^ (-(1 / 4 : ℝ))) * Φ (p.2 * p.1) ^ (2:ℕ))) := by
    fun_prop
  have hmeas : Measurable (fun s : ℝ => ∫⁻ t in Ioo (0:ℝ) 1,
      ENNReal.ofReal (s ^ (-(3 / 2 : ℝ))) *
        (w t * ENNReal.ofReal (t ^ (-(1 / 4 : ℝ))) * Φ (t * s) ^ (2:ℕ))) :=
    hF.lintegral_prod_right'
  have hAE : AEMeasurable (Function.uncurry fun (s t : ℝ) => ENNReal.ofReal (s ^ (-(3 / 2 : ℝ))) *
      (w t * ENNReal.ofReal (t ^ (-(1 / 4 : ℝ))) * Φ (t * s) ^ (2:ℕ)))
      ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioo (0:ℝ) 1))) :=
    hF.aemeasurable
  have hwA : Measurable (fun t : ℝ => w t * ENNReal.ofReal (t ^ (1 / 4 : ℝ))) := by fun_prop
  calc (∫⁻ s in Ioi (0:ℝ), ENNReal.ofReal (s ^ (-(3 / 2 : ℝ))) *
          (∫⁻ t in Ioo (0:ℝ) 1, w t * Φ (t * s)) ^ (2:ℕ))
      ≤ ∫⁻ s in Ioi (0:ℝ), ENNReal.ofReal (s ^ (-(3 / 2 : ℝ))) *
          ((∫⁻ t in Ioo (0:ℝ) 1, w t * ENNReal.ofReal (t ^ (1 / 4 : ℝ))) *
            ∫⁻ t in Ioo (0:ℝ) 1, w t * ENNReal.ofReal (t ^ (-(1 / 4 : ℝ))) * Φ (t * s) ^ (2:ℕ)) :=
        lintegral_mono (fun s => by gcongr; exact hcs s)
    _ = ∫⁻ s in Ioi (0:ℝ), (∫⁻ t in Ioo (0:ℝ) 1, w t * ENNReal.ofReal (t ^ (1 / 4 : ℝ))) *
          ∫⁻ t in Ioo (0:ℝ) 1, ENNReal.ofReal (s ^ (-(3 / 2 : ℝ))) *
            (w t * ENNReal.ofReal (t ^ (-(1 / 4 : ℝ))) * Φ (t * s) ^ (2:ℕ)) := by
        refine lintegral_congr (fun s => ?_)
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        ring
    _ = (∫⁻ t in Ioo (0:ℝ) 1, w t * ENNReal.ofReal (t ^ (1 / 4 : ℝ))) *
          ∫⁻ s in Ioi (0:ℝ), ∫⁻ t in Ioo (0:ℝ) 1, ENNReal.ofReal (s ^ (-(3 / 2 : ℝ))) *
            (w t * ENNReal.ofReal (t ^ (-(1 / 4 : ℝ))) * Φ (t * s) ^ (2:ℕ)) :=
        lintegral_const_mul _ hmeas
    _ = (∫⁻ t in Ioo (0:ℝ) 1, w t * ENNReal.ofReal (t ^ (1 / 4 : ℝ))) *
          ∫⁻ t in Ioo (0:ℝ) 1, ∫⁻ s in Ioi (0:ℝ), ENNReal.ofReal (s ^ (-(3 / 2 : ℝ))) *
            (w t * ENNReal.ofReal (t ^ (-(1 / 4 : ℝ))) * Φ (t * s) ^ (2:ℕ)) := by
        rw [lintegral_lintegral_swap hAE]
    _ = (∫⁻ t in Ioo (0:ℝ) 1, w t * ENNReal.ofReal (t ^ (1 / 4 : ℝ))) *
          ∫⁻ t in Ioo (0:ℝ) 1, w t * ENNReal.ofReal (t ^ (-(1 / 4 : ℝ))) *
            (ENNReal.ofReal (t ^ (1 / 2 : ℝ)) *
              ∫⁻ σ in Ioi (0:ℝ), ENNReal.ofReal (σ ^ (-(3 / 2 : ℝ))) * Φ σ ^ (2:ℕ)) := by
        congr 1
        refine setLIntegral_congr_fun measurableSet_Ioo (fun t ht => ?_)
        have hwt : ∫⁻ s in Ioi (0:ℝ), ENNReal.ofReal (s ^ (-(3 / 2 : ℝ))) *
            (w t * ENNReal.ofReal (t ^ (-(1 / 4 : ℝ))) * Φ (t * s) ^ (2:ℕ)) =
            (w t * ENNReal.ofReal (t ^ (-(1 / 4 : ℝ)))) *
              ∫⁻ s in Ioi (0:ℝ), ENNReal.ofReal (s ^ (-(3 / 2 : ℝ))) * Φ (t * s) ^ (2:ℕ) := by
          calc _ = ∫⁻ s in Ioi (0:ℝ), (w t * ENNReal.ofReal (t ^ (-(1 / 4 : ℝ)))) *
                (ENNReal.ofReal (s ^ (-(3 / 2 : ℝ))) * Φ (t * s) ^ (2:ℕ)) :=
                lintegral_congr (fun s => by ring)
            _ = _ := lintegral_const_mul _ (by fun_prop)
        rw [hwt, hm_dil t ht.1 Φ]
    _ = (∫⁻ t in Ioo (0:ℝ) 1, w t * ENNReal.ofReal (t ^ (1 / 4 : ℝ))) *
          ∫⁻ t in Ioo (0:ℝ) 1, w t * ENNReal.ofReal (t ^ (1 / 4 : ℝ)) *
            (∫⁻ σ in Ioi (0:ℝ), ENNReal.ofReal (σ ^ (-(3 / 2 : ℝ))) * Φ σ ^ (2:ℕ)) := by
        congr 1
        refine setLIntegral_congr_fun measurableSet_Ioo (fun t ht => ?_)
        have h0 : 0 < t := ht.1
        have e : ENNReal.ofReal (t ^ (-(1 / 4 : ℝ))) * ENNReal.ofReal (t ^ (1 / 2 : ℝ)) =
            ENNReal.ofReal (t ^ (1 / 4 : ℝ)) := by
          rw [← ENNReal.ofReal_mul (Real.rpow_nonneg h0.le _), ← Real.rpow_add h0]; norm_num
        calc _ = w t * (ENNReal.ofReal (t ^ (-(1 / 4 : ℝ))) * ENNReal.ofReal (t ^ (1 / 2 : ℝ))) *
                (∫⁻ σ in Ioi (0:ℝ), ENNReal.ofReal (σ ^ (-(3 / 2 : ℝ))) * Φ σ ^ (2:ℕ)) := by ring
          _ = _ := by rw [e]
    _ = (∫⁻ t in Ioo (0:ℝ) 1, w t * ENNReal.ofReal (t ^ (1 / 4 : ℝ))) *
          ((∫⁻ t in Ioo (0:ℝ) 1, w t * ENNReal.ofReal (t ^ (1 / 4 : ℝ))) *
            ∫⁻ σ in Ioi (0:ℝ), ENNReal.ofReal (σ ^ (-(3 / 2 : ℝ))) * Φ σ ^ (2:ℕ)) := by
        congr 1
        exact lintegral_mul_const _ hwA
    _ = (∫⁻ t in Ioo (0:ℝ) 1, w t * ENNReal.ofReal (t ^ (1 / 4 : ℝ))) ^ (2:ℕ) *
          ∫⁻ σ in Ioi (0:ℝ), ENNReal.ofReal (σ ^ (-(3 / 2 : ℝ))) * Φ σ ^ (2:ℕ) := by ring

end UnforcedLeray.Short.PartIIa.N01
