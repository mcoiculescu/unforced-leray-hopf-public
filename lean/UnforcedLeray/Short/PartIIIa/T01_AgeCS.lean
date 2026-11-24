import UnforcedLeray.Short.PartIIIa.Targets

/-!
# T01: age Cauchy-Schwarz (SP 2753-2758)

Proves `UnforcedLeray.Short.IIIa.AgeCS` (statement in `Targets.lean`): for `A > 0` and a
measurable `h : ℝ → ℝ≥0∞`,
`∫_{(A,∞)} s^{-5/4} h(s) ds ≤ A^{-1/2} (∫_{(A,∞)} s^{-1/2} h(s)² ds)^{1/2}`.

Proof. Write `s^{-5/4} = s^{-1} · s^{-1/4}`, so the integrand is `f · g` with
`f = s^{-1}` and `g = s^{-1/4} h`. Cauchy-Schwarz with exponents `2, 2` on `(A, ∞)` gives
`∫ f g ≤ (∫ f²)^{1/2} (∫ g²)^{1/2}`. Here `∫_A^∞ f² = ∫_A^∞ s^{-2} ds = A^{-1}` and
`g² = s^{-1/2} h²`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

/-- `∫_A^∞ s^{-2} ds = A^{-1}`, in `ℝ≥0∞` form, for `A > 0`. -/
lemma ageCS_lintegral_Ioi_rpow_neg_two {A : ℝ} (hA : 0 < A) :
    ∫⁻ s in Ioi A, ENNReal.ofReal (s ^ (-2 : ℝ)) = ENNReal.ofReal (A ^ (-1 : ℝ)) := by
  have hint : IntegrableOn (fun s : ℝ => s ^ (-2 : ℝ)) (Ioi A) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) hA
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi A)] fun s : ℝ => s ^ (-2 : ℝ) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact Real.rpow_nonneg (le_of_lt (lt_trans hA ht)) _
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn,
    integral_Ioi_rpow_of_lt (a := -2) (by norm_num) hA]
  congr 1
  rw [show (-2 : ℝ) + 1 = -1 by norm_num]
  ring

/-- Cauchy-Schwarz in the age integral (SP 2753-2758), proving `AgeCS`. -/
theorem ageCS : UnforcedLeray.Short.IIIa.AgeCS := by
  unfold AgeCS
  intro A hA h hh
  set f : ℝ → ℝ≥0∞ := fun s => ENNReal.ofReal (s ^ (-1 : ℝ)) with hf
  set g : ℝ → ℝ≥0∞ := fun s => ENNReal.ofReal (s ^ (-1 / 4 : ℝ)) * h s with hg
  have hfm : AEMeasurable f (volume.restrict (Ioi A)) :=
    (measurable_id.pow_const _).ennreal_ofReal.aemeasurable
  have hgm : AEMeasurable g (volume.restrict (Ioi A)) :=
    ((measurable_id.pow_const _).ennreal_ofReal.mul hh).aemeasurable
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict (Ioi A))
    Real.HolderConjugate.two_two hfm hgm
  -- the integrand splits as `f * g`
  have e1 : ∫⁻ s in Ioi A, ENNReal.ofReal (s ^ (-5 / 4 : ℝ)) * h s =
      ∫⁻ s in Ioi A, (f * g) s := by
    refine setLIntegral_congr_fun measurableSet_Ioi (fun s hs => ?_)
    have hs0 : 0 < s := lt_trans hA hs
    simp only [Pi.mul_apply, hf, hg]
    rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.rpow_nonneg hs0.le _), ← Real.rpow_add hs0]
    norm_num
  -- `∫ f² = A^{-1}`
  have e2 : ∫⁻ s in Ioi A, f s ^ (2 : ℝ) = ENNReal.ofReal (A ^ (-1 : ℝ)) := by
    rw [← ageCS_lintegral_Ioi_rpow_neg_two hA]
    refine setLIntegral_congr_fun measurableSet_Ioi (fun s hs => ?_)
    have hs0 : 0 < s := lt_trans hA hs
    simp only [hf]
    rw [ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg hs0.le _) (by norm_num : (0:ℝ) ≤ 2),
      ← Real.rpow_mul hs0.le]
    norm_num
  -- `∫ g² = ∫ s^{-1/2} h²`
  have e3 : ∫⁻ s in Ioi A, g s ^ (2 : ℝ) =
      ∫⁻ s in Ioi A, ENNReal.ofReal (s ^ (-1 / 2 : ℝ)) * h s ^ (2 : ℝ) := by
    refine setLIntegral_congr_fun measurableSet_Ioi (fun s hs => ?_)
    have hs0 : 0 < s := lt_trans hA hs
    simp only [hg]
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 2),
      ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg hs0.le _) (by norm_num : (0:ℝ) ≤ 2),
      ← Real.rpow_mul hs0.le]
    norm_num
  -- `(A^{-1})^{1/2} = A^{-1/2}`
  have e4 : (ENNReal.ofReal (A ^ (-1 : ℝ))) ^ (1 / 2 : ℝ) =
      ENNReal.ofReal (A ^ (-1 / 2 : ℝ)) := by
    rw [ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg hA.le _) (by norm_num : (0:ℝ) ≤ 1 / 2),
      ← Real.rpow_mul hA.le]
    norm_num
  rw [e1]
  rw [e2, e3, e4] at hH
  exact hH

end UnforcedLeray.Short.IIIa
