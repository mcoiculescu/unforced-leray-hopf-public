import UnforcedLeray.Short.PartI.Sub.PartI_S11_1_1_2

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray UnforcedLeray.Planar.NUE

/-- Real directional derivative of a complex-differentiable map. -/
theorem origin_fderiv_holo (F : ℂ → ℂ) (F' z v : ℂ) (h : HasDerivAt F F' z) :
    fderiv ℝ F z v = F' * v := by
  have h2 := h.hasFDerivAt.restrictScalars ℝ
  rw [h2.fderiv]
  simp [mul_comm]

/-- The pure second derivatives of a `C²` map whose complex derivative is `g` cancel. -/
theorem origin_lap_holo (f : ℂ → ℂ) (hf : ContDiff ℝ 2 f) (g : ℂ → ℂ)
    (hg : ∀ z, HasDerivAt f (g z) z) (hg' : Differentiable ℂ g) (y : ℂ) :
    iteratedFDeriv ℝ 2 f y ![1, 1] + iteratedFDeriv ℝ 2 f y ![Complex.I, Complex.I] = 0 := by
  have hD : DifferentiableAt ℝ (fderiv ℝ f) y :=
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)) y
  have key : ∀ v w : ℂ, fderiv ℝ (fderiv ℝ f) y v w = deriv g y * w * v := by
    intro v w
    have e1 : fderiv ℝ (fun z => fderiv ℝ f z w) y v = fderiv ℝ (fderiv ℝ f) y v w := by
      rw [fderiv_clm_apply hD (differentiableAt_const w)]
      simp
    have e2 : (fun z => fderiv ℝ f z w) = fun z => g z * w := by
      funext z
      exact origin_fderiv_holo f (g z) z w (hg z)
    rw [← e1, e2]
    have hd : HasDerivAt (fun z => g z * w) (deriv (fun z => g z * w) y) y :=
      ((hg' y).mul_const w).hasDerivAt
    rw [origin_fderiv_holo _ _ y v hd, deriv_mul_const_field]
  rw [iteratedFDeriv_two_apply, iteratedFDeriv_two_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [key 1 1, key Complex.I Complex.I]
  linear_combination (deriv g y) * Complex.I_mul_I

/-- Reflection: second derivatives of `conj ∘ F` are the conjugates of those of `F`. -/
theorem origin_conj_lap (F : ℂ → ℂ) (hF : ContDiff ℝ 2 F) (y : ℂ) :
    iteratedFDeriv ℝ 2 (fun z => (starRingEnd ℂ) (F z)) y ![1, 1] +
        iteratedFDeriv ℝ 2 (fun z => (starRingEnd ℂ) (F z)) y ![Complex.I, Complex.I] =
      (starRingEnd ℂ) (iteratedFDeriv ℝ 2 F y ![1, 1] + iteratedFDeriv ℝ 2 F y ![Complex.I, Complex.I]) := by
  have hc : (fun z => (starRingEnd ℂ) (F z)) = (Complex.conjCLE : ℂ →L[ℝ] ℂ) ∘ F := by
    funext z
    simp
  have h1 : ∀ v : Fin 2 → ℂ, iteratedFDeriv ℝ 2 (fun z => (starRingEnd ℂ) (F z)) y v =
      (starRingEnd ℂ) (iteratedFDeriv ℝ 2 F y v) := by
    intro v
    rw [hc, ContinuousLinearMap.iteratedFDeriv_comp_left (Complex.conjCLE : ℂ →L[ℝ] ℂ) hF.contDiffAt le_rfl]
    simp
  rw [h1, h1, map_add]

/-- Sum of pure second derivatives of `c z^n`. -/
theorem origin_lap_pow (c : ℂ) (n : ℕ) (y : ℂ) :
    iteratedFDeriv ℝ 2 (fun z : ℂ => c * z ^ n) y ![1, 1] +
        iteratedFDeriv ℝ 2 (fun z : ℂ => c * z ^ n) y ![Complex.I, Complex.I] = 0 :=
  origin_lap_holo _ (contDiff_const.mul (contDiff_id.pow n)) (fun z => c * ((n : ℂ) * z ^ (n - 1)))
    (fun z => (hasDerivAt_pow n z).const_mul c) (by fun_prop) y

/-- Sum of pure second derivatives of `c ȳ^n`. -/
theorem origin_lap_conj_pow (c : ℂ) (n : ℕ) (y : ℂ) :
    iteratedFDeriv ℝ 2 (fun z : ℂ => c * (starRingEnd ℂ z) ^ n) y ![1, 1] +
        iteratedFDeriv ℝ 2 (fun z : ℂ => c * (starRingEnd ℂ z) ^ n) y ![Complex.I, Complex.I] = 0 := by
  have hF : (fun z : ℂ => c * (starRingEnd ℂ z) ^ n) =
      fun z => (starRingEnd ℂ) ((starRingEnd ℂ c) * z ^ n) := by
    funext z
    simp
  have hcd : ContDiff ℝ 2 (fun z : ℂ => (starRingEnd ℂ c) * z ^ n) :=
    (contDiff_const.mul (contDiff_id.pow n)).of_le (by first | simp | exact_mod_cast le_top)
  rw [hF, origin_conj_lap _ hcd y, origin_lap_pow _ n y, map_zero]

theorem secOrigin_proof : SecOrigin := by
  intro m c hm
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg m
  · have hn : n ≠ 0 := by
      rintro rfl
      simp at hm
    have hnat : ((n : ℤ)).natAbs = n := by simp
    rw [hnat]
    have hid : Ang.ofProfile (n : ℤ) (fun r : ℝ => c * (r : ℂ) ^ n) = fun y => c * y ^ n := by
      funext y
      by_cases hy : y = 0
      · subst hy
        simp [Ang.ofProfile, Ang.angPhase, zero_pow hn]
      · have hr : ((‖y‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 hy)
        simp only [Ang.ofProfile, Ang.angPhase, zpow_natCast]
        rw [div_pow]
        field_simp
    rw [hid]
    refine ⟨contDiff_const.mul (contDiff_id.pow n), fun y => ?_⟩
    exact origin_lap_pow c n y
  · have hn : n ≠ 0 := by
      rintro rfl
      simp at hm
    have hnat : (-(n : ℤ)).natAbs = n := by simp
    rw [hnat]
    have hid : Ang.ofProfile (-(n : ℤ)) (fun r : ℝ => c * (r : ℂ) ^ n) =
        fun y => c * (starRingEnd ℂ y) ^ n := by
      funext y
      by_cases hy : y = 0
      · subst hy
        simp [Ang.ofProfile, Ang.angPhase, zero_pow hn]
      · have hr : ((‖y‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 hy)
        have h1 : y * (starRingEnd ℂ) y = ((‖y‖ : ℝ) : ℂ) ^ 2 := by
          rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
          push_cast
          ring
        have hc : (starRingEnd ℂ) y = ((‖y‖ : ℝ) : ℂ) ^ 2 / y :=
          eq_div_of_mul_eq hy (by rw [mul_comm]; exact h1)
        simp only [Ang.ofProfile, Ang.angPhase, zpow_neg, zpow_natCast]
        rw [← inv_pow, inv_div, hc]
        simp only [div_pow]
        ring
    rw [hid]
    refine ⟨?_, fun y => ?_⟩
    · exact contDiff_const.mul ((Complex.conjCLE.contDiff).pow n)
    · exact origin_lap_conj_pow c n y

end UnforcedLeray.Short.PartI
