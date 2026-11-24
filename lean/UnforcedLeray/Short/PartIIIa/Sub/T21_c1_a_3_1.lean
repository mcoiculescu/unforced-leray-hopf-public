import UnforcedLeray.Short.PartIIIa.Sub.T21_c1_a_3_of

/-!
# Part III-a, `PartIII-a:T21/c1/a/3/1`: the seed profile is of order two at `0`

Source: `the November 2 reference manuscript`, lines 601-610.
Proves `SeedProfileOrderTwo` (defined in `T21_c1_a_3_of.lean`).

Argument. Let `φ(x) = seedPlanar h x` for real `x`. Then `φ` is smooth, `φ(0) = 0` (the
angular factor `(0/0)^2` vanishes), and `φ` is even: `φ(-r) = h(r) = φ(r)` for `r > 0`, because
`angPhase 2` is `1` on the real axis. Evenness gives `φ'(0) = 0`; the mean value theorem applied
to `φ'` gives `|φ'(t)| ≤ K t` on `[0,1]`; and the fencing theorem with bound `K t²/2` gives
`|φ(t)| ≤ K t²/2` on `[0,1]`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.IIIa.SeedProfileOrderTwoAux

lemma seedPlanar_ofReal_pos (h : ℝ → ℂ) (r : ℝ) (hr : 0 < r) :
    UnforcedLeray.Short.PartI.seedPlanar h (r : ℂ) = h r := by
  have hn : ‖(r : ℂ)‖ = r := by
    rw [Complex.norm_real, Real.norm_of_nonneg hr.le]
  have hz : (r : ℂ) / ((r : ℝ) : ℂ) = 1 := div_self (by exact_mod_cast hr.ne')
  unfold UnforcedLeray.Short.PartI.seedPlanar UnforcedLeray.Planar.NUE.Ang.ofProfile
    UnforcedLeray.Planar.NUE.Ang.angPhase
  rw [hn, hz, one_zpow, mul_one]

lemma seedPlanar_ofReal_neg (h : ℝ → ℂ) (r : ℝ) (hr : 0 < r) :
    UnforcedLeray.Short.PartI.seedPlanar h ((-r : ℝ) : ℂ) = h r := by
  have hn : ‖((-r : ℝ) : ℂ)‖ = r := by
    rw [Complex.norm_real, norm_neg, Real.norm_of_nonneg hr.le]
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hz : ((-r : ℝ) : ℂ) / ((r : ℝ) : ℂ) = -1 := by
    rw [show ((-r : ℝ) : ℂ) = -(r : ℂ) by push_cast; ring, neg_div, div_self hrC]
  unfold UnforcedLeray.Short.PartI.seedPlanar UnforcedLeray.Planar.NUE.Ang.ofProfile
    UnforcedLeray.Planar.NUE.Ang.angPhase
  rw [hn, hz]
  norm_num

lemma seedPlanar_zero_real (h : ℝ → ℂ) :
    UnforcedLeray.Short.PartI.seedPlanar h ((0 : ℝ) : ℂ) = 0 := by
  unfold UnforcedLeray.Short.PartI.seedPlanar UnforcedLeray.Planar.NUE.Ang.ofProfile
    UnforcedLeray.Planar.NUE.Ang.angPhase
  simp

lemma seedPlanar_even_real (h : ℝ → ℂ) (x : ℝ) :
    UnforcedLeray.Short.PartI.seedPlanar h ((-x : ℝ) : ℂ) =
      UnforcedLeray.Short.PartI.seedPlanar h (x : ℂ) := by
  rcases lt_trichotomy x 0 with hx | hx | hx
  · have hy : 0 < -x := by linarith
    have e1 := seedPlanar_ofReal_neg h (-x) hy
    rw [neg_neg] at e1
    rw [e1, seedPlanar_ofReal_pos h (-x) hy]
  · subst hx
    simp
  · rw [seedPlanar_ofReal_neg h x hx, seedPlanar_ofReal_pos h x hx]

/-- Abstract Taylor bound: a smooth even `φ` on `ℝ` with `φ 0 = 0` satisfies
`‖φ t‖ ≤ K t² / 2` on `(0, 1]`. -/
lemma taylor_even_bound (φ : ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ) (h0 : φ 0 = 0)
    (heven : ∀ x, φ (-x) = φ x) :
    ∃ K : ℝ, ∀ t : ℝ, 0 < t → t ≤ 1 → ‖φ t‖ ≤ K * t ^ 2 / 2 := by
  have hdiff : Differentiable ℝ φ := hφ.differentiable (by simp)
  have hd1 : ContDiff ℝ ∞ (deriv φ) := (contDiff_infty_iff_deriv.1 hφ).2
  have hdiff1 : Differentiable ℝ (deriv φ) := hd1.differentiable (by simp)
  have hd2 : ContDiff ℝ ∞ (deriv (deriv φ)) := (contDiff_infty_iff_deriv.1 hd1).2
  have hd0 : deriv φ 0 = 0 := by
    have hfun : (fun x => φ (-x)) = φ := funext heven
    have h1 : deriv (fun x => φ (-x)) 0 = -deriv φ (-0) := deriv_comp_neg φ 0
    rw [hfun, neg_zero] at h1
    linear_combination (1 / 2 : ℂ) * h1
  obtain ⟨K, hK⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).exists_bound_of_continuousOn
    hd2.continuous.continuousOn
  have hgb : ∀ t ∈ Icc (0 : ℝ) 1, ‖deriv φ t‖ ≤ K * t := by
    intro t ht
    have h2 := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_deriv_le
      (f := deriv φ) (fun x _ => hdiff1 x) (fun x hx => hK x hx)
      (left_mem_Icc.2 zero_le_one) ht
    simp only [hd0, sub_zero] at h2
    rw [Real.norm_of_nonneg ht.1] at h2
    exact h2
  have hBderiv : ∀ x : ℝ, HasDerivAt (fun t : ℝ => K * t ^ 2 / 2) (K * x) x := by
    intro x
    have := ((hasDerivAt_pow 2 x).const_mul K).div_const 2
    exact this.congr_deriv (by
      rw [show (2 - 1 : ℕ) = 1 from rfl, pow_one]
      push_cast
      ring)
  refine ⟨K, fun t ht0 ht1 => ?_⟩
  have key := image_norm_le_of_norm_deriv_right_le_deriv_boundary (f := φ) (f' := deriv φ)
    (a := 0) (b := 1) (B := fun t : ℝ => K * t ^ 2 / 2) (B' := fun t : ℝ => K * t)
    hφ.continuous.continuousOn (fun x _ => (hdiff x).hasDerivAt.hasDerivWithinAt)
    (by rw [h0]; simp) hBderiv (fun x hx => hgb x (Ico_subset_Icc_self hx))
  exact key ⟨ht0.le, ht1⟩

end UnforcedLeray.Short.IIIa.SeedProfileOrderTwoAux

open UnforcedLeray.Short.IIIa.SeedProfileOrderTwoAux in
theorem seedProfileOrderTwo_proof : UnforcedLeray.Short.IIIa.SeedProfileOrderTwo := by
  unfold UnforcedLeray.Short.IIIa.SeedProfileOrderTwo
  intro h hsm
  have hφ : ContDiff ℝ ∞ (fun x : ℝ => UnforcedLeray.Short.PartI.seedPlanar h (x : ℂ)) :=
    hsm.comp Complex.ofRealCLM.contDiff
  obtain ⟨K, hK⟩ := taylor_even_bound (fun x : ℝ => UnforcedLeray.Short.PartI.seedPlanar h (x : ℂ))
    hφ (seedPlanar_zero_real h) (fun x => seedPlanar_even_real h x)
  refine ⟨K / 2, fun r hr0 hr1 => ?_⟩
  have h3 : ‖UnforcedLeray.Short.PartI.seedPlanar h (r : ℂ)‖ ≤ K * r ^ 2 / 2 := hK r hr0 hr1
  rw [seedPlanar_ofReal_pos h r hr0] at h3
  linarith [show K * r ^ 2 / 2 = K / 2 * r ^ 2 by ring]
