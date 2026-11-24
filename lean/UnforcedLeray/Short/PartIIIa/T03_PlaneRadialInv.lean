import UnforcedLeray.Short.PartIIIa.Targets

/-!
# Part III-a: polar coordinates for `PlaneRadialInv` (SP 2790-2795)

`∫_{ℝ²} f(|x'|^{-2}) dx' = π ∫_0^∞ u^{-2} f(u) du`. The proof uses polar coordinates
(`lintegral_comp_polarCoord_symm`), the integral over the angle `(-π, π)` (length `2π`), and the
substitution `u = r^{-2}` on `(0, ∞)` (`lintegral_image_eq_lintegral_abs_deriv_mul`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

/-- `r ↦ (r²)⁻¹` maps `(0, ∞)` onto `(0, ∞)`. -/
lemma planeRadialInv_image_Ioi :
    (fun r : ℝ => (r ^ 2)⁻¹) '' Ioi (0 : ℝ) = Ioi (0 : ℝ) := by
  ext u
  constructor
  · rintro ⟨r, hr, rfl⟩
    have hr' : (0 : ℝ) < r := hr
    exact inv_pos.mpr (pow_pos hr' 2)
  · intro hu
    have hu' : (0 : ℝ) < u := hu
    refine ⟨(Real.sqrt u)⁻¹, inv_pos.mpr (Real.sqrt_pos.mpr hu'), ?_⟩
    have hs : Real.sqrt u ^ 2 = u := Real.sq_sqrt hu'.le
    simp only [inv_pow, inv_inv, hs]

/-- Derivative of `y ↦ (y²)⁻¹` at `r ≠ 0`. -/
lemma planeRadialInv_hasDerivAt (r : ℝ) (hr : r ≠ 0) :
    HasDerivAt (fun y : ℝ => (y ^ 2)⁻¹) (-(2 / r ^ 3)) r := by
  have h := (hasDerivAt_pow 2 r).inv (pow_ne_zero 2 hr)
  refine h.congr_deriv ?_
  rw [show (2 : ℕ) - 1 = 1 from rfl, pow_one, neg_div, neg_inj,
    div_eq_div_iff (pow_ne_zero 2 (pow_ne_zero 2 hr)) (pow_ne_zero 3 hr)]
  push_cast
  ring

/-- `y ↦ (y²)⁻¹` is injective on `(0, ∞)`. -/
lemma planeRadialInv_injOn : InjOn (fun y : ℝ => (y ^ 2)⁻¹) (Ioi (0 : ℝ)) := by
  intro a ha b hb hab
  have ha' : (0 : ℝ) < a := ha
  have hb' : (0 : ℝ) < b := hb
  have h2 : a ^ 2 = b ^ 2 := inv_injective hab
  have h3 : (a - b) * (a + b) = 0 := by
    have e : (a - b) * (a + b) = a ^ 2 - b ^ 2 := by ring
    rw [e, h2, sub_self]
  rcases mul_eq_zero.mp h3 with h | h
  · linarith
  · linarith

/-- The one-dimensional substitution `u = r^{-2}` on `(0, ∞)` (SP 2790-2795). -/
lemma planeRadialInv_lintegral_Ioi (f : ℝ → ℝ≥0∞) :
    ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (u ^ (-2 : ℝ)) * f u =
      ENNReal.ofReal 2 * ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal r * f ((r ^ 2)⁻¹) := by
  have hcv : ∫⁻ u in (fun y : ℝ => (y ^ 2)⁻¹) '' Ioi (0 : ℝ),
        ENNReal.ofReal (u ^ (-2 : ℝ)) * f u =
      ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal |-(2 / r ^ 3)| *
        (ENNReal.ofReal (((r ^ 2)⁻¹) ^ (-2 : ℝ)) * f ((r ^ 2)⁻¹)) :=
    lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioi
      (fun r hr => (planeRadialInv_hasDerivAt r (Set.mem_Ioi.mp hr).ne').hasDerivWithinAt)
      planeRadialInv_injOn _
  rw [planeRadialInv_image_Ioi] at hcv
  rw [hcv, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_congr_fun measurableSet_Ioi ?_
  intro r hr
  have hr' : (0 : ℝ) < r := hr
  have hexp : ((r ^ 2)⁻¹) ^ (-2 : ℝ) = r ^ 4 := by
    rw [Real.rpow_neg (show (0 : ℝ) ≤ (r ^ 2)⁻¹ by positivity), Real.rpow_two, inv_pow, inv_inv]
    ring
  have habs : |-(2 / r ^ 3)| = 2 / r ^ 3 := by
    rw [abs_neg, abs_of_pos (show (0 : ℝ) < 2 / r ^ 3 by positivity)]
  have key : ENNReal.ofReal (2 / r ^ 3) * ENNReal.ofReal (r ^ 4) =
      ENNReal.ofReal 2 * ENNReal.ofReal r := by
    rw [← ENNReal.ofReal_mul (show (0 : ℝ) ≤ 2 / r ^ 3 by positivity),
      ← ENNReal.ofReal_mul (show (0 : ℝ) ≤ 2 by norm_num)]
    congr 1
    rw [div_mul_eq_mul_div, div_eq_iff (pow_ne_zero 3 hr'.ne')]
    ring
  calc ENNReal.ofReal |-(2 / r ^ 3)| *
        (ENNReal.ofReal (((r ^ 2)⁻¹) ^ (-2 : ℝ)) * f ((r ^ 2)⁻¹))
      = (ENNReal.ofReal (2 / r ^ 3) * ENNReal.ofReal (r ^ 4)) * f ((r ^ 2)⁻¹) := by
        rw [habs, hexp]
        ring
    _ = (ENNReal.ofReal 2 * ENNReal.ofReal r) * f ((r ^ 2)⁻¹) := by rw [key]
    _ = ENNReal.ofReal 2 * (ENNReal.ofReal r * f ((r ^ 2)⁻¹)) := by ring

/-- `PlaneRadialInv`: polar coordinates and `u = |x'|^{-2}` (SP 2790-2795):
`∫_{ℝ²} f(|x'|^{-2}) dx' = π ∫_0^∞ u^{-2} f(u) du`. -/
theorem planeRadialInv : UnforcedLeray.Short.IIIa.PlaneRadialInv := by
  unfold PlaneRadialInv
  intro f hf
  have hmeas : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal p.1 * f ((p.1 ^ 2)⁻¹)) :=
    (ENNReal.measurable_ofReal.comp measurable_fst).mul
      (hf.comp ((measurable_fst.pow_const 2).inv))
  have htarget : polarCoord.target = Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi := rfl
  have hsymm : ∀ p : ℝ × ℝ, polarCoord.symm p = (p.1 * Real.cos p.2, p.1 * Real.sin p.2) :=
    fun p => rfl
  have hsc : ∀ p : ℝ × ℝ, (p.1 * Real.cos p.2) ^ 2 + (p.1 * Real.sin p.2) ^ 2 = p.1 ^ 2 := by
    intro p
    linear_combination (p.1 ^ 2) * Real.sin_sq_add_cos_sq p.2
  have hT : MeasurableSet polarCoord.target := by
    rw [htarget]
    exact measurableSet_Ioi.prod measurableSet_Ioo
  calc ∫⁻ x' : ℝ × ℝ, f ((x'.1 ^ 2 + x'.2 ^ 2)⁻¹)
      = ∫⁻ p in polarCoord.target, ENNReal.ofReal p.1 * f ((p.1 ^ 2)⁻¹) := by
        rw [← lintegral_comp_polarCoord_symm (fun x' : ℝ × ℝ => f ((x'.1 ^ 2 + x'.2 ^ 2)⁻¹))]
        refine setLIntegral_congr_fun hT ?_
        intro p _
        simp only [smul_eq_mul, hsymm]
        rw [hsc p]
    _ = ∫⁻ r in Ioi (0 : ℝ), ∫⁻ t in Ioo (-Real.pi) Real.pi,
          ENNReal.ofReal r * f ((r ^ 2)⁻¹) := by
        rw [htarget, MeasureTheory.Measure.volume_eq_prod]
        exact setLIntegral_prod (fun p : ℝ × ℝ => ENNReal.ofReal p.1 * f ((p.1 ^ 2)⁻¹))
          hmeas.aemeasurable
    _ = ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal r * f ((r ^ 2)⁻¹) *
          ENNReal.ofReal (Real.pi - -Real.pi) := by
        simp only [setLIntegral_const, Real.volume_Ioo]
    _ = ENNReal.ofReal Real.pi * ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (u ^ (-2 : ℝ)) * f u := by
        have hC : ENNReal.ofReal (Real.pi - -Real.pi) =
            ENNReal.ofReal Real.pi * ENNReal.ofReal 2 := by
          rw [← ENNReal.ofReal_mul Real.pi_pos.le]
          congr 1
          ring
        rw [planeRadialInv_lintegral_Ioi f, lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, hC]
        ring

end UnforcedLeray.Short.IIIa
