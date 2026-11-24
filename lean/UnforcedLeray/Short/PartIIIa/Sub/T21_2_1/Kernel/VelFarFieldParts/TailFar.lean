import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_1_2_7
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_1.Kernel.NearFar

/-!
# Part III-a, far field of the periodic kernel (SP 2084, 3056-3057)

Closed form `K_c(w) = -(1/(2c)) - p/(c(1-p))`, `p = exp(π w I / c)^2`, valid for `Im w > 0`
(from `cot u = -(i)(1+e^{2iu})/(1-e^{2iu})`), so `|K_c - mean shear| ≤ C exp(-(2π/c) Im w)`
on `|Im w| ≥ 1`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- Closed form of the cylinder kernel: `K_c(w) = -(1/(2c)) - ζ²/(c(1-ζ²))`, `ζ = exp(π w I/c)`. -/
theorem cylBS_closed (c : ℝ) (hc : 0 < c) (w : ℂ)
    (hne : 1 - Complex.exp (↑Real.pi * w / ↑c * Complex.I) ^ 2 ≠ 0) :
    UnforcedLeray.Kernels.cylinderBS c w =
      -(1 / (2 * (c : ℂ))) - Complex.exp (↑Real.pi * w / ↑c * Complex.I) ^ 2 /
        ((c : ℂ) * (1 - Complex.exp (↑Real.pi * w / ↑c * Complex.I) ^ 2)) := by
  unfold UnforcedLeray.Kernels.cylinderBS
  rw [Complex.cot_eq_cos_div_sin]
  have hc0 : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  have hc2 := Complex.two_cos (x := (Real.pi : ℂ) * w / (c : ℂ))
  have hs2 := Complex.two_sin (x := (Real.pi : ℂ) * w / (c : ℂ))
  have hneg : Complex.exp (-((Real.pi : ℂ) * w / (c : ℂ)) * Complex.I) =
      (Complex.exp ((Real.pi : ℂ) * w / (c : ℂ) * Complex.I))⁻¹ := by
    rw [neg_mul, Complex.exp_neg]
  rw [hneg] at hc2 hs2
  generalize hζ : Complex.exp ((Real.pi : ℂ) * w / (c : ℂ) * Complex.I) = ζ at hc2 hs2 hne ⊢
  have hζ0 : ζ ≠ 0 := by
    rw [← hζ]; exact Complex.exp_ne_zero _
  have hcos : Complex.cos ((Real.pi : ℂ) * w / (c : ℂ)) = (ζ + ζ⁻¹) / 2 := by
    linear_combination hc2 / 2
  have hsin : Complex.sin ((Real.pi : ℂ) * w / (c : ℂ)) = (ζ⁻¹ - ζ) * Complex.I / 2 := by
    linear_combination hs2 / 2
  rw [hcos, hsin]
  have hinv : ζ⁻¹ - ζ = (1 - ζ ^ 2) / ζ := by
    field_simp
  rw [hinv]
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring

/-- The modulus of `ζ²`: `‖exp(π w I / c)²‖ = exp(-(2π/c) Im w)`. -/
theorem norm_exp_sq_closed (c : ℝ) (hc : 0 < c) (w : ℂ) :
    ‖Complex.exp (↑Real.pi * w / ↑c * Complex.I) ^ 2‖ =
      Real.exp (-(2 * Real.pi / c * w.im)) := by
  have hre : (↑Real.pi * w / ↑c * Complex.I : ℂ).re = -(Real.pi / c * w.im) := by
    have e : (↑Real.pi * w / ↑c * Complex.I : ℂ) = ((Real.pi / c : ℝ) : ℂ) * (w * Complex.I) := by
      push_cast; ring
    rw [e, Complex.re_ofReal_mul, Complex.mul_I_re]
    ring
  rw [norm_pow, Complex.norm_exp, hre, ← Real.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- Far-field bound for the real and imaginary parts of `K_c(w)`, `Im w ≥ 1`. -/
theorem cylBS_far (c : ℝ) (hc : 1 ≤ c) (w : ℂ) (hw : 1 ≤ w.im) :
    |(UnforcedLeray.Kernels.cylinderBS c w).re - (-(1 / (2 * c)))| ≤
        (1 / (c * (1 - Real.exp (-(2 * Real.pi / c))))) * Real.exp (-(2 * Real.pi / c * w.im)) ∧
      |(UnforcedLeray.Kernels.cylinderBS c w).im| ≤
        (1 / (c * (1 - Real.exp (-(2 * Real.pi / c))))) * Real.exp (-(2 * Real.pi / c * w.im)) := by
  have hc0 : 0 < c := by linarith
  have hpos : 0 < 2 * Real.pi / c := by positivity
  have hpn := norm_exp_sq_closed c hc0 w
  have hr0 : Real.exp (-(2 * Real.pi / c)) < 1 := by
    have := Real.exp_lt_exp.2 (show -(2 * Real.pi / c) < 0 by linarith)
    simpa using this
  have hle : ‖Complex.exp (↑Real.pi * w / ↑c * Complex.I) ^ 2‖ ≤
      Real.exp (-(2 * Real.pi / c)) := by
    rw [hpn]
    apply Real.exp_le_exp.2
    nlinarith
  have hne : 1 - Complex.exp (↑Real.pi * w / ↑c * Complex.I) ^ 2 ≠ 0 := by
    intro h
    have h1 : Complex.exp (↑Real.pi * w / ↑c * Complex.I) ^ 2 = 1 := by linear_combination -h
    have h2 : ‖Complex.exp (↑Real.pi * w / ↑c * Complex.I) ^ 2‖ = 1 := by rw [h1, norm_one]
    linarith
  rw [cylBS_closed c hc0 w hne]
  obtain ⟨p, hp⟩ : ∃ p, p = Complex.exp (↑Real.pi * w / ↑c * Complex.I) ^ 2 := ⟨_, rfl⟩
  rw [← hp] at hne hpn hle ⊢
  have hcast : -(1 / (2 * (c : ℂ))) = ((-(1 / (2 * c)) : ℝ) : ℂ) := by push_cast; ring
  rw [hcast]
  have hn1 : 1 - Real.exp (-(2 * Real.pi / c)) ≤ ‖1 - p‖ := by
    have := norm_sub_norm_le (1 : ℂ) p
    rw [norm_one] at this
    linarith
  have hpos1 : 0 < c * (1 - Real.exp (-(2 * Real.pi / c))) := by
    apply mul_pos hc0; linarith
  have hden : c * (1 - Real.exp (-(2 * Real.pi / c))) ≤ c * ‖1 - p‖ :=
    mul_le_mul_of_nonneg_left hn1 hc0.le
  have hv : ‖p / ((c : ℂ) * (1 - p))‖ ≤
      (1 / (c * (1 - Real.exp (-(2 * Real.pi / c))))) * Real.exp (-(2 * Real.pi / c * w.im)) := by
    rw [norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg hc0.le, ← hpn]
    have h3 : ‖p‖ / (c * ‖1 - p‖) ≤ ‖p‖ / (c * (1 - Real.exp (-(2 * Real.pi / c)))) :=
      div_le_div_of_nonneg_left (norm_nonneg _) hpos1 hden
    calc ‖p‖ / (c * ‖1 - p‖) ≤ ‖p‖ / (c * (1 - Real.exp (-(2 * Real.pi / c)))) := h3
      _ = _ := by ring
  constructor
  · rw [Complex.sub_re, Complex.ofReal_re]
    have e : -(1 / (2 * c)) - (p / ((c : ℂ) * (1 - p))).re - -(1 / (2 * c)) =
        -(p / ((c : ℂ) * (1 - p))).re := by ring
    rw [e, abs_neg]
    exact le_trans (Complex.abs_re_le_norm _) hv
  · rw [Complex.sub_im, Complex.ofReal_im, zero_sub, abs_neg]
    exact le_trans (Complex.abs_im_le_norm _) hv

/-- The real and imaginary parts of the kernel, as components. -/
theorem kerD_comp (c : ℝ) (z : ℝ × ℝ) :
    kerD c z 0 = (UnforcedLeray.Kernels.cylinderBS c ((z.1 : ℂ) + (z.2 : ℂ) * Complex.I)).re ∧
    kerD c z 1 = -(UnforcedLeray.Kernels.cylinderBS c ((z.1 : ℂ) + (z.2 : ℂ) * Complex.I)).im := by
  unfold kerD UnforcedLeray.Cyl.bsKernel UnforcedLeray.Cyl.bsC
  constructor <;> simp

/-- **Far field of the periodic kernel** (SP 2084, 3056-3057): for `z.2 ≥ 1`,
`|K_c(z) - meanShear c 1 z| ≤ C_c exp(-(2π/c) z.2)`, `C_c = 1/(c(1 - exp(-2π/c)))`. -/
theorem kerD_far_pos (c : ℝ) (hc : 1 ≤ c) (z : ℝ × ℝ) (hz : 1 ≤ z.2) (j : Fin 2) :
    |kerD c z j - meanShear c 1 z j| ≤
      (1 / (c * (1 - Real.exp (-(2 * Real.pi / c))))) * Real.exp (-(2 * Real.pi / c * z.2)) := by
  have hwim : ((z.1 : ℂ) + (z.2 : ℂ) * Complex.I).im = z.2 := by simp
  have key := cylBS_far c hc ((z.1 : ℂ) + (z.2 : ℂ) * Complex.I) (by rw [hwim]; exact hz)
  rw [hwim] at key
  have hs : Real.sign z.2 = 1 := Real.sign_of_pos (by linarith)
  obtain ⟨h0, h1⟩ := kerD_comp c z
  fin_cases j
  · simpa [meanShear, hs, h0] using key.1
  · simpa [meanShear, h1, abs_neg] using key.2

end UnforcedLeray.Short.IIIa
