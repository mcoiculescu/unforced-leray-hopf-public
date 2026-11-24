import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_1_2_5
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_1.Kernel.DivPointwiseParts.RegSmooth

/-!
# Leaf `PartIII-a:T21/2/1/2/5/2`: the derivatives of the regularised stream function

Source of record: `the November 2 reference manuscript` lines 2081-2084, 3121.
`kerReg d ε z = (4π)⁻¹ log (den d z + ε)`, `den d z = cosh(2πη/d) - cos(2πq/d)`, and
`kerD d z j` is the `j`-th component of the cylinder kernel `Cyl.bsKernel d z`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- Algebra of the cylinder kernel: `(2πi)⁻¹ (π/d) (a - ib)/q = (-b - ia)/(2dq)`. -/
theorem final_alg (d p a b q : ℝ) (hd : d ≠ 0) (hp : p ≠ 0) (hq : q ≠ 0) :
    (2 * (p : ℂ) * Complex.I)⁻¹ * (((p : ℂ) / (d : ℂ)) *
      (((a : ℂ) - (b : ℂ) * Complex.I) / (q : ℂ))) =
      ((-b / (2 * d * q) : ℝ) : ℂ) + ((-(a / (2 * d * q)) : ℝ) : ℂ) * Complex.I := by
  have hdc : (d : ℂ) ≠ 0 := by exact_mod_cast hd
  have hpc : (p : ℂ) ≠ 0 := by exact_mod_cast hp
  have hqc : (q : ℂ) ≠ 0 := by exact_mod_cast hq
  have hIc : Complex.I ≠ 0 := Complex.I_ne_zero
  push_cast
  field_simp
  ring_nf
  simp only [Complex.I_sq]
  ring_nf

/-- Off the lattice, the cylinder kernel `K = (2πi)⁻¹ (π/d) cot(π z/d)` has the explicit real and
imaginary parts of `(2 d den)⁻¹ (-sinh(2πη/d) - i sin(2πq/d))`. -/
theorem cyl_formula (d : ℝ) (hd : d ≠ 0) (z1 z2 : ℝ)
    (hden : UnforcedLeray.B0592.den d (z1, z2) ≠ 0) :
    UnforcedLeray.Cyl.bsC d (z1, z2) =
      ((-Real.sinh (2 * Real.pi * z2 / d) / (2 * d * UnforcedLeray.B0592.den d (z1, z2)) : ℝ) : ℂ) +
      ((-(Real.sin (2 * Real.pi * z1 / d) / (2 * d * UnforcedLeray.B0592.den d (z1, z2))) : ℝ) : ℂ)
        * Complex.I := by
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = Real.pi * z1 / d := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y : ℝ, y = Real.pi * z2 / d := ⟨_, rfl⟩
  have e1 : 2 * Real.pi * z1 / d = 2 * x := by rw [hx]; ring
  have e2 : 2 * Real.pi * z2 / d = 2 * y := by rw [hy]; ring
  have hQ : UnforcedLeray.B0592.den d (z1, z2) = Real.cosh (2 * y) - Real.cos (2 * x) := by
    show Real.cosh (2 * Real.pi * z2 / d) - Real.cos (2 * Real.pi * z1 / d) = _
    rw [e1, e2]
  have hQe : Real.cosh (2 * y) - Real.cos (2 * x) =
      Real.cosh y ^ 2 + Real.sinh y ^ 2 - (2 * Real.cos x ^ 2 - 1) := by
    rw [Real.cosh_two_mul, Real.cos_two_mul]
  have hQe0 : Real.cosh y ^ 2 + Real.sinh y ^ 2 - (2 * Real.cos x ^ 2 - 1) ≠ 0 := by
    rw [← hQe]
    rw [hQ] at hden
    exact hden
  have hQc : ((Real.cosh y ^ 2 + Real.sinh y ^ 2 - (2 * Real.cos x ^ 2 - 1) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hQe0
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hW : (Real.pi : ℂ) * ((z1 : ℂ) + (z2 : ℂ) * Complex.I) / (d : ℂ) =
      (x : ℂ) + (y : ℂ) * Complex.I := by
    rw [hx, hy]; push_cast; ring
  have hcyl : UnforcedLeray.Cyl.bsC d (z1, z2) = (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
      (((Real.pi : ℂ) / (d : ℂ)) *
        Complex.cot ((Real.pi : ℂ) * ((z1 : ℂ) + (z2 : ℂ) * Complex.I) / (d : ℂ))) := rfl
  have hwre : ((x : ℂ) + (y : ℂ) * Complex.I).re = x := by simp
  have hwim : ((x : ℂ) + (y : ℂ) * Complex.I).im = y := by simp
  have hS : Complex.sin ((x : ℂ) + (y : ℂ) * Complex.I) =
      ((Real.sin x * Real.cosh y : ℝ) : ℂ) + ((Real.cos x * Real.sinh y : ℝ) : ℂ) * Complex.I := by
    rw [UnforcedLeray.Kernels.sin_eq_re_im, hwre, hwim]
  have hC : Complex.cos ((x : ℂ) + (y : ℂ) * Complex.I) =
      ((Real.cos x * Real.cosh y : ℝ) : ℂ) +
        ((-(Real.sin x * Real.sinh y) : ℝ) : ℂ) * Complex.I := by
    rw [UnforcedLeray.Kernels.cos_eq_re_im, hwre, hwim]
  have hS0 : Complex.sin ((x : ℂ) + (y : ℂ) * Complex.I) ≠ 0 := by
    intro h
    have hn := UnforcedLeray.Kernels.norm_sin_sq ((x : ℂ) + (y : ℂ) * Complex.I)
    rw [h, hwre, hwim] at hn
    have hsum : Real.sin x ^ 2 + Real.sinh y ^ 2 = 0 := by
      rw [← hn]; simp
    apply hden
    rw [UnforcedLeray.B0592.den_eq]
    have hsum' : Real.sin (Real.pi * z1 / d) ^ 2 + Real.sinh (Real.pi * z2 / d) ^ 2 = 0 := by
      rw [hx, hy] at hsum
      exact hsum
    show 2 * (Real.sin (Real.pi * z1 / d) ^ 2 + Real.sinh (Real.pi * z2 / d) ^ 2) = 0
    rw [hsum']
    ring
  have hkey : Complex.cos ((x : ℂ) + (y : ℂ) * Complex.I) /
      Complex.sin ((x : ℂ) + (y : ℂ) * Complex.I) =
      (((2 * Real.sin x * Real.cos x : ℝ) : ℂ) - ((2 * Real.sinh y * Real.cosh y : ℝ) : ℂ) * Complex.I) /
        ((Real.cosh y ^ 2 + Real.sinh y ^ 2 - (2 * Real.cos x ^ 2 - 1) : ℝ) : ℂ) := by
    rw [div_eq_div_iff hS0 hQc, hC, hS]
    have hcosh := Real.cosh_sq y
    have hsc := Real.sin_sq_add_cos_sq x
    apply Complex.ext
    · simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
        Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im]
      linear_combination (Real.cos x * Real.cosh y) * hcosh - 2 * (Real.cos x * Real.cosh y) * hsc
    · simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
        Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im]
      linear_combination (Real.sin x * Real.sinh y) * hcosh
  rw [hcyl, hW, Complex.cot_eq_cos_div_sin, hkey]
  rw [e1, e2, hQ, hQe, Real.sinh_two_mul, Real.sin_two_mul]
  exact final_alg d Real.pi _ _ _ hd Real.pi_ne_zero hQe0

/-- **Leaf `KerRegDeriv`** (SP 2081-2084, 3121): the regularised stream function has
`∂_q G_{d,ε} = (den/(den+ε)) K_{d,1}` and `∂_η G_{d,ε} = -(den/(den+ε)) K_{d,0}` off the lattice. -/
theorem kerRegDeriv : KerRegDeriv := by
  intro d ε hd hε z hz
  obtain ⟨z1, z2⟩ := z
  have hd0 : d ≠ 0 := hd.ne'
  have hpos : 0 < UnforcedLeray.B0592.den d (z1, z2) + ε := by
    linarith [den_nonneg d (z1, z2)]
  have hne : UnforcedLeray.B0592.den d (z1, z2) + ε ≠ 0 := hpos.ne'
  have hsm : ContDiff ℝ ∞ (kerReg d ε) := (kerRegSmooth d ε hd hε).1
  have hdiff : DifferentiableAt ℝ (kerReg d ε) (z1, z2) :=
    (hsm.differentiable (by simp)) _
  have hc0 : HasDerivAt (fun t : ℝ => (t, z2)) ((1 : ℝ), (0 : ℝ)) z1 :=
    (hasDerivAt_id z1).prodMk (hasDerivAt_const z1 z2)
  have hc1 : HasDerivAt (fun t : ℝ => (z1, t)) ((0 : ℝ), (1 : ℝ)) z2 :=
    (hasDerivAt_const z2 z1).prodMk (hasDerivAt_id z2)
  have hG0 : HasDerivAt (fun t : ℝ => kerReg d ε (t, z2))
      (fderiv ℝ (kerReg d ε) (z1, z2) (1, 0)) z1 :=
    hdiff.hasFDerivAt.comp_hasDerivAt (f := fun t : ℝ => (t, z2)) (x := z1) hc0
  have hG1 : HasDerivAt (fun t : ℝ => kerReg d ε (z1, t))
      (fderiv ℝ (kerReg d ε) (z1, z2) (0, 1)) z2 :=
    hdiff.hasFDerivAt.comp_hasDerivAt (f := fun t : ℝ => (z1, t)) (x := z2) hc1
  have hq1 : HasDerivAt (fun t : ℝ => 2 * Real.pi * t / d) (2 * Real.pi * 1 / d) z1 :=
    ((hasDerivAt_id z1).const_mul (2 * Real.pi)).div_const d
  have hq2 : HasDerivAt (fun t : ℝ => 2 * Real.pi * t / d) (2 * Real.pi * 1 / d) z2 :=
    ((hasDerivAt_id z2).const_mul (2 * Real.pi)).div_const d
  have hfq : HasDerivAt (fun t : ℝ => UnforcedLeray.B0592.den d (t, z2) + ε)
      (-(-Real.sin (2 * Real.pi * z1 / d) * (2 * Real.pi * 1 / d))) z1 :=
    ((hq1.cos).const_sub (Real.cosh (2 * Real.pi * z2 / d))).add_const ε
  have hfη : HasDerivAt (fun t : ℝ => UnforcedLeray.B0592.den d (z1, t) + ε)
      (Real.sinh (2 * Real.pi * z2 / d) * (2 * Real.pi * 1 / d)) z2 :=
    ((hq2.cosh).sub_const (Real.cos (2 * Real.pi * z1 / d))).add_const ε
  have hGq : HasDerivAt (fun t : ℝ => kerReg d ε (t, z2))
      ((-(-Real.sin (2 * Real.pi * z1 / d) * (2 * Real.pi * 1 / d))) /
        (UnforcedLeray.B0592.den d (z1, z2) + ε) / (4 * Real.pi)) z1 := by
    unfold kerReg
    exact (hfq.log hne).div_const (4 * Real.pi)
  have hGη : HasDerivAt (fun t : ℝ => kerReg d ε (z1, t))
      ((Real.sinh (2 * Real.pi * z2 / d) * (2 * Real.pi * 1 / d)) /
        (UnforcedLeray.B0592.den d (z1, z2) + ε) / (4 * Real.pi)) z2 := by
    unfold kerReg
    exact (hfη.log hne).div_const (4 * Real.pi)
  have hE0 : fderiv ℝ (kerReg d ε) (z1, z2) (1, 0) =
      (-(-Real.sin (2 * Real.pi * z1 / d) * (2 * Real.pi * 1 / d))) /
        (UnforcedLeray.B0592.den d (z1, z2) + ε) / (4 * Real.pi) :=
    hG0.unique hGq
  have hE1 : fderiv ℝ (kerReg d ε) (z1, z2) (0, 1) =
      (Real.sinh (2 * Real.pi * z2 / d) * (2 * Real.pi * 1 / d)) /
        (UnforcedLeray.B0592.den d (z1, z2) + ε) / (4 * Real.pi) :=
    hG1.unique hGη
  have hbs := cyl_formula d hd0 z1 z2 hz
  have hre : (UnforcedLeray.Cyl.bsC d (z1, z2)).re =
      -Real.sinh (2 * Real.pi * z2 / d) / (2 * d * UnforcedLeray.B0592.den d (z1, z2)) := by
    rw [hbs]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im]
    ring
  have him : (UnforcedLeray.Cyl.bsC d (z1, z2)).im =
      -(Real.sin (2 * Real.pi * z1 / d) / (2 * d * UnforcedLeray.B0592.den d (z1, z2))) := by
    rw [hbs]
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im]
    ring
  have hk0 : kerD d (z1, z2) 0 =
      -Real.sinh (2 * Real.pi * z2 / d) / (2 * d * UnforcedLeray.B0592.den d (z1, z2)) := by
    unfold kerD UnforcedLeray.Cyl.bsKernel UnforcedLeray.Cyl.vec
    simp [hre]
  have hk1 : kerD d (z1, z2) 1 =
      Real.sin (2 * Real.pi * z1 / d) / (2 * d * UnforcedLeray.B0592.den d (z1, z2)) := by
    unfold kerD UnforcedLeray.Cyl.bsKernel UnforcedLeray.Cyl.vec
    simp [him]
  have hpd0 : B0579.pd 0 (kerReg d ε) (z1, z2) =
      fderiv ℝ (kerReg d ε) (z1, z2) (1, 0) := rfl
  have hpd1 : B0579.pd 1 (kerReg d ε) (z1, z2) =
      fderiv ℝ (kerReg d ε) (z1, z2) (0, 1) := rfl
  refine ⟨?_, ?_⟩
  · rw [hpd0, hE0, hk1]
    field_simp
    ring
  · rw [hpd1, hE1, hk0]
    field_simp
    ring

end UnforcedLeray.Short.IIIa
