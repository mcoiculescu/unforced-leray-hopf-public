import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_1_2_6_2

/-!
# `KerLapFormula`: the Laplacian of the regularised stream function (SP 2081-2084)

`kerReg d ε = (4π)⁻¹ log (den d + ε)`.  Its first partial derivatives are the closed forms
`kLF_G1 = ∂_q kerReg` and `kLF_G2 = ∂_η kerReg`; differentiating once more and using
`sin² + sinh² = (cosh - cos)(cosh + cos)` gives `lapForm d ε`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- `∂_q` of a function differentiable at `z`, as a one-variable derivative. -/
lemma kLF_pd0_eq_deriv (f : ℝ × ℝ → ℝ) (z : ℝ × ℝ) (hf : DifferentiableAt ℝ f z) :
    B0579.pd 0 f z = deriv (fun t : ℝ => f (t, z.2)) z.1 := by
  have hline : HasDerivAt (fun t : ℝ => (t, z.2)) ((1 : ℝ), (0 : ℝ)) z.1 :=
    (hasDerivAt_id' z.1).prodMk (hasDerivAt_const z.1 z.2)
  have h : deriv (fun t : ℝ => f (t, z.2)) z.1 = fderiv ℝ f z (1, 0) :=
    (hf.hasFDerivAt.comp_hasDerivAt z.1 hline).deriv
  rw [h]
  rfl

/-- `∂_η` of a function differentiable at `z`, as a one-variable derivative. -/
lemma kLF_pd1_eq_deriv (f : ℝ × ℝ → ℝ) (z : ℝ × ℝ) (hf : DifferentiableAt ℝ f z) :
    B0579.pd 1 f z = deriv (fun t : ℝ => f (z.1, t)) z.2 := by
  have hline : HasDerivAt (fun t : ℝ => (z.1, t)) ((0 : ℝ), (1 : ℝ)) z.2 :=
    (hasDerivAt_const z.2 z.1).prodMk (hasDerivAt_id' z.2)
  have h : deriv (fun t : ℝ => f (z.1, t)) z.2 = fderiv ℝ f z (0, 1) :=
    (hf.hasFDerivAt.comp_hasDerivAt z.2 hline).deriv
  rw [h]
  rfl

lemma kLF_D_pos {d ε : ℝ} (hε : 0 < ε) (z : ℝ × ℝ) :
    0 < Real.cosh (2 * Real.pi * z.2 / d) - Real.cos (2 * Real.pi * z.1 / d) + ε := by
  linarith [Real.one_le_cosh (2 * Real.pi * z.2 / d), Real.cos_le_one (2 * Real.pi * z.1 / d)]

/-- `∂_q G_{d,ε}` in closed form. -/
def kLF_G1 (d ε : ℝ) (z : ℝ × ℝ) : ℝ :=
  Real.sin (2 * Real.pi * z.1 / d) /
    (2 * d * (Real.cosh (2 * Real.pi * z.2 / d) - Real.cos (2 * Real.pi * z.1 / d) + ε))

/-- `∂_η G_{d,ε}` in closed form. -/
def kLF_G2 (d ε : ℝ) (z : ℝ × ℝ) : ℝ :=
  Real.sinh (2 * Real.pi * z.2 / d) /
    (2 * d * (Real.cosh (2 * Real.pi * z.2 / d) - Real.cos (2 * Real.pi * z.1 / d) + ε))

lemma kLF_kerReg_diff {d ε : ℝ} (hε : 0 < ε) (z : ℝ × ℝ) :
    DifferentiableAt ℝ (kerReg d ε) z := by
  have hden : DifferentiableAt ℝ (fun w : ℝ × ℝ => UnforcedLeray.B0592.den d w + ε) z := by
    unfold UnforcedLeray.B0592.den
    fun_prop
  have hlog := DifferentiableAt.log hden (kLF_D_pos (d := d) hε z).ne'
  have h2 := hlog.mul_const (4 * Real.pi)⁻¹
  unfold kerReg
  simpa only [div_eq_mul_inv] using h2

lemma kLF_G1_diff {d ε : ℝ} (hd : 0 < d) (hε : 0 < ε) (z : ℝ × ℝ) :
    DifferentiableAt ℝ (fun w : ℝ × ℝ => kLF_G1 d ε w) z := by
  have hs : DifferentiableAt ℝ (fun w : ℝ × ℝ => Real.sin (2 * Real.pi * w.1 / d)) z := by
    fun_prop
  have hD : DifferentiableAt ℝ (fun w : ℝ × ℝ =>
      2 * d * (Real.cosh (2 * Real.pi * w.2 / d) - Real.cos (2 * Real.pi * w.1 / d) + ε)) z := by
    fun_prop
  have hi := hD.inv (mul_ne_zero (mul_ne_zero two_ne_zero hd.ne') (kLF_D_pos (d := d) hε z).ne')
  have h := hs.mul hi
  unfold kLF_G1
  exact h

lemma kLF_G2_diff {d ε : ℝ} (hd : 0 < d) (hε : 0 < ε) (z : ℝ × ℝ) :
    DifferentiableAt ℝ (fun w : ℝ × ℝ => kLF_G2 d ε w) z := by
  have hs : DifferentiableAt ℝ (fun w : ℝ × ℝ => Real.sinh (2 * Real.pi * w.2 / d)) z := by
    fun_prop
  have hD : DifferentiableAt ℝ (fun w : ℝ × ℝ =>
      2 * d * (Real.cosh (2 * Real.pi * w.2 / d) - Real.cos (2 * Real.pi * w.1 / d) + ε)) z := by
    fun_prop
  have hi := hD.inv (mul_ne_zero (mul_ne_zero two_ne_zero hd.ne') (kLF_D_pos (d := d) hε z).ne')
  have h := hs.mul hi
  unfold kLF_G2
  exact h

lemma kLF_pd0_kerReg (d ε : ℝ) (hd : 0 < d) (hε : 0 < ε) :
    B0579.pd 0 (kerReg d ε) = fun w : ℝ × ℝ => kLF_G1 d ε w := by
  funext z
  have hDz := (kLF_D_pos (d := d) hε z).ne'
  rw [kLF_pd0_eq_deriv _ z (kLF_kerReg_diff hε z)]
  have hθ : HasDerivAt (fun t : ℝ => 2 * Real.pi * t / d) (2 * Real.pi * 1 / d) z.1 :=
    ((hasDerivAt_id' z.1).const_mul (2 * Real.pi)).div_const d
  have hden := ((hθ.cos).const_sub (Real.cosh (2 * Real.pi * z.2 / d))).add_const ε
  have hlog := (hden.log hDz).div_const (4 * Real.pi)
  refine hlog.deriv.trans ?_
  unfold kLF_G1
  field_simp
  ring

lemma kLF_pd1_kerReg (d ε : ℝ) (hd : 0 < d) (hε : 0 < ε) :
    B0579.pd 1 (kerReg d ε) = fun w : ℝ × ℝ => kLF_G2 d ε w := by
  funext z
  have hDz := (kLF_D_pos (d := d) hε z).ne'
  rw [kLF_pd1_eq_deriv _ z (kLF_kerReg_diff hε z)]
  have hθ : HasDerivAt (fun t : ℝ => 2 * Real.pi * t / d) (2 * Real.pi * 1 / d) z.2 :=
    ((hasDerivAt_id' z.2).const_mul (2 * Real.pi)).div_const d
  have hden : HasDerivAt
      (fun t : ℝ => Real.cosh (2 * Real.pi * t / d) - Real.cos (2 * Real.pi * z.1 / d) + ε)
      (Real.sinh (2 * Real.pi * z.2 / d) * (2 * Real.pi * 1 / d)) z.2 :=
    (hθ.cosh.sub_const _).add_const ε
  have hlog := (hden.log hDz).div_const (4 * Real.pi)
  refine hlog.deriv.trans ?_
  unfold kLF_G2
  field_simp
  ring

lemma kLF_pd00 (d ε : ℝ) (hd : 0 < d) (hε : 0 < ε) (z : ℝ × ℝ) :
    B0579.pd 0 (fun w : ℝ × ℝ => kLF_G1 d ε w) z =
      2 * Real.pi / d *
        (Real.cos (2 * Real.pi * z.1 / d) *
            (Real.cosh (2 * Real.pi * z.2 / d) - Real.cos (2 * Real.pi * z.1 / d) + ε) -
          Real.sin (2 * Real.pi * z.1 / d) ^ 2) /
        (2 * d * (Real.cosh (2 * Real.pi * z.2 / d) - Real.cos (2 * Real.pi * z.1 / d) + ε) ^ 2) := by
  have hDz := (kLF_D_pos (d := d) hε z).ne'
  rw [kLF_pd0_eq_deriv _ z (kLF_G1_diff hd hε z)]
  have hθ : HasDerivAt (fun t : ℝ => 2 * Real.pi * t / d) (2 * Real.pi * 1 / d) z.1 :=
    ((hasDerivAt_id' z.1).const_mul (2 * Real.pi)).div_const d
  have hnum : HasDerivAt (fun t : ℝ => Real.sin (2 * Real.pi * t / d))
      (Real.cos (2 * Real.pi * z.1 / d) * (2 * Real.pi * 1 / d)) z.1 := hθ.sin
  have hden := ((hθ.cos).const_sub (Real.cosh (2 * Real.pi * z.2 / d))).add_const ε
  have hDd := hden.const_mul (2 * d)
  have hq := hnum.div hDd (mul_ne_zero (mul_ne_zero two_ne_zero hd.ne') hDz)
  refine hq.deriv.trans ?_
  field_simp

lemma kLF_pd11 (d ε : ℝ) (hd : 0 < d) (hε : 0 < ε) (z : ℝ × ℝ) :
    B0579.pd 1 (fun w : ℝ × ℝ => kLF_G2 d ε w) z =
      2 * Real.pi / d *
        (Real.cosh (2 * Real.pi * z.2 / d) *
            (Real.cosh (2 * Real.pi * z.2 / d) - Real.cos (2 * Real.pi * z.1 / d) + ε) -
          Real.sinh (2 * Real.pi * z.2 / d) ^ 2) /
        (2 * d * (Real.cosh (2 * Real.pi * z.2 / d) - Real.cos (2 * Real.pi * z.1 / d) + ε) ^ 2) := by
  have hDz := (kLF_D_pos (d := d) hε z).ne'
  rw [kLF_pd1_eq_deriv _ z (kLF_G2_diff hd hε z)]
  have hθ : HasDerivAt (fun t : ℝ => 2 * Real.pi * t / d) (2 * Real.pi * 1 / d) z.2 :=
    ((hasDerivAt_id' z.2).const_mul (2 * Real.pi)).div_const d
  have hnum : HasDerivAt (fun t : ℝ => Real.sinh (2 * Real.pi * t / d))
      (Real.cosh (2 * Real.pi * z.2 / d) * (2 * Real.pi * 1 / d)) z.2 := hθ.sinh
  have hden : HasDerivAt
      (fun t : ℝ => Real.cosh (2 * Real.pi * t / d) - Real.cos (2 * Real.pi * z.1 / d) + ε)
      (Real.sinh (2 * Real.pi * z.2 / d) * (2 * Real.pi * 1 / d)) z.2 :=
    (hθ.cosh.sub_const _).add_const ε
  have hDd := hden.const_mul (2 * d)
  have hq := hnum.div hDd (mul_ne_zero (mul_ne_zero two_ne_zero hd.ne') hDz)
  refine hq.deriv.trans ?_
  field_simp

theorem kerLapFormula : UnforcedLeray.Short.IIIa.KerLapFormula := by
  intro d ε hd hε z
  rw [kLF_pd0_kerReg d ε hd hε, kLF_pd1_kerReg d ε hd hε, kLF_pd00 d ε hd hε z,
    kLF_pd11 d ε hd hε z]
  have hDz := (kLF_D_pos (d := d) hε z).ne'
  have hs : Real.sin (2 * Real.pi * z.1 / d) ^ 2 =
      (Real.cosh (2 * Real.pi * z.2 / d) - Real.cos (2 * Real.pi * z.1 / d)) *
        (Real.cosh (2 * Real.pi * z.2 / d) + Real.cos (2 * Real.pi * z.1 / d)) -
      Real.sinh (2 * Real.pi * z.2 / d) ^ 2 := by
    linear_combination Real.sin_sq_add_cos_sq (2 * Real.pi * z.1 / d) -
      Real.cosh_sq (2 * Real.pi * z.2 / d)
  unfold lapForm UnforcedLeray.B0592.den
  rw [hs]
  field_simp
  ring

end UnforcedLeray.Short.IIIa
