import UnforcedLeray.Short.PartIIb.Tasks.BlockFactorization.CoupledPropagator.ZeroCirculation.EtaCutoff
import UnforcedLeray.Short.PartIIb.Tasks.InteractionCylinder.CylWeightedKernel
import UnforcedLeray.Short.PartIIb.Tasks.GreenSelector.CylCoupledPairing.KBound
import UnforcedLeray.Units.B0592.Kernel

/-!
# Helper for `PartII-b:F2/2/2`: Weak Divergence-Freeness of `Cyl.K c g`

Proves:
- Uniform `L¹(cell c)` kernel-test majorant `lintegral_norm_bsKernel_mul_test_le`;
- Pointwise weak divergence-freeness of `x ↦ Cyl.bsKernel c (x - y)` via regularized stream
  `kerReg c ε z = log (B0592.den c z + ε) / (4π)` (`ε → 0⁺`);
- `integrableOn_K_mul_test` and `integral_K_dot_grad_test_eq_zero` for `g : Xmc c m` (`1 < m`,
  `1 ≤ c`) and `hφ : B0579.IsCylTest c φ` via Fubini.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff InnerProductSpace

namespace UnforcedLeray.Short.IIb.ZeroCircAux

open UnforcedLeray

/-! ## 1. Uniform kernel-test `L¹(cell c)` bound -/

/-- Every cylinder test function is uniformly bounded on `B0579.cell c`. -/
private theorem exists_bound_on_cell_of_isCylTest {c : ℝ} {ψ : B0579.Plane → ℝ}
    (hψ : B0579.IsCylTest c ψ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ B0579.cell c, ‖ψ x‖ ≤ M := by
  obtain ⟨R0, hR0⟩ := hψ.band
  set R := max R0 0
  let K : Set B0579.Plane := Icc (-(c / 2)) (c / 2) ×ˢ Icc (-R) R
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hψ.continuous.continuousOn
  refine ⟨max B 0, le_max_right _ _, fun x hx => ?_⟩
  by_cases hx2 : |x.2| ≤ R
  · have hxK : x ∈ K := ⟨⟨hx.1.1, hx.1.2.le⟩, abs_le.1 hx2⟩
    exact (hB x hxK).trans (le_max_left _ _)
  · push Not at hx2
    have hgt : R0 < |x.2| := lt_of_le_of_lt (le_max_left _ _) hx2
    rw [hR0 x hgt, norm_zero]
    exact le_max_right _ _

/-- Uniform in `y` bound on `∫⁻ x in cell c, ‖bsKernel c (x - y)‖ₑ * ‖ψ x‖ₑ`. -/
theorem lintegral_norm_bsKernel_mul_test_le {c : ℝ} (hc : 1 ≤ c) {ψ : B0579.Plane → ℝ}
    (hψ : B0579.IsCylTest c ψ) :
    ∃ C_ψ : ℝ≥0∞, C_ψ < ⊤ ∧ ∀ y : B0579.Plane,
      ∫⁻ x in B0579.cell c, ‖Cyl.bsKernel c (x - y)‖ₑ * ‖ψ x‖ₑ ≤ C_ψ := by
  have hc0 : 0 < c := by linarith
  obtain ⟨M, _hM0, hM⟩ := exists_bound_on_cell_of_isCylTest hψ
  let Iψ : ℝ≥0∞ := ∫⁻ x in B0579.cell c, ‖ψ x‖ₑ
  have hIψ_lt : Iψ < ⊤ := hψ.integrableOn.2
  let C_ψ : ℝ≥0∞ :=
    ENNReal.ofReal M * ENNReal.ofReal nearKernelConst + ENNReal.ofReal 2 * Iψ
  have hC_lt : C_ψ < ⊤ :=
    ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top,
      ENNReal.mul_lt_top ENNReal.ofReal_lt_top hIψ_lt⟩
  refine ⟨C_ψ, hC_lt, fun y => ?_⟩
  have hpw : ∀ x ∈ B0579.cell c,
      ‖Cyl.bsKernel c (x - y)‖ₑ * ‖ψ x‖ₑ ≤
        ENNReal.ofReal M * ‖kNearR c 1 (x - y)‖ₑ + ENNReal.ofReal 2 * ‖ψ x‖ₑ := by
    intro x hx
    rw [← kNearR_add_kFarR c 1 (x - y)]
    have htri : ‖kNearR c 1 (x - y) + kFarR c 1 (x - y)‖ₑ ≤
        ‖kNearR c 1 (x - y)‖ₑ + ‖kFarR c 1 (x - y)‖ₑ := enorm_add_le _ _
    have h1 : ‖kNearR c 1 (x - y)‖ₑ * ‖ψ x‖ₑ ≤ ENNReal.ofReal M * ‖kNearR c 1 (x - y)‖ₑ := by
      rw [mul_comm]
      refine mul_le_mul_of_nonneg_right ?_ zero_le
      rw [← enorm_norm, Real.enorm_eq_ofReal (norm_nonneg _)]
      exact ENNReal.ofReal_le_ofReal (hM x hx)
    have h2 : ‖kFarR c 1 (x - y)‖ₑ * ‖ψ x‖ₑ ≤ ENNReal.ofReal 2 * ‖ψ x‖ₑ := by
      refine mul_le_mul_of_nonneg_right ?_ zero_le
      rw [← enorm_norm, Real.enorm_eq_ofReal (norm_nonneg _)]
      have hf := norm_kFarR_le hc one_pos (x - y)
      norm_num at hf
      exact ENNReal.ofReal_le_ofReal hf
    calc ‖kNearR c 1 (x - y) + kFarR c 1 (x - y)‖ₑ * ‖ψ x‖ₑ
        ≤ (‖kNearR c 1 (x - y)‖ₑ + ‖kFarR c 1 (x - y)‖ₑ) * ‖ψ x‖ₑ :=
          mul_le_mul_of_nonneg_right htri zero_le
      _ = ‖kNearR c 1 (x - y)‖ₑ * ‖ψ x‖ₑ + ‖kFarR c 1 (x - y)‖ₑ * ‖ψ x‖ₑ := add_mul _ _ _
      _ ≤ ENNReal.ofReal M * ‖kNearR c 1 (x - y)‖ₑ + ENNReal.ofReal 2 * ‖ψ x‖ₑ :=
          add_le_add h1 h2
  have hm_near : Measurable (fun x : B0579.Plane => ‖kNearR c 1 (x - y)‖ₑ) :=
    ((measurable_kNearR c 1).comp (measurable_id.sub measurable_const)).enorm
  have hm_psi : Measurable (fun x : B0579.Plane => ‖ψ x‖ₑ) := hψ.continuous.measurable.enorm
  have hnear_shift : ∫⁻ x in B0579.cell c, ‖kNearR c 1 (x - y)‖ₑ =
      ∫⁻ x in B0579.cell c, ‖kNearR c 1 x‖ₑ := by
    let G : B0579.Plane → ℝ≥0∞ := fun z => ‖kNearR c 1 (-z)‖ₑ
    have hG_per : Cyl.IsPeriodic c G := by
      intro z
      simp only [G]
      have hsub : -((z.1 + c, z.2) : B0579.Plane) = (-z.1 - c, -z.2) := by
        ext <;> simp; ring
      have hadd : ((-z.1 - c + c, -z.2) : B0579.Plane) = -z := by ext <;> simp
      have hp := isPeriodic_kNearR hc0 1 (-z.1 - c, -z.2)
      change kNearR c 1 (-z.1 - c + c, -z.2) = kNearR c 1 (-z.1 - c, -z.2) at hp
      rw [hadd] at hp
      rw [hsub, ← hp]
    have heq_y : (fun x : B0579.Plane => ‖kNearR c 1 (x - y)‖ₑ) = fun x => G (y - x) := by
      funext x; simp [G, neg_sub]
    have heq_0 : (fun x : B0579.Plane => ‖kNearR c 1 x‖ₑ) = fun x => G (0 - x) := by
      funext x; simp [G]
    rw [cell_eq_cylCell, heq_y, Cyl.lintegral_cell_comp_sub_left hc0 hG_per y,
      ← Cyl.lintegral_cell_comp_sub_left hc0 hG_per 0, ← heq_0, ← cell_eq_cylCell]
  calc ∫⁻ x in B0579.cell c, ‖Cyl.bsKernel c (x - y)‖ₑ * ‖ψ x‖ₑ
      ≤ ∫⁻ x in B0579.cell c,
          (ENNReal.ofReal M * ‖kNearR c 1 (x - y)‖ₑ + ENNReal.ofReal 2 * ‖ψ x‖ₑ) :=
        setLIntegral_mono' (B0579.measurableSet_cell c) hpw
    _ = ENNReal.ofReal M * (∫⁻ x in B0579.cell c, ‖kNearR c 1 (x - y)‖ₑ) +
          ENNReal.ofReal 2 * Iψ := by
        rw [lintegral_add_left (hm_near.const_mul _),
          lintegral_const_mul _ hm_near, lintegral_const_mul _ hm_psi]
    _ ≤ ENNReal.ofReal M * ENNReal.ofReal nearKernelConst + ENNReal.ofReal 2 * Iψ := by
        rw [hnear_shift]
        exact add_le_add
          (mul_le_mul_of_nonneg_left (lintegral_kNearR_le hc le_rfl) zero_le) le_rfl

/-- Integrability of `x ↦ ‖Cyl.bsKernel c (x - y)‖ * |ψ x|` on `B0579.cell c`. -/
theorem integrableOn_norm_bsKernel_mul_test {c : ℝ} (hc : 1 ≤ c) (y : B0579.Plane)
    {ψ : B0579.Plane → ℝ} (hψ : B0579.IsCylTest c ψ) :
    IntegrableOn (fun x => ‖Cyl.bsKernel c (x - y)‖ * |ψ x|) (B0579.cell c) volume := by
  obtain ⟨C_ψ, hC_lt, hC⟩ := lintegral_norm_bsKernel_mul_test_le hc hψ
  refine ⟨(((Cyl.measurable_bsKernel c).comp
      (measurable_id.sub measurable_const)).norm.mul
      hψ.continuous.measurable.abs).aestronglyMeasurable, ?_⟩
  have heq : (fun x : B0579.Plane => ‖‖Cyl.bsKernel c (x - y)‖ * |ψ x|‖ₑ) =
      fun x => ‖Cyl.bsKernel c (x - y)‖ₑ * ‖ψ x‖ₑ := by
    funext x
    rw [enorm_mul, enorm_norm, Real.enorm_eq_ofReal_abs, abs_abs, ← Real.enorm_eq_ofReal_abs]
  change ∫⁻ x in B0579.cell c, ‖‖Cyl.bsKernel c (x - y)‖ * |ψ x|‖ₑ < ⊤
  rw [heq]
  exact (hC y).trans_lt hC_lt

/-! ## 2. Regularized stream function and pointwise divergence-freeness of `bsKernel` -/

/-- Explicit real-trigonometric formula for `Cyl.bsKernel c z` (`c > 0`, all `z : Plane`). -/
private theorem bsKernel_eq_trig {c : ℝ} (hc : 0 < c) (z : B0579.Plane) :
    Cyl.bsKernel c z 0 = -Real.sinh (2 * Real.pi * z.2 / c) / (2 * c * B0592.den c z) ∧
    Cyl.bsKernel c z 1 = Real.sin (2 * Real.pi * z.1 / c) / (2 * c * B0592.den c z) := by
  set a : ℝ := Real.pi * z.1 / c
  set b : ℝ := Real.pi * z.2 / c
  set w : ℂ := (a : ℂ) + (b : ℂ) * Complex.I
  have hc0 : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hpi0 : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hw_eq : (Real.pi : ℂ) * ((z.1 : ℂ) + (z.2 : ℂ) * Complex.I) / (c : ℂ) = w := by
    simp only [w, a, b]
    push_cast
    field_simp
  have hpref : (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * ((Real.pi : ℂ) / (c : ℂ)) =
      (-Complex.I) * (((2 * c)⁻¹ : ℝ) : ℂ) := by
    have hI0 : Complex.I ≠ 0 := Complex.I_ne_zero
    push_cast
    field_simp
    rw [Complex.I_sq]
    ring
  have hbsC : Cyl.bsC c z = (-Complex.I) * ((((2 * c)⁻¹ : ℝ) : ℂ) * Complex.cot w) := by
    unfold Cyl.bsC Kernels.cylinderBS
    rw [hw_eq, ← mul_assoc, hpref, mul_assoc]
  have wre : w.re = a := by simp [w]
  have wim : w.im = b := by simp [w]
  have hsin_re : (Complex.sin w).re = Real.sin a * Real.cosh b := by
    rw [Kernels.sin_eq_re_im, wre, wim]
    simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hsin_im : (Complex.sin w).im = Real.cos a * Real.sinh b := by
    rw [Kernels.sin_eq_re_im, wre, wim]
    simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hcos_re : (Complex.cos w).re = Real.cos a * Real.cosh b := by
    rw [Kernels.cos_eq_re_im, wre, wim]
    simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hcos_im : (Complex.cos w).im = -(Real.sin a * Real.sinh b) := by
    rw [Kernels.cos_eq_re_im, wre, wim]
    simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hnsq : Complex.normSq (Complex.sin w) = B0592.den c z / 2 := by
    rw [← Complex.sq_norm, Kernels.norm_sin_sq, wre, wim, B0592.den_eq]
    simp only [a, b]
    ring
  have hcot_im : (Complex.cot w).im = -Real.sinh (2 * Real.pi * z.2 / c) / B0592.den c z := by
    rw [Complex.cot_eq_cos_div_sin, Complex.div_im, ← sub_div, hcos_im, hsin_re, hcos_re,
      hsin_im, hnsq]
    have hnum : -(Real.sin a * Real.sinh b) * (Real.sin a * Real.cosh b) -
        Real.cos a * Real.cosh b * (Real.cos a * Real.sinh b) =
        -Real.sinh (2 * Real.pi * z.2 / c) / 2 := by
      have h2b : 2 * Real.pi * z.2 / c = 2 * b := by simp only [b]; ring
      rw [h2b, Real.sinh_two_mul]
      linear_combination -(Real.sinh b * Real.cosh b) * Real.sin_sq_add_cos_sq a
    rw [hnum, div_div_div_cancel_right₀ (by norm_num : (2 : ℝ) ≠ 0)]
  have hcot_re : (Complex.cot w).re = Real.sin (2 * Real.pi * z.1 / c) / B0592.den c z := by
    rw [Complex.cot_eq_cos_div_sin, Complex.div_re, ← add_div, hcos_re, hsin_re, hcos_im,
      hsin_im, hnsq]
    have hnum : Real.cos a * Real.cosh b * (Real.sin a * Real.cosh b) +
        -(Real.sin a * Real.sinh b) * (Real.cos a * Real.sinh b) =
        Real.sin (2 * Real.pi * z.1 / c) / 2 := by
      have h2a : 2 * Real.pi * z.1 / c = 2 * a := by simp only [a]; ring
      rw [h2a, Real.sin_two_mul]
      linear_combination (Real.sin a * Real.cos a) * Real.cosh_sq b
    rw [hnum, div_div_div_cancel_right₀ (by norm_num : (2 : ℝ) ≠ 0)]
  refine ⟨?_, ?_⟩
  · simp only [Cyl.bsKernel, Cyl.vec_zero, hbsC, Complex.mul_re, Complex.mul_im, Complex.neg_re,
      Complex.neg_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, hcot_im,
      div_eq_mul_inv, mul_inv]
    ring
  · simp only [Cyl.bsKernel, Cyl.vec_one, hbsC, Complex.mul_re, Complex.mul_im, Complex.neg_re,
      Complex.neg_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, hcot_re,
      div_eq_mul_inv, mul_inv]
    ring

private theorem den_nonneg (c : ℝ) (z : B0579.Plane) : 0 ≤ B0592.den c z := by
  rw [B0592.den_eq]
  positivity

private theorem sin_and_sinh_zero_of_den_eq_zero {c : ℝ} {z : B0579.Plane}
    (h : B0592.den c z = 0) :
    Real.sin (2 * Real.pi * z.1 / c) = 0 ∧ Real.sinh (2 * Real.pi * z.2 / c) = 0 := by
  rw [B0592.den_eq] at h
  have hs1 : Real.sin (Real.pi * z.1 / c) ^ 2 = 0 := by
    nlinarith [sq_nonneg (Real.sin (Real.pi * z.1 / c)),
      sq_nonneg (Real.sinh (Real.pi * z.2 / c))]
  have hs2 : Real.sinh (Real.pi * z.2 / c) ^ 2 = 0 := by
    nlinarith [sq_nonneg (Real.sin (Real.pi * z.1 / c)),
      sq_nonneg (Real.sinh (Real.pi * z.2 / c))]
  have h1 : Real.sin (Real.pi * z.1 / c) = 0 := sq_eq_zero_iff.mp hs1
  have h2 : Real.sinh (Real.pi * z.2 / c) = 0 := sq_eq_zero_iff.mp hs2
  refine ⟨?_, ?_⟩
  · rw [show 2 * Real.pi * z.1 / c = 2 * (Real.pi * z.1 / c) by ring, Real.sin_two_mul, h1]
    ring
  · rw [show 2 * Real.pi * z.2 / c = 2 * (Real.pi * z.2 / c) by ring, Real.sinh_two_mul, h2]
    ring

/-- Regularized cylinder stream function `log (den c z + ε) / (4π)`. -/
private def kerReg (c ε : ℝ) (z : B0579.Plane) : ℝ :=
  Real.log (B0592.den c z + ε) / (4 * Real.pi)

private theorem contDiff_kerReg (c : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ContDiff ℝ ∞ (kerReg c ε) := by
  have hden : ContDiff ℝ ∞ (fun z : B0579.Plane => B0592.den c z + ε) := by
    unfold B0592.den
    fun_prop
  have hpos : ∀ z : B0579.Plane, B0592.den c z + ε ≠ 0 := fun z =>
    (add_pos_of_nonneg_of_pos (den_nonneg c z) hε).ne'
  exact (hden.log hpos).div_const (4 * Real.pi)

private theorem kerReg_sub_periodic {c : ℝ} (hc : 0 < c) (ε : ℝ) (y : B0579.Plane) :
    ∀ x : B0579.Plane, kerReg c ε ((x.1 + c, x.2) - y) = kerReg c ε (x - y) := by
  intro x
  unfold kerReg B0592.den
  have h1 : ((x.1 + c, x.2) - y).2 = (x - y).2 := rfl
  have h2 : 2 * Real.pi * ((x.1 + c, x.2) - y).1 / c =
      2 * Real.pi * (x - y).1 / c + 2 * Real.pi := by
    have hc0 : c ≠ 0 := hc.ne'
    change 2 * Real.pi * (x.1 + c - y.1) / c = 2 * Real.pi * (x.1 - y.1) / c + 2 * Real.pi
    field_simp
    ring
  rw [h1, h2, Real.cos_add_two_pi]

private theorem pd_kerReg_sub {c ε : ℝ} (hc : 0 < c) (hε : 0 < ε) (y x : B0579.Plane) :
    B0579.pd 0 (fun z => kerReg c ε (z - y)) x =
      (B0592.den c (x - y) / (B0592.den c (x - y) + ε)) * Cyl.bsKernel c (x - y) 1 ∧
    B0579.pd 1 (fun z => kerReg c ε (z - y)) x =
      -(B0592.den c (x - y) / (B0592.den c (x - y) + ε)) * Cyl.bsKernel c (x - y) 0 := by
  have hsm : ContDiff ℝ ∞ (fun z : B0579.Plane => kerReg c ε (z - y)) :=
    (contDiff_kerReg c hε).comp (contDiff_id.sub contDiff_const)
  have hdiff : DifferentiableAt ℝ (fun z : B0579.Plane => kerReg c ε (z - y)) x :=
    (hsm.differentiable (by simp)) x
  have hden_pos : 0 < B0592.den c (x - y) + ε :=
    add_pos_of_nonneg_of_pos (den_nonneg c (x - y)) hε
  have hc0 : c ≠ 0 := hc.ne'
  have hpi0 : Real.pi ≠ 0 := Real.pi_ne_zero
  obtain ⟨hk0, hk1⟩ := bsKernel_eq_trig hc (x - y)
  refine ⟨?_, ?_⟩
  · have hlin : HasDerivAt (fun t : ℝ => 2 * Real.pi * (t - y.1) / c)
        (2 * Real.pi * 1 / c) x.1 :=
      (((hasDerivAt_id x.1).sub_const y.1).const_mul (2 * Real.pi)).div_const c
    have hden_d : HasDerivAt (fun t : ℝ => B0592.den c ((t, x.2) - y) + ε)
        (-(-Real.sin (2 * Real.pi * (x.1 - y.1) / c) * (2 * Real.pi * 1 / c))) x.1 := by
      have := (hlin.cos.const_sub (Real.cosh (2 * Real.pi * (x.2 - y.2) / c))).add_const ε
      simpa [B0592.den] using this
    have h1d : HasDerivAt (fun t : ℝ => kerReg c ε ((t, x.2) - y))
        (-(-Real.sin (2 * Real.pi * (x.1 - y.1) / c) * (2 * Real.pi * 1 / c)) /
          (B0592.den c (x - y) + ε) / (4 * Real.pi)) x.1 :=
      (hden_d.log hden_pos.ne').div_const (4 * Real.pi)
    have hcomp : HasDerivAt (fun t : ℝ => kerReg c ε ((t, x.2) - y))
        (B0579.pd 0 (fun z => kerReg c ε (z - y)) x) x.1 := by
      change HasDerivAt (fun t : ℝ => kerReg c ε ((t, x.2) - y))
        (fderiv ℝ (fun z => kerReg c ε (z - y)) x (1, 0)) x.1
      exact hdiff.hasFDerivAt.comp_hasDerivAt x.1
        ((hasDerivAt_id' x.1).prodMk (hasDerivAt_const x.1 x.2))
    rw [hcomp.unique h1d, hk1]
    rcases eq_or_ne (B0592.den c (x - y)) 0 with hd0 | hd_ne
    · obtain ⟨hsin0, _⟩ := sin_and_sinh_zero_of_den_eq_zero hd0
      have hsin0' : Real.sin (2 * Real.pi * (x.1 - y.1) / c) = 0 := hsin0
      simp [hd0, hsin0']
    · have hde_ne : B0592.den c (x - y) + ε ≠ 0 := hden_pos.ne'
      change -(-Real.sin (2 * Real.pi * (x - y).1 / c) * (2 * Real.pi * 1 / c)) /
          (B0592.den c (x - y) + ε) / (4 * Real.pi) =
        B0592.den c (x - y) / (B0592.den c (x - y) + ε) *
          (Real.sin (2 * Real.pi * (x - y).1 / c) / (2 * c * B0592.den c (x - y)))
      field_simp
      ring
  · have hlin : HasDerivAt (fun t : ℝ => 2 * Real.pi * (t - y.2) / c)
        (2 * Real.pi * 1 / c) x.2 :=
      (((hasDerivAt_id x.2).sub_const y.2).const_mul (2 * Real.pi)).div_const c
    have hden_d : HasDerivAt (fun t : ℝ => B0592.den c ((x.1, t) - y) + ε)
        (Real.sinh (2 * Real.pi * (x.2 - y.2) / c) * (2 * Real.pi * 1 / c)) x.2 := by
      have := (hlin.cosh.sub_const (Real.cos (2 * Real.pi * (x.1 - y.1) / c))).add_const ε
      simpa [B0592.den] using this
    have h1d : HasDerivAt (fun t : ℝ => kerReg c ε ((x.1, t) - y))
        (Real.sinh (2 * Real.pi * (x.2 - y.2) / c) * (2 * Real.pi * 1 / c) /
          (B0592.den c (x - y) + ε) / (4 * Real.pi)) x.2 :=
      (hden_d.log hden_pos.ne').div_const (4 * Real.pi)
    have hcomp : HasDerivAt (fun t : ℝ => kerReg c ε ((x.1, t) - y))
        (B0579.pd 1 (fun z => kerReg c ε (z - y)) x) x.2 := by
      change HasDerivAt (fun t : ℝ => kerReg c ε ((x.1, t) - y))
        (fderiv ℝ (fun z => kerReg c ε (z - y)) x (0, 1)) x.2
      exact hdiff.hasFDerivAt.comp_hasDerivAt x.2
        ((hasDerivAt_const x.2 x.1).prodMk (hasDerivAt_id' x.2))
    rw [hcomp.unique h1d, hk0]
    rcases eq_or_ne (B0592.den c (x - y)) 0 with hd0 | hd_ne
    · obtain ⟨_, hsinh0⟩ := sin_and_sinh_zero_of_den_eq_zero hd0
      have hsinh0' : Real.sinh (2 * Real.pi * (x.2 - y.2) / c) = 0 := hsinh0
      simp [hd0, hsinh0']
    · have hde_ne : B0592.den c (x - y) + ε ≠ 0 := hden_pos.ne'
      change Real.sinh (2 * Real.pi * (x - y).2 / c) * (2 * Real.pi * 1 / c) /
          (B0592.den c (x - y) + ε) / (4 * Real.pi) =
        -(B0592.den c (x - y) / (B0592.den c (x - y) + ε)) *
          (-Real.sinh (2 * Real.pi * (x - y).2 / c) / (2 * c * B0592.den c (x - y)))
      field_simp
      ring

/-- Orthogonality of `∇φ` and `∇^⊥ψ` on `B0579.cell c` for cylinder tests `φ, ψ`. -/
private theorem integral_grad_dot_rot_eq_zero {c : ℝ} (hc : 0 < c) {φ ψ : B0579.Plane → ℝ}
    (hφ : B0579.IsCylTest c φ) (hψ : B0579.IsCylTest c ψ) :
    ∫ x in B0579.cell c,
      (B0579.pd 0 φ x * B0579.pd 1 ψ x - B0579.pd 1 φ x * B0579.pd 0 ψ x) = 0 := by
  have hφ' := toSobCylTest hφ
  have hψ' := toSobCylTest hψ
  have h0 := (Cyl.mem_divFree.1 (Cyl.rotL_mem_divFree hc hψ')) φ hφ'
  rw [Cyl.gradL, Cyl.rotL, Cyl.inner_toLp_eq, ← cell_eq_cylCell] at h0
  rw [← h0]
  refine setIntegral_congr_fun (B0579.measurableSet_cell c) fun z _ => ?_
  simp only [Cyl.gradT, Cyl.rotT, Cyl.inner_vec,
    Cyl.partialQ_eq_fderiv hφ'.differentiable, Cyl.partialEta_eq_fderiv hφ'.differentiable,
    Cyl.partialQ_eq_fderiv hψ'.differentiable, Cyl.partialEta_eq_fderiv hψ'.differentiable,
    B0579.pd, B0579.dir, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-- Pointwise weak divergence-freeness of `x ↦ Cyl.bsKernel c (x - y)` on `B0579.cell c`. -/
theorem integral_bsKernel_dot_grad_test_eq_zero {c : ℝ} (hc : 1 ≤ c) (y : B0579.Plane)
    {φ : B0579.Plane → ℝ} (hφ : B0579.IsCylTest c φ) :
    ∫ x in B0579.cell c,
      (Cyl.bsKernel c (x - y) 0 * B0579.pd 0 φ x +
        Cyl.bsKernel c (x - y) 1 * B0579.pd 1 φ x) = 0 := by
  have hc0 : 0 < c := by linarith
  obtain ⟨M, hM⟩ := hφ.band
  set R0 : ℝ := max M 0 + 1
  have hR0 : 0 < R0 := by positivity
  let εSeq : ℕ → ℝ := fun n => ((n : ℝ) + 1)⁻¹
  have hε_pos : ∀ n : ℕ, 0 < εSeq n := fun n => inv_pos.2 (by positivity)
  let Kdot : B0579.Plane → ℝ := fun x =>
    Cyl.bsKernel c (x - y) 0 * B0579.pd 0 φ x + Cyl.bsKernel c (x - y) 1 * B0579.pd 1 φ x
  let F : ℕ → B0579.Plane → ℝ := fun n x =>
    (B0592.den c (x - y) / (B0592.den c (x - y) + εSeq n)) * Kdot x
  have hF_int_zero : ∀ n : ℕ, ∫ x in B0579.cell c, F n x = 0 := by
    intro n
    let G : B0579.Plane → ℝ := fun x => kerReg c (εSeq n) (x - y)
    have hG_sm : ContDiff ℝ ∞ G :=
      (contDiff_kerReg c (hε_pos n)).comp (contDiff_id.sub contDiff_const)
    have hG_diff : Differentiable ℝ G := hG_sm.differentiable (by simp)
    let ψ : B0579.Plane → ℝ := fun x => etaCut R0 x * G x
    have hψ : B0579.IsCylTest c ψ :=
      isCylTest_etaCut_mul hR0 hG_sm (kerReg_sub_periodic hc0 (εSeq n) y)
    have hpt : ∀ x : B0579.Plane,
        F n x = -(B0579.pd 0 φ x * B0579.pd 1 ψ x - B0579.pd 1 φ x * B0579.pd 0 ψ x) := by
      intro x
      rcases lt_or_ge |x.2| R0 with hlt | hge
      · obtain ⟨hpd0G, hpd1G⟩ := pd_kerReg_sub hc0 (hε_pos n) y x
        obtain ⟨hpd0ψ, hpd1ψ⟩ := pd_etaCut_mul R0 hG_diff x
        have hcut1 : etaCut R0 x = 1 := etaCut_eq_one hR0 hlt.le
        have hcut_pd1 : B0579.pd 1 (etaCut R0) x = 0 := by
          have hU : IsOpen {z : B0579.Plane | |z.2| < R0} :=
            isOpen_lt continuous_snd.abs continuous_const
          have hev : etaCut R0 =ᶠ[𝓝 x] fun _ => (1 : ℝ) :=
            Filter.eventually_of_mem (hU.mem_nhds hlt) fun z hz => etaCut_eq_one hR0 hz.le
          simp only [B0579.pd, hev.fderiv_eq, fderiv_const_apply, zero_apply]
        change F n x =
          -(B0579.pd 0 φ x * B0579.pd 1 (fun z => etaCut R0 z * G z) x -
            B0579.pd 1 φ x * B0579.pd 0 (fun z => etaCut R0 z * G z) x)
        rw [hpd0ψ, hpd1ψ, hcut1, hcut_pd1]
        change (B0592.den c (x - y) / (B0592.den c (x - y) + εSeq n)) *
            (Cyl.bsKernel c (x - y) 0 * B0579.pd 0 φ x +
              Cyl.bsKernel c (x - y) 1 * B0579.pd 1 φ x) =
          -(B0579.pd 0 φ x * (1 * B0579.pd 1 G x + 0 * G x) -
            B0579.pd 1 φ x * (1 * B0579.pd 0 G x))
        rw [hpd0G, hpd1G]
        ring
      · have hM_lt : M < |x.2| := lt_of_lt_of_le (by linarith [le_max_left M 0]) hge
        have hU : IsOpen {z : B0579.Plane | M < |z.2|} :=
          isOpen_lt continuous_const continuous_snd.abs
        have hev : φ =ᶠ[𝓝 x] fun _ => (0 : ℝ) :=
          Filter.eventually_of_mem (hU.mem_nhds hM_lt) fun z hz => hM z hz
        have hpd0φ : B0579.pd 0 φ x = 0 := by
          simp only [B0579.pd, hev.fderiv_eq, fderiv_const_apply, zero_apply]
        have hpd1φ : B0579.pd 1 φ x = 0 := by
          simp only [B0579.pd, hev.fderiv_eq, fderiv_const_apply, zero_apply]
        simp only [F, Kdot, hpd0φ, hpd1φ]
        ring
    simp_rw [hpt, integral_neg, integral_grad_dot_rot_eq_zero hc0 hφ hψ, neg_zero]
  let maj : B0579.Plane → ℝ := fun x =>
    ‖Cyl.bsKernel c (x - y)‖ * |B0579.pd 0 φ x| +
      ‖Cyl.bsKernel c (x - y)‖ * |B0579.pd 1 φ x|
  have hmaj_int : IntegrableOn maj (B0579.cell c) volume :=
    (integrableOn_norm_bsKernel_mul_test hc y (hφ.pd 0)).add
      (integrableOn_norm_bsKernel_mul_test hc y (hφ.pd 1))
  have hKdot_meas : Measurable Kdot := by
    have hk0 : Measurable (fun x : B0579.Plane => Cyl.bsKernel c (x - y) 0) :=
      (EuclideanSpace.proj (0 : Fin 2)).continuous.measurable.comp
        ((Cyl.measurable_bsKernel c).comp (measurable_id.sub measurable_const))
    have hk1 : Measurable (fun x : B0579.Plane => Cyl.bsKernel c (x - y) 1) :=
      (EuclideanSpace.proj (1 : Fin 2)).continuous.measurable.comp
        ((Cyl.measurable_bsKernel c).comp (measurable_id.sub measurable_const))
    exact (hk0.mul (hφ.pd 0).continuous.measurable).add
      (hk1.mul (hφ.pd 1).continuous.measurable)
  have hden_meas : Measurable (fun x : B0579.Plane => B0592.den c (x - y)) := by
    unfold B0592.den
    fun_prop
  have htend_int : Tendsto (fun n : ℕ => ∫ x in B0579.cell c, F n x) atTop
      (𝓝 (∫ x in B0579.cell c, Kdot x)) := by
    refine tendsto_integral_of_dominated_convergence maj ?_ hmaj_int ?_ ?_
    · intro n
      exact ((hden_meas.div (hden_meas.add measurable_const)).mul
        hKdot_meas).aestronglyMeasurable
    · intro n
      refine Eventually.of_forall fun x => ?_
      have hd_nn : 0 ≤ B0592.den c (x - y) := den_nonneg c (x - y)
      have hde_pos : 0 < B0592.den c (x - y) + εSeq n :=
        add_pos_of_nonneg_of_pos hd_nn (hε_pos n)
      have hrat_nn : 0 ≤ B0592.den c (x - y) / (B0592.den c (x - y) + εSeq n) :=
        div_nonneg hd_nn hde_pos.le
      have hrat_le1 : B0592.den c (x - y) / (B0592.den c (x - y) + εSeq n) ≤ 1 :=
        (div_le_one hde_pos).2 (by linarith [hε_pos n])
      have hk0_le : |Cyl.bsKernel c (x - y) 0| ≤ ‖Cyl.bsKernel c (x - y)‖ := by
        simpa [Real.norm_eq_abs] using PiLp.norm_apply_le (Cyl.bsKernel c (x - y)) 0
      have hk1_le : |Cyl.bsKernel c (x - y) 1| ≤ ‖Cyl.bsKernel c (x - y)‖ := by
        simpa [Real.norm_eq_abs] using PiLp.norm_apply_le (Cyl.bsKernel c (x - y)) 1
      have hK_le : ‖Kdot x‖ ≤ maj x := by
        rw [Real.norm_eq_abs]
        calc |Cyl.bsKernel c (x - y) 0 * B0579.pd 0 φ x +
              Cyl.bsKernel c (x - y) 1 * B0579.pd 1 φ x|
            ≤ |Cyl.bsKernel c (x - y) 0 * B0579.pd 0 φ x| +
                |Cyl.bsKernel c (x - y) 1 * B0579.pd 1 φ x| := abs_add_le _ _
          _ = |Cyl.bsKernel c (x - y) 0| * |B0579.pd 0 φ x| +
                |Cyl.bsKernel c (x - y) 1| * |B0579.pd 1 φ x| := by rw [abs_mul, abs_mul]
          _ ≤ maj x := add_le_add
                (mul_le_mul_of_nonneg_right hk0_le (abs_nonneg _))
                (mul_le_mul_of_nonneg_right hk1_le (abs_nonneg _))
      calc ‖F n x‖
          = (B0592.den c (x - y) / (B0592.den c (x - y) + εSeq n)) * ‖Kdot x‖ := by
            rw [norm_mul, Real.norm_of_nonneg hrat_nn]
        _ ≤ 1 * ‖Kdot x‖ := mul_le_mul_of_nonneg_right hrat_le1 (norm_nonneg _)
        _ ≤ maj x := by rw [one_mul]; exact hK_le
    · refine Eventually.of_forall fun x => ?_
      rcases eq_or_ne (B0592.den c (x - y)) 0 with hd0 | hd_ne
      · obtain ⟨hk0, hk1⟩ := bsKernel_eq_trig hc0 (x - y)
        have hK0 : Kdot x = 0 := by simp [Kdot, hk0, hk1, hd0]
        simp [F, hK0]
      · have hε_tend : Tendsto εSeq atTop (𝓝 0) :=
          tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
        have hrat_tend : Tendsto
            (fun n : ℕ => B0592.den c (x - y) / (B0592.den c (x - y) + εSeq n))
            atTop (𝓝 1) := by
          have h1 := (tendsto_const_nhds (x := B0592.den c (x - y))).div
            ((tendsto_const_nhds (x := B0592.den c (x - y))).add hε_tend)
            (by simpa using hd_ne)
          rw [add_zero, div_self hd_ne] at h1
          exact h1
        simpa [F, one_mul] using hrat_tend.mul_const (Kdot x)
  have hzero_tend : Tendsto (fun n : ℕ => ∫ x in B0579.cell c, F n x) atTop (𝓝 0) := by
    simp_rw [hF_int_zero]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique htend_int hzero_tend

/-! ## 3. Fubini and weak divergence-freeness of `Cyl.K c g` -/

private def prodTerm (c : ℝ) (g0 ψ : B0579.Plane → ℝ) (j : Fin 2)
    (p : B0579.Plane × B0579.Plane) : ℝ :=
  g0 p.2 * (Cyl.bsKernel c (p.1 - p.2) j * ψ p.1)

private theorem integrable_prodTerm {c : ℝ} (hc : 1 ≤ c) {g0 : B0579.Plane → ℝ}
    (hg0_m : Measurable g0) (hg0_int : IntegrableOn g0 (B0579.cell c) volume)
    {ψ : B0579.Plane → ℝ} (hψ : B0579.IsCylTest c ψ) (j : Fin 2) :
    Integrable (prodTerm c g0 ψ j)
      ((volume.restrict (B0579.cell c)).prod (volume.restrict (B0579.cell c))) := by
  let μ := volume.restrict (B0579.cell c)
  have hm_k : Measurable (fun p : B0579.Plane × B0579.Plane => Cyl.bsKernel c (p.1 - p.2) j) :=
    (EuclideanSpace.proj j).continuous.measurable.comp
      ((Cyl.measurable_bsKernel c).comp (measurable_fst.sub measurable_snd))
  have hm_prod : Measurable (prodTerm c g0 ψ j) :=
    (hg0_m.comp measurable_snd).mul (hm_k.mul (hψ.continuous.measurable.comp measurable_fst))
  refine ⟨hm_prod.aestronglyMeasurable, ?_⟩
  obtain ⟨C_ψ, hC_lt, hC⟩ := lintegral_norm_bsKernel_mul_test_le hc hψ
  change ∫⁻ p, ‖prodTerm c g0 ψ j p‖ₑ ∂(μ.prod μ) < ⊤
  rw [lintegral_prod_symm _ hm_prod.enorm.aemeasurable]
  have h_inner : ∀ y : B0579.Plane,
      (∫⁻ x, ‖prodTerm c g0 ψ j (x, y)‖ₑ ∂μ) ≤ ‖g0 y‖ₑ * C_ψ := by
    intro y
    have hm_x : Measurable (fun x : B0579.Plane => ‖Cyl.bsKernel c (x - y)‖ₑ * ‖ψ x‖ₑ) :=
      (((Cyl.measurable_bsKernel c).comp (measurable_id.sub measurable_const)).enorm).mul
        hψ.continuous.measurable.enorm
    have hpw : ∀ x : B0579.Plane,
        ‖prodTerm c g0 ψ j (x, y)‖ₑ ≤
          ‖g0 y‖ₑ * (‖Cyl.bsKernel c (x - y)‖ₑ * ‖ψ x‖ₑ) := by
      intro x
      simp only [prodTerm, enorm_mul]
      refine mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right ?_ zero_le) zero_le
      rw [← enorm_norm, ← enorm_norm (Cyl.bsKernel c (x - y)),
        Real.enorm_eq_ofReal (norm_nonneg _), Real.enorm_eq_ofReal (norm_nonneg _)]
      exact ENNReal.ofReal_le_ofReal (PiLp.norm_apply_le (Cyl.bsKernel c (x - y)) j)
    calc ∫⁻ x, ‖prodTerm c g0 ψ j (x, y)‖ₑ ∂μ
        ≤ ∫⁻ x, ‖g0 y‖ₑ * (‖Cyl.bsKernel c (x - y)‖ₑ * ‖ψ x‖ₑ) ∂μ := lintegral_mono hpw
      _ = ‖g0 y‖ₑ * ∫⁻ x, ‖Cyl.bsKernel c (x - y)‖ₑ * ‖ψ x‖ₑ ∂μ :=
          lintegral_const_mul _ hm_x
      _ ≤ ‖g0 y‖ₑ * C_ψ := mul_le_mul_of_nonneg_left (hC y) zero_le
  calc ∫⁻ y, (∫⁻ x, ‖prodTerm c g0 ψ j (x, y)‖ₑ ∂μ) ∂μ
      ≤ ∫⁻ y, ‖g0 y‖ₑ * C_ψ ∂μ := lintegral_mono h_inner
    _ = (∫⁻ y, ‖g0 y‖ₑ ∂μ) * C_ψ := lintegral_mul_const _ hg0_m.enorm
    _ < ⊤ := ENNReal.mul_lt_top hg0_int.2 hC_lt

private theorem ae_K_coord_mul_eq_integral {c m : ℝ} (hc : 1 ≤ c) (hm : 1 < m) (g : Xmc c m)
    {g0 : B0579.Plane → ℝ} (hg0_ae : (g : B0579.Plane → ℝ) =ᵐ[volume.restrict (B0579.cell c)] g0)
    (ψ : B0579.Plane → ℝ) (j : Fin 2) :
    (fun x => Cyl.K c g x j * ψ x) =ᵐ[volume.restrict (B0579.cell c)]
      fun x => ∫ y, prodTerm c g0 ψ j (x, y) ∂(volume.restrict (B0579.cell c)) := by
  let μ := volume.restrict (B0579.cell c)
  filter_upwards [ae_integrable_bsKernel hc hm g] with x hx
  have hx0 : Integrable (fun y => g0 y • Cyl.bsKernel c (x - y)) μ := by
    refine hx.congr ?_
    filter_upwards [hg0_ae] with y hy
    rw [hy]
  rw [CCP.K_eq_rep g g0 hg0_ae x]
  let Lj : Cyl.Vec2 →L[ℝ] ℝ := EuclideanSpace.proj j
  have hproj : Cyl.K c g0 x j = ∫ y, g0 y * Cyl.bsKernel c (x - y) j ∂μ := by
    change Lj (Cyl.K c g0 x) = _
    unfold Cyl.K
    rw [← cell_eq_cylCell, ← Lj.integral_comp_comm hx0]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp [Lj]
  rw [hproj, ← integral_mul_const]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp [prodTerm, mul_assoc]

/-- Integrability of `x ↦ Cyl.K c g x j * ψ x` on `B0579.cell c` for any cylinder test `ψ`. -/
theorem integrableOn_K_mul_test {c m : ℝ} (hc : 1 ≤ c) (hm : 1 < m) (g : Xmc c m)
    {ψ : B0579.Plane → ℝ} (hψ : B0579.IsCylTest c ψ) (j : Fin 2) :
    IntegrableOn (fun x => Cyl.K c g x j * ψ x) (B0579.cell c) volume := by
  obtain ⟨C1, _, hC1⟩ := CCP.exists_L1_const c m (by linarith)
  obtain ⟨g0, hg0_m, hg0_int, _, hg0_ae, _, _⟩ := CCP.exists_rep (by linarith) C1 hC1 g
  have hprod := integrable_prodTerm hc hg0_m hg0_int.integrableOn hψ j
  exact hprod.integral_prod_left.congr
    (ae_K_coord_mul_eq_integral hc hm g hg0_ae ψ j).symm

/-- Weak divergence-freeness of `Cyl.K c g`:
`∫_{cell c} (K_c g · ∇φ) = 0` for every cylinder test `φ`. -/
theorem integral_K_dot_grad_test_eq_zero {c m : ℝ} (hc : 1 ≤ c) (hm : 1 < m) (g : Xmc c m)
    {φ : B0579.Plane → ℝ} (hφ : B0579.IsCylTest c φ) :
    ∫ x in B0579.cell c,
      (Cyl.K c g x 0 * B0579.pd 0 φ x + Cyl.K c g x 1 * B0579.pd 1 φ x) = 0 := by
  let μ := volume.restrict (B0579.cell c)
  obtain ⟨C1, _, hC1⟩ := CCP.exists_L1_const c m (by linarith)
  obtain ⟨g0, hg0_m, hg0_int, _, hg0_ae, _, _⟩ := CCP.exists_rep (by linarith) C1 hC1 g
  have hprod0 := integrable_prodTerm hc hg0_m hg0_int.integrableOn (hφ.pd 0) 0
  have hprod1 := integrable_prodTerm hc hg0_m hg0_int.integrableOn (hφ.pd 1) 1
  have hint0 := integrableOn_K_mul_test hc hm g (hφ.pd 0) 0
  have hint1 := integrableOn_K_mul_test hc hm g (hφ.pd 1) 1
  have hfub0 : ∫ x, Cyl.K c g x 0 * B0579.pd 0 φ x ∂μ =
      ∫ y, (∫ x, prodTerm c g0 (B0579.pd 0 φ) 0 (x, y) ∂μ) ∂μ := by
    rw [integral_congr_ae (ae_K_coord_mul_eq_integral hc hm g hg0_ae (B0579.pd 0 φ) 0),
      ← integral_prod _ hprod0, integral_prod_symm _ hprod0]
  have hfub1 : ∫ x, Cyl.K c g x 1 * B0579.pd 1 φ x ∂μ =
      ∫ y, (∫ x, prodTerm c g0 (B0579.pd 1 φ) 1 (x, y) ∂μ) ∂μ := by
    rw [integral_congr_ae (ae_K_coord_mul_eq_integral hc hm g hg0_ae (B0579.pd 1 φ) 1),
      ← integral_prod _ hprod1, integral_prod_symm _ hprod1]
  change ∫ x, (Cyl.K c g x 0 * B0579.pd 0 φ x + Cyl.K c g x 1 * B0579.pd 1 φ x) ∂μ = 0
  rw [integral_add hint0 hint1, hfub0, hfub1,
    ← integral_add hprod0.integral_prod_right hprod1.integral_prod_right]
  have hae_zero : ∀ᵐ y ∂μ,
      (∫ x, prodTerm c g0 (B0579.pd 0 φ) 0 (x, y) ∂μ) +
        (∫ x, prodTerm c g0 (B0579.pd 1 φ) 1 (x, y) ∂μ) = 0 := by
    filter_upwards [hprod0.prod_left_ae, hprod1.prod_left_ae] with y hy0 hy1
    rw [← integral_add hy0 hy1]
    have heq : (fun x : B0579.Plane =>
        prodTerm c g0 (B0579.pd 0 φ) 0 (x, y) + prodTerm c g0 (B0579.pd 1 φ) 1 (x, y)) =
        fun x => g0 y *
          (Cyl.bsKernel c (x - y) 0 * B0579.pd 0 φ x +
            Cyl.bsKernel c (x - y) 1 * B0579.pd 1 φ x) := by
      funext x
      simp only [prodTerm]
      ring
    rw [heq, integral_const_mul]
    change g0 y * (∫ x in B0579.cell c,
      (Cyl.bsKernel c (x - y) 0 * B0579.pd 0 φ x +
        Cyl.bsKernel c (x - y) 1 * B0579.pd 1 φ x)) = 0
    rw [integral_bsKernel_dot_grad_test_eq_zero hc y hφ, mul_zero]
  rw [integral_congr_ae hae_zero, integral_zero]

end UnforcedLeray.Short.IIb.ZeroCircAux
