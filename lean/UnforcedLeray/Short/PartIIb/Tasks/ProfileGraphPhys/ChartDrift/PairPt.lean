import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.ChartDrift.Lift

/-!
# `PartII-b:T10/6/3/1/2a`: the pointwise pairing of the lifted test with `N_v b`

Off the axis the frame `(e_r, e_z)` is orthonormal, so `dotL (N_v B) (N_v b) = s B·b` with
`s = age`; on the axis `age = 0` and both sides vanish.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.IIb.ChartLift

open UnforcedLeray.PhaseSpace UnforcedLeray.Cons.C03.Concrete

/-- Component formula for the complex ring lift `N_v`. -/
theorem nvC_comp_apply (R : ℝ) (b : CProf) (τ : ℝ) (y : EuclideanSpace ℝ (Fin 3)) (j : Fin 3) :
    NvC R b (τ, y) j = ((√(UnforcedLeray.Axi.age R y) : ℝ) : ℂ) *
      (b (UnforcedLeray.Axi.chart R τ y) 0 * ((UnforcedLeray.Axi.eR y j : ℝ) : ℂ) +
        b (UnforcedLeray.Axi.chart R τ y) 1 * ((UnforcedLeray.Axi.e3 j : ℝ) : ℂ)) := by
  have e0 : (((b (UnforcedLeray.Axi.chart R τ y)) 0).re : ℂ) +
      Complex.I * ((((b (UnforcedLeray.Axi.chart R τ y)) 0).im : ℝ) : ℂ) =
        (b (UnforcedLeray.Axi.chart R τ y)) 0 := by
    rw [mul_comm]; exact Complex.re_add_im _
  have e1 : ((((b (UnforcedLeray.Axi.chart R τ y)) 1).re : ℝ) : ℂ) +
      Complex.I * ((((b (UnforcedLeray.Axi.chart R τ y)) 1).im : ℝ) : ℂ) =
        (b (UnforcedLeray.Axi.chart R τ y)) 1 := by
    rw [mul_comm]; exact Complex.re_add_im _
  unfold NvC
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, UnforcedLeray.Axi.Nv,
    UnforcedLeray.Axi.frameL_apply, B0412.realC_apply, reM, imM]
  push_cast
  linear_combination (((√(UnforcedLeray.Axi.age R y) : ℝ) : ℂ) * ((UnforcedLeray.Axi.eR y j : ℝ) : ℂ)) * e0 + (((√(UnforcedLeray.Axi.age R y) : ℝ) : ℂ) * ((UnforcedLeray.Axi.e3 j : ℝ) : ℂ)) * e1

/-- On `ϱ ≠ 0` the meridional frame vector has unit length. -/
theorem eR_sq_sum (y : EuclideanSpace ℝ (Fin 3)) (hϱ : UnforcedLeray.Axi.ϱ y ≠ 0) :
    UnforcedLeray.Axi.eR y 0 ^ 2 + UnforcedLeray.Axi.eR y 1 ^ 2 = 1 := by
  rw [UnforcedLeray.Axi.eR_apply_zero, UnforcedLeray.Axi.eR_apply_one, div_pow, div_pow,
    ← add_div, ← UnforcedLeray.Axi.ϱ_sq, div_self (pow_ne_zero 2 hϱ)]

theorem pairPt_proof : UnforcedLeray.Short.IIb.ChartLift.PairPt := by
  intro c ε φ i b p hε
  obtain ⟨τ, y⟩ := p
  unfold liftTest pairG
  rw [dotL_apply]
  simp only [Fin.sum_univ_three, nvC_comp_apply]
  unfold liftB
  have ha0 : 0 ≤ UnforcedLeray.Axi.age ε⁻¹ y := UnforcedLeray.Axi.age_nonneg _ _
  have hz1 : (UnforcedLeray.Axi.chart ε⁻¹ τ y).1 = UnforcedLeray.Axi.age ε⁻¹ y := rfl
  have hS : ((√(UnforcedLeray.Axi.age ε⁻¹ y) : ℝ) : ℂ) * ((√(UnforcedLeray.Axi.age ε⁻¹ y) : ℝ) : ℂ)
      = ((UnforcedLeray.Axi.age ε⁻¹ y : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt ha0]
  have hpow_r : UnforcedLeray.Axi.age ε⁻¹ y ^ ((5:ℝ)/2) =
      UnforcedLeray.Axi.age ε⁻¹ y * UnforcedLeray.Axi.age ε⁻¹ y ^ ((3:ℝ)/2) := by
    rcases ha0.eq_or_lt with h0 | hpos
    · rw [← h0]; simp
    · have h52 : (5:ℝ)/2 = 3/2 + 1 := by norm_num
      rw [h52, Real.rpow_add hpos, Real.rpow_one]; ring
  have hpow : ((UnforcedLeray.Axi.age ε⁻¹ y ^ ((5:ℝ)/2) : ℝ) : ℂ) =
      ((UnforcedLeray.Axi.age ε⁻¹ y : ℝ) : ℂ) *
        ((UnforcedLeray.Axi.age ε⁻¹ y ^ ((3:ℝ)/2) : ℝ) : ℂ) := by
    rw [hpow_r]; push_cast; ring
  rw [hz1]
  generalize UnforcedLeray.Axi.chart ε⁻¹ τ y = z
  generalize hA : UnforcedLeray.Axi.age ε⁻¹ y = a at hS hpow ha0 ⊢
  by_cases hϱ : UnforcedLeray.Axi.ϱ y = 0
  · have ha : a = 0 := by
      rw [← hA]; simp [UnforcedLeray.Axi.age, hϱ]
    subst ha
    fin_cases i <;> norm_num [hϱ]
  · have hE : (y 0 / UnforcedLeray.Axi.ϱ y) ^ 2 + (y 1 / UnforcedLeray.Axi.ϱ y) ^ 2 = 1 := by
      have h := eR_sq_sum y hϱ
      simpa only [UnforcedLeray.Axi.eR_apply_zero, UnforcedLeray.Axi.eR_apply_one] using h
    have hEc : ((y 0 / UnforcedLeray.Axi.ϱ y : ℝ) : ℂ) ^ 2 + ((y 1 / UnforcedLeray.Axi.ϱ y : ℝ) : ℂ) ^ 2 = 1 := by
      rw [← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_add, hE, Complex.ofReal_one]
    push_cast at hEc
    fin_cases i <;> simp
    · linear_combination (((c:ℂ) * (ε:ℂ) ^ 2 / (Real.pi:ℂ) * ((a ^ ((3:ℝ)/2) : ℝ) : ℂ) * ((perCoord c φ z : ℝ) : ℂ)) * (b z 0) * ((((y 0 : ℝ) : ℂ) / ((UnforcedLeray.Axi.ϱ y : ℝ) : ℂ)) ^ 2 + (((y 1 : ℝ) : ℂ) / ((UnforcedLeray.Axi.ϱ y : ℝ) : ℂ)) ^ 2)) * hS + (((c:ℂ) * (ε:ℂ) ^ 2 / (Real.pi:ℂ) * ((a ^ ((3:ℝ)/2) : ℝ) : ℂ) * ((perCoord c φ z : ℝ) : ℂ)) * (b z 0) * ((a:ℝ):ℂ)) * hEc - (((c:ℂ) * (ε:ℂ) ^ 2 / (Real.pi:ℂ) * ((perCoord c φ z : ℝ) : ℂ)) * (b z 0)) * hpow
    · linear_combination (((c:ℂ) * (ε:ℂ) ^ 2 / (Real.pi:ℂ) * ((a ^ ((3:ℝ)/2) : ℝ) : ℂ) * ((perCoord c φ z : ℝ) : ℂ)) * (b z 1)) * hS - (((c:ℂ) * (ε:ℂ) ^ 2 / (Real.pi:ℂ) * ((perCoord c φ z : ℝ) : ℂ)) * (b z 1)) * hpow

end UnforcedLeray.Short.IIb.ChartLift
