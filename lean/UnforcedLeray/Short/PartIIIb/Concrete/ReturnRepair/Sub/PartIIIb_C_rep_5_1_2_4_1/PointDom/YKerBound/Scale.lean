import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4_1.PointDom.YKerBound.Dil

/-!
# `PDYKerBound` helpers (8): parabolic scaling

Source `the November 2 reference manuscript` 3604-3610 (the kernels are
homogeneous: `∇K_t(x) = t^{-2}(∇K_1)(x/√t)`), 4178-4186.

The kernel of `X = 𝒞_y X₀` is parabolically homogeneous of degree `-4`:
`fullKer (νc²) (c y) (c z) = c^{-4} fullKer ν y z`, and `D_{μ+1}` commutes with the dilation up to
`ν ↦ νc²` (`ykb_physDmu_scale`).  This reduces `PDYKerBound` to the receiver radius `ϱ y = 1`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- `fderiv` of `y ↦ g (c y)`, unconditionally. -/
theorem ykb_fderiv_comp_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : Space → E) {c : ℝ} (hc : c ≠ 0) (y v : Space) :
    fderiv ℝ (fun y' => g (c • y')) y v = c • fderiv ℝ g (c • y) v := by
  set e : Space ≃L[ℝ] Space := ContinuousLinearEquiv.smulLeft (Units.mk0 c hc) with hedef
  have he : ∀ w : Space, e w = c • w := fun w => by
    simp [hedef, Units.smul_def]
  have hfun : (fun y' => g (c • y')) = g ∘ e := by
    funext y'; simp [he]
  rw [hfun, ContinuousLinearEquiv.comp_right_fderiv]
  simp only [ContinuousLinearMap.coe_comp', ContinuousLinearEquiv.coe_coe, Function.comp_apply,
    he, map_smul]

theorem ykb_fderiv_smul_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : Space → E) (a : ℝ) {c : ℝ} (hc : c ≠ 0) (y v : Space) :
    fderiv ℝ (fun y' => a • g (c • y')) y v = (a * c) • fderiv ℝ g (c • y) v := by
  have e : (fun y' => a • g (c • y')) = a • (fun y' => g (c • y')) := rfl
  rw [e, fderiv_const_smul_field]
  simp only [Pi.smul_apply, ContinuousLinearMap.smul_apply]
  rw [ykb_fderiv_comp_smul g hc, smul_smul]

/-- **`D_μ` and the dilation.** -/
theorem ykb_physDmu_scale (ν μ' a : ℝ) {c : ℝ} (hc : c ≠ 0) (X Y : ℝ → Space → Space) (h : ℝ)
    (y : Space) (hXY : ∀ᶠ t in 𝓝 h, ∀ y', X t y' = a • Y t (c • y')) :
    physDmu ν μ' X h y = a • physDmu (ν * c ^ 2) μ' Y h (c • y) := by
  have hXh : X h = fun y' => a • Y h (c • y') := funext hXY.self_of_nhds
  have hd : deriv (fun t => X t y) h = a • deriv (fun t => Y t (c • y)) h := by
    have hev : (fun t => X t y) =ᶠ[𝓝 h] (a • fun t => Y t (c • y)) :=
      hXY.mono fun t ht => ht y
    rw [hev.deriv_eq, deriv_const_smul_field]
  have hf : fderiv ℝ (X h) y y = a • fderiv ℝ (Y h) (c • y) (c • y) := by
    rw [hXh, ykb_fderiv_smul_comp (Y h) a hc y y, map_smul, smul_smul]
  have hl : physLap (X h) y = (a * c ^ 2) • physLap (Y h) (c • y) := by
    unfold physLap physPd2 physPd
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hin : (fun y' => fderiv ℝ (X h) y' (coordinateVector j)) =
        fun y' => (a * c) • (fun w => fderiv ℝ (Y h) w (coordinateVector j)) (c • y') := by
      funext y'
      rw [hXh, ykb_fderiv_smul_comp (Y h) a hc y' (coordinateVector j)]
    rw [hin, ykb_fderiv_smul_comp (fun w => fderiv ℝ (Y h) w (coordinateVector j)) (a * c) hc y
      (coordinateVector j)]
    congr 1
    ring
  unfold physDmu
  rw [hd, hf, hl]
  have hX : X h y = a • Y h (c • y) := by rw [hXh]
  rw [hX]
  module

/-- Parabolic scaling of the phase-lag kernel. -/
theorem ykb_xKer_scale (ν μ t : ℝ) (hν : 0 < ν) (ht : 0 < t) {c : ℝ} (hc : 0 < c) (x : Space)
    (M : Matrix (Fin 3) (Fin 3) ℝ) :
    xKer (ν * c ^ 2) μ t (c • x) M = (c ^ 4)⁻¹ • xKer ν μ t x M := by
  have hT := kb_hT ν t hν ht
  set T := ν * (1 - pdLam t ^ 2) with hTdef
  have hT' : ν * c ^ 2 * (1 - pdLam t ^ 2) = c ^ 2 * T := by rw [hTdef]; ring
  unfold xKer
  rw [hT', scale_gradK _ (by positivity), scale_gradK _ hT, smul_comm (c ^ 4)⁻¹]
  congr 1
  have hs : Real.sqrt (c ^ 2 * T) = c * Real.sqrt T := by
    rw [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc.le]
  rw [hs, smul_smul]
  have hsT : 0 < Real.sqrt T := Real.sqrt_pos.2 hT
  have e1 : (c * Real.sqrt T)⁻¹ * c = (Real.sqrt T)⁻¹ := by field_simp
  rw [e1, smul_smul]
  congr 1
  field_simp

/-- Scaling of the outward primitive. -/
theorem ykb_sKer_scale (ν μ t : ℝ) (hν : 0 < ν) (ht : 0 < t) {c : ℝ} (hc : 0 < c) (r y3 : ℝ)
    (z : Space) (M : Matrix (Fin 3) (Fin 3) ℝ) :
    sKer (ν * c ^ 2) μ t (c * r) (c * y3) (c • z) M = (c ^ 2)⁻¹ * sKer ν μ t r y3 z M := by
  unfold sKer
  have h := integral_comp_mul_left_Ioi
    (fun ρ : ℝ => ρ * xKer (ν * c ^ 2) μ t (!₂[ρ, 0, c * y3] - pdLam t • c • z) M 2) r hc
  have h2 : ∫ ρ in Ioi (c * r), ρ * xKer (ν * c ^ 2) μ t (!₂[ρ, 0, c * y3] - pdLam t • c • z) M 2 =
      c * ∫ ρ in Ioi r, (c * ρ) * xKer (ν * c ^ 2) μ t (!₂[c * ρ, 0, c * y3] - pdLam t • c • z) M 2 := by
    rw [h, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul]
  rw [h2]
  have h3 : ∀ ρ : ℝ, (c * ρ) * xKer (ν * c ^ 2) μ t (!₂[c * ρ, 0, c * y3] - pdLam t • c • z) M 2 =
      (c ^ 3)⁻¹ * (ρ * xKer ν μ t (!₂[ρ, 0, y3] - pdLam t • z) M 2) := by
    intro ρ
    have e : (!₂[c * ρ, 0, c * y3] - pdLam t • c • z : Space) = c • (!₂[ρ, 0, y3] - pdLam t • z) := by
      ext i; fin_cases i <;> simp <;> ring
    rw [e, ykb_xKer_scale ν μ t hν ht hc]
    simp only [PiLp.smul_apply, smul_eq_mul]
    field_simp
  simp_rw [h3]
  rw [integral_const_mul]
  field_simp

/-- **Parabolic homogeneity of `fullKer`.** -/
theorem ykb_fullKer_scale (ν μ R : ℝ) (χ : ℝ → ℝ) (t : ℝ) (hν : 0 < ν) (ht : 0 < t) {c : ℝ}
    (hc : 0 < c) (y z : Space) (M : Matrix (Fin 3) (Fin 3) ℝ) :
    fullKer ν μ R χ t y z M = c ^ 4 • fullKer (ν * c ^ 2) μ R χ t (c • y) (c • z) M := by
  have hϱ : ϱ (c • y) = c * ϱ y := ykb_ϱ_smul hc.le y
  have hage : ν * c ^ 2 * age R (c • y) = ν * age R y := by
    unfold age; rw [hϱ, mul_pow, div_mul_eq_div_div]
    field_simp
  have h2 : (c • y) 2 = c * y 2 := by simp
  have hx : c • y - pdLam t • c • z = c • (y - pdLam t • z) := by
    rw [smul_comm (pdLam t) c z, smul_sub]
  unfold fullKer
  rw [hage, hϱ, h2, hx, ykb_xKer_scale ν μ t hν ht hc, ykb_sKer_scale ν μ t hν ht hc]
  rw [smul_add, smul_smul, smul_smul]
  have e1 : c ^ 4 * χ (ν * age R y) * (c ^ 4)⁻¹ = χ (ν * age R y) := by field_simp
  rw [e1]
  congr 1
  rw [smul_smul]
  congr 1
  by_cases h0 : ϱ y = 0
  · simp [h0]
  · field_simp

end UnforcedLeray.Short.PartIIIb.Concrete

end
