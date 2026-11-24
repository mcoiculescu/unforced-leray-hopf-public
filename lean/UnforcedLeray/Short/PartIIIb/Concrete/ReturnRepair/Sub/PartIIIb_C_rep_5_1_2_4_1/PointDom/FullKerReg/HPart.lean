import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4_1.PointDom.FullKerReg.Small

/-!
# The `h`-derivative and the limit `h ↓ 0` of the two parts of `fullKer`
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray

/-- The `PDKerBounds` conclusion for one constant. -/
def PDKB (C : ℝ) : Prop := ∀ (ν μ h : ℝ), 0 < ν → -(1 / 4) < μ → μ ≤ 1 → 0 < h →
    ∀ (M : Matrix (Fin 3) (Fin 3) ℝ),
      ContDiff ℝ 2 (fun x' => xKer ν μ h x' M) ∧
      (∀ x : Space, DifferentiableAt ℝ (fun h' => xKer ν μ h' x M) h) ∧
      ∀ x : Space, x ≠ 0 →
        ‖xKer ν μ h x M‖ ≤ C * pdLam h ^ (2 * μ + 3) * (‖x‖ ^ 4)⁻¹ * IIIa.tensorNorm M ∧
        ‖fderiv ℝ (fun x' => xKer ν μ h x' M) x‖ ≤
          C * pdLam h ^ (2 * μ + 3) * (‖x‖ ^ 5)⁻¹ * IIIa.tensorNorm M ∧
        ‖iteratedFDeriv ℝ 2 (fun x' => xKer ν μ h x' M) x‖ ≤
          C * pdLam h ^ (2 * μ + 3) * (‖x‖ ^ 6)⁻¹ * IIIa.tensorNorm M ∧
        ‖deriv (fun h' => xKer ν μ h' x M) h‖ ≤
          C * pdLam h ^ (2 * μ + 3) * ((‖x‖ ^ 4)⁻¹ + ν * (‖x‖ ^ 6)⁻¹) * IIIa.tensorNorm M ∧
        ‖wKer ν μ h x M‖ ≤ C * pdLam h ^ (2 * μ + 3) * (‖x‖ ^ 4)⁻¹ * IIIa.tensorNorm M

/-- The vector-valued joint kernel. -/
def Jv (ν μ : ℝ) (M : Matrix (Fin 3) (Fin 3) ℝ) (p : ℝ × Space) : Space := xKer ν μ p.1 p.2 M

theorem Jv_diffAt (ν μ : ℝ) (hν : 0 < ν) (M : Matrix (Fin 3) (Fin 3) ℝ) {h : ℝ} (hh : 0 < h)
    (x : Space) : DifferentiableAt ℝ (Jv ν μ M) (h, x) :=
  (((xKer_jointC2 ν μ hν M).differentiableOn (by norm_num) (h, x) hh)).differentiableAt
    ((isOpen_lt continuous_const continuous_fst).mem_nhds hh)

theorem Jv_dir (ν μ : ℝ) (hν : 0 < ν) (M : Matrix (Fin 3) (Fin 3) ℝ) {h : ℝ} (hh : 0 < h)
    (x v : Space) :
    fderiv ℝ (Jv ν μ M) (h, x) (1, v) = deriv (fun h' => xKer ν μ h' x M) h +
      fderiv ℝ (fun x' => xKer ν μ h x' M) x v := by
  have hJ := (Jv_diffAt ν μ hν M hh x).hasFDerivAt
  have h1 : HasDerivAt (fun h' => xKer ν μ h' x M) (fderiv ℝ (Jv ν μ M) (h, x) (1, 0)) h := by
    have := hJ.comp_hasDerivAt h ((hasDerivAt_id h).prodMk (hasDerivAt_const h x))
    simpa [Jv, Function.comp_def] using this
  have h2 : HasFDerivAt (fun x' => xKer ν μ h x' M)
      ((fderiv ℝ (Jv ν μ M) (h, x)).comp (ContinuousLinearMap.prod 0 (ContinuousLinearMap.id ℝ Space))) x :=
    hJ.comp x ((hasFDerivAt_const h x).prodMk (hasFDerivAt_id x))
  rw [h1.deriv, h2.fderiv]
  have : ((1 : ℝ), v) = ((1 : ℝ), (0 : Space)) + ((0 : ℝ), v) := by simp
  rw [this, map_add]
  simp

/-- `h`-derivative of the `χ_y xKer` part. -/
theorem xHder {C : ℝ} (hC0 : 0 ≤ C) (hC : PDKB C) (ν μ R : ℝ) (hν : 0 < ν) (hμ0 : -(1 / 4) < μ)
    (hμ1 : μ ≤ 1) {χ : ℝ → ℝ} (hχ : IsYoungCutoff χ) {r₁ ρ₀ Y : ℝ} (hρ₀ : 0 ≤ ρ₀) (hρr : ρ₀ < r₁)
    (M : Matrix (Fin 3) (Fin 3) ℝ) {z : Space} (hz : ϱ z ≤ ρ₀) {h : ℝ} (hh : 0 < h)
    {y : Space} (hy : r₁ < ϱ y) (hyY : ‖y‖ < Y) :
    ∃ d : Space, HasDerivAt (fun h' => χ (ν * age R y) • xKer ν μ h' (y - pdLam h' • z) M) d h ∧
      ‖d‖ ≤ (C * pdLam h ^ (2 * μ + 3) * IIIa.tensorNorm M) * ((‖y - pdLam h • z‖ ^ 4)⁻¹ *
        (2 + ν * ((r₁ - ρ₀)⁻¹) ^ 2 + Y * (r₁ - ρ₀)⁻¹)) := by
  set δ := r₁ - ρ₀ with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  have hl0 := pdLam_pos h
  have hl1 := (pdLam_lt_one hh).le
  set x := y - pdLam h • z with hx
  have hxδ : δ ≤ ‖x‖ := norm_sub_lam_ge hl0 hl1 hz hy
  have hx0 : x ≠ 0 := by intro h0; rw [h0, norm_zero] at hxδ; linarith
  have hxd : HasDerivAt (fun h' => y - pdLam h' • z) ((pdLam h / 2) • z) h := by
    have h1 := (pdLam_hasDerivAt h).smul_const z
    have h2 := h1.const_sub y
    refine h2.congr_deriv ?_
    rw [← neg_smul]; congr 1; ring
  have hJd := (Jv_diffAt ν μ hν M hh x).hasFDerivAt.comp_hasDerivAt h ((hasDerivAt_id h).prodMk hxd)
  refine ⟨χ (ν * age R y) • fderiv ℝ (Jv ν μ M) (h, x) (1, (pdLam h / 2) • z),
    hJd.const_smul (χ (ν * age R y)), ?_⟩
  rw [norm_smul, Real.norm_eq_abs, Jv_dir ν μ hν M hh]
  obtain ⟨-, -, hb⟩ := hC ν μ h hν hμ0 hμ1 hh M
  obtain ⟨-, hb1, -, hb3, -⟩ := hb x hx0
  have hchi : |χ (ν * age R y)| ≤ 1 := by
    rw [abs_of_nonneg (hχ.range _).1]; exact (hχ.range _).2
  have hv : ‖(pdLam h / 2) • z‖ ≤ ‖x‖ + Y := by
    have := lam_norm_le (z := z) (y := y) (l := pdLam h) (Y := Y) hl0 hyY
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith : 0 < pdLam h / 2)]
    nlinarith [norm_nonneg z]
  have e1 : ‖fderiv ℝ (fun x' => xKer ν μ h x' M) x ((pdLam h / 2) • z)‖ ≤
      (C * pdLam h ^ (2 * μ + 3) * (‖x‖ ^ 5)⁻¹ * IIIa.tensorNorm M) * (‖x‖ + Y) :=
    ((fderiv ℝ (fun x' => xKer ν μ h x' M) x).le_opNorm _).trans
      (mul_le_mul hb1 hv (norm_nonneg _)
        (mul_nonneg (mul_nonneg (mul_nonneg hC0 (kb_coef_bounds μ h hμ0 hμ1 hh).1)
          (inv_nonneg.2 (pow_nonneg (norm_nonneg _) 5))) (kb_tensor_nonneg M)))
  have hk := inv_pow_succ_le hδ0 hxδ
  have e5 : (‖x‖ ^ 5)⁻¹ ≤ δ⁻¹ * (‖x‖ ^ 4)⁻¹ := hk 4
  have e6 : (‖x‖ ^ 6)⁻¹ ≤ δ⁻¹ ^ 2 * (‖x‖ ^ 4)⁻¹ := by
    calc (‖x‖ ^ 6)⁻¹ ≤ δ⁻¹ * (‖x‖ ^ 5)⁻¹ := hk 5
      _ ≤ δ⁻¹ * (δ⁻¹ * (‖x‖ ^ 4)⁻¹) := mul_le_mul_of_nonneg_left e5 (by positivity)
      _ = δ⁻¹ ^ 2 * (‖x‖ ^ 4)⁻¹ := by ring
  have hK0 : 0 ≤ C * pdLam h ^ (2 * μ + 3) * IIIa.tensorNorm M :=
    mul_nonneg (mul_nonneg hC0 (kb_coef_bounds μ h hμ0 hμ1 hh).1) (kb_tensor_nonneg M)
  have hP : 0 ≤ (‖x‖ ^ 4)⁻¹ := by positivity
  have hxp : 0 < ‖x‖ := lt_of_lt_of_le hδ0 hxδ
  have hx5 : (‖x‖ ^ 5)⁻¹ * ‖x‖ = (‖x‖ ^ 4)⁻¹ := by field_simp
  have hY0 : 0 ≤ Y := by have := norm_nonneg y; linarith
  have e2 : (‖x‖ ^ 5)⁻¹ * (‖x‖ + Y) ≤ (‖x‖ ^ 4)⁻¹ * (1 + Y * δ⁻¹) := by
    calc (‖x‖ ^ 5)⁻¹ * (‖x‖ + Y) = (‖x‖ ^ 4)⁻¹ + Y * (‖x‖ ^ 5)⁻¹ := by
          rw [mul_add, hx5]; ring
      _ ≤ (‖x‖ ^ 4)⁻¹ + Y * (δ⁻¹ * (‖x‖ ^ 4)⁻¹) := by gcongr
      _ = (‖x‖ ^ 4)⁻¹ * (1 + Y * δ⁻¹) := by ring
  calc |χ (ν * age R y)| * ‖deriv (fun h' => xKer ν μ h' x M) h +
        fderiv ℝ (fun x' => xKer ν μ h x' M) x ((pdLam h / 2) • z)‖
      ≤ 1 * (‖deriv (fun h' => xKer ν μ h' x M) h‖ +
        ‖fderiv ℝ (fun x' => xKer ν μ h x' M) x ((pdLam h / 2) • z)‖) :=
        mul_le_mul hchi (norm_add_le _ _) (norm_nonneg _) zero_le_one
    _ ≤ 1 * ((C * pdLam h ^ (2 * μ + 3) * ((‖x‖ ^ 4)⁻¹ + ν * (‖x‖ ^ 6)⁻¹) * IIIa.tensorNorm M) +
        (C * pdLam h ^ (2 * μ + 3) * IIIa.tensorNorm M) * ((‖x‖ ^ 5)⁻¹ * (‖x‖ + Y))) := by
        refine mul_le_mul_of_nonneg_left (add_le_add hb3 (e1.trans (le_of_eq (by ring)))) (by norm_num)
    _ ≤ _ := by
        have h1 : (C * pdLam h ^ (2 * μ + 3) * IIIa.tensorNorm M) * ((‖x‖ ^ 5)⁻¹ * (‖x‖ + Y)) ≤
            (C * pdLam h ^ (2 * μ + 3) * IIIa.tensorNorm M) * ((‖x‖ ^ 4)⁻¹ * (1 + Y * δ⁻¹)) :=
          mul_le_mul_of_nonneg_left e2 hK0
        have h2 : (C * pdLam h ^ (2 * μ + 3) * ((‖x‖ ^ 4)⁻¹ + ν * (‖x‖ ^ 6)⁻¹) * IIIa.tensorNorm M) ≤
            (C * pdLam h ^ (2 * μ + 3) * IIIa.tensorNorm M) * ((‖x‖ ^ 4)⁻¹ * (1 + ν * δ⁻¹ ^ 2)) := by
          have : (‖x‖ ^ 4)⁻¹ + ν * (‖x‖ ^ 6)⁻¹ ≤ (‖x‖ ^ 4)⁻¹ * (1 + ν * δ⁻¹ ^ 2) := by
            have := mul_le_mul_of_nonneg_left e6 hν.le
            nlinarith
          have h3 := mul_le_mul_of_nonneg_left this hK0
          calc _ = (C * pdLam h ^ (2 * μ + 3) * IIIa.tensorNorm M) * ((‖x‖ ^ 4)⁻¹ + ν * (‖x‖ ^ 6)⁻¹) := by ring
            _ ≤ _ := h3
        rw [one_mul]
        exact (add_le_add h2 h1).trans (le_of_eq (by ring))

end UnforcedLeray.Short.PartIIIb.Concrete

end
