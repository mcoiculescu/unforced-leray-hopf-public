import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4_1.PointDom.FullKerReg.Coef

/-!
# The `χ_y xKer` part of `fullKer`: smoothness and bounds in `y`
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray

/-- `‖x‖⁻ᵐ ≤ δ⁻¹ ‖x‖⁻ᵐ⁺¹`-type comparisons. -/
theorem inv_pow_succ_le {t δ : ℝ} (hδ : 0 < δ) (hδt : δ ≤ t) (k : ℕ) :
    (t ^ (k + 1))⁻¹ ≤ δ⁻¹ * (t ^ k)⁻¹ := by
  have ht : 0 < t := lt_of_lt_of_le hδ hδt
  rw [pow_succ, mul_inv]
  have : t⁻¹ ≤ δ⁻¹ := inv_anti₀ hδ hδt
  have h0 : 0 ≤ (t ^ k)⁻¹ := by positivity
  nlinarith

theorem xPart1 (C : ℝ) (hC0 : 0 ≤ C) (hC : ∀ (ν μ h : ℝ), 0 < ν → -(1 / 4) < μ → μ ≤ 1 → 0 < h →
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
        ‖wKer ν μ h x M‖ ≤ C * pdLam h ^ (2 * μ + 3) * (‖x‖ ^ 4)⁻¹ * IIIa.tensorNorm M)
    (ν μ R : ℝ) (hν : 0 < ν) (hμ0 : -(1 / 4) < μ) (hμ1 : μ ≤ 1) {χ : ℝ → ℝ} (hχ : IsYoungCutoff χ)
    {r₁ ρ₀ Y : ℝ} (hρ₀ : 0 ≤ ρ₀) (hρr : ρ₀ < r₁) {Bch : ℝ} (hBch0 : 0 ≤ Bch)
    (hBch : ∀ y : Space, r₁ ≤ ϱ y → ‖y‖ ≤ Y → ∀ i : ℕ, i ≤ 2 →
      ‖iteratedFDeriv ℝ i (fun y' : Space => χ (ν * age R y')) y‖ ≤ Bch)
    (M : Matrix (Fin 3) (Fin 3) ℝ) {z : Space} (hz : ϱ z ≤ ρ₀) {h : ℝ} (hh : 0 < h)
    {y : Space} (hy : r₁ < ϱ y) (hyY : ‖y‖ < Y) :
    ContDiffAt ℝ 2 (fun y' => χ (ν * age R y') • xKer ν μ h (y' - pdLam h • z) M) y ∧
    ∀ n : ℕ, n ≤ 2 → ‖iteratedFDeriv ℝ n
        (fun y' => χ (ν * age R y') • xKer ν μ h (y' - pdLam h • z) M) y‖ ≤
      4 * Bch * ((C * pdLam h ^ (2 * μ + 3) * IIIa.tensorNorm M) *
        ((‖y - pdLam h • z‖ ^ 4)⁻¹ * (1 + (r₁ - ρ₀)⁻¹ + ((r₁ - ρ₀)⁻¹) ^ 2))) := by
  set δ := r₁ - ρ₀ with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  have hr₁ : 0 < r₁ := lt_of_le_of_lt hρ₀ hρr
  have hl0 := pdLam_pos h
  have hl1 := (pdLam_lt_one hh).le
  set x := y - pdLam h • z with hx
  have hxδ : δ ≤ ‖x‖ := norm_sub_lam_ge hl0 hl1 hz hy
  have hx0 : x ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hxδ; linarith
  obtain ⟨hcd, -, hb⟩ := hC ν μ h hν hμ0 hμ1 hh M
  obtain ⟨hb0, hb1, hb2, -, -⟩ := hb x hx0
  set s : Set Space := {y | r₁ < ϱ y} with hs
  have hso : IsOpen s := isOpen_lt continuous_const continuous_ϱ
  have hξ : ContDiff ℝ 2 (fun y' : Space => xKer ν μ h (y' - pdLam h • z) M) :=
    hcd.comp (contDiff_id.sub contDiff_const)
  have hchs : ContDiffOn ℝ 2 (fun y' : Space => χ (ν * age R y')) s :=
    (ch_contDiffOn hχ ν R).mono (fun y' hy' => lt_trans hr₁ hy')
  refine ⟨?_, fun n hn => ?_⟩
  · exact ((hchs.smul hξ.contDiffOn).contDiffAt (hso.mem_nhds hy))
  · have hξn : ∀ i : ℕ, ‖iteratedFDeriv ℝ i (fun y' : Space => xKer ν μ h (y' - pdLam h • z) M) y‖ =
        ‖iteratedFDeriv ℝ i (fun x' => xKer ν μ h x' M) x‖ := by
      intro i
      have := iteratedFDeriv_comp_add_right (𝕜 := ℝ) (f := fun x' : Space => xKer ν μ h x' M) i
        (-(pdLam h • z)) y
      simp only [← sub_eq_add_neg] at this
      rw [this]
    have hk := inv_pow_succ_le hδ0 hxδ
    have hP : 0 ≤ (‖x‖ ^ 4)⁻¹ := by positivity
    have hK0 : 0 ≤ C * pdLam h ^ (2 * μ + 3) * IIIa.tensorNorm M :=
      mul_nonneg (mul_nonneg hC0 (kb_coef_bounds μ h hμ0 hμ1 hh).1) (kb_tensor_nonneg M)
    set K := C * pdLam h ^ (2 * μ + 3) * IIIa.tensorNorm M with hK
    have hBξ0 : 0 ≤ K * ((‖x‖ ^ 4)⁻¹ * (1 + δ⁻¹ + δ⁻¹ ^ 2)) := by positivity
    have hbound : ∀ i : ℕ, i ≤ 2 → ‖iteratedFDeriv ℝ i
        (fun y' : Space => xKer ν μ h (y' - pdLam h • z) M) y‖ ≤
        K * ((‖x‖ ^ 4)⁻¹ * (1 + δ⁻¹ + δ⁻¹ ^ 2)) := by
      intro i hi
      rw [hξn]
      have e5 : (‖x‖ ^ 5)⁻¹ ≤ δ⁻¹ * (‖x‖ ^ 4)⁻¹ := hk 4
      have e6 : (‖x‖ ^ 6)⁻¹ ≤ δ⁻¹ * (‖x‖ ^ 5)⁻¹ := hk 5
      have e6' : (‖x‖ ^ 6)⁻¹ ≤ δ⁻¹ ^ 2 * (‖x‖ ^ 4)⁻¹ := by
        calc (‖x‖ ^ 6)⁻¹ ≤ δ⁻¹ * (‖x‖ ^ 5)⁻¹ := e6
          _ ≤ δ⁻¹ * (δ⁻¹ * (‖x‖ ^ 4)⁻¹) := mul_le_mul_of_nonneg_left e5 (by positivity)
          _ = δ⁻¹ ^ 2 * (‖x‖ ^ 4)⁻¹ := by ring
      interval_cases i
      · rw [norm_iteratedFDeriv_zero]
        refine hb0.trans ?_
        rw [hK]; nlinarith [mul_nonneg hK0 hP, mul_nonneg hK0 (mul_nonneg hP (by positivity : (0:ℝ) ≤ δ⁻¹)),
          mul_nonneg hK0 (mul_nonneg hP (by positivity : (0:ℝ) ≤ δ⁻¹ ^ 2))]
      · rw [norm_iteratedFDeriv_one]
        refine hb1.trans ?_
        have := mul_le_mul_of_nonneg_left e5 hK0
        nlinarith [mul_nonneg hK0 hP, mul_nonneg hK0 (mul_nonneg hP (by positivity : (0:ℝ) ≤ δ⁻¹ ^ 2)),
          mul_nonneg hK0 (mul_nonneg hP (by positivity : (0:ℝ) ≤ δ⁻¹))]
      · refine hb2.trans ?_
        have := mul_le_mul_of_nonneg_left e6' hK0
        nlinarith [mul_nonneg hK0 hP, mul_nonneg hK0 (mul_nonneg hP (by positivity : (0:ℝ) ≤ δ⁻¹ ^ 2)),
          mul_nonneg hK0 (mul_nonneg hP (by positivity : (0:ℝ) ≤ δ⁻¹))]
    have := smul_bound hso hchs hξ.contDiffOn hy hBch0 hBξ0
      (fun i hi => hBch y hy.le hyY.le i hi) hbound n hn
    refine this.trans (le_of_eq ?_)
    ring

end UnforcedLeray.Short.PartIIIb.Concrete

end
