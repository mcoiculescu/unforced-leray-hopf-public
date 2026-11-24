import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4_1.PointDom.FullKerReg.HPart

/-!
# Stream part: `h`-derivative and the limit `h ↓ 0`
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray

theorem ringMap_norm_le (y : Space) : ‖ringMap y‖ ≤ ‖y‖ := by
  have h1 : ‖ringMap y‖ ^ 2 = ϱ y ^ 2 + y 2 ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]
    simp [ringMap, Real.norm_eq_abs, sq_abs, ϱ_sq]
  have h2 := norm_sq_eq_ϱ_sq_add y
  have : ‖ringMap y‖ ^ 2 ≤ ‖y‖ ^ 2 := by rw [h1, h2]
  exact (abs_le_of_sq_le_sq' this (norm_nonneg _)).2

theorem sHder {C : ℝ} (hC0 : 0 ≤ C) (hC : PDKB C) (ν μ R : ℝ) (hν : 0 < ν) (hμ0 : -(1 / 4) < μ)
    (hμ1 : μ ≤ 1) {χ : ℝ → ℝ} {r₁ ρ₀ Y : ℝ} (hρ₀ : 0 ≤ ρ₀) (hρr : ρ₀ < r₁)
    (M : Matrix (Fin 3) (Fin 3) ℝ) {z : Space} (hz : ϱ z ≤ ρ₀) {h : ℝ} (hh : 0 < h)
    {y : Space} (hy : r₁ < ϱ y) (hyY : ‖y‖ < Y) {Bcf : ℝ}
    (hcf : |deriv χ (ν * age R y) * (-2 * ν * R ^ 2 / ϱ y ^ 3) / ϱ y| ≤ Bcf) :
    ∃ d : Space, HasDerivAt (fun h' => (deriv χ (ν * age R y) * (-2 * ν * R ^ 2 / ϱ y ^ 3) / ϱ y *
        sKer ν μ h' (ϱ y) (y 2) z M) • (coordinateVector 2 : Space)) d h ∧
      ‖d‖ ≤ Bcf * (((ρ₀ / (r₁ - ρ₀) + 1) * (3 + ν * ((r₁ - ρ₀) ^ 2)⁻¹ + Y / (r₁ - ρ₀))) *
        (C * pdLam h ^ (2 * μ + 3) * IIIa.tensorNorm M) *
        (1 / (2 * ((ϱ y - ρ₀) ^ 2 + (y 2 - pdLam h * z 2) ^ 2)))) := by
  set δ := r₁ - ρ₀ with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  have hY0 : 0 ≤ Y := by have := norm_nonneg y; linarith
  have hq : ρ₀ + δ < (ringMap y) 0 := by
    rw [ringMap_apply0]; have : ρ₀ + δ = r₁ := by rw [hδ]; ring
    rw [this]; exact hy
  obtain ⟨d, hd, hdb⟩ := primH_main C hC0 hC ν μ hν hμ0 hμ1 M z (ringMap y) hρ₀ hδ0 hY0
    ((ringMap_norm_le y).trans hyY.le) ((varrho_ge0 z).trans hz) hq hh
  set cf := deriv χ (ν * age R y) * (-2 * ν * R ^ 2 / ϱ y ^ 3) / ϱ y with hcfdef
  have hfun : (fun h' => (cf * sKer ν μ h' (ϱ y) (y 2) z M) • (coordinateVector 2 : Space)) =
      fun h' => (cf * -(primInt (xKerA ν μ h' M) (pdLam h' • z) (ringMap y))) •
        (coordinateVector 2 : Space) := by
    funext h'
    rw [sKer_eq_primInt]; rfl
  rw [hfun]
  refine ⟨(cf * -d) • (coordinateVector 2 : Space), (hd.neg.const_mul cf).smul_const _, ?_⟩
  rw [norm_smul, coord2_norm, mul_one, Real.norm_eq_abs, abs_mul, abs_neg]
  rw [ringMap_apply0, ringMap_apply2] at hdb
  have hdb' : |d| ≤ ((ρ₀ / δ + 1) * (3 + ν * (δ ^ 2)⁻¹ + Y / δ)) *
      (C * pdLam h ^ (2 * μ + 3) * IIIa.tensorNorm M) *
      (1 / (2 * ((ϱ y - ρ₀) ^ 2 + (y 2 - pdLam h * z 2) ^ 2))) := hdb
  exact mul_le_mul hcf hdb' (abs_nonneg _) (le_trans (abs_nonneg _) hcf)

theorem tendsto_parts {C0 : ℝ} (hC0 : 0 ≤ C0) (hsmall : ∀ (ν μ h : ℝ), 0 < ν → -(1 / 4) < μ → μ ≤ 1 → 0 < h →
    ∀ (M : Matrix (Fin 3) (Fin 3) ℝ) (x : Space), x ≠ 0 →
      ‖xKer ν μ h x M‖ ≤ ((1 - pdLam h ^ 2) * (C0 * IIIa.tensorNorm M)) * (‖x‖ ^ 4)⁻¹)
    (ν μ R : ℝ) (hν : 0 < ν) (hμ0 : -(1 / 4) < μ) (hμ1 : μ ≤ 1) {χ : ℝ → ℝ} (hχ : IsYoungCutoff χ)
    {r₁ ρ₀ : ℝ} (hρ₀ : 0 ≤ ρ₀) (hρr : ρ₀ < r₁)
    (M : Matrix (Fin 3) (Fin 3) ℝ) {z : Space} (hz : ϱ z ≤ ρ₀)
    {y : Space} (hy : r₁ < ϱ y) {Bcf : ℝ}
    (hcf : |deriv χ (ν * age R y) * (-2 * ν * R ^ 2 / ϱ y ^ 3) / ϱ y| ≤ Bcf) :
    Tendsto (fun h => χ (ν * age R y) • xKer ν μ h (y - pdLam h • z) M) (𝓝[>] 0) (𝓝 0) ∧
    Tendsto (fun h => (deriv χ (ν * age R y) * (-2 * ν * R ^ 2 / ϱ y ^ 3) / ϱ y *
        sKer ν μ h (ϱ y) (y 2) z M) • (coordinateVector 2 : Space)) (𝓝[>] 0) (𝓝 0) := by
  set δ := r₁ - ρ₀ with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  have hT := kb_tensor_nonneg M
  have hlim : Tendsto (fun h : ℝ => (1 - pdLam h ^ 2) * (C0 * IIIa.tensorNorm M)) (𝓝[>] 0) (𝓝 0) := by
    simpa using small_tendsto.mul_const (C0 * IIIa.tensorNorm M)
  have hpos : ∀ᶠ h in 𝓝[>] (0 : ℝ), 0 < h := self_mem_nhdsWithin
  have hnn : ∀ h : ℝ, 0 < h → 0 ≤ (1 - pdLam h ^ 2) * (C0 * IIIa.tensorNorm M) := fun h hh => by
    have := pdLam_lt_one hh
    have : 0 ≤ 1 - pdLam h ^ 2 := by nlinarith [pdLam_pos h]
    positivity
  refine ⟨?_, ?_⟩
  · refine squeeze_zero_norm' (a := fun h => ((1 - pdLam h ^ 2) * (C0 * IIIa.tensorNorm M)) * (δ ^ 4)⁻¹)
      (hpos.mono fun h hh => ?_) (by
        have := hlim.mul_const (δ ^ 4)⁻¹
        simp only [zero_mul] at this
        exact this)
    have hl0 := pdLam_pos h
    have hl1 := (pdLam_lt_one hh).le
    have hxδ : δ ≤ ‖y - pdLam h • z‖ := norm_sub_lam_ge hl0 hl1 hz hy
    have hx0 : y - pdLam h • z ≠ 0 := by intro h0; rw [h0, norm_zero] at hxδ; linarith
    rw [norm_smul, Real.norm_eq_abs]
    have hchi : |χ (ν * age R y)| ≤ 1 := by
      rw [abs_of_nonneg (hχ.range _).1]; exact (hχ.range _).2
    have h4 : (‖y - pdLam h • z‖ ^ 4)⁻¹ ≤ (δ ^ 4)⁻¹ := inv_anti₀ (by positivity) (pow_le_pow_left₀ hδ0.le hxδ 4)
    calc |χ (ν * age R y)| * ‖xKer ν μ h (y - pdLam h • z) M‖
        ≤ 1 * (((1 - pdLam h ^ 2) * (C0 * IIIa.tensorNorm M)) * (‖y - pdLam h • z‖ ^ 4)⁻¹) :=
          mul_le_mul hchi (hsmall ν μ h hν hμ0 hμ1 hh M _ hx0) (norm_nonneg _) zero_le_one
      _ ≤ _ := by
          rw [one_mul]
          exact mul_le_mul_of_nonneg_left h4 (hnn h hh)
  · refine squeeze_zero_norm' (a := fun h => Bcf * (primCp ρ₀ δ * ((1 - pdLam h ^ 2) * (C0 * IIIa.tensorNorm M)) *
        (1 / (2 * δ ^ 2)))) (hpos.mono fun h hh => ?_)
      (by
        have := ((hlim.const_mul (primCp ρ₀ δ)).mul_const (1 / (2 * δ ^ 2))).const_mul Bcf
        simp only [mul_zero, zero_mul] at this
        exact this)
    have hl0 := pdLam_pos h
    have hl1 := (pdLam_lt_one hh).le
    have hq : ρ₀ + δ < (ringMap y) 0 := by
      rw [ringMap_apply0]; have : ρ₀ + δ = r₁ := by rw [hδ]; ring
      rw [this]; exact hy
    have hw0 : (pdLam h • z) 0 ≤ ρ₀ := by
      simpa using lam_mul_le hl0 hl1 hρ₀ ((varrho_ge0 z).trans hz)
    have b0 : ∀ x : Space, x ≠ 0 → |xKerA ν μ h M x| ≤
        ((1 - pdLam h ^ 2) * (C0 * IIIa.tensorNorm M)) * (‖x‖ ^ 4)⁻¹ := fun x hx =>
      (by
        have := PiLp.norm_apply_le (xKer ν μ h x M) 2
        have h2 : |xKer ν μ h x M 2| ≤ ‖xKer ν μ h x M‖ := by simpa [Real.norm_eq_abs] using this
        exact h2.trans (hsmall ν μ h hν hμ0 hμ1 hh M x hx))
    have hP := primInt_abs_le (A := xKerA ν μ h M) (w := pdLam h • z) (hnn h hh) hρ₀ hδ0 hw0 b0 (ringMap y) hq
    rw [ringMap_apply0, ringMap_apply2] at hP
    rw [norm_smul, coord2_norm, mul_one, Real.norm_eq_abs, abs_mul]
    have hs : |sKer ν μ h (ϱ y) (y 2) z M| = |primInt (xKerA ν μ h M) (pdLam h • z) (ringMap y)| := by
      rw [sKer_eq_primInt, abs_neg]; rfl
    rw [hs]
    have hcp := primCp_nonneg hρ₀ hδ0
    have ha : δ ^ 2 ≤ (ϱ y - ρ₀) ^ 2 + (y 2 - (pdLam h • z) 2) ^ 2 := by
      have : δ ≤ ϱ y - ρ₀ := by rw [hδ]; linarith
      nlinarith [sq_nonneg (y 2 - (pdLam h • z) 2)]
    have hfrac : 1 / (2 * ((ϱ y - ρ₀) ^ 2 + (y 2 - (pdLam h • z) 2) ^ 2)) ≤ 1 / (2 * δ ^ 2) := by
      apply one_div_le_one_div_of_le (by positivity)
      linarith
    refine mul_le_mul hcf ?_ (abs_nonneg _) (le_trans (abs_nonneg _) hcf)
    refine hP.trans ?_
    exact mul_le_mul_of_nonneg_left hfrac (mul_nonneg hcp (hnn h hh))

end UnforcedLeray.Short.PartIIIb.Concrete

end
