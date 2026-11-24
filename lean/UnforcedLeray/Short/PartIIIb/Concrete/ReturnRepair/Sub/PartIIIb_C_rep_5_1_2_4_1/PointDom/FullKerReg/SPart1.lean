import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4_1.PointDom.FullKerReg.XPart1

/-!
# The stream part of `fullKer`: smoothness and bounds in `y`
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray

/-- The statement of `primY_main` for a given `D`. -/
def PrimYSpec (r₁ Y D : ℝ) : Prop :=
  ∀ {A : Space → ℝ}, ContDiff ℝ 2 A → ∀ (w : Space) {K ρ₀ δ : ℝ}, 0 ≤ K → 0 ≤ ρ₀ →
      0 < δ → ρ₀ + δ = r₁ → w 0 ≤ ρ₀ →
      (∀ x : Space, x ≠ 0 → |A x| ≤ K * (‖x‖ ^ 4)⁻¹) →
      (∀ x : Space, x ≠ 0 → ‖iteratedFDeriv ℝ 1 A x‖ ≤ K * (‖x‖ ^ 5)⁻¹) →
      (∀ x : Space, x ≠ 0 → ‖iteratedFDeriv ℝ 2 A x‖ ≤ K * (‖x‖ ^ 6)⁻¹) →
      ∀ y : Space, r₁ < ϱ y → ‖y‖ < Y →
        ContDiffAt ℝ 2 (fun y' => primInt A w (ringMap y')) y ∧
        ∀ n : ℕ, n ≤ 2 → ‖iteratedFDeriv ℝ n (fun y' => primInt A w (ringMap y')) y‖ ≤
          (n.factorial : ℝ) * (primCp ρ₀ δ * K *
            (1 / (2 * ((ϱ y - ρ₀) ^ 2 + (y 2 - w 2) ^ 2)))) * D ^ n

theorem primY_spec {r₁ : ℝ} (hr₁ : 0 < r₁) (Y : ℝ) : ∃ D : ℝ, 1 ≤ D ∧ PrimYSpec r₁ Y D := by
  obtain ⟨D, hD, h⟩ := primY_main hr₁ Y
  exact ⟨D, hD, h⟩

theorem varrho_ge0 (z : Space) : z 0 ≤ ϱ z := by
  have : z 0 ^ 2 ≤ ϱ z ^ 2 := by rw [ϱ_sq]; nlinarith [sq_nonneg (z 1)]
  exact (abs_le_of_sq_le_sq' this (ϱ_nonneg z)).2

theorem coord2_norm : ‖(coordinateVector 2 : Space)‖ = 1 := by
  simp [coordinateVector]

theorem sPart1 (C : ℝ) (hC0 : 0 ≤ C) (hC : ∀ (ν μ h : ℝ), 0 < ν → -(1 / 4) < μ → μ ≤ 1 → 0 < h →
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
    {r₁ ρ₀ Y D : ℝ} (hρ₀ : 0 ≤ ρ₀) (hρr : ρ₀ < r₁) (hD : 1 ≤ D) (hspec : PrimYSpec r₁ Y D)
    {Bcf : ℝ} (hBcf0 : 0 ≤ Bcf)
    (hBcf : ∀ y : Space, r₁ ≤ ϱ y → ‖y‖ ≤ Y → ∀ i : ℕ, i ≤ 2 →
      ‖iteratedFDeriv ℝ i (fun y' : Space =>
        deriv χ (ν * age R y') * (-2 * ν * R ^ 2 / ϱ y' ^ 3) / ϱ y') y‖ ≤ Bcf)
    (M : Matrix (Fin 3) (Fin 3) ℝ) {z : Space} (hz : ϱ z ≤ ρ₀) {h : ℝ} (hh : 0 < h)
    {y : Space} (hy : r₁ < ϱ y) (hyY : ‖y‖ < Y) :
    ContDiffAt ℝ 2 (fun y' => (deriv χ (ν * age R y') * (-2 * ν * R ^ 2 / ϱ y' ^ 3) / ϱ y' *
        sKer ν μ h (ϱ y') (y' 2) z M) • (coordinateVector 2 : Space)) y ∧
    ∀ n : ℕ, n ≤ 2 → ‖iteratedFDeriv ℝ n (fun y' => (deriv χ (ν * age R y') *
        (-2 * ν * R ^ 2 / ϱ y' ^ 3) / ϱ y' * sKer ν μ h (ϱ y') (y' 2) z M) •
          (coordinateVector 2 : Space)) y‖ ≤
      4 * Bcf * (2 * (primCp ρ₀ (r₁ - ρ₀) * (C * pdLam h ^ (2 * μ + 3) * IIIa.tensorNorm M) *
        (1 / (2 * ((ϱ y - ρ₀) ^ 2 + (y 2 - pdLam h * z 2) ^ 2)))) * D ^ 2) := by
  set δ := r₁ - ρ₀ with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  have hr₁ : 0 < r₁ := lt_of_le_of_lt hρ₀ hρr
  have hl0 := pdLam_pos h
  have hl1 := (pdLam_lt_one hh).le
  set K := C * pdLam h ^ (2 * μ + 3) * IIIa.tensorNorm M with hK
  have hK0 : 0 ≤ K :=
    mul_nonneg (mul_nonneg hC0 (kb_coef_bounds μ h hμ0 hμ1 hh).1) (kb_tensor_nonneg M)
  obtain ⟨hcd, b0, b1, b2⟩ := xKerA_props C hC0 hC ν μ h hν hμ0 hμ1 hh M
  have hw0 : (pdLam h • z) 0 ≤ ρ₀ := by
    simpa using lam_mul_le hl0 hl1 hρ₀ ((varrho_ge0 z).trans hz)
  have hspec' := fun y' (h1 : r₁ < ϱ y') (h2 : ‖y'‖ < Y) =>
    hspec (A := xKerA ν μ h M) hcd (pdLam h • z) (K := K) (ρ₀ := ρ₀) (δ := δ) hK0 hρ₀ hδ0
      (by rw [hδ]; ring) hw0 b0 b1 b2 y' h1 h2
  set s' : Set Space := {y' | r₁ < ϱ y'} ∩ {y' | ‖y'‖ < Y} with hs'
  have hso : IsOpen s' :=
    (isOpen_lt continuous_const continuous_ϱ).inter (isOpen_lt continuous_norm continuous_const)
  have hys : y ∈ s' := ⟨hy, hyY⟩
  set g : Space → ℝ := fun y' => primInt (xKerA ν μ h M) (pdLam h • z) (ringMap y') with hg
  set f : Space → ℝ := fun y' =>
    -(deriv χ (ν * age R y') * (-2 * ν * R ^ 2 / ϱ y' ^ 3) / ϱ y') with hf
  have hgs : ContDiffOn ℝ 2 g s' := fun y' hy' => (hspec' y' hy'.1 hy'.2).1.contDiffWithinAt
  have hfs : ContDiffOn ℝ 2 f s' :=
    ((cf_contDiffOn hχ ν R).neg).mono (fun y' hy' => lt_trans hr₁ hy'.1)
  set L : ℝ →L[ℝ] Space := (ContinuousLinearMap.id ℝ ℝ).smulRight (coordinateVector 2 : Space) with hL
  have hLn : ‖L‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun t => by
    rw [hL, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply, norm_smul, coord2_norm]
    simp)
  have hS : (fun y' => (deriv χ (ν * age R y') * (-2 * ν * R ^ 2 / ϱ y' ^ 3) / ϱ y' *
        sKer ν μ h (ϱ y') (y' 2) z M) • (coordinateVector 2 : Space)) =
      L ∘ (fun y' => f y' * g y') := by
    funext y'
    simp only [Function.comp_apply, hL, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.id_apply, hf, hg]
    rw [sKer_eq_primInt]
    congr 1
    show _ = _ * primInt (xKerA ν μ h M) (pdLam h • z) !₂[ϱ y', 0, y' 2]
    ring
  rw [hS]
  have hfg : ContDiffOn ℝ 2 (fun y' => f y' * g y') s' := hfs.mul hgs
  refine ⟨L.contDiff.contDiffAt.comp y (hfg.contDiffAt (hso.mem_nhds hys)), fun n hn => ?_⟩
  have hfgAt : ContDiffAt ℝ 2 (fun y' => f y' * g y') y := hfg.contDiffAt (hso.mem_nhds hys)
  have h1 := L.norm_iteratedFDeriv_comp_left hfgAt (by exact_mod_cast hn)
  refine h1.trans ?_
  set G0 := primCp ρ₀ δ * K * (1 / (2 * ((ϱ y - ρ₀) ^ 2 + (y 2 - (pdLam h • z) 2) ^ 2))) with hG0
  have hG00 : 0 ≤ G0 := by
    rw [hG0]; have := primCp_nonneg hρ₀ hδ0; positivity
  have hbg : ∀ i : ℕ, i ≤ 2 → ‖iteratedFDeriv ℝ i g y‖ ≤ 2 * G0 * D ^ 2 := by
    intro i hi
    refine ((hspec' y hy hyY).2 i hi).trans ?_
    have hfac : (i.factorial : ℝ) ≤ 2 := by
      interval_cases i <;> norm_num [Nat.factorial]
    have hDi : D ^ i ≤ D ^ 2 := pow_le_pow_right₀ hD hi
    have hDi0 : 0 ≤ D ^ i := by positivity
    calc (i.factorial : ℝ) * G0 * D ^ i ≤ 2 * G0 * D ^ i :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hfac hG00) hDi0
      _ ≤ 2 * G0 * D ^ 2 := mul_le_mul_of_nonneg_left hDi (by positivity)
  have hbf : ∀ i : ℕ, i ≤ 2 → ‖iteratedFDeriv ℝ i f y‖ ≤ Bcf := by
    intro i hi
    have e := iteratedFDeriv_neg_apply (𝕜 := ℝ) (i := i) (x := y) (f := fun y' : Space =>
      deriv χ (ν * age R y') * (-2 * ν * R ^ 2 / ϱ y' ^ 3) / ϱ y')
    have e2 : ‖iteratedFDeriv ℝ i f y‖ = ‖iteratedFDeriv ℝ i (fun y' : Space =>
      deriv χ (ν * age R y') * (-2 * ν * R ^ 2 / ϱ y' ^ 3) / ϱ y') y‖ := by
      have : f = -(fun y' : Space =>
        deriv χ (ν * age R y') * (-2 * ν * R ^ 2 / ϱ y' ^ 3) / ϱ y') := rfl
      rw [this, e, norm_neg]
    rw [e2]
    exact hBcf y hy.le hyY.le i hi
  have hprod := smul_bound hso hfs hgs hys hBcf0 (by positivity) hbf hbg n hn
  have hprod' : ‖iteratedFDeriv ℝ n (fun y' => f y' * g y') y‖ ≤ 4 * Bcf * (2 * G0 * D ^ 2) := hprod
  calc ‖L‖ * ‖iteratedFDeriv ℝ n (fun y' => f y' * g y') y‖
      ≤ 1 * (4 * Bcf * (2 * G0 * D ^ 2)) := mul_le_mul hLn hprod' (norm_nonneg _) zero_le_one
    _ = _ := by
      rw [one_mul, hG0]; simp [smul_eq_mul]

end UnforcedLeray.Short.PartIIIb.Concrete

end
