import UnforcedLeray.Infra.PeriodicDichotomy.Evolution

/-!
# Periodic dichotomy, III: the two exponential rates

Continuation of `PeriodicDichotomy/Evolution.lean` (`paper/main.tex`, lines 361-404). Assume a
strip bound `‖E(τ, s)‖ ≤ C` for `0 ≤ τ - s ≤ P`. The Riesz rates of
`UnforcedLeray.Infra.RieszProjection.exists_rates`,

  `‖ℳⁿ P₋‖ ≤ C' ρⁿ`,  `‖Sⁿ‖ ≤ C' R⁻ⁿ`,  `0 < ρ < r < R`,

give, with `β₋ = log ρ / P < β = log r / P < β₊ = log R / P`,

* `‖E(τ, s) Π₋(s)‖ ≤ K e^{β₋(τ - s)}` for `τ ≥ s` (`norm_E_mul_piMinus_le`);
* `‖E₊(τ, s) Π₊(s)‖ ≤ K e^{β₊(τ - s)}` for `τ ≤ s` (`norm_extEvol_mul_piPlus_le`);
* `‖Π₊(t)‖ ≤ K`, `‖Π₋(t)‖ ≤ K`.

Factoring the interval `[s, τ]` into at most two phase strips and whole periods,
`E(τ,s) Π₋(s) = E(θ,0) ℳᵐ P₋ E(P,φ)` (`index τ - index s = m + 1`) and
`E₊(τ,s) = E(θ,0) S^{m+1} E(P,φ)` (`index τ - index s = -m`). If `P₊X = {0}` the statements
hold unchanged (then `S = 0`), so any `β₊ > β` is allowed (`exists_rates` gives some `R > r`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open Metric Complex Set
open UnforcedLeray.Infra.RieszProjection

namespace UnforcedLeray.Infra.PeriodicDichotomy

/-! ### Scalar lemmas -/

theorem exp_mul_sub_le (b t d L : ℝ) (hd : |d| ≤ L) :
    Real.exp (b * (t - d)) ≤ Real.exp (b * t) * Real.exp (|b| * L) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.2
  have h1 : -(b * d) ≤ |b| * |d| := by
    rw [← abs_mul]; exact neg_le_abs _
  have h2 : |b| * |d| ≤ |b| * L := mul_le_mul_of_nonneg_left hd (abs_nonneg b)
  have h3 : b * (t - d) = b * t - b * d := by ring
  linarith

theorem pow_eq_exp_log_div_mul {a : ℝ} (ha : 0 < a) {P : ℝ} (hP : P ≠ 0) (n : ℕ) :
    a ^ n = Real.exp (Real.log a / P * (n * P)) := by
  have h : Real.log a / P * (n * P) = n * Real.log a := by field_simp
  rw [h, Real.exp_nat_mul, Real.exp_log ha]

theorem inv_pow_eq_exp_log_div_mul {a : ℝ} (ha : 0 < a) {P : ℝ} (hP : P ≠ 0) (n : ℕ) :
    a⁻¹ ^ n = Real.exp (Real.log a / P * (-(n * P))) := by
  have h : Real.log a / P * (-(n * P)) = -(n * Real.log a) := by field_simp
  rw [h, Real.exp_neg, Real.exp_nat_mul, Real.exp_log ha, inv_pow]

namespace PeriodicSplitting

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  (D : PeriodicSplitting X)

/-! ### Index arithmetic -/

theorem E_eq_of_index_sub_eq {s τ : ℝ} {n : ℕ} (h : D.index τ - D.index s = n) :
    D.E τ s = D.E (n * D.P + D.phase τ) (D.phase s) := by
  have hτ := D.index_mul_add_phase τ
  have hs := D.index_mul_add_phase s
  have hn : (n : ℝ) = (D.index τ : ℝ) - D.index s := by
    have := congrArg (fun z : ℤ => (z : ℝ)) h
    simp only [Int.cast_natCast, Int.cast_sub] at this
    exact this.symm
  rw [← D.E_add_intCast_mul (n * D.P + D.phase τ) (D.phase s) (D.index s)]
  congr 1
  · rw [hn]; linarith
  · linarith

theorem sub_eq_of_index_sub_eq {s τ : ℝ} {z : ℤ} (h : D.index τ - D.index s = z) :
    τ - s = z * D.P + D.phase τ - D.phase s := by
  have hτ := D.index_mul_add_phase τ
  have hs := D.index_mul_add_phase s
  have hz : (z : ℝ) = (D.index τ : ℝ) - D.index s := by
    rw [← h]; push_cast; ring
  rw [hz]; linarith

theorem exists_index_sub_eq_natCast {s τ : ℝ} (hsτ : s ≤ τ) :
    ∃ n : ℕ, D.index τ - D.index s = n :=
  ⟨(D.index τ - D.index s).toNat,
    (Int.toNat_of_nonneg (sub_nonneg.2 (D.index_le_index hsτ))).symm⟩

theorem exists_index_sub_eq_neg {s τ : ℝ} (hτs : τ ≤ s) :
    ∃ m : ℕ, D.index τ - D.index s = -(m : ℤ) := by
  refine ⟨(D.index s - D.index τ).toNat, ?_⟩
  rw [Int.toNat_of_nonneg (sub_nonneg.2 (D.index_le_index hτs)), neg_sub]

/-- `E((m+1)P + θ, φ) = E(θ, 0) ℳᵐ E(P, φ)` for `θ ≥ 0`, `0 ≤ φ ≤ P`. -/
theorem E_natCast_succ_mul_add (m : ℕ) {θ φ : ℝ} (hθ : 0 ≤ θ) (hφ : φ ≤ D.P) :
    D.E (((m + 1 : ℕ) : ℝ) * D.P + θ) φ = D.E θ 0 * D.monodromy ^ m * D.E D.P φ := by
  have hP := D.P_pos
  have hm : (0 : ℝ) ≤ m * D.P := by positivity
  have h1 : φ ≤ ((m + 1 : ℕ) : ℝ) * D.P := by push_cast; nlinarith
  rw [← D.E_comp φ (((m + 1 : ℕ) : ℝ) * D.P) _ h1 (by linarith)]
  have h2 := D.E_add_natCast_mul θ 0 (m + 1)
  rw [zero_add, add_comm θ] at h2
  rw [h2, mul_assoc]
  congr 1
  rw [← D.E_natCast_mul_add_period m hφ]
  congr 1
  push_cast; ring

/-! ### The interior part -/

/-- `E(τ,s) Π₋(s) = E(θ,0) ℳᵐ P₋ E(P,φ)` when `index τ - index s = m + 1`. -/
theorem E_mul_piMinus_eq_of_index_sub_eq_succ {s τ : ℝ} {m : ℕ}
    (h : D.index τ - D.index s = ((m + 1 : ℕ) : ℤ)) :
    D.E τ s * D.piMinus s =
      D.E (D.phase τ) 0 * (D.monodromy ^ m * D.projMinus) * D.E D.P (D.phase s) := by
  have hsτ : s ≤ τ := by
    have h' := D.sub_eq_of_index_sub_eq h
    have hθ := D.phase_nonneg τ
    have hφ := D.phase_lt s
    have hP := D.P_pos
    have : (0 : ℝ) ≤ ((m + 1 : ℕ) : ℤ) * D.P - D.P := by push_cast; nlinarith
    linarith
  rw [piMinus, mul_sub, mul_one, D.E_mul_piPlus_eq_extEvol hsτ,
    D.extEvol_eq_of_index_sub_eq_natCast h, D.E_eq_of_index_sub_eq h,
    D.E_natCast_succ_mul_add m (D.phase_nonneg τ) (D.phase_le s)]
  have h2 : D.E (D.phase τ) 0 * D.monodromy ^ (m + 1) * D.outerInv * D.E D.P (D.phase s) =
      D.E (D.phase τ) 0 * (D.monodromy ^ m * D.projPlus) * D.E D.P (D.phase s) := by
    rw [← D.monodromy_pow_succ_mul_outerInv]; simp only [mul_assoc]
  rw [h2, projPlus]
  simp only [mul_sub, sub_mul, mul_one, mul_assoc]
  abel

/-- `E(τ,s) Π₋(s) = E(θ,φ) - E(θ,0) S E(P,φ)` when `index τ = index s`. -/
theorem E_mul_piMinus_eq_of_index_sub_eq_zero {s τ : ℝ} (hsτ : s ≤ τ)
    (h : D.index τ - D.index s = ((0 : ℕ) : ℤ)) :
    D.E τ s * D.piMinus s =
      D.E (D.phase τ) (D.phase s) - D.E (D.phase τ) 0 * D.outerInv * D.E D.P (D.phase s) := by
  rw [piMinus, mul_sub, mul_one, D.E_mul_piPlus_eq_extEvol hsτ,
    D.extEvol_eq_of_index_sub_eq_natCast h, D.E_eq_of_index_sub_eq h, pow_zero, mul_one,
    Nat.cast_zero, zero_mul, zero_add]

/-! ### Bounds -/

omit [CompleteSpace X] in
theorem norm_three_le {A B T : X →L[ℂ] X} {a b c : ℝ} (ha : ‖A‖ ≤ a) (hb : ‖B‖ ≤ b)
    (hc : ‖T‖ ≤ c) (hb0 : 0 ≤ b) : ‖A * B * T‖ ≤ a * b * c := by
  refine (norm_mul_le _ _).trans (mul_le_mul ((norm_mul_le _ _).trans ?_) hc (norm_nonneg _)
    (mul_nonneg ((norm_nonneg _).trans ha) hb0))
  exact mul_le_mul ha hb (norm_nonneg _) ((norm_nonneg _).trans ha)

section Bounds

variable {C : ℝ} (hC : ∀ s τ, s ≤ τ → τ ≤ s + D.P → ‖D.E τ s‖ ≤ C)
include hC

theorem strip_nonneg : 0 ≤ C :=
  (norm_nonneg _).trans (hC 0 0 le_rfl (by linarith [D.P_pos]))

theorem norm_E_phase_zero_le (t : ℝ) : ‖D.E (D.phase t) 0‖ ≤ C :=
  hC 0 _ (D.phase_nonneg t) (by linarith [D.phase_lt t])

theorem norm_E_period_phase_le (t : ℝ) : ‖D.E D.P (D.phase t)‖ ≤ C :=
  hC _ _ (D.phase_le t) (by linarith [D.phase_nonneg t])

/-- `‖Π₊(t)‖ ≤ C ‖S‖ C`. -/
theorem norm_piPlus_le (t : ℝ) : ‖D.piPlus t‖ ≤ C * ‖D.outerInv‖ * C := by
  have hC0 := D.strip_nonneg hC
  rw [piPlus_eq]
  refine (norm_mul_le _ _).trans ?_
  refine mul_le_mul ((norm_mul_le _ _).trans ?_) (D.norm_E_period_phase_le hC t) (norm_nonneg _)
    (by positivity)
  exact mul_le_mul_of_nonneg_right (D.norm_E_phase_zero_le hC t) (norm_nonneg _)

/-- `‖Π₋(t)‖ ≤ 1 + C ‖S‖ C`. -/
theorem norm_piMinus_le (t : ℝ) : ‖D.piMinus t‖ ≤ 1 + C * ‖D.outerInv‖ * C := by
  rw [piMinus]
  refine (norm_sub_le _ _).trans (add_le_add ?_ (D.norm_piPlus_le hC t))
  rw [ContinuousLinearMap.one_def]
  exact ContinuousLinearMap.norm_id_le

end Bounds

/-! ### The rates -/

/-- **The exponential dichotomy of the periodic evolution.** Under a strip bound
`‖E(τ,s)‖ ≤ C` for `0 ≤ τ - s ≤ P`, there are rates `β₋ < log r / P < β₊` and a constant `K`
with `‖E(τ,s) Π₋(s)‖ ≤ K e^{β₋(τ-s)}` for `τ ≥ s`, `‖E₊(τ,s) Π₊(s)‖ ≤ K e^{β₊(τ-s)}` for
`τ ≤ s`, and `‖Π_±(t)‖ ≤ K`. -/
theorem exists_dichotomy_rates {C : ℝ} (hC : ∀ s τ, s ≤ τ → τ ≤ s + D.P → ‖D.E τ s‖ ≤ C) :
    ∃ βm βp K : ℝ, βm < Real.log D.r / D.P ∧ Real.log D.r / D.P < βp ∧ 0 ≤ K ∧
      (∀ t, ‖D.piPlus t‖ ≤ K) ∧ (∀ t, ‖D.piMinus t‖ ≤ K) ∧
      (∀ s τ, s ≤ τ → ‖D.E τ s * D.piMinus s‖ ≤ K * Real.exp (βm * (τ - s))) ∧
      (∀ s τ, τ ≤ s → ‖D.extEvol τ s * D.piPlus s‖ ≤ K * Real.exp (βp * (τ - s))) := by
  obtain ⟨ρ, R, C', hρ, hρr, hrR, hC', hM, hS⟩ :=
    exists_rates D.r_pos D.sphere_subset_monodromy
  have hP := D.P_pos
  have hC0 := D.strip_nonneg hC
  have hR : 0 < R := D.r_pos.trans hrR
  set A := ‖D.outerInv‖ with hA
  have hA0 : 0 ≤ A := norm_nonneg _
  set βm := Real.log ρ / D.P with hβm
  set βp := Real.log R / D.P with hβp
  set L := Real.exp (|βm| * (2 * D.P) + |βp| * (2 * D.P)) with hL
  have hL1 : 1 ≤ L := Real.one_le_exp (by positivity)
  have hLm : Real.exp (|βm| * (2 * D.P)) ≤ L :=
    Real.exp_le_exp.2 (by have := abs_nonneg βp; nlinarith)
  have hLp : Real.exp (|βp| * (2 * D.P)) ≤ L :=
    Real.exp_le_exp.2 (by have := abs_nonneg βm; nlinarith)
  set K₀ := C + C * A * C + C * C' * C + 1 with hK₀
  have hC'0 : (0 : ℝ) ≤ C' := by linarith
  have hCC' : 0 ≤ C * C' * C := by positivity
  have hCAC : 0 ≤ C * A * C := by positivity
  have hK₀0 : 0 ≤ K₀ := by positivity
  refine ⟨βm, βp, K₀ * L, ?_, ?_, by positivity, ?_, ?_, ?_, ?_⟩
  · exact div_lt_div_of_pos_right (Real.log_lt_log hρ hρr) hP
  · exact div_lt_div_of_pos_right (Real.log_lt_log D.r_pos hrR) hP
  · intro t
    refine (D.norm_piPlus_le hC t).trans ?_
    calc C * A * C ≤ K₀ * 1 := by rw [mul_one]; linarith
      _ ≤ K₀ * L := mul_le_mul_of_nonneg_left hL1 hK₀0
  · intro t
    refine (D.norm_piMinus_le hC t).trans ?_
    calc 1 + C * A * C ≤ K₀ * 1 := by rw [mul_one]; linarith
      _ ≤ K₀ * L := mul_le_mul_of_nonneg_left hL1 hK₀0
  · intro s τ hsτ
    obtain ⟨n, hn⟩ := D.exists_index_sub_eq_natCast hsτ
    have hts := D.sub_eq_of_index_sub_eq hn
    have hθ0 := D.phase_nonneg τ
    have hθP := D.phase_lt τ
    have hφ0 := D.phase_nonneg s
    have hφP := D.phase_lt s
    rcases n with _ | m
    · -- the same period: one phase strip
      rw [D.E_mul_piMinus_eq_of_index_sub_eq_zero hsτ hn]
      have hts' : τ - s = D.phase τ - D.phase s := by
        rw [hts]; push_cast; ring
      have hφθ : D.phase s ≤ D.phase τ := by linarith
      have h1 : ‖D.E (D.phase τ) (D.phase s)‖ ≤ C := hC _ _ hφθ (by linarith)
      have h2 : ‖D.E (D.phase τ) 0 * D.outerInv * D.E D.P (D.phase s)‖ ≤ C * A * C :=
        norm_three_le (D.norm_E_phase_zero_le hC τ) le_rfl (D.norm_E_period_phase_le hC s)
          hA0
      have hexp : 1 ≤ Real.exp (βm * (τ - s)) * L := by
        have := exp_mul_sub_le βm (τ - s) (τ - s) (2 * D.P)
          (by rw [abs_of_nonneg (by linarith)]; linarith)
        rw [sub_self, mul_zero, Real.exp_zero] at this
        exact this.trans (mul_le_mul_of_nonneg_left hLm (Real.exp_pos _).le)
      calc ‖D.E (D.phase τ) (D.phase s) - D.E (D.phase τ) 0 * D.outerInv * D.E D.P (D.phase s)‖
          ≤ C + C * A * C := (norm_sub_le _ _).trans (add_le_add h1 h2)
        _ ≤ K₀ * 1 := by rw [mul_one]; linarith
        _ ≤ K₀ * (Real.exp (βm * (τ - s)) * L) := mul_le_mul_of_nonneg_left hexp hK₀0
        _ = K₀ * L * Real.exp (βm * (τ - s)) := by ring
    · -- whole periods in between
      rw [D.E_mul_piMinus_eq_of_index_sub_eq_succ hn]
      have h1 : ‖D.E (D.phase τ) 0 * (D.monodromy ^ m * D.projMinus) * D.E D.P (D.phase s)‖ ≤
          C * (C' * ρ ^ m) * C :=
        norm_three_le (D.norm_E_phase_zero_le hC τ) (hM m) (D.norm_E_period_phase_le hC s)
          (mul_nonneg (by linarith) (pow_nonneg hρ.le m))
      have hρm : ρ ^ m ≤ Real.exp (βm * (τ - s)) * L := by
        rw [pow_eq_exp_log_div_mul hρ hP.ne' m]
        have hd : (m : ℝ) * D.P = (τ - s) - (D.P + D.phase τ - D.phase s) := by
          rw [hts]; push_cast; ring
        rw [hd]
        refine (exp_mul_sub_le βm (τ - s) _ (2 * D.P) ?_).trans
          (mul_le_mul_of_nonneg_left hLm (Real.exp_pos _).le)
        rw [abs_le]; constructor <;> linarith
      calc ‖D.E (D.phase τ) 0 * (D.monodromy ^ m * D.projMinus) * D.E D.P (D.phase s)‖
          ≤ C * C' * C * ρ ^ m := by linarith
        _ ≤ C * C' * C * (Real.exp (βm * (τ - s)) * L) := mul_le_mul_of_nonneg_left hρm hCC'
        _ ≤ K₀ * (Real.exp (βm * (τ - s)) * L) :=
            mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        _ = K₀ * L * Real.exp (βm * (τ - s)) := by ring
  · intro s τ hτs
    obtain ⟨m, hm⟩ := D.exists_index_sub_eq_neg hτs
    have hts := D.sub_eq_of_index_sub_eq hm
    have hθ0 := D.phase_nonneg τ
    have hθP := D.phase_lt τ
    have hφ0 := D.phase_nonneg s
    have hφP := D.phase_lt s
    rw [D.extEvol_mul_piPlus, D.extEvol_eq_of_index_sub_eq_neg hm]
    have h1 : ‖D.E (D.phase τ) 0 * D.outerInv ^ (m + 1) * D.E D.P (D.phase s)‖ ≤
        C * (C' * R⁻¹ ^ (m + 1)) * C :=
      norm_three_le (D.norm_E_phase_zero_le hC τ) (hS (m + 1)) (D.norm_E_period_phase_le hC s)
        (mul_nonneg (by linarith) (pow_nonneg (inv_nonneg.2 hR.le) (m + 1)))
    have hRm : R⁻¹ ^ (m + 1) ≤ Real.exp (βp * (τ - s)) * L := by
      rw [inv_pow_eq_exp_log_div_mul hR hP.ne' (m + 1)]
      have hd : -(((m + 1 : ℕ) : ℝ) * D.P) = (τ - s) - (D.phase τ - D.phase s + D.P) := by
        rw [hts]; push_cast; ring
      rw [hd]
      refine (exp_mul_sub_le βp (τ - s) _ (2 * D.P) ?_).trans
        (mul_le_mul_of_nonneg_left hLp (Real.exp_pos _).le)
      rw [abs_le]; constructor <;> linarith
    calc ‖D.E (D.phase τ) 0 * D.outerInv ^ (m + 1) * D.E D.P (D.phase s)‖
        ≤ C * C' * C * R⁻¹ ^ (m + 1) := by linarith
      _ ≤ C * C' * C * (Real.exp (βp * (τ - s)) * L) := mul_le_mul_of_nonneg_left hRm hCC'
      _ ≤ K₀ * (Real.exp (βp * (τ - s)) * L) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = K₀ * L * Real.exp (βp * (τ - s)) := by ring

/-! ### Uniform bounds for `F θ`, `G θ`, and the trivial exterior -/

/-- `‖F θ‖ ≤ C` for `0 ≤ θ ≤ P`. -/
theorem norm_F_le {C : ℝ} (hC : ∀ s τ, s ≤ τ → τ ≤ s + D.P → ‖D.E τ s‖ ≤ C) {θ : ℝ}
    (h0 : 0 ≤ θ) (hP : θ ≤ D.P) : ‖D.F θ‖ ≤ C := by
  have hC0 := D.strip_nonneg hC
  refine ContinuousLinearMap.opNorm_le_bound _ hC0 (fun v => ?_)
  rw [F_apply, Submodule.coe_norm]
  exact ((D.E θ 0).le_opNorm _).trans
    (mul_le_mul_of_nonneg_right (hC 0 θ h0 (by linarith)) (norm_nonneg _))

/-- `‖G θ‖ ≤ ‖S‖ C` for `0 ≤ θ ≤ P`. -/
theorem norm_G_le {C : ℝ} (hC : ∀ s τ, s ≤ τ → τ ≤ s + D.P → ‖D.E τ s‖ ≤ C) {θ : ℝ}
    (h0 : 0 ≤ θ) (hP : θ ≤ D.P) : ‖D.G θ‖ ≤ ‖D.outerInv‖ * C := by
  have hC0 := D.strip_nonneg hC
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun x => ?_)
  rw [Submodule.coe_norm, coe_G_apply, ← mul_apply_eq_comp]
  refine ((D.outerInv * D.E D.P θ).le_opNorm x).trans
    (mul_le_mul_of_nonneg_right ((norm_mul_le _ _).trans ?_) (norm_nonneg _))
  exact mul_le_mul_of_nonneg_left (hC θ D.P hP (by linarith)) (norm_nonneg _)

theorem eq_zero_of_exterior_eq_bot (h : D.exterior = ⊥) (v : D.exterior) : v = 0 :=
  Submodule.coe_eq_zero.1 ((Submodule.eq_bot_iff _).1 h v v.2)

/-- If `P₊X = {0}`, the exterior evolution vanishes. -/
theorem extEvol_eq_zero_of_exterior_eq_bot (h : D.exterior = ⊥) (τ s : ℝ) :
    D.extEvol τ s = 0 := by
  ext x
  rw [extEvol, ContinuousLinearMap.comp_apply,
    D.eq_zero_of_exterior_eq_bot h (((D.zpowPlus _).comp (D.G _)) x), map_zero,
    zero_apply]

/-- If `P₊X = {0}`, then `Π₊ = 0`. -/
theorem piPlus_eq_zero_of_exterior_eq_bot (h : D.exterior = ⊥) (t : ℝ) : D.piPlus t = 0 := by
  ext x
  rw [piPlus, piPlusPhase, ContinuousLinearMap.comp_apply,
    D.eq_zero_of_exterior_eq_bot h (D.G _ x), map_zero, zero_apply]

/-- If `P₊X = {0}`, any exterior rate is allowed. -/
theorem norm_extEvol_mul_piPlus_of_exterior_eq_bot (h : D.exterior = ⊥) (βp K : ℝ)
    (hK : 0 ≤ K) (τ s : ℝ) : ‖D.extEvol τ s * D.piPlus s‖ ≤ K * Real.exp (βp * (τ - s)) := by
  rw [D.extEvol_eq_zero_of_exterior_eq_bot h, zero_mul, norm_zero]
  positivity

end PeriodicSplitting

end UnforcedLeray.Infra.PeriodicDichotomy
