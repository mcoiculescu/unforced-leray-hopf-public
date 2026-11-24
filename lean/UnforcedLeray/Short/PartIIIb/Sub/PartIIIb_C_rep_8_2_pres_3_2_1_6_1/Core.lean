import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_3_2_1_6_1.Geom

/-!
# Weighted decay of the lifted pressure from weighted bounds on the profile

Source `the November 2 reference manuscript`
lines 1213-1225, 2541-2552, 2697-2713.  If a profile `P(s,q,η)` and its derivative satisfy
`(1+|η|)^4 (|P| + ‖DP‖) ≤ A e^{-a s}` for `s > 0`, then `p_lift = s P∘chart` and its gradient are
`≤ C (1+|y|)^{-2}`: with `t = √s = R/ϱ`, `t (1+|y|) ≤ t + R + |η|`, so `s (1+|y|)² ≤ Q² (1+|η|)²`,
`Q = t + R + 1`, and the exponential absorbs every power of `t`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- `(1+t)^5 e^{-a t²}` is bounded. -/
theorem lpc_poly_exp {a : ℝ} (ha : 0 < a) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t : ℝ, 0 ≤ t → (1 + t) ^ 5 * Real.exp (-(a * t ^ 2)) ≤ K := by
  refine ⟨32 + 32 * (6 / a ^ 3), by positivity, fun t ht => ?_⟩
  have hexp1 : Real.exp (-(a * t ^ 2)) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith [sq_nonneg t]
  have hexp0 : 0 < Real.exp (-(a * t ^ 2)) := Real.exp_pos _
  have h6 : t ^ 6 * Real.exp (-(a * t ^ 2)) ≤ 6 / a ^ 3 := by
    have h := Real.pow_div_factorial_le_exp (x := a * t ^ 2) (by positivity) 3
    have e : (3 : ℕ).factorial = 6 := by norm_num [Nat.factorial]
    rw [e] at h
    have h' : (a * t ^ 2) ^ 3 ≤ 6 * Real.exp (a * t ^ 2) := by
      have := (div_le_iff₀ (by norm_num : (0:ℝ) < 6)).1 (by simpa using h)
      linarith
    have hm : Real.exp (a * t ^ 2) * Real.exp (-(a * t ^ 2)) = 1 := by
      rw [← Real.exp_add]; simp
    have : (a * t ^ 2) ^ 3 * Real.exp (-(a * t ^ 2)) ≤ 6 := by
      calc (a * t ^ 2) ^ 3 * Real.exp (-(a * t ^ 2)) ≤
            6 * Real.exp (a * t ^ 2) * Real.exp (-(a * t ^ 2)) :=
            mul_le_mul_of_nonneg_right h' hexp0.le
        _ = 6 := by rw [mul_assoc, hm, mul_one]
    rw [le_div_iff₀ (by positivity)]
    calc t ^ 6 * Real.exp (-(a * t ^ 2)) * a ^ 3 = (a * t ^ 2) ^ 3 * Real.exp (-(a * t ^ 2)) := by
          ring
      _ ≤ 6 := this
  have hpoly : (1 + t) ^ 5 ≤ 32 + 32 * t ^ 6 := by
    rcases le_or_gt t 1 with h | h
    · have : (1 + t) ^ 5 ≤ 2 ^ 5 := pow_le_pow_left₀ (by linarith) (by linarith) 5
      nlinarith [pow_nonneg ht 6]
    · have h1 : (1 + t) ^ 5 ≤ (2 * t) ^ 5 := pow_le_pow_left₀ (by linarith) (by linarith) 5
      have h2 : t ^ 5 ≤ t ^ 6 := pow_le_pow_right₀ h.le (by norm_num)
      have : (2 * t) ^ 5 = 32 * t ^ 5 := by ring
      nlinarith [pow_nonneg ht 6]
  calc (1 + t) ^ 5 * Real.exp (-(a * t ^ 2)) ≤
        (32 + 32 * t ^ 6) * Real.exp (-(a * t ^ 2)) := mul_le_mul_of_nonneg_right hpoly hexp0.le
    _ = 32 * Real.exp (-(a * t ^ 2)) + 32 * (t ^ 6 * Real.exp (-(a * t ^ 2))) := by ring
    _ ≤ 32 * 1 + 32 * (6 / a ^ 3) := by gcongr
    _ = _ := by ring

theorem lpc_norm_le_add (y : Space) : ‖y‖ ≤ ϱ y + |y 2| := by
  refine (pow_le_pow_iff_left₀ (norm_nonneg y) (add_nonneg (ϱ_nonneg y) (abs_nonneg _))
    two_ne_zero).1 ?_
  rw [norm_sq_eq_ϱ_sq_add]
  nlinarith [abs_nonneg (y 2), sq_abs (y 2), ϱ_nonneg y]

theorem lpc_aux (t R u : ℝ) (hR : 0 < R) (hu : 0 ≤ u) :
    2 * t ^ 2 + 2 * R + u + 2 ≤ (2 * t ^ 2 + 2 * R + 2) * (1 + u) ^ 2 := by
  have hc : 2 ≤ 2 * t ^ 2 + 2 * R + 2 := by nlinarith [sq_nonneg t]
  have h1 : 0 ≤ (2 * t ^ 2 + 2 * R + 2 - 2) * u := mul_nonneg (by linarith) hu
  have h2 : 0 ≤ (2 * t ^ 2 + 2 * R + 2) * (u * u) := mul_nonneg (by linarith) (mul_nonneg hu hu)
  nlinarith

theorem lpc_aux2 (t R : ℝ) (hR : 0 < R) (ht : 0 ≤ t) :
    2 * t ^ 2 + 2 * R + 2 ≤ (2 + 2 * R) * (1 + t) ^ 2 := by
  nlinarith [mul_nonneg hR.le (sq_nonneg t), mul_nonneg hR.le ht, sq_nonneg t]

set_option maxHeartbeats 1600000 in
/-- **Core estimate.** -/
theorem lpc_core {R τ : ℝ} (hR : 0 < R) {P : ℝ × (ℝ × ℝ) → ℝ}
    (hdiff : ∀ x : ℝ × (ℝ × ℝ), 0 < x.1 → DifferentiableAt ℝ P x) {A a : ℝ} (hA : 0 ≤ A)
    (ha : 0 < a)
    (hP : ∀ x : ℝ × (ℝ × ℝ), 0 < x.1 → (1 + |x.2.2|) ^ 4 * |P x| ≤ A * Real.exp (-(a * x.1)))
    (hG : ∀ x : ℝ × (ℝ × ℝ), 0 < x.1 →
      (1 + |x.2.2|) ^ 4 * ‖fderiv ℝ P x‖ ≤ A * Real.exp (-(a * x.1))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : Space, y ∉ axis →
      (1 + ‖y‖) ^ 2 * |age R y * P (chart R τ y)| ≤ C ∧
      (1 + ‖y‖) ^ 2 * ‖physGrad (fun y => age R y * P (chart R τ y)) y‖ ≤ C := by
  obtain ⟨K, hK0, hK⟩ := lpc_poly_exp ha
  refine ⟨A * K * (1 + R) ^ 2 + 3 / R * (1 + R) ^ 2 * (2 + 2 * R) * (A * K), by positivity, ?_⟩
  intro y hy
  have hρ := ϱ_pos hy
  have hR0 := hR.ne'
  have hs0 : 0 < age R y := age_pos hR0 hy
  set t : ℝ := R / ϱ y with htdef
  have ht0 : 0 < t := by positivity
  have hs : age R y = t ^ 2 := by unfold age; rw [htdef, div_pow]
  set η : ℝ := Axi.trans R y with hηdef
  set E : ℝ := 1 + |η| with hEdef
  have hE1 : 1 ≤ E := by have := abs_nonneg η; linarith
  have hEpos : 0 < E := by linarith
  set W : ℝ := Real.exp (-(a * t ^ 2)) with hWdef
  have hW0 : 0 < W := Real.exp_pos _
  have hx1 : (chart R τ y).1 = t ^ 2 := hs
  have hx2 : (chart R τ y).2.2 = η := rfl
  have hPx := hP (chart R τ y) (by rw [hx1]; positivity)
  have hGx := hG (chart R τ y) (by rw [hx1]; positivity)
  rw [hx1, hx2] at hPx hGx
  rw [← hEdef, ← hWdef] at hPx hGx
  -- geometry: t (1 + ‖y‖) ≤ (t + R + 1) E
  have hη : |η| = t * |y 2| := by
    rw [hηdef]; unfold Axi.trans
    rw [abs_div, abs_mul, abs_of_pos hR, abs_of_pos hρ, htdef]; ring
  have htρ : t * ϱ y = R := by rw [htdef]; field_simp
  set Q : ℝ := t + R + 1 with hQdef
  have hQ0 : 0 < Q := by positivity
  have hgeo : t * (1 + ‖y‖) ≤ Q * E := by
    have h1 := lpc_norm_le_add y
    have h2 : t * (1 + ‖y‖) ≤ t + R + |η| := by
      calc t * (1 + ‖y‖) = t + t * ‖y‖ := by ring
        _ ≤ t + t * (ϱ y + |y 2|) := by gcongr
        _ = t + R + |η| := by rw [mul_add, htρ, hη]; ring
    have h3 : t + R + |η| ≤ Q * E := by
      rw [hEdef, hQdef]; nlinarith [abs_nonneg η, mul_nonneg ht0.le (abs_nonneg η),
        mul_nonneg hR.le (abs_nonneg η)]
    exact h2.trans h3
  have hgeo2 : (1 + ‖y‖) ^ 2 * age R y ≤ (Q * E) ^ 2 := by
    rw [hs]
    have : (1 + ‖y‖) ^ 2 * t ^ 2 = (t * (1 + ‖y‖)) ^ 2 := by ring
    rw [this]
    exact pow_le_pow_left₀ (by positivity) hgeo 2
  -- polynomial/exponential absorption
  have hQ2 : Q ^ 2 ≤ (1 + R) ^ 2 * (1 + t) ^ 2 := by
    have h1 : Q ≤ (1 + R) * (1 + t) := by
      rw [hQdef]; nlinarith [mul_nonneg hR.le ht0.le]
    have h2 : Q ^ 2 ≤ ((1 + R) * (1 + t)) ^ 2 := pow_le_pow_left₀ hQ0.le h1 2
    calc Q ^ 2 ≤ ((1 + R) * (1 + t)) ^ 2 := h2
      _ = (1 + R) ^ 2 * (1 + t) ^ 2 := by ring
  have hQ5 : Q ^ 2 ≤ (1 + R) ^ 2 * (1 + t) ^ 5 := by
    have h3 : (1 + t) ^ 2 ≤ (1 + t) ^ 5 := pow_le_pow_right₀ (by linarith) (by norm_num)
    calc Q ^ 2 ≤ (1 + R) ^ 2 * (1 + t) ^ 2 := hQ2
      _ ≤ (1 + R) ^ 2 * (1 + t) ^ 5 := by gcongr
  have hKt := hK t ht0.le
  rw [← hWdef] at hKt
  have hE2 : E ^ 2 ≤ E ^ 4 := pow_le_pow_right₀ hE1 (by norm_num)
  have hE4pos : 0 < E ^ 4 := by positivity
  constructor
  · -- the value
    rw [abs_mul, abs_of_pos hs0]
    have hPabs : E ^ 2 * |P (chart R τ y)| ≤ A * W := by
      refine le_trans ?_ hPx
      exact mul_le_mul_of_nonneg_right hE2 (abs_nonneg _)
    calc (1 + ‖y‖) ^ 2 * (age R y * |P (chart R τ y)|)
        = ((1 + ‖y‖) ^ 2 * age R y) * |P (chart R τ y)| := by ring
      _ ≤ (Q * E) ^ 2 * |P (chart R τ y)| :=
          mul_le_mul_of_nonneg_right hgeo2 (abs_nonneg _)
      _ = Q ^ 2 * (E ^ 2 * |P (chart R τ y)|) := by ring
      _ ≤ Q ^ 2 * (A * W) := mul_le_mul_of_nonneg_left hPabs (by positivity)
      _ ≤ ((1 + R) ^ 2 * (1 + t) ^ 5) * (A * W) :=
          mul_le_mul_of_nonneg_right hQ5 (by positivity)
      _ = (1 + R) ^ 2 * A * ((1 + t) ^ 5 * W) := by ring
      _ ≤ (1 + R) ^ 2 * A * K := mul_le_mul_of_nonneg_left hKt (by positivity)
      _ ≤ _ := by
          have : 0 ≤ 3 / R * (1 + R) ^ 2 * (2 + 2 * R) * (A * K) := by positivity
          nlinarith
  · -- the gradient
    set B : ℝ := A * W / E ^ 4 with hBdef
    have hB0 : 0 ≤ B := by positivity
    have hBE : B * E ^ 4 = A * W := by rw [hBdef]; field_simp
    have hPB : |P (chart R τ y)| ≤ B := by
      rw [hBdef, le_div_iff₀ hE4pos]; linarith [hPx]
    have hGB : ‖fderiv ℝ P (chart R τ y)‖ ≤ B := by
      rw [hBdef, le_div_iff₀ hE4pos]; linarith [hGx]
    have hg := lpc_grad_bound hR hy (hdiff _ (by rw [hx1]; positivity)) hB0 hPB hGB
    have hX : 2 * age R y + 2 * R + |η| + 2 ≤ (2 * t ^ 2 + 2 * R + 2) * E ^ 2 := by
      rw [hs]
      exact lpc_aux t R |η| hR (abs_nonneg _)
    have hinv : 1 / ϱ y = t / R := by rw [htdef]; field_simp
    have hB1 : B / ϱ y = B * t / R := by
      rw [div_eq_mul_one_div, hinv]; ring
    calc (1 + ‖y‖) ^ 2 * ‖physGrad (fun y => age R y * P (chart R τ y)) y‖
        ≤ (1 + ‖y‖) ^ 2 * (3 * ((B / ϱ y) * age R y *
            (2 * age R y + 2 * R + |Axi.trans R y| + 2))) :=
          mul_le_mul_of_nonneg_left hg (by positivity)
      _ = 3 * (B * t / R) * (((1 + ‖y‖) ^ 2 * age R y) *
            (2 * age R y + 2 * R + |η| + 2)) := by rw [hB1]; ring
      _ ≤ 3 * (B * t / R) * ((Q * E) ^ 2 * ((2 * t ^ 2 + 2 * R + 2) * E ^ 2)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul hgeo2 hX (by positivity) (by positivity)
      _ = 3 / R * Q ^ 2 * (2 * t ^ 2 + 2 * R + 2) * t * (B * E ^ 4) := by ring
      _ = 3 / R * Q ^ 2 * (2 * t ^ 2 + 2 * R + 2) * t * (A * W) := by rw [hBE]
      _ ≤ 3 / R * ((1 + R) ^ 2 * (1 + t) ^ 2) * ((2 + 2 * R) * (1 + t) ^ 2) * (1 + t) * (A * W) := by
          have h1 : 2 * t ^ 2 + 2 * R + 2 ≤ (2 + 2 * R) * (1 + t) ^ 2 := by
            exact lpc_aux2 t R hR ht0.le
          have h2 : t ≤ 1 + t := by linarith
          have h3 : 3 / R * Q ^ 2 ≤ 3 / R * ((1 + R) ^ 2 * (1 + t) ^ 2) :=
            mul_le_mul_of_nonneg_left hQ2 (by positivity)
          have h4 : 3 / R * Q ^ 2 * (2 * t ^ 2 + 2 * R + 2) ≤
              3 / R * ((1 + R) ^ 2 * (1 + t) ^ 2) * ((2 + 2 * R) * (1 + t) ^ 2) :=
            mul_le_mul h3 h1 (by positivity) (by positivity)
          have h5 := mul_le_mul h4 h2 ht0.le (by positivity)
          exact mul_le_mul_of_nonneg_right h5 (by positivity)
      _ = 3 / R * (1 + R) ^ 2 * (2 + 2 * R) * A * ((1 + t) ^ 5 * W) := by ring
      _ ≤ 3 / R * (1 + R) ^ 2 * (2 + 2 * R) * A * K :=
          mul_le_mul_of_nonneg_left hKt (by positivity)
      _ ≤ _ := by
          have : 0 ≤ A * K * (1 + R) ^ 2 := by positivity
          nlinarith

end UnforcedLeray.Short.PartIIIb.Concrete

end
