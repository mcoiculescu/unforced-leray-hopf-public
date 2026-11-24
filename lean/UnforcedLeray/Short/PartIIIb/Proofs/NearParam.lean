import UnforcedLeray.Short.PartIIIb.Tasks

/-!
# Proof of `nearParam` (target `T_nearParam`; source: `the November 2 reference manuscript`, lines 4109-4124)

Parameter choice for `NearParameterChoice`, from the exponent bookkeeping `T_epsPow`.
Write `θ = min (min (a/2) (b/2)) (min (1/100) (3/22))` and `d₀ = γ/3`, and `ε = C_* ν^r e^{-d₀/ν}`.
The six terms of `deltaNRhs` are:

* `ε^{a/2}`, `ε^{b/2}`: `(p, x) = (a/2, 0)`, `(b/2, 0)`;
* `ε e^{(m₀+ηδ)/ν}`: `(1, m₀+ηδ)`;
* `ε^{1/50-K(a+b)} e^{ηδ/ν}`: `(1/50-K(a+b), ηδ)`;
* `ε^{3/22} e^{(ηδ+m₀/2)/ν}`: `(3/22, ηδ+m₀/2)`;
* `e^{-(Dp-ηδ)/ν}`: bounded directly, since `Dp - ηδ > θ d₀`.

For each `(p, x)` in the list, `θ ≤ p` and `x ≤ θ d₀/4`, so `p d₀ - x ≥ θ d₀/2`. Then `T_epsPow`
bounds the term by `C ν⁻ᵏ e^{-θ d₀/(2ν)}`. The six bounds are added, and `ν⁻¹ ≥ 1` (from `ν ≤ 1`)
puts all the powers `ν⁻ᵏ` at the common exponent `k₁ + ⋯ + k₅`.
-/

set_option autoImplicit false

noncomputable section

open Set

namespace UnforcedLeray.Short.PartIIIb

theorem nearParam : UnforcedLeray.Short.PartIIIb.T_nearParam := by
  unfold UnforcedLeray.Short.PartIIIb.T_nearParam
  intro hE
  unfold UnforcedLeray.Short.PartIIIb.T_epsPow at hE
  unfold UnforcedLeray.Short.PartIIIb.NearParameterChoice
  intro a b γ ηδ m0 Dp K c1 c2 rmax ha hb hγ _hηδ0 _hm0 _hK hKab hηδθ hm0θ hDp hc1 hc12 hrmax
  obtain ⟨θ, hθdef⟩ : ∃ θ : ℝ, θ = min (min (a / 2) (b / 2)) (min (1 / 100) (3 / 22)) :=
    ⟨_, rfl⟩
  rw [← hθdef] at hηδθ hm0θ hDp ⊢
  have hd0 : 0 < γ / 3 := div_pos hγ (by norm_num)
  have hθpos : 0 < θ := by
    rw [hθdef]
    exact lt_min (lt_min (half_pos ha) (half_pos hb)) (lt_min (by norm_num) (by norm_num))
  have hθa : θ ≤ a / 2 := by
    rw [hθdef]; exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hθb : θ ≤ b / 2 := by
    rw [hθdef]; exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hθc : θ ≤ 1 / 100 := by
    rw [hθdef]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hθd : θ ≤ 3 / 22 := by
    rw [hθdef]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  have hθ1 : θ ≤ 1 := le_trans hθd (by norm_num)
  have hθd0 : 0 < θ * (γ / 3) := mul_pos hθpos hd0
  have hx0 : (0 : ℝ) ≤ θ * (γ / 3) / 4 := div_nonneg hθd0.le (by norm_num)
  -- One term `ε ^ p * exp (x / ν)` with `θ ≤ p` and `x ≤ θ d₀ / 4`.
  have key : ∀ p x : ℝ, θ ≤ p → 0 < p → x ≤ θ * (γ / 3) / 4 →
      ∃ (C : ℝ) (k : ℕ) (ν₀ : ℝ), 0 ≤ C ∧ 0 < ν₀ ∧ ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
        ∀ Cs ∈ Icc c1 c2, ∀ r ∈ Icc (-rmax) rmax,
          (Cs * ν ^ r * Real.exp (-(γ / 3) / ν)) ^ p * Real.exp (x / ν) ≤
            C * ν⁻¹ ^ k * Real.exp (-(θ * (γ / 3) / 2) / ν) := by
    intro p x hθp hp hx
    obtain ⟨C, k, ν₀, hν₀, h⟩ := hE c1 c2 rmax (γ / 3) p x hc1 hc12 hrmax hd0 hp
    refine ⟨|C|, k, ν₀, abs_nonneg C, hν₀, ?_⟩
    intro ν hν hνν₀ Cs hCs r hr
    have h1 := h ν hν hνν₀ Cs hCs r hr
    have hA0 : 0 ≤ ν⁻¹ ^ k := pow_nonneg (inv_nonneg.2 hν.le) k
    have hE1 : 0 ≤ Real.exp (-(p * (γ / 3) - x) / ν) := (Real.exp_pos _).le
    have hpd : θ * (γ / 3) ≤ p * (γ / 3) := mul_le_mul_of_nonneg_right hθp hd0.le
    have hexp : -(p * (γ / 3) - x) / ν ≤ -(θ * (γ / 3) / 2) / ν :=
      div_le_div_of_nonneg_right (by linarith) hν.le
    calc (Cs * ν ^ r * Real.exp (-(γ / 3) / ν)) ^ p * Real.exp (x / ν)
        ≤ C * ν⁻¹ ^ k * Real.exp (-(p * (γ / 3) - x) / ν) := h1
      _ ≤ |C| * ν⁻¹ ^ k * Real.exp (-(p * (γ / 3) - x) / ν) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self C) hA0) hE1
      _ ≤ |C| * ν⁻¹ ^ k * Real.exp (-(θ * (γ / 3) / 2) / ν) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) (mul_nonneg (abs_nonneg C) hA0)
  obtain ⟨C1, k1, n1, hC1, hn1, h1⟩ := key (a / 2) 0 hθa (half_pos ha) hx0
  obtain ⟨C2, k2, n2, hC2, hn2, h2⟩ := key (b / 2) 0 hθb (half_pos hb) hx0
  obtain ⟨C3, k3, n3, hC3, hn3, h3⟩ := key 1 (m0 + ηδ) hθ1 one_pos (by linarith)
  obtain ⟨C4, k4, n4, hC4, hn4, h4⟩ :=
    key (1 / 50 - K * (a + b)) ηδ (by linarith) (by linarith) (by linarith)
  obtain ⟨C5, k5, n5, hC5, hn5, h5⟩ := key (3 / 22) (ηδ + m0 / 2) hθd (by norm_num) (by linarith)
  refine ⟨C1 + C2 + C3 + C4 + C5 + 1, k1 + k2 + k3 + k4 + k5,
    min (min (min (min (min n1 n2) n3) n4) n5) 1,
    lt_min (lt_min (lt_min (lt_min (lt_min hn1 hn2) hn3) hn4) hn5) one_pos, ?_⟩
  intro ν hν hνν Cs hCs r hr
  simp only [le_min_iff] at hνν
  obtain ⟨⟨⟨⟨⟨hA1, hA2⟩, hA3⟩, hA4⟩, hA5⟩, hA6⟩ := hνν
  have hM1 : 1 ≤ ν⁻¹ := (one_le_inv₀ hν).2 hA6
  have hEpos : 0 ≤ Real.exp (-(θ * (γ / 3) / 2) / ν) := (Real.exp_pos _).le
  have hk : ∀ k : ℕ, k ≤ k1 + k2 + k3 + k4 + k5 →
      ν⁻¹ ^ k ≤ ν⁻¹ ^ (k1 + k2 + k3 + k4 + k5) :=
    fun k hkle => pow_le_pow_right₀ hM1 hkle
  have t1 := h1 ν hν hA1 Cs hCs r hr
  have t2 := h2 ν hν hA2 Cs hCs r hr
  have t3 := h3 ν hν hA3 Cs hCs r hr
  have t4 := h4 ν hν hA4 Cs hCs r hr
  have t5 := h5 ν hν hA5 Cs hCs r hr
  rw [zero_div, Real.exp_zero, mul_one] at t1 t2
  rw [Real.rpow_one] at t3
  have t6 : Real.exp (-(Dp - ηδ) / ν) ≤ Real.exp (-(θ * (γ / 3) / 2) / ν) :=
    Real.exp_le_exp.mpr (div_le_div_of_nonneg_right (by linarith) hν.le)
  have hEq : -(θ * (γ / 3)) / (2 * ν) = -(θ * (γ / 3) / 2) / ν := by ring
  rw [hEq]
  unfold UnforcedLeray.Short.PartIIIb.deltaNRhs
  have b1 := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (hk k1 (by omega)) hC1) hEpos
  have b2 := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (hk k2 (by omega)) hC2) hEpos
  have b3 := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (hk k3 (by omega)) hC3) hEpos
  have b4 := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (hk k4 (by omega)) hC4) hEpos
  have b5 := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (hk k5 (by omega)) hC5) hEpos
  have hp1 : (1 : ℝ) ≤ ν⁻¹ ^ (k1 + k2 + k3 + k4 + k5) := one_le_pow₀ hM1
  have b6 : Real.exp (-(Dp - ηδ) / ν) ≤
      1 * ν⁻¹ ^ (k1 + k2 + k3 + k4 + k5) * Real.exp (-(θ * (γ / 3) / 2) / ν) := by
    calc Real.exp (-(Dp - ηδ) / ν) ≤ Real.exp (-(θ * (γ / 3) / 2) / ν) := t6
      _ = 1 * 1 * Real.exp (-(θ * (γ / 3) / 2) / ν) := by ring
      _ ≤ 1 * ν⁻¹ ^ (k1 + k2 + k3 + k4 + k5) * Real.exp (-(θ * (γ / 3) / 2) / ν) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp1 zero_le_one) hEpos
  linarith [t1, t2, t3, t4, t5, t6, b1, b2, b3, b4, b5, b6]

end UnforcedLeray.Short.PartIIIb
