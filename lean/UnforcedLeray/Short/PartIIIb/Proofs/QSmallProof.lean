import UnforcedLeray.Short.PartIIIb.Tasks

/-!
# Proof of `T_qsmall` (target `qSmall`)

Source: `the November 2 reference manuscript`, lines 5644-5686 (Proposition
`repair:complete-graph-error`), with `a = γ/8` and the pair norm `‖V‖ = ‖T‖ + e^{-a/ν}‖w‖`.

For `V = (T, w)` put `v = v_Q(T)`, `B = ‖M v‖`, `A = ‖Tc V‖`, `G = ‖wc V‖`.
The fourth clause of `IsGraphLift` gives `Tc (Q V) = -D_N⁻¹ (M v)` and
`wc (Q V) = -(v - S_N (D_N⁻¹ (M v)))`. Hence `‖Tc (Q V)‖ ≤ q B` and
`‖wc (Q V)‖ ≤ ‖v‖ + s ‖Tc (Q V)‖`, where `q = |C₂| ν⁻¹^{k₂}` and
`s = q e^{η_δ/ν}`. The error-family bounds control `B` and `‖v‖` by `A` and `G`.
Collecting terms gives `‖Q V‖ ≤ M ‖V‖` with six exponential terms. Each term is
`≤ D ν⁻¹^K e^{-γ/(100ν)}`, and the exponent inequalities follow by `linarith` from
`ωb, m₀, η_δ < γ/1000`.
-/

set_option autoImplicit false

noncomputable section

open Filter Topology Set

namespace UnforcedLeray.Short.PartIIIb

/-- Monotonicity of the exponential factor: `x ≤ -c` gives `e^{x/ν} ≤ e^{-c/ν}`. -/
theorem qs_exp_le {ν c x : ℝ} (hν : 0 < ν) (hx : x ≤ -c) :
    Real.exp (x / ν) ≤ Real.exp (-c / ν) :=
  Real.exp_le_exp.2 (div_le_div_of_nonneg_right hx hν.le)

/-- Power monotonicity of `ν⁻¹` for `0 < ν ≤ 1`. -/
theorem qs_pow_le {ν : ℝ} (hν : 0 < ν) (hν1 : ν ≤ 1) {j K : ℕ} (hjK : j ≤ K) :
    ν⁻¹ ^ j ≤ ν⁻¹ ^ K :=
  pow_le_pow_right₀ ((one_le_inv₀ hν).2 hν1) hjK

/-- A single term `c ν⁻¹^j e^{x/ν}` with `c ≤ D`, `j ≤ K`, `x ≤ -γ/100` is bounded by
`D ν⁻¹^K e^{-γ/(100ν)}`. -/
theorem qs_term {ν γ c D x : ℝ} {j K : ℕ} (hν : 0 < ν) (hν1 : ν ≤ 1) (hjK : j ≤ K)
    (hc0 : 0 ≤ c) (hcD : c ≤ D) (hx : x ≤ -(γ / 100)) :
    c * ν⁻¹ ^ j * Real.exp (x / ν) ≤ D * ν⁻¹ ^ K * Real.exp (-(γ / 100) / ν) := by
  have hp : 0 ≤ ν⁻¹ ^ j := pow_nonneg (inv_nonneg.2 hν.le) j
  have hK : 0 ≤ ν⁻¹ ^ K := pow_nonneg (inv_nonneg.2 hν.le) K
  have hD : 0 ≤ D := le_trans hc0 hcD
  have he : 0 ≤ Real.exp (x / ν) := (Real.exp_pos _).le
  have h1 : c * ν⁻¹ ^ j ≤ D * ν⁻¹ ^ K :=
    calc c * ν⁻¹ ^ j ≤ D * ν⁻¹ ^ j := mul_le_mul_of_nonneg_right hcD hp
      _ ≤ D * ν⁻¹ ^ K := mul_le_mul_of_nonneg_left (qs_pow_le hν hν1 hjK) hD
  exact mul_le_mul h1 (qs_exp_le hν hx) he (mul_nonneg hD hK)

/-- Replace a real constant by its absolute value (one factor). -/
theorem qs_abs2 {C a y : ℝ} (ha : 0 ≤ a) (hy : 0 ≤ y) : C * a * y ≤ |C| * a * y :=
  mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self C) ha) hy

/-- Replace a real constant by its absolute value (two factors). -/
theorem qs_abs3 {C a b y : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hy : 0 ≤ y) :
    C * a * b * y ≤ |C| * a * b * y :=
  mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self C) ha) hb) hy

/-- Constants of the six terms are bounded by a common `D = (1 + c₁)(1 + c₂)²`. -/
theorem qs_consts {c1 c2 : ℝ} (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2) :
    c2 * c1 ≤ (1 + c1) * (1 + c2) ^ 2 ∧ c2 * c2 * c1 ≤ (1 + c1) * (1 + c2) ^ 2 ∧
      c1 ≤ (1 + c1) * (1 + c2) ^ 2 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    nlinarith [sq_nonneg (1 + c2), mul_nonneg hc1 hc2, mul_nonneg hc1 (mul_nonneg hc2 hc2)]

/-- Pure real arithmetic for one `V`: from the chain
`‖QV‖ = A' + εG'`, `A' ≤ q B`, `G' ≤ v + s A'`, `B ≤ δA A + δG G`, `v ≤ χA A + χG G`
and the pair norm `‖V‖ = A + εG` with `εE = 1`, the bound `‖QV‖ ≤ M ‖V‖`. -/
theorem qs_pointwise {nQ nV Ap Gp nv bM A G q s ε E δA δG χA χG : ℝ}
    (hq : 0 ≤ q) (hs : 0 ≤ s) (hε : 0 ≤ ε) (hE : 0 ≤ E) (hεE : ε * E = 1)
    (hA : 0 ≤ A) (hG : 0 ≤ G) (hδA : 0 ≤ δA) (hδG : 0 ≤ δG) (hχA : 0 ≤ χA) (hχG : 0 ≤ χG)
    (hnQ : nQ = Ap + ε * Gp) (hnV : nV = A + ε * G)
    (hAp : Ap ≤ q * bM) (hGp : Gp ≤ nv + s * Ap)
    (hbM : bM ≤ δA * A + δG * G) (hnv : nv ≤ χA * A + χG * G) :
    nQ ≤ (q * δA + ε * s * q * δA + ε * χA + E * q * δG + s * q * δG + χG) * nV := by
  have hp : 0 ≤ 1 + ε * s := by nlinarith [mul_nonneg hε hs]
  have hqp : 0 ≤ (1 + ε * s) * q := mul_nonneg hp hq
  have k1 : ε * Gp ≤ ε * (nv + s * Ap) := mul_le_mul_of_nonneg_left hGp hε
  have k2 : (1 + ε * s) * Ap ≤ (1 + ε * s) * (q * bM) := mul_le_mul_of_nonneg_left hAp hp
  have k3 : (1 + ε * s) * q * bM ≤ (1 + ε * s) * q * (δA * A + δG * G) :=
    mul_le_mul_of_nonneg_left hbM hqp
  have k4 : ε * nv ≤ ε * (χA * A + χG * G) := mul_le_mul_of_nonneg_left hnv hε
  have hnQle : nQ ≤ ((1 + ε * s) * q * δA + ε * χA) * A
      + ((1 + ε * s) * q * δG + ε * χG) * G := by
    rw [hnQ]
    nlinarith [k1, k2, k3, k4]
  have ha1 : 0 ≤ (1 + ε * s) * q * δA + ε * χA :=
    add_nonneg (mul_nonneg hqp hδA) (mul_nonneg hε hχA)
  have ha2 : 0 ≤ (1 + ε * s) * q * δG + ε * χG :=
    add_nonneg (mul_nonneg hqp hδG) (mul_nonneg hε hχG)
  have hid : (q * δA + ε * s * q * δA + ε * χA + E * q * δG + s * q * δG + χG) * (A + ε * G)
      = ((1 + ε * s) * q * δA + ε * χA) * A + ((1 + ε * s) * q * δG + ε * χG) * G
        + (((1 + ε * s) * q * δA + ε * χA) * (ε * G)
          + ((1 + ε * s) * q * δG + ε * χG) * (E * A)) := by
    linear_combination (((1 + ε * s) * q * δG + ε * χG) * G
      - (s * q * δG + χG) * (A + ε * G)) * hεE
  have hpos1 : 0 ≤ ((1 + ε * s) * q * δA + ε * χA) * (ε * G) :=
    mul_nonneg ha1 (mul_nonneg hε hG)
  have hpos2 : 0 ≤ ((1 + ε * s) * q * δG + ε * χG) * (E * A) :=
    mul_nonneg ha2 (mul_nonneg hE hA)
  rw [hnV]
  linarith [hnQle, hid, hpos1, hpos2]

/-- The six-term exponential estimate. Each term is `≤ D ν⁻¹^K e^{-γ/(100ν)}` with
`K = k₁ + 2 k₂`, so the sum is `≤ 6 D ν⁻¹^K e^{-γ/(100ν)}`. -/
theorem qs_six {ν γ ωb m0 ηδ c1 c2 D : ℝ} {k1 k2 : ℕ} (hν : 0 < ν) (hν1 : ν ≤ 1)
    (hγ : 0 < γ) (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2)
    (hD1 : c2 * c1 ≤ D) (hD2 : c2 * c2 * c1 ≤ D) (hD3 : c1 ≤ D)
    (hωb : ωb < γ / 1000) (hm0 : m0 < γ / 1000) (hηδ : ηδ < γ / 1000) :
    c2 * ν⁻¹ ^ k2 * (c1 * ν⁻¹ ^ k1 * Real.exp (-(γ / 15 - ωb - 3 * m0 / 2) / ν))
      + Real.exp (-(γ / 8) / ν) * (c2 * ν⁻¹ ^ k2 * Real.exp (ηδ / ν)) * (c2 * ν⁻¹ ^ k2)
          * (c1 * ν⁻¹ ^ k1 * Real.exp (-(γ / 15 - ωb - 3 * m0 / 2) / ν))
      + Real.exp (-(γ / 8) / ν) * (c1 * ν⁻¹ ^ k1 * Real.exp ((γ / 10 + ωb + 3 * m0 / 2) / ν))
      + Real.exp (γ / 8 / ν) * (c2 * ν⁻¹ ^ k2)
          * (c1 * ν⁻¹ ^ k1 * Real.exp (-(19 * γ / 66 - ωb - 3 * m0 / 2) / ν))
      + (c2 * ν⁻¹ ^ k2 * Real.exp (ηδ / ν)) * (c2 * ν⁻¹ ^ k2)
          * (c1 * ν⁻¹ ^ k1 * Real.exp (-(19 * γ / 66 - ωb - 3 * m0 / 2) / ν))
      + c1 * ν⁻¹ ^ k1 * Real.exp (-(31 * γ / 165 - ωb - 3 * m0 / 2) / ν)
      ≤ 6 * D * ν⁻¹ ^ (k1 + 2 * k2) * Real.exp (-(γ / 100) / ν) := by
  have hK1 : k2 + k1 ≤ k1 + 2 * k2 := by omega
  have hK2 : 2 * k2 + k1 ≤ k1 + 2 * k2 := by omega
  have hK3 : k1 ≤ k1 + 2 * k2 := by omega
  -- term 1: q δA
  have t1 : c2 * ν⁻¹ ^ k2 * (c1 * ν⁻¹ ^ k1 * Real.exp (-(γ / 15 - ωb - 3 * m0 / 2) / ν))
      ≤ D * ν⁻¹ ^ (k1 + 2 * k2) * Real.exp (-(γ / 100) / ν) := by
    have e : c2 * ν⁻¹ ^ k2 * (c1 * ν⁻¹ ^ k1 * Real.exp (-(γ / 15 - ωb - 3 * m0 / 2) / ν))
        = c2 * c1 * ν⁻¹ ^ (k2 + k1) * Real.exp (-(γ / 15 - ωb - 3 * m0 / 2) / ν) := by
      ring
    have hx : -(γ / 15 - ωb - 3 * m0 / 2) ≤ -(γ / 100) := by linarith
    rw [e]
    exact qs_term hν hν1 hK1 (mul_nonneg hc2 hc1) hD1 hx
  -- term 2: ε s q δA
  have t2 : Real.exp (-(γ / 8) / ν) * (c2 * ν⁻¹ ^ k2 * Real.exp (ηδ / ν)) * (c2 * ν⁻¹ ^ k2)
          * (c1 * ν⁻¹ ^ k1 * Real.exp (-(γ / 15 - ωb - 3 * m0 / 2) / ν))
      ≤ D * ν⁻¹ ^ (k1 + 2 * k2) * Real.exp (-(γ / 100) / ν) := by
    have e : Real.exp (-(γ / 8) / ν) * (c2 * ν⁻¹ ^ k2 * Real.exp (ηδ / ν)) * (c2 * ν⁻¹ ^ k2)
          * (c1 * ν⁻¹ ^ k1 * Real.exp (-(γ / 15 - ωb - 3 * m0 / 2) / ν))
        = c2 * c2 * c1 * ν⁻¹ ^ (2 * k2 + k1)
          * (Real.exp (-(γ / 8) / ν) * Real.exp (ηδ / ν)
            * Real.exp (-(γ / 15 - ωb - 3 * m0 / 2) / ν)) := by
      ring
    have hE : Real.exp (-(γ / 8) / ν) * Real.exp (ηδ / ν)
          * Real.exp (-(γ / 15 - ωb - 3 * m0 / 2) / ν)
        = Real.exp ((-(γ / 8) + ηδ + -(γ / 15 - ωb - 3 * m0 / 2)) / ν) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    have hx : -(γ / 8) + ηδ + -(γ / 15 - ωb - 3 * m0 / 2) ≤ -(γ / 100) := by linarith
    rw [e, hE]
    exact qs_term hν hν1 hK2 (mul_nonneg (mul_nonneg hc2 hc2) hc1) hD2 hx
  -- term 3: ε χA
  have t3 : Real.exp (-(γ / 8) / ν) * (c1 * ν⁻¹ ^ k1 * Real.exp ((γ / 10 + ωb + 3 * m0 / 2) / ν))
      ≤ D * ν⁻¹ ^ (k1 + 2 * k2) * Real.exp (-(γ / 100) / ν) := by
    have e : Real.exp (-(γ / 8) / ν) * (c1 * ν⁻¹ ^ k1 * Real.exp ((γ / 10 + ωb + 3 * m0 / 2) / ν))
        = c1 * ν⁻¹ ^ k1
          * (Real.exp (-(γ / 8) / ν) * Real.exp ((γ / 10 + ωb + 3 * m0 / 2) / ν)) := by
      ring
    have hE : Real.exp (-(γ / 8) / ν) * Real.exp ((γ / 10 + ωb + 3 * m0 / 2) / ν)
        = Real.exp ((-(γ / 8) + (γ / 10 + ωb + 3 * m0 / 2)) / ν) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hx : -(γ / 8) + (γ / 10 + ωb + 3 * m0 / 2) ≤ -(γ / 100) := by linarith
    rw [e, hE]
    exact qs_term hν hν1 hK3 hc1 hD3 hx
  -- term 4: E q δG
  have t4 : Real.exp (γ / 8 / ν) * (c2 * ν⁻¹ ^ k2)
          * (c1 * ν⁻¹ ^ k1 * Real.exp (-(19 * γ / 66 - ωb - 3 * m0 / 2) / ν))
      ≤ D * ν⁻¹ ^ (k1 + 2 * k2) * Real.exp (-(γ / 100) / ν) := by
    have e : Real.exp (γ / 8 / ν) * (c2 * ν⁻¹ ^ k2)
          * (c1 * ν⁻¹ ^ k1 * Real.exp (-(19 * γ / 66 - ωb - 3 * m0 / 2) / ν))
        = c2 * c1 * ν⁻¹ ^ (k2 + k1)
          * (Real.exp (γ / 8 / ν) * Real.exp (-(19 * γ / 66 - ωb - 3 * m0 / 2) / ν)) := by
      ring
    have hE : Real.exp (γ / 8 / ν) * Real.exp (-(19 * γ / 66 - ωb - 3 * m0 / 2) / ν)
        = Real.exp ((γ / 8 + -(19 * γ / 66 - ωb - 3 * m0 / 2)) / ν) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hx : γ / 8 + -(19 * γ / 66 - ωb - 3 * m0 / 2) ≤ -(γ / 100) := by linarith
    rw [e, hE]
    exact qs_term hν hν1 hK1 (mul_nonneg hc2 hc1) hD1 hx
  -- term 5: s q δG
  have t5 : (c2 * ν⁻¹ ^ k2 * Real.exp (ηδ / ν)) * (c2 * ν⁻¹ ^ k2)
          * (c1 * ν⁻¹ ^ k1 * Real.exp (-(19 * γ / 66 - ωb - 3 * m0 / 2) / ν))
      ≤ D * ν⁻¹ ^ (k1 + 2 * k2) * Real.exp (-(γ / 100) / ν) := by
    have e : (c2 * ν⁻¹ ^ k2 * Real.exp (ηδ / ν)) * (c2 * ν⁻¹ ^ k2)
          * (c1 * ν⁻¹ ^ k1 * Real.exp (-(19 * γ / 66 - ωb - 3 * m0 / 2) / ν))
        = c2 * c2 * c1 * ν⁻¹ ^ (2 * k2 + k1)
          * (Real.exp (ηδ / ν) * Real.exp (-(19 * γ / 66 - ωb - 3 * m0 / 2) / ν)) := by
      ring
    have hE : Real.exp (ηδ / ν) * Real.exp (-(19 * γ / 66 - ωb - 3 * m0 / 2) / ν)
        = Real.exp ((ηδ + -(19 * γ / 66 - ωb - 3 * m0 / 2)) / ν) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hx : ηδ + -(19 * γ / 66 - ωb - 3 * m0 / 2) ≤ -(γ / 100) := by linarith
    rw [e, hE]
    exact qs_term hν hν1 hK2 (mul_nonneg (mul_nonneg hc2 hc2) hc1) hD2 hx
  -- term 6: χG
  have t6 : c1 * ν⁻¹ ^ k1 * Real.exp (-(31 * γ / 165 - ωb - 3 * m0 / 2) / ν)
      ≤ D * ν⁻¹ ^ (k1 + 2 * k2) * Real.exp (-(γ / 100) / ν) := by
    have hx : -(31 * γ / 165 - ωb - 3 * m0 / 2) ≤ -(γ / 100) := by linarith
    exact qs_term hν hν1 hK3 hc1 hD3 hx
  linarith [t1, t2, t3, t4, t5, t6]

/-- Proof of `T_qsmall` (target `qSmall`, source lines 5644-5686). -/
theorem qSmall : UnforcedLeray.Short.PartIIIb.T_qsmall := by
  intro S γ ωb m0 ηδ hγ hωb0 hm00 hηδ0 hωγ hmγ hηγ hpos hlim hG hEF hPN
  obtain ⟨C1, k1, N1, hEF'⟩ := hEF
  obtain ⟨C2, k2, N2, hPN'⟩ := hPN
  obtain ⟨N3, hN3⟩ := Filter.eventually_atTop.1
    (hlim.eventually (Iio_mem_nhds (zero_lt_one : (0 : ℝ) < 1)))
  refine ⟨6 * ((1 + |C1|) * (1 + |C2|) ^ 2), k1 + 2 * k2, N1 + N2 + N3, ?_⟩
  intro n hn z hz
  have hn1 : N1 ≤ n := by omega
  have hn2 : N2 ≤ n := by omega
  have hn3 : N3 ≤ n := by omega
  have hν0 : 0 < S.ν n := hpos n
  have hν1 : S.ν n ≤ 1 := (Set.mem_Iio.1 (hN3 n hn3)).le
  have hEFn := hEF' n hn1 z hz
  obtain ⟨hDN, hSN, hnormV⟩ := hPN' n hn2 z hz
  obtain ⟨_, _, _, hQ⟩ := hG n z hz
  obtain ⟨hD1, hD2, hD3⟩ := qs_consts (abs_nonneg C1) (abs_nonneg C2)
  have hsix := qs_six (ν := S.ν n) (γ := γ) (ωb := ωb) (m0 := m0) (ηδ := ηδ)
    (c1 := |C1|) (c2 := |C2|) (D := (1 + |C1|) * (1 + |C2|) ^ 2) (k1 := k1) (k2 := k2)
    hν0 hν1 hγ (abs_nonneg C1) (abs_nonneg C2) hD1 hD2 hD3 hωγ hmγ hηγ
  have hq0 : 0 ≤ (S.ν n)⁻¹ ^ k2 := pow_nonneg (inv_nonneg.2 hν0.le) k2
  have hq0' : 0 ≤ (S.ν n)⁻¹ ^ k1 := pow_nonneg (inv_nonneg.2 hν0.le) k1
  have hRnn : 0 ≤ 6 * ((1 + |C1|) * (1 + |C2|) ^ 2) * (S.ν n)⁻¹ ^ (k1 + 2 * k2)
      * Real.exp (-(γ / 100) / S.ν n) :=
    mul_nonneg (mul_nonneg (by positivity) (pow_nonneg (inv_nonneg.2 hν0.le) _))
      (Real.exp_pos _).le
  refine ContinuousLinearMap.opNorm_le_bound _ hRnn ?_
  intro V
  -- graph-lift identities for `Q V`
  have hTQ : (S.ops n z).Tc ((S.ops n z).Q V)
      = -((S.ops n z).DNinv ((S.ops n z).M ((S.ops n z).vQ ((S.ops n z).Tc V)))) :=
    congrArg Prod.fst (hQ V)
  have hWQ : (S.ops n z).wc ((S.ops n z).Q V)
      = -((S.ops n z).vQ ((S.ops n z).Tc V)
          - (S.ops n z).SN ((S.ops n z).DNinv ((S.ops n z).M ((S.ops n z).vQ ((S.ops n z).Tc V)))))
      := congrArg Prod.snd (hQ V)
  obtain ⟨hB0, hv0⟩ := hEFn V
  have hDNa : ∀ T : S.Str n, ‖(S.ops n z).DNinv T‖ ≤ |C2| * (S.ν n)⁻¹ ^ k2 * ‖T‖ :=
    fun T => le_trans (hDN T) (qs_abs2 hq0 (norm_nonneg T))
  have hSNa : ∀ T : S.Str n, ‖(S.ops n z).SN T‖
      ≤ |C2| * (S.ν n)⁻¹ ^ k2 * Real.exp (ηδ / S.ν n) * ‖T‖ :=
    fun T => le_trans (hSN T) (qs_abs3 hq0 (Real.exp_pos (ηδ / S.ν n)).le (norm_nonneg T))
  have hAp : ‖(S.ops n z).Tc ((S.ops n z).Q V)‖
      ≤ |C2| * (S.ν n)⁻¹ ^ k2 * ‖(S.ops n z).M ((S.ops n z).vQ ((S.ops n z).Tc V))‖ := by
    rw [hTQ, norm_neg]
    exact hDNa _
  have hGp : ‖(S.ops n z).wc ((S.ops n z).Q V)‖
      ≤ ‖(S.ops n z).vQ ((S.ops n z).Tc V)‖
        + |C2| * (S.ν n)⁻¹ ^ k2 * Real.exp (ηδ / S.ν n)
          * ‖(S.ops n z).Tc ((S.ops n z).Q V)‖ := by
    rw [hWQ, norm_neg, hTQ, norm_neg]
    have h1 := norm_sub_le ((S.ops n z).vQ ((S.ops n z).Tc V))
      ((S.ops n z).SN ((S.ops n z).DNinv ((S.ops n z).M ((S.ops n z).vQ ((S.ops n z).Tc V)))))
    have h2 := hSNa ((S.ops n z).DNinv ((S.ops n z).M ((S.ops n z).vQ ((S.ops n z).Tc V))))
    linarith
  have hbM : ‖(S.ops n z).M ((S.ops n z).vQ ((S.ops n z).Tc V))‖
      ≤ |C1| * (S.ν n)⁻¹ ^ k1 * Real.exp (-(γ / 15 - ωb - 3 * m0 / 2) / S.ν n)
          * ‖(S.ops n z).Tc V‖
        + |C1| * (S.ν n)⁻¹ ^ k1 * Real.exp (-(19 * γ / 66 - ωb - 3 * m0 / 2) / S.ν n)
          * ‖(S.ops n z).wc V‖ :=
    le_trans hB0 (add_le_add
      (qs_abs3 hq0' (Real.exp_pos (-(γ / 15 - ωb - 3 * m0 / 2) / S.ν n)).le (norm_nonneg _))
      (qs_abs3 hq0' (Real.exp_pos (-(19 * γ / 66 - ωb - 3 * m0 / 2) / S.ν n)).le
        (norm_nonneg _)))
  have hnv : ‖(S.ops n z).vQ ((S.ops n z).Tc V)‖
      ≤ |C1| * (S.ν n)⁻¹ ^ k1 * Real.exp ((γ / 10 + ωb + 3 * m0 / 2) / S.ν n)
          * ‖(S.ops n z).Tc V‖
        + |C1| * (S.ν n)⁻¹ ^ k1 * Real.exp (-(31 * γ / 165 - ωb - 3 * m0 / 2) / S.ν n)
          * ‖(S.ops n z).wc V‖ :=
    le_trans hv0 (add_le_add
      (qs_abs3 hq0' (Real.exp_pos ((γ / 10 + ωb + 3 * m0 / 2) / S.ν n)).le (norm_nonneg _))
      (qs_abs3 hq0' (Real.exp_pos (-(31 * γ / 165 - ωb - 3 * m0 / 2) / S.ν n)).le
        (norm_nonneg _)))
  have hεE : Real.exp (-(γ / 8) / S.ν n) * Real.exp (γ / 8 / S.ν n) = 1 := by
    rw [← Real.exp_add, show -(γ / 8) / S.ν n + γ / 8 / S.ν n = 0 by ring, Real.exp_zero]
  have hqnn : 0 ≤ |C2| * (S.ν n)⁻¹ ^ k2 := mul_nonneg (abs_nonneg _) hq0
  have hsnn : 0 ≤ |C2| * (S.ν n)⁻¹ ^ k2 * Real.exp (ηδ / S.ν n) :=
    mul_nonneg hqnn (Real.exp_pos _).le
  have hδAnn : 0 ≤ |C1| * (S.ν n)⁻¹ ^ k1 * Real.exp (-(γ / 15 - ωb - 3 * m0 / 2) / S.ν n) :=
    mul_nonneg (mul_nonneg (abs_nonneg _) hq0') (Real.exp_pos _).le
  have hδGnn : 0 ≤ |C1| * (S.ν n)⁻¹ ^ k1 * Real.exp (-(19 * γ / 66 - ωb - 3 * m0 / 2) / S.ν n) :=
    mul_nonneg (mul_nonneg (abs_nonneg _) hq0') (Real.exp_pos _).le
  have hχAnn : 0 ≤ |C1| * (S.ν n)⁻¹ ^ k1 * Real.exp ((γ / 10 + ωb + 3 * m0 / 2) / S.ν n) :=
    mul_nonneg (mul_nonneg (abs_nonneg _) hq0') (Real.exp_pos _).le
  have hχGnn : 0 ≤ |C1| * (S.ν n)⁻¹ ^ k1 * Real.exp (-(31 * γ / 165 - ωb - 3 * m0 / 2) / S.ν n) :=
    mul_nonneg (mul_nonneg (abs_nonneg _) hq0') (Real.exp_pos _).le
  have key := qs_pointwise hqnn hsnn (Real.exp_pos (-(γ / 8) / S.ν n)).le
    (Real.exp_pos (γ / 8 / S.ν n)).le hεE (norm_nonneg _) (norm_nonneg _)
    hδAnn hδGnn hχAnn hχGnn (hnormV ((S.ops n z).Q V)) (hnormV V) hAp hGp hbM hnv
  exact le_trans key (mul_le_mul_of_nonneg_right hsix (norm_nonneg V))

end UnforcedLeray.Short.PartIIIb
