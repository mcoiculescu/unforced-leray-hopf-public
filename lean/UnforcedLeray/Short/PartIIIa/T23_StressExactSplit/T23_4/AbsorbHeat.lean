import UnforcedLeray.Short.PartIIIa.Sub.T23_4_Leaves
import UnforcedLeray.Lib.BudgetsGronwall.PolyBounded
import UnforcedLeray.Lib.Gaussian.Absorb

/-!
# Part III-a, task `PartIII-a:T23/4/4`: absorption of the heat-width exponential

Source of record: `the November 2 reference manuscript`, lines 2751-2754
(`stress-short:transverse`, "increasing `C_⊥` absorbs the fixed weights"), and `sct:transverse`
(SP 463-467), whose heat-width term is `e^{-bl/c}` with `c = (ν²)⁻¹`.

Proves `tailAbsorbHeat : TailAbsorbHeat` (pure real calculus): with `X = |η|`, `l = X - C'/ν - 2`,
`c = (ν²)⁻¹`, one has `e^{-bl/c} = e^{-bν²l} ≤ e^{b(|C'|+2)} e^{-bν²X}`, the polynomial factor is
`≤ C' ν^{-2N} e^{NK/ν}`, `(1+S)^M ≤ 2^M e^{MK/ν}`, `(1+η²)^m ≤ 2^m X^{2m}`, and
`X^{2m} e^{-bν²X} ≤ (2/b)^{2m}(2m)! ν^{-4m} e^{-bC_⊥ν^{-1}/2}` (`pow_mul_exp_neg_le_factorial`
applied to `y = bν²X/2`). The exponent `e^{(M+N)K/ν - bC_⊥/(2ν)} ≤ e^{-(D+1)/ν}` fixes `C_⊥`,
and the remaining `G ν^{-p} e^{-1/ν} ≤ 1/4` for small `ν` (`tendsto_inv_pow_mul_exp_neg`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology

namespace UnforcedLeray.Short.IIIa

namespace T23AH

/-- A small-`ν` bound: `G ν^{-p} e^{-1/ν} ≤ 1/4` for `0 < ν ≤ ν₀`. -/
theorem final_small (G : ℝ) (p : ℕ) :
    ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
      G * (ν⁻¹ ^ p * Real.exp (-1 / ν)) ≤ 1 / 4 := by
  have h := (UnforcedLeray.Budget.tendsto_inv_pow_mul_exp_neg p (κ := 1) one_pos).const_mul G
  have hev := h.eventually (Iio_mem_nhds (by norm_num : G * 0 < 1 / 4))
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
  obtain ⟨ε, hε, hP⟩ := hev
  refine ⟨ε / 2, by positivity, fun ν hν hνle => ?_⟩
  have hd : dist ν 0 < ε := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hν]
    linarith
  exact (Set.mem_Iio.1 (hP hd hν)).le

/-- Product of four nonnegative factors, each bounded. -/
theorem mul4_le {a1 a2 a3 a4 b1 b2 b3 b4 : ℝ} (h1 : 0 ≤ a1) (h2 : 0 ≤ a2) (h3 : 0 ≤ a3)
    (h4 : 0 ≤ a4) (g1 : a1 ≤ b1) (g2 : a2 ≤ b2) (g3 : a3 ≤ b3) (g4 : a4 ≤ b4) :
    a1 * a2 * (a3 * a4) ≤ b1 * b2 * (b3 * b4) := by
  have hb1 := h1.trans g1
  have hb2 := h2.trans g2
  have hb3 := h3.trans g3
  exact mul_le_mul (mul_le_mul g1 g2 h2 hb1) (mul_le_mul g3 g4 h4 hb3)
    (mul_nonneg h3 h4) (mul_nonneg hb1 hb2)

/-- The polynomial factor: `polyPS C N ν (ν²)⁻¹ S ≤ |C| 6^N ν⁻¹^{2N} e^{NK/ν}` for
`0 < ν ≤ 1`, `1 ≤ S ≤ e^{K/ν}`. -/
theorem polyPS_bound (C : ℝ) (N : ℕ) {ν K S : ℝ} (hν : 0 < ν) (hν1 : ν ≤ 1) (hK : 0 ≤ K)
    (hS1 : 1 ≤ S) (hSK : S ≤ Real.exp (K / ν)) :
    UnforcedLeray.Short.PartI.polyPS C N ν (ν ^ 2)⁻¹ S ≤
      |C| * 6 ^ N * (ν⁻¹) ^ (2 * N) * Real.exp (K / ν) ^ N := by
  have ha1 : 1 ≤ ν⁻¹ := (one_le_inv₀ hν).2 hν1
  have hc : (ν ^ 2)⁻¹ = (ν⁻¹) ^ 2 := by rw [inv_pow]
  have hE1 : 1 ≤ Real.exp (K / ν) := Real.one_le_exp (div_nonneg hK hν.le)
  have hu0 : 0 ≤ (1 + (ν ^ 2)⁻¹ + ν⁻¹) * (1 + S) := by
    apply mul_nonneg
    · have : 0 ≤ (ν ^ 2)⁻¹ := by positivity
      have : 0 ≤ ν⁻¹ := by positivity
      linarith
    · linarith
  have hu : (1 + (ν ^ 2)⁻¹ + ν⁻¹) * (1 + S) ≤
      (3 * (ν⁻¹) ^ 2) * (2 * Real.exp (K / ν)) := by
    rw [hc]
    apply mul_le_mul
    · nlinarith
    · linarith
    · linarith
    · positivity
  have hpow := pow_le_pow_left₀ hu0 hu N
  unfold UnforcedLeray.Short.PartI.polyPS
  calc C * ((1 + (ν ^ 2)⁻¹ + ν⁻¹) * (1 + S)) ^ N
      ≤ |C| * ((1 + (ν ^ 2)⁻¹ + ν⁻¹) * (1 + S)) ^ N :=
        mul_le_mul_of_nonneg_right (le_abs_self C) (pow_nonneg hu0 N)
    _ ≤ |C| * ((3 * (ν⁻¹) ^ 2) * (2 * Real.exp (K / ν))) ^ N :=
        mul_le_mul_of_nonneg_left hpow (abs_nonneg C)
    _ = |C| * 6 ^ N * (ν⁻¹) ^ (2 * N) * Real.exp (K / ν) ^ N := by ring

/-- `(1+S)^M ≤ 2^M e^{MK/ν}` for `1 ≤ S ≤ E`, `1 ≤ E`. -/
theorem onePS_pow (M : ℕ) {S E : ℝ} (hS1 : 1 ≤ S) (hSE : S ≤ E) (hE : 1 ≤ E) :
    (1 + S) ^ M ≤ 2 ^ M * E ^ M := by
  rw [← mul_pow]
  exact pow_le_pow_left₀ (by linarith) (by linarith) M

/-- The heat exponential: `e^{-bl/c} ≤ e^{b(|C'|+2)} e^{-bν²X}` for `0 < ν ≤ 1`,
`l = X - C'/ν - 2`, `c = (ν²)⁻¹`. -/
theorem exp_heat_shift (b C' ν X : ℝ) (hb : 0 < b) (hν : 0 < ν) (hν1 : ν ≤ 1) :
    Real.exp (-(b * (X - C' / ν - 2) / (ν ^ 2)⁻¹)) ≤
      Real.exp (b * (|C'| + 2)) * Real.exp (-(b * ν ^ 2 * X)) := by
  have hν0 : ν ≠ 0 := hν.ne'
  have e : -(b * (X - C' / ν - 2) / (ν ^ 2)⁻¹) =
      -(b * ν ^ 2 * X) + (b * ν * C' + 2 * b * ν ^ 2) := by
    field_simp
    ring
  have h1 : ν * C' ≤ |C'| := by
    have := le_abs_self C'
    have := abs_nonneg C'
    nlinarith
  have h2 : b * ν * C' ≤ b * |C'| := by
    have : b * ν * C' = b * (ν * C') := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_left h1 hb.le
  have h3 : 2 * b * ν ^ 2 ≤ 2 * b := by
    have : ν ^ 2 ≤ 1 := by nlinarith
    nlinarith
  calc Real.exp (-(b * (X - C' / ν - 2) / (ν ^ 2)⁻¹))
      = Real.exp (-(b * ν ^ 2 * X) + (b * ν * C' + 2 * b * ν ^ 2)) := by rw [e]
    _ ≤ Real.exp (-(b * ν ^ 2 * X) + b * (|C'| + 2)) :=
        Real.exp_le_exp.2 (by nlinarith)
    _ = Real.exp (b * (|C'| + 2)) * Real.exp (-(b * ν ^ 2 * X)) := by
        rw [Real.exp_add]
        ring

/-- The `X`-power against the heat exponential, `X = |η| ≥ Cp ((ν²)⁻¹/ν)`:
`X^{2m} e^{-bν²X} ≤ (2/b)^{2m}(2m)! ν^{-4m} e^{-bCp ν^{-1}/2}`. -/
theorem x_pow_exp (b ν X Cp : ℝ) (m : ℕ) (hb : 0 < b) (hν : 0 < ν) (hX : 0 ≤ X)
    (hXC : Cp * ((ν ^ 2)⁻¹ / ν) ≤ X) :
    X ^ (2 * m) * Real.exp (-(b * ν ^ 2 * X)) ≤
      (2 / b) ^ (2 * m) * ((2 * m).factorial : ℝ) * (ν⁻¹) ^ (4 * m) *
        Real.exp (-(b * Cp * ν⁻¹ / 2)) := by
  have hbν : 0 < b * ν ^ 2 := mul_pos hb (pow_pos hν 2)
  have hy0 : 0 ≤ b * ν ^ 2 * X / 2 := div_nonneg (mul_nonneg hbν.le hX) (by norm_num)
  have hpow : (2 / (b * ν ^ 2) * (b * ν ^ 2 * X / 2)) ^ (2 * m) = X ^ (2 * m) := by
    congr 1
    field_simp
  have hfac : X ^ (2 * m) * Real.exp (-(b * ν ^ 2 * X / 2)) ≤
      (2 / (b * ν ^ 2)) ^ (2 * m) * ((2 * m).factorial : ℝ) := by
    have key := UnforcedLeray.Gaussian.pow_mul_exp_neg_le_factorial (2 * m) hy0
    calc X ^ (2 * m) * Real.exp (-(b * ν ^ 2 * X / 2))
        = (2 / (b * ν ^ 2) * (b * ν ^ 2 * X / 2)) ^ (2 * m) *
            Real.exp (-(b * ν ^ 2 * X / 2)) := by rw [hpow]
      _ = (2 / (b * ν ^ 2)) ^ (2 * m) *
            ((b * ν ^ 2 * X / 2) ^ (2 * m) * Real.exp (-(b * ν ^ 2 * X / 2))) := by
          rw [mul_pow]
          ring
      _ ≤ (2 / (b * ν ^ 2)) ^ (2 * m) * ((2 * m).factorial : ℝ) :=
          mul_le_mul_of_nonneg_left key (pow_nonneg (div_nonneg (by norm_num) hbν.le) _)
  have h1 : ν ^ 2 * ((ν ^ 2)⁻¹ / ν) = ν⁻¹ := by
    field_simp
  have h2 : b * Cp * ν⁻¹ / 2 ≤ b * ν ^ 2 * X / 2 := by
    have h3 : b * Cp * ν⁻¹ = (b * ν ^ 2) * (Cp * ((ν ^ 2)⁻¹ / ν)) := by
      rw [← h1]
      ring
    rw [h3]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hXC hbν.le) (by norm_num)
  have hexp : Real.exp (-(b * ν ^ 2 * X / 2)) ≤ Real.exp (-(b * Cp * ν⁻¹ / 2)) :=
    Real.exp_le_exp.2 (neg_le_neg h2)
  have hsplit : Real.exp (-(b * ν ^ 2 * X)) =
      Real.exp (-(b * ν ^ 2 * X / 2)) * Real.exp (-(b * ν ^ 2 * X / 2)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hdiv : (2 / (b * ν ^ 2)) = (2 / b) * (ν⁻¹) ^ 2 := by
    field_simp
  calc X ^ (2 * m) * Real.exp (-(b * ν ^ 2 * X))
      = (X ^ (2 * m) * Real.exp (-(b * ν ^ 2 * X / 2))) *
          Real.exp (-(b * ν ^ 2 * X / 2)) := by
        rw [hsplit]
        ring
    _ ≤ ((2 / (b * ν ^ 2)) ^ (2 * m) * ((2 * m).factorial : ℝ)) *
          Real.exp (-(b * Cp * ν⁻¹ / 2)) :=
        mul_le_mul hfac hexp (Real.exp_nonneg _)
          (mul_nonneg (pow_nonneg (div_nonneg (by norm_num) hbν.le) _) (Nat.cast_nonneg _))
    _ = (2 / b) ^ (2 * m) * ((2 * m).factorial : ℝ) * (ν⁻¹) ^ (4 * m) *
          Real.exp (-(b * Cp * ν⁻¹ / 2)) := by
        rw [hdiv, mul_pow]
        ring

end T23AH

/-- **Absorption of the heat-width exponential** (SP 2751-2754), `TailAbsorbHeat`. -/
theorem tailAbsorbHeat : UnforcedLeray.Short.IIIa.TailAbsorbHeat := by
  intro b C' C K D N M m hb hD hK
  have hb2 : (0 : ℝ) ≤ 2 / b := div_nonneg (by norm_num) hb.le
  obtain ⟨G, hGdef⟩ : ∃ G : ℝ, G = 2 ^ M * 2 ^ m * (|C| * 6 ^ N) *
      Real.exp (b * (|C'| + 2)) * (2 / b) ^ (2 * m) * ((2 * m).factorial : ℝ) := ⟨_, rfl⟩
  have hG0 : 0 ≤ G := by
    rw [hGdef]
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (by positivity))
      (Real.exp_nonneg _)) (pow_nonneg hb2 _)) (Nat.cast_nonneg _)
  obtain ⟨νs, hνs, hsm⟩ := T23AH.final_small G (2 * N + 4 * m)
  obtain ⟨Cp, hCpdef⟩ : ∃ Cp : ℝ, Cp = max 1 (2 * (((M : ℝ) + N) * K + D + 1) / b) := ⟨_, rfl⟩
  have hCp1 : 1 ≤ Cp := by rw [hCpdef]; exact le_max_left _ _
  have hCpb : ((M : ℝ) + N) * K + D + 1 ≤ b * Cp / 2 := by
    have h := le_max_right 1 (2 * (((M : ℝ) + N) * K + D + 1) / b)
    rw [← hCpdef] at h
    rw [div_le_iff₀ hb] at h
    linarith
  refine ⟨Cp, min νs 1, lt_of_lt_of_le one_pos hCp1, lt_min hνs one_pos, ?_⟩
  intro ν hν hν1 S hS1 hSK η hη
  have hνs' : ν ≤ νs := hν1.trans (min_le_left _ _)
  have hνle1 : ν ≤ 1 := hν1.trans (min_le_right _ _)
  have hE1 : 1 ≤ Real.exp (K / ν) := Real.one_le_exp (div_nonneg hK hν.le)
  have hinv : 1 ≤ (ν ^ 2)⁻¹ / ν := by
    rw [le_div_iff₀ hν, ← one_div, le_div_iff₀ (by positivity)]
    nlinarith
  have hXC : Cp * ((ν ^ 2)⁻¹ / ν) ≤ |η| := by
    have e : Cp * ((ν ^ 2)⁻¹ / ν + Real.sqrt S + 1) =
        Cp * ((ν ^ 2)⁻¹ / ν) + Cp * (Real.sqrt S + 1) := by ring
    have h0 : 0 ≤ Cp * (Real.sqrt S + 1) := mul_nonneg (by linarith) (by positivity)
    have := hη
    rw [e] at this
    linarith
  have hX1 : 1 ≤ |η| := by
    have : 1 ≤ Cp * ((ν ^ 2)⁻¹ / ν) := by nlinarith
    linarith
  have hη2 : η ^ 2 = |η| ^ 2 := (sq_abs η).symm
  have hX0 : 0 ≤ |η| := abs_nonneg η
  have F1 : (1 + S) ^ M ≤ 2 ^ M * Real.exp (K / ν) ^ M := T23AH.onePS_pow M hS1 hSK hE1
  have F3 : (1 + η ^ 2) ^ m ≤ 2 ^ m * |η| ^ (2 * m) := by
    have hh : 1 + η ^ 2 ≤ 2 * |η| ^ 2 := by
      rw [← hη2]
      nlinarith
    calc (1 + η ^ 2) ^ m ≤ (2 * |η| ^ 2) ^ m := pow_le_pow_left₀ (by positivity) hh m
      _ = 2 ^ m * |η| ^ (2 * m) := by rw [mul_pow, ← pow_mul]
  have hP := T23AH.polyPS_bound C N hν hνle1 hK hS1 hSK
  have hQ := T23AH.exp_heat_shift b C' ν |η| hb hν hνle1
  have hxp := T23AH.x_pow_exp b ν |η| Cp m hb hν hX0 hXC
  have hP'0 : 0 ≤ |C| * 6 ^ N * (ν⁻¹) ^ (2 * N) * Real.exp (K / ν) ^ N :=
    mul_nonneg (mul_nonneg (mul_nonneg (abs_nonneg C) (by positivity))
      (pow_nonneg (inv_nonneg.2 hν.le) _)) (by positivity)
  have hQ'0 : 0 ≤ Real.exp (b * (|C'| + 2)) * Real.exp (-(b * ν ^ 2 * |η|)) :=
    mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _)
  have hAB : 0 ≤ (1 + S) ^ M * (1 + η ^ 2) ^ m := by
    apply mul_nonneg
    · exact pow_nonneg (by linarith) M
    · exact pow_nonneg (by positivity) m
  have hmain : (1 + S) ^ M * (1 + η ^ 2) ^ m *
      (UnforcedLeray.Short.PartI.polyPS C N ν (ν ^ 2)⁻¹ S *
        Real.exp (-(b * (|η| - C' / ν - 2) / (ν ^ 2)⁻¹))) ≤
      (2 ^ M * Real.exp (K / ν) ^ M) * (2 ^ m * |η| ^ (2 * m)) *
        ((|C| * 6 ^ N * (ν⁻¹) ^ (2 * N) * Real.exp (K / ν) ^ N) *
          (Real.exp (b * (|C'| + 2)) * Real.exp (-(b * ν ^ 2 * |η|)))) := by
    have hPQ : UnforcedLeray.Short.PartI.polyPS C N ν (ν ^ 2)⁻¹ S *
        Real.exp (-(b * (|η| - C' / ν - 2) / (ν ^ 2)⁻¹)) ≤
        (|C| * 6 ^ N * (ν⁻¹) ^ (2 * N) * Real.exp (K / ν) ^ N) *
          (Real.exp (b * (|C'| + 2)) * Real.exp (-(b * ν ^ 2 * |η|))) :=
      mul_le_mul hP hQ (Real.exp_nonneg _) hP'0
    calc (1 + S) ^ M * (1 + η ^ 2) ^ m *
          (UnforcedLeray.Short.PartI.polyPS C N ν (ν ^ 2)⁻¹ S *
            Real.exp (-(b * (|η| - C' / ν - 2) / (ν ^ 2)⁻¹)))
        = ((1 + S) ^ M * (1 + η ^ 2) ^ m) *
          (UnforcedLeray.Short.PartI.polyPS C N ν (ν ^ 2)⁻¹ S *
            Real.exp (-(b * (|η| - C' / ν - 2) / (ν ^ 2)⁻¹))) := by ring
      _ ≤ ((1 + S) ^ M * (1 + η ^ 2) ^ m) *
          ((|C| * 6 ^ N * (ν⁻¹) ^ (2 * N) * Real.exp (K / ν) ^ N) *
            (Real.exp (b * (|C'| + 2)) * Real.exp (-(b * ν ^ 2 * |η|)))) :=
          mul_le_mul_of_nonneg_left hPQ hAB
      _ ≤ (2 ^ M * Real.exp (K / ν) ^ M) * (2 ^ m * |η| ^ (2 * m)) *
          ((|C| * 6 ^ N * (ν⁻¹) ^ (2 * N) * Real.exp (K / ν) ^ N) *
            (Real.exp (b * (|C'| + 2)) * Real.exp (-(b * ν ^ 2 * |η|)))) :=
          mul_le_mul_of_nonneg_right (mul_le_mul F1 F3 (pow_nonneg (by positivity) m)
            (by positivity)) (mul_nonneg hP'0 hQ'0)
  have hpre : 0 ≤ 2 ^ M * 2 ^ m * (|C| * 6 ^ N) * Real.exp (b * (|C'| + 2)) *
      (ν⁻¹) ^ (2 * N) * (Real.exp (K / ν) ^ M * Real.exp (K / ν) ^ N) :=
    mul_nonneg (mul_nonneg (by positivity) (pow_nonneg (inv_nonneg.2 hν.le) _))
      (by positivity)
  have hrest : (2 ^ M * Real.exp (K / ν) ^ M) * (2 ^ m * |η| ^ (2 * m)) *
      ((|C| * 6 ^ N * (ν⁻¹) ^ (2 * N) * Real.exp (K / ν) ^ N) *
        (Real.exp (b * (|C'| + 2)) * Real.exp (-(b * ν ^ 2 * |η|)))) ≤
      G * (ν⁻¹) ^ (2 * N + 4 * m) *
        (Real.exp (K / ν) ^ M * Real.exp (K / ν) ^ N *
          Real.exp (-(b * Cp * ν⁻¹ / 2))) := by
    calc (2 ^ M * Real.exp (K / ν) ^ M) * (2 ^ m * |η| ^ (2 * m)) *
          ((|C| * 6 ^ N * (ν⁻¹) ^ (2 * N) * Real.exp (K / ν) ^ N) *
            (Real.exp (b * (|C'| + 2)) * Real.exp (-(b * ν ^ 2 * |η|))))
        = (2 ^ M * 2 ^ m * (|C| * 6 ^ N) * Real.exp (b * (|C'| + 2))) *
          (ν⁻¹) ^ (2 * N) * (Real.exp (K / ν) ^ M * Real.exp (K / ν) ^ N) *
          (|η| ^ (2 * m) * Real.exp (-(b * ν ^ 2 * |η|))) := by ring
      _ ≤ (2 ^ M * 2 ^ m * (|C| * 6 ^ N) * Real.exp (b * (|C'| + 2))) *
          (ν⁻¹) ^ (2 * N) * (Real.exp (K / ν) ^ M * Real.exp (K / ν) ^ N) *
          ((2 / b) ^ (2 * m) * ((2 * m).factorial : ℝ) * (ν⁻¹) ^ (4 * m) *
            Real.exp (-(b * Cp * ν⁻¹ / 2))) :=
          mul_le_mul_of_nonneg_left hxp hpre
      _ = G * (ν⁻¹) ^ (2 * N + 4 * m) *
          (Real.exp (K / ν) ^ M * Real.exp (K / ν) ^ N *
            Real.exp (-(b * Cp * ν⁻¹ / 2))) := by
          rw [hGdef, pow_add]
          ring
  have hfin : G * (ν⁻¹) ^ (2 * N + 4 * m) *
      (Real.exp (K / ν) ^ M * Real.exp (K / ν) ^ N * Real.exp (-(b * Cp * ν⁻¹ / 2))) ≤
      G * (ν⁻¹) ^ (2 * N + 4 * m) * Real.exp (-(D + 1) / ν) := by
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg hG0 (pow_nonneg (inv_nonneg.2 hν.le) _))
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.2
    have e2 : (M : ℝ) * (K / ν) + (N : ℝ) * (K / ν) + -(b * Cp * ν⁻¹ / 2) =
        (((M : ℝ) + N) * K - b * Cp / 2) / ν := by
      ring
    rw [e2]
    apply div_le_div_of_nonneg_right _ hν.le
    linarith
  have hfinal : G * (ν⁻¹) ^ (2 * N + 4 * m) * Real.exp (-(D + 1) / ν) ≤
      Real.exp (-D / ν) / 4 := by
    have hs : Real.exp (-(D + 1) / ν) = Real.exp (-D / ν) * Real.exp (-1 / ν) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hs]
    have hh := hsm ν hν hνs'
    have hE := Real.exp_pos (-D / ν)
    calc G * (ν⁻¹) ^ (2 * N + 4 * m) * (Real.exp (-D / ν) * Real.exp (-1 / ν))
        = Real.exp (-D / ν) * (G * (ν⁻¹ ^ (2 * N + 4 * m) * Real.exp (-1 / ν))) := by ring
      _ ≤ Real.exp (-D / ν) * (1 / 4) := mul_le_mul_of_nonneg_left hh hE.le
      _ = Real.exp (-D / ν) / 4 := by ring
  exact le_trans hmain (le_trans hrest (le_trans hfin hfinal))

end UnforcedLeray.Short.IIIa
