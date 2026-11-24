import UnforcedLeray.Short.PartIIIa.Sub.T23_4_Leaves
import UnforcedLeray.Lib.BudgetsGronwall.PolyBounded
import UnforcedLeray.Lib.Gaussian.Absorb

/-!
# Part III-a, task `PartIII-a:T23/4/5`: absorption of the Gaussian vorticity exponential

Source of record: `the November 2 reference manuscript`, lines 2750-2754
(`stress-short:transverse`, "increasing `C_⊥` absorbs the fixed weights"), and `sct:transverse`
(SP 463-467), whose Gaussian term is `e^{-bl²/(C₀+νS)}`.

Proves `tailAbsorbGauss : TailAbsorbGauss` (pure real calculus). With `X = |η|`, `T = ν⁻¹`,
`Q = C₀+νS`, `l = X - C'/ν - 2`: `l ≥ X/2` once `C_⊥ ≥ 2(|C'|+2)`; then
`e^{-bl²/Q} ≤ e^{-u}²` with `u = bX²/(8Q)`; `X^{2m} e^{-u} ≤ (8Q/b)^m m!`; `Q ≤ (C₀+1)(T⁶+S)ν`
and `X² ≥ C_⊥²(T⁶+S)` give `u ≥ κ T` with `κ = bC_⊥²/(8(C₀+1))`; and the exponent
`e^{((M+N+m)K-κ)T} ≤ e^{-(D+1)T}` fixes `C_⊥`, while `G T^{2N} e^{-(D+1)/ν} ≤ e^{-D/ν}/4`
for small `ν`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology

namespace UnforcedLeray.Short.IIIa

namespace T23AG

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

/-- Splitting the Gaussian exponential: `e^{-bl²/Q} ≤ e^{-u}²`, `u = bX²/(8Q)`, when
`X/2 ≤ l`. -/
theorem gauss_split (b C₀ C' X ν S : ℝ) (hb : 0 < b) (hQ : 0 < C₀ + ν * S)
    (hl : X / 2 ≤ X - C' / ν - 2) (hX0 : 0 ≤ X) :
    Real.exp (-(b * (X - C' / ν - 2) ^ 2 / (C₀ + ν * S))) ≤
      Real.exp (-(b * X ^ 2 / (8 * (C₀ + ν * S)))) *
        Real.exp (-(b * X ^ 2 / (8 * (C₀ + ν * S)))) := by
  have hl2 : (X / 2) ^ 2 ≤ (X - C' / ν - 2) ^ 2 := pow_le_pow_left₀ (by linarith) hl 2
  have h1 : b * X ^ 2 / (4 * (C₀ + ν * S)) ≤ b * (X - C' / ν - 2) ^ 2 / (C₀ + ν * S) := by
    rw [div_le_div_iff₀ (by linarith) hQ]
    nlinarith [mul_le_mul_of_nonneg_left hl2 (mul_pos hb hQ).le]
  have h2 : Real.exp (-(b * (X - C' / ν - 2) ^ 2 / (C₀ + ν * S))) ≤
      Real.exp (-(b * X ^ 2 / (4 * (C₀ + ν * S)))) :=
    Real.exp_le_exp.2 (neg_le_neg h1)
  have e4 : b * X ^ 2 / (4 * (C₀ + ν * S)) = 2 * (b * X ^ 2 / (8 * (C₀ + ν * S))) := by
    rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv, mul_inv]
    ring
  have h3 : Real.exp (-(b * X ^ 2 / (4 * (C₀ + ν * S)))) =
      Real.exp (-(b * X ^ 2 / (8 * (C₀ + ν * S)))) *
        Real.exp (-(b * X ^ 2 / (8 * (C₀ + ν * S)))) := by
    rw [e4, ← Real.exp_add]
    congr 1
    ring
  rw [← h3]
  exact h2

/-- The `X`-power against the Gaussian: `X^{2m} e^{-bX²/(8Q)} ≤ (8Q/b)^m m!`. -/
theorem gauss_pow (b Q X : ℝ) (m : ℕ) (hb : 0 < b) (hQ : 0 < Q) (hX0 : 0 ≤ X) :
    X ^ (2 * m) * Real.exp (-(b * X ^ 2 / (8 * Q))) ≤
      (8 * Q / b) ^ m * ((m.factorial : ℕ) : ℝ) := by
  have hu0 : 0 ≤ b * X ^ 2 / (8 * Q) :=
    div_nonneg (mul_nonneg hb.le (sq_nonneg X)) (by linarith)
  have hX2 : X ^ 2 = (8 * Q / b) * (b * X ^ 2 / (8 * Q)) := by
    field_simp
  have key := UnforcedLeray.Gaussian.pow_mul_exp_neg_le_factorial m hu0
  calc X ^ (2 * m) * Real.exp (-(b * X ^ 2 / (8 * Q)))
      = ((8 * Q / b) * (b * X ^ 2 / (8 * Q))) ^ m * Real.exp (-(b * X ^ 2 / (8 * Q))) := by
        rw [pow_mul, ← hX2]
    _ = (8 * Q / b) ^ m * ((b * X ^ 2 / (8 * Q)) ^ m *
          Real.exp (-(b * X ^ 2 / (8 * Q)))) := by
        rw [mul_pow]
        ring
    _ ≤ (8 * Q / b) ^ m * ((m.factorial : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left key (pow_nonneg (div_nonneg (by linarith) hb.le) _)

/-- The Gaussian exponent against the heat-type exponent: `κ T ≤ bX²/(8Q)` with
`κ = bC_⊥²/(8(C₀+1))`, `T = ν⁻¹`, `Q = C₀+νS`. -/
theorem gauss_T (b C₀ Cp ν S X : ℝ) (hb : 0 < b) (hC₀ : 0 < C₀) (hν : 0 < ν) (hν1 : ν ≤ 1)
    (hS0 : 0 ≤ S) (hCp : 1 ≤ Cp) (hX : Cp * ((ν ^ 2)⁻¹ / ν + Real.sqrt S + 1) ≤ X) :
    b * Cp ^ 2 / (8 * (C₀ + 1)) * ν⁻¹ ≤ b * X ^ 2 / (8 * (C₀ + ν * S)) := by
  have hν0 : ν ≠ 0 := hν.ne'
  have hC1 : C₀ + 1 ≠ 0 := by linarith
  have hT1 : 1 ≤ ν⁻¹ := (one_le_inv₀ hν).2 hν1
  have hνT : ν * ν⁻¹ = 1 := mul_inv_cancel₀ hν0
  have hc : (ν ^ 2)⁻¹ / ν = ν⁻¹ ^ 3 := by ring
  rw [hc] at hX
  have hs : Real.sqrt S ^ 2 = S := Real.sq_sqrt hS0
  have hsn : 0 ≤ Real.sqrt S := Real.sqrt_nonneg S
  have hT0 : 0 ≤ ν⁻¹ := by linarith
  have hA : Cp ^ 2 * (ν⁻¹ ^ 6 + S) ≤ X ^ 2 := by
    have h1 : Cp * (ν⁻¹ ^ 3 + Real.sqrt S) ≤ X := by
      have e : Cp * (ν⁻¹ ^ 3 + Real.sqrt S + 1) = Cp * (ν⁻¹ ^ 3 + Real.sqrt S) + Cp := by ring
      linarith
    have h2 : (Cp * (ν⁻¹ ^ 3 + Real.sqrt S)) ^ 2 ≤ X ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg (by linarith) (by positivity)) h1 2
    have e2 : (Cp * (ν⁻¹ ^ 3 + Real.sqrt S)) ^ 2 =
        Cp ^ 2 * (ν⁻¹ ^ 6 + Real.sqrt S ^ 2) + Cp ^ 2 * (2 * ν⁻¹ ^ 3 * Real.sqrt S) := by
      ring
    have h4 : 0 ≤ Cp ^ 2 * (2 * ν⁻¹ ^ 3 * Real.sqrt S) :=
      mul_nonneg (sq_nonneg Cp) (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hT0 3)) hsn)
    rw [e2, hs] at h2
    linarith
  have hνT6 : 1 ≤ ν * ν⁻¹ ^ 6 := by
    have h5 : 1 ≤ ν⁻¹ ^ 5 := one_le_pow₀ hT1
    have e : ν * ν⁻¹ ^ 6 = ν⁻¹ ^ 5 := by
      calc ν * ν⁻¹ ^ 6 = (ν * ν⁻¹) * ν⁻¹ ^ 5 := by ring
        _ = ν⁻¹ ^ 5 := by rw [hνT, one_mul]
    rw [e]
    exact h5
  have hQ : C₀ + ν * S ≤ (C₀ + 1) * ν * (ν⁻¹ ^ 6 + S) := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ C₀ + 1) (sub_nonneg.2 hνT6),
      mul_nonneg hC₀.le (mul_nonneg hν.le hS0)]
  have hκ : b * Cp ^ 2 / (8 * (C₀ + 1)) * ν⁻¹ * (8 * (C₀ + ν * S)) ≤ b * X ^ 2 := by
    have hκ0 : 0 ≤ b * Cp ^ 2 / (8 * (C₀ + 1)) * ν⁻¹ :=
      mul_nonneg (div_nonneg (mul_nonneg hb.le (sq_nonneg Cp)) (by linarith)) hT0
    calc b * Cp ^ 2 / (8 * (C₀ + 1)) * ν⁻¹ * (8 * (C₀ + ν * S))
        ≤ b * Cp ^ 2 / (8 * (C₀ + 1)) * ν⁻¹ * (8 * ((C₀ + 1) * ν * (ν⁻¹ ^ 6 + S))) :=
          mul_le_mul_of_nonneg_left (by linarith) hκ0
      _ = b * (Cp ^ 2 * (ν⁻¹ ^ 6 + S)) := by
          field_simp
      _ ≤ b * X ^ 2 := mul_le_mul_of_nonneg_left hA hb.le
  have hQ0 : 0 < C₀ + ν * S := add_pos_of_pos_of_nonneg hC₀ (mul_nonneg hν.le hS0)
  rw [le_div_iff₀ (by linarith)]
  exact hκ

end T23AG

set_option maxHeartbeats 1000000 in
/-- **Absorption of the Gaussian exponential** (SP 2750, 2754), `TailAbsorbGauss`. -/
theorem tailAbsorbGauss : UnforcedLeray.Short.IIIa.TailAbsorbGauss := by
  intro b C₀ C' C K D N M m hb hC₀ hD hK
  have hb2 : (0 : ℝ) ≤ 8 * (C₀ + 1) / b := div_nonneg (by linarith) hb.le
  obtain ⟨G, hGdef⟩ : ∃ G : ℝ, G = 2 ^ M * 2 ^ m * (|C| * 6 ^ N) *
      (8 * (C₀ + 1) / b) ^ m * ((m.factorial : ℕ) : ℝ) := ⟨_, rfl⟩
  have hG0 : 0 ≤ G := by
    rw [hGdef]
    exact mul_nonneg (mul_nonneg (by positivity) (pow_nonneg hb2 _)) (Nat.cast_nonneg _)
  obtain ⟨νs, hνs, hsm⟩ := T23AG.final_small G (2 * N)
  obtain ⟨Cp, hCpdef⟩ : ∃ Cp : ℝ, Cp = max (2 * (|C'| + 2))
      (max 1 (8 * (C₀ + 1) * (((M : ℝ) + N + m) * K + D + 1) / b)) := ⟨_, rfl⟩
  have hCpA : 2 * (|C'| + 2) ≤ Cp := by rw [hCpdef]; exact le_max_left _ _
  have hCp1 : 1 ≤ Cp := by
    rw [hCpdef]; exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hCpC : 8 * (C₀ + 1) * (((M : ℝ) + N + m) * K + D + 1) / b ≤ Cp := by
    rw [hCpdef]; exact le_trans (le_max_right _ _) (le_max_right _ _)
  have hCpb : ((M : ℝ) + N + m) * K + D + 1 ≤ b * Cp ^ 2 / (8 * (C₀ + 1)) := by
    have h1 : 8 * (C₀ + 1) * (((M : ℝ) + N + m) * K + D + 1) ≤ b * Cp := by
      rw [div_le_iff₀ hb] at hCpC
      linarith
    have h2 : b * Cp ≤ b * Cp ^ 2 := by
      have : Cp ≤ Cp ^ 2 := by nlinarith
      exact mul_le_mul_of_nonneg_left this hb.le
    rw [le_div_iff₀ (by linarith : (0 : ℝ) < 8 * (C₀ + 1))]
    nlinarith
  refine ⟨Cp, min νs 1, lt_of_lt_of_le one_pos hCp1, lt_min hνs one_pos, ?_⟩
  intro ν hν hν1 S hS1 hSK η hη
  have hνs' : ν ≤ νs := hν1.trans (min_le_left _ _)
  have hνle1 : ν ≤ 1 := hν1.trans (min_le_right _ _)
  have hS0 : 0 ≤ S := by linarith
  have hE1 : 1 ≤ Real.exp (K / ν) := Real.one_le_exp (div_nonneg hK hν.le)
  have hX0 : 0 ≤ |η| := abs_nonneg η
  have hXC : Cp * ((ν ^ 2)⁻¹ / ν + Real.sqrt S + 1) ≤ |η| := hη.le
  have hT1 : 1 ≤ ν⁻¹ := (one_le_inv₀ hν).2 hνle1
  have hT3 : 1 ≤ ν⁻¹ ^ 3 := one_le_pow₀ hT1
  have hc : (ν ^ 2)⁻¹ / ν = ν⁻¹ ^ 3 := by ring
  rw [hc] at hXC
  have hXT : 2 * (|C'| + 2) * ν⁻¹ ≤ |η| := by
    have h1 : 2 * (|C'| + 2) * ν⁻¹ ≤ 2 * (|C'| + 2) * ν⁻¹ ^ 3 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have hT2 : 1 ≤ ν⁻¹ ^ 2 := one_le_pow₀ hT1
      have h6 := mul_le_mul_of_nonneg_left hT2 (inv_nonneg.2 hν.le)
      have h7 : ν⁻¹ ^ 3 = ν⁻¹ * ν⁻¹ ^ 2 := by ring
      rw [h7]
      linarith
    have h2 : 2 * (|C'| + 2) * ν⁻¹ ^ 3 ≤ Cp * ν⁻¹ ^ 3 :=
      mul_le_mul_of_nonneg_right hCpA (by positivity)
    have h3 : Cp * ν⁻¹ ^ 3 ≤ Cp * (ν⁻¹ ^ 3 + Real.sqrt S + 1) := by
      have : 0 ≤ Cp * (Real.sqrt S + 1) := mul_nonneg (by linarith) (by positivity)
      nlinarith
    linarith
  have hl : |η| / 2 ≤ |η| - C' / ν - 2 := by
    have e1 : C' / ν = C' * ν⁻¹ := div_eq_mul_inv _ _
    rw [e1]
    nlinarith [mul_nonneg (sub_nonneg.2 (le_abs_self C')) (inv_nonneg.2 hν.le)]
  have hX1 : 1 ≤ |η| := by
    have h1 : 1 ≤ Cp * ν⁻¹ ^ 3 := by
      have := mul_le_mul hCp1 hT3 zero_le_one (by linarith)
      linarith
    have h2 : Cp * ν⁻¹ ^ 3 ≤ Cp * (ν⁻¹ ^ 3 + Real.sqrt S + 1) := by
      have : 0 ≤ Cp * (Real.sqrt S + 1) := mul_nonneg (by linarith) (by positivity)
      have e : Cp * (ν⁻¹ ^ 3 + Real.sqrt S + 1) = Cp * ν⁻¹ ^ 3 + Cp * (Real.sqrt S + 1) := by
        ring
      rw [e]
      exact le_add_of_nonneg_right this
    linarith
  have hQpos : 0 < C₀ + ν * S := add_pos_of_pos_of_nonneg hC₀ (mul_nonneg hν.le hS0)
  have hη2 : η ^ 2 = |η| ^ 2 := (sq_abs η).symm
  have F1 : (1 + S) ^ M ≤ 2 ^ M * Real.exp (K / ν) ^ M := T23AG.onePS_pow M hS1 hSK hE1
  have F3 : (1 + η ^ 2) ^ m ≤ 2 ^ m * |η| ^ (2 * m) := by
    have hh : 1 + η ^ 2 ≤ 2 * |η| ^ 2 := by
      rw [← hη2]
      nlinarith
    calc (1 + η ^ 2) ^ m ≤ (2 * |η| ^ 2) ^ m := pow_le_pow_left₀ (by positivity) hh m
      _ = 2 ^ m * |η| ^ (2 * m) := by rw [mul_pow, ← pow_mul]
  have hP := T23AG.polyPS_bound C N hν hνle1 hK hS1 hSK
  have hQg := T23AG.gauss_split b C₀ C' |η| ν S hb hQpos hl hX0
  -- the `X`-power against the Gaussian, with `8Q/b ≤ R E`
  have hQE : C₀ + ν * S ≤ (C₀ + 1) * Real.exp (K / ν) := by
    nlinarith [mul_nonneg hC₀.le (sub_nonneg.2 hS1), mul_nonneg (sub_nonneg.2 hνle1) hS0,
      mul_le_mul_of_nonneg_left hSK (by linarith : (0 : ℝ) ≤ C₀ + 1)]
  have hR : 8 * (C₀ + ν * S) / b ≤ 8 * (C₀ + 1) / b * Real.exp (K / ν) := by
    have e : 8 * (C₀ + 1) / b * Real.exp (K / ν) = 8 * ((C₀ + 1) * Real.exp (K / ν)) / b := by
      ring
    rw [e]
    exact div_le_div_of_nonneg_right (by linarith) hb.le
  have hxp := T23AG.gauss_pow b (C₀ + ν * S) |η| m hb hQpos hX0
  have hxp' : |η| ^ (2 * m) * Real.exp (-(b * |η| ^ 2 / (8 * (C₀ + ν * S)))) ≤
      (8 * (C₀ + 1) / b * Real.exp (K / ν)) ^ m * ((m.factorial : ℕ) : ℝ) :=
    le_trans hxp (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (div_nonneg (by linarith) hb.le) hR m) (Nat.cast_nonneg _))
  have hTk := T23AG.gauss_T b C₀ Cp ν S |η| hb hC₀ hν hνle1 hS0 hCp1 (by rw [hc]; exact hXC)
  have hexpu : Real.exp (-(b * |η| ^ 2 / (8 * (C₀ + ν * S)))) ≤
      Real.exp (-(b * Cp ^ 2 / (8 * (C₀ + 1)) * ν⁻¹)) :=
    Real.exp_le_exp.2 (neg_le_neg hTk)
  have hEU0 : 0 ≤ Real.exp (-(b * |η| ^ 2 / (8 * (C₀ + ν * S)))) := Real.exp_nonneg _
  have hP'0 : 0 ≤ |C| * 6 ^ N * (ν⁻¹) ^ (2 * N) * Real.exp (K / ν) ^ N :=
    mul_nonneg (mul_nonneg (mul_nonneg (abs_nonneg C) (by positivity))
      (pow_nonneg (inv_nonneg.2 hν.le) _)) (by positivity)
  have hAB : 0 ≤ (1 + S) ^ M * (1 + η ^ 2) ^ m :=
    mul_nonneg (pow_nonneg (by linarith) M) (pow_nonneg (by positivity) m)
  have hmain : (1 + S) ^ M * (1 + η ^ 2) ^ m *
      (UnforcedLeray.Short.PartI.polyPS C N ν (ν ^ 2)⁻¹ S *
        Real.exp (-(b * (|η| - C' / ν - 2) ^ 2 / (C₀ + ν * S)))) ≤
      (2 ^ M * Real.exp (K / ν) ^ M) * (2 ^ m * |η| ^ (2 * m)) *
        ((|C| * 6 ^ N * (ν⁻¹) ^ (2 * N) * Real.exp (K / ν) ^ N) *
          (Real.exp (-(b * |η| ^ 2 / (8 * (C₀ + ν * S)))) *
            Real.exp (-(b * |η| ^ 2 / (8 * (C₀ + ν * S)))))) := by
    have hPQ : UnforcedLeray.Short.PartI.polyPS C N ν (ν ^ 2)⁻¹ S *
        Real.exp (-(b * (|η| - C' / ν - 2) ^ 2 / (C₀ + ν * S))) ≤
        (|C| * 6 ^ N * (ν⁻¹) ^ (2 * N) * Real.exp (K / ν) ^ N) *
          (Real.exp (-(b * |η| ^ 2 / (8 * (C₀ + ν * S)))) *
            Real.exp (-(b * |η| ^ 2 / (8 * (C₀ + ν * S))))) :=
      mul_le_mul hP hQg (Real.exp_nonneg _) hP'0
    calc (1 + S) ^ M * (1 + η ^ 2) ^ m *
          (UnforcedLeray.Short.PartI.polyPS C N ν (ν ^ 2)⁻¹ S *
            Real.exp (-(b * (|η| - C' / ν - 2) ^ 2 / (C₀ + ν * S))))
        = ((1 + S) ^ M * (1 + η ^ 2) ^ m) *
          (UnforcedLeray.Short.PartI.polyPS C N ν (ν ^ 2)⁻¹ S *
            Real.exp (-(b * (|η| - C' / ν - 2) ^ 2 / (C₀ + ν * S)))) := by ring
      _ ≤ ((1 + S) ^ M * (1 + η ^ 2) ^ m) *
          ((|C| * 6 ^ N * (ν⁻¹) ^ (2 * N) * Real.exp (K / ν) ^ N) *
            (Real.exp (-(b * |η| ^ 2 / (8 * (C₀ + ν * S)))) *
              Real.exp (-(b * |η| ^ 2 / (8 * (C₀ + ν * S)))))) :=
          mul_le_mul_of_nonneg_left hPQ hAB
      _ ≤ (2 ^ M * Real.exp (K / ν) ^ M) * (2 ^ m * |η| ^ (2 * m)) *
          ((|C| * 6 ^ N * (ν⁻¹) ^ (2 * N) * Real.exp (K / ν) ^ N) *
            (Real.exp (-(b * |η| ^ 2 / (8 * (C₀ + ν * S)))) *
              Real.exp (-(b * |η| ^ 2 / (8 * (C₀ + ν * S)))))) :=
          mul_le_mul_of_nonneg_right (mul_le_mul F1 F3 (pow_nonneg (by positivity) m)
            (by positivity)) (mul_nonneg hP'0 (mul_nonneg hEU0 hEU0))
  have hPref0 : 0 ≤ 2 ^ M * 2 ^ m * (|C| * 6 ^ N) * (ν⁻¹) ^ (2 * N) *
      (Real.exp (K / ν) ^ M * Real.exp (K / ν) ^ N) :=
    mul_nonneg (mul_nonneg (by positivity) (pow_nonneg (inv_nonneg.2 hν.le) _))
      (by positivity)
  have hRE0 : 0 ≤ (8 * (C₀ + 1) / b * Real.exp (K / ν)) ^ m * ((m.factorial : ℕ) : ℝ) :=
    mul_nonneg (pow_nonneg (mul_nonneg hb2 (Real.exp_nonneg _)) _) (Nat.cast_nonneg _)
  have hY : |η| ^ (2 * m) * Real.exp (-(b * |η| ^ 2 / (8 * (C₀ + ν * S)))) *
      Real.exp (-(b * |η| ^ 2 / (8 * (C₀ + ν * S)))) ≤
      (8 * (C₀ + 1) / b * Real.exp (K / ν)) ^ m * ((m.factorial : ℕ) : ℝ) *
        Real.exp (-(b * Cp ^ 2 / (8 * (C₀ + 1)) * ν⁻¹)) := by
    calc |η| ^ (2 * m) * Real.exp (-(b * |η| ^ 2 / (8 * (C₀ + ν * S)))) *
          Real.exp (-(b * |η| ^ 2 / (8 * (C₀ + ν * S))))
        ≤ (8 * (C₀ + 1) / b * Real.exp (K / ν)) ^ m * ((m.factorial : ℕ) : ℝ) *
            Real.exp (-(b * |η| ^ 2 / (8 * (C₀ + ν * S)))) :=
          mul_le_mul_of_nonneg_right hxp' hEU0
      _ ≤ (8 * (C₀ + 1) / b * Real.exp (K / ν)) ^ m * ((m.factorial : ℕ) : ℝ) *
            Real.exp (-(b * Cp ^ 2 / (8 * (C₀ + 1)) * ν⁻¹)) :=
          mul_le_mul_of_nonneg_left hexpu hRE0
  have hexp2 : Real.exp (K / ν) ^ M * Real.exp (K / ν) ^ N * Real.exp (K / ν) ^ m *
      Real.exp (-(b * Cp ^ 2 / (8 * (C₀ + 1)) * ν⁻¹)) ≤ Real.exp (-(D + 1) / ν) := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add,
      ← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.2
    have e2 : (M : ℝ) * (K / ν) + (N : ℝ) * (K / ν) + (m : ℝ) * (K / ν) +
        -(b * Cp ^ 2 / (8 * (C₀ + 1)) * ν⁻¹) =
        (((M : ℝ) + N + m) * K - b * Cp ^ 2 / (8 * (C₀ + 1))) / ν := by
      ring
    rw [e2]
    apply div_le_div_of_nonneg_right _ hν.le
    linarith [hCpb]
  have hrest : (2 ^ M * Real.exp (K / ν) ^ M) * (2 ^ m * |η| ^ (2 * m)) *
      ((|C| * 6 ^ N * (ν⁻¹) ^ (2 * N) * Real.exp (K / ν) ^ N) *
        (Real.exp (-(b * |η| ^ 2 / (8 * (C₀ + ν * S)))) *
          Real.exp (-(b * |η| ^ 2 / (8 * (C₀ + ν * S)))))) ≤
      G * (ν⁻¹) ^ (2 * N) * (Real.exp (K / ν) ^ M * Real.exp (K / ν) ^ N *
        Real.exp (K / ν) ^ m * Real.exp (-(b * Cp ^ 2 / (8 * (C₀ + 1)) * ν⁻¹))) := by
    calc (2 ^ M * Real.exp (K / ν) ^ M) * (2 ^ m * |η| ^ (2 * m)) *
          ((|C| * 6 ^ N * (ν⁻¹) ^ (2 * N) * Real.exp (K / ν) ^ N) *
            (Real.exp (-(b * |η| ^ 2 / (8 * (C₀ + ν * S)))) *
              Real.exp (-(b * |η| ^ 2 / (8 * (C₀ + ν * S))))))
        = (2 ^ M * 2 ^ m * (|C| * 6 ^ N) * (ν⁻¹) ^ (2 * N) *
            (Real.exp (K / ν) ^ M * Real.exp (K / ν) ^ N)) *
          (|η| ^ (2 * m) * Real.exp (-(b * |η| ^ 2 / (8 * (C₀ + ν * S)))) *
            Real.exp (-(b * |η| ^ 2 / (8 * (C₀ + ν * S))))) := by ring
      _ ≤ (2 ^ M * 2 ^ m * (|C| * 6 ^ N) * (ν⁻¹) ^ (2 * N) *
            (Real.exp (K / ν) ^ M * Real.exp (K / ν) ^ N)) *
          ((8 * (C₀ + 1) / b * Real.exp (K / ν)) ^ m * ((m.factorial : ℕ) : ℝ) *
            Real.exp (-(b * Cp ^ 2 / (8 * (C₀ + 1)) * ν⁻¹))) :=
          mul_le_mul_of_nonneg_left hY hPref0
      _ = G * (ν⁻¹) ^ (2 * N) * (Real.exp (K / ν) ^ M * Real.exp (K / ν) ^ N *
            Real.exp (K / ν) ^ m * Real.exp (-(b * Cp ^ 2 / (8 * (C₀ + 1)) * ν⁻¹))) := by
          rw [hGdef, mul_pow]
          ring
  have hfin : G * (ν⁻¹) ^ (2 * N) * (Real.exp (K / ν) ^ M * Real.exp (K / ν) ^ N *
        Real.exp (K / ν) ^ m * Real.exp (-(b * Cp ^ 2 / (8 * (C₀ + 1)) * ν⁻¹))) ≤
      G * (ν⁻¹) ^ (2 * N) * Real.exp (-(D + 1) / ν) :=
    mul_le_mul_of_nonneg_left hexp2 (mul_nonneg hG0 (pow_nonneg (inv_nonneg.2 hν.le) _))
  have hfinal : G * (ν⁻¹) ^ (2 * N) * Real.exp (-(D + 1) / ν) ≤ Real.exp (-D / ν) / 4 := by
    have hs : Real.exp (-(D + 1) / ν) = Real.exp (-D / ν) * Real.exp (-1 / ν) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hs]
    have hh := hsm ν hν hνs'
    have hE := Real.exp_pos (-D / ν)
    calc G * (ν⁻¹) ^ (2 * N) * (Real.exp (-D / ν) * Real.exp (-1 / ν))
        = Real.exp (-D / ν) * (G * (ν⁻¹ ^ (2 * N) * Real.exp (-1 / ν))) := by ring
      _ ≤ Real.exp (-D / ν) * (1 / 4) := mul_le_mul_of_nonneg_left hh hE.le
      _ = Real.exp (-D / ν) / 4 := by ring
  exact le_trans hmain (le_trans hrest (le_trans hfin hfinal))

end UnforcedLeray.Short.IIIa
