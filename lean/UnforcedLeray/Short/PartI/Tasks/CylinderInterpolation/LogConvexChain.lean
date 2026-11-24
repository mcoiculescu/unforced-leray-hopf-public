import UnforcedLeray.Short.PartI.Sub.T07

/-!
# Part I, task `PartI:T07`: the log-convex chain (pure real analysis)

Target: `logConvexChain_proof : UnforcedLeray.Short.PartI.LogConvexChain`.

Source of record: `the November 2 reference manuscript`, lines 355-357 (the
period-independent Gagliardo-Nirenberg chain `‖D^l f‖ ≤ C ‖f‖_∞^{1-l/m} ‖D^m f‖^{l/m}`, whose
real-analysis core is the log-convexity of the sequence `a_j`).

Proof outline. Zeros propagate along the chain: if some interior `a_j` vanishes (`1 ≤ j < m`),
then every interior `a_i` vanishes, so the claim is `0 ≤ RHS` there; if `a_0` or `a_m` vanishes
while some interior term is positive, the same argument gives a contradiction. Otherwise all
`a_j > 0` for `0 ≤ j ≤ m`, and `d_j = log a_j + j² (log K)/2` has nonnegative second differences
(`d_i + d_{i+2} - 2 d_{i+1} = log a_i + log a_{i+2} - 2 log a_{i+1} + log K ≥ 0`). A sequence with
nonnegative second differences lies below its chord, `m d_l ≤ (m-l) d_0 + l d_m`, and exponentiating
gives the claim.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.PartI

/-! ### Discrete convexity: the chord bound -/

/-- Right slopes dominate the left slope: `(n+1) (d_{l+1} - d_l) ≤ d_{l+n+1} - d_l`. -/
lemma lcc_right (m : ℕ) (d : ℕ → ℝ)
    (hd : ∀ i, i + 1 + 1 ≤ m → 0 ≤ d i + d (i + 1 + 1) - 2 * d (i + 1)) :
    ∀ n l, l + n + 1 ≤ m → ((n : ℝ) + 1) * (d (l + 1) - d l) ≤ d (l + n + 1) - d l := by
  intro n
  induction n with
  | zero => intro l _; simp
  | succ n ih =>
    intro l hl
    have h1 := ih (l + 1) (by omega)
    have h2 : 0 ≤ d l + d (l + 1 + 1) - 2 * d (l + 1) := hd l (by omega)
    have h3 : 0 ≤ ((n : ℝ) + 1) * (d (l + 1 + 1) - d (l + 1) - (d (l + 1) - d l)) :=
      mul_nonneg (by positivity) (by linarith)
    have e : l + (n + 1) + 1 = l + 1 + n + 1 := by omega
    rw [e]
    push_cast
    linarith

/-- Left slope bound: `d_{p+1} - d_0 ≤ (p+1) (d_{p+1} - d_p)`. -/
lemma lcc_left (m : ℕ) (d : ℕ → ℝ)
    (hd : ∀ i, i + 1 + 1 ≤ m → 0 ≤ d i + d (i + 1 + 1) - 2 * d (i + 1)) :
    ∀ p, p + 1 ≤ m → d (p + 1) - d 0 ≤ ((p : ℝ) + 1) * (d (p + 1) - d p) := by
  intro p
  induction p with
  | zero => intro _; simp
  | succ p ih =>
    intro hp
    have h1 := ih (by omega)
    have h2 : 0 ≤ d p + d (p + 1 + 1) - 2 * d (p + 1) := hd p (by omega)
    have h3 : 0 ≤ ((p : ℝ) + 1) * (d (p + 1 + 1) - d (p + 1) - (d (p + 1) - d p)) :=
      mul_nonneg (by positivity) (by linarith)
    push_cast
    linarith

/-- Chord bound for discretely convex sequences: `m d_l ≤ (m-l) d_0 + l d_m` for `l ≤ m`. -/
lemma lcc_chord (m : ℕ) (d : ℕ → ℝ)
    (hd : ∀ i, i + 1 + 1 ≤ m → 0 ≤ d i + d (i + 1 + 1) - 2 * d (i + 1)) :
    ∀ l, l ≤ m → (m : ℝ) * d l ≤ ((m : ℝ) - l) * d 0 + (l : ℝ) * d m := by
  intro l hl
  rcases Nat.eq_zero_or_pos l with h0 | hl0
  · subst h0; simp
  rcases hl.eq_or_lt with hm | hlm
  · subst hm; simp
  obtain ⟨p, rfl⟩ : ∃ p, l = p + 1 := ⟨l - 1, by omega⟩
  obtain ⟨n, hn⟩ : ∃ n, m = p + 1 + n + 1 := ⟨m - (p + 1) - 1, by omega⟩
  have hC : d (p + 1) - d p ≤ d (p + 1 + 1) - d (p + 1) := by
    have h := hd p (by omega)
    linarith
  have hA : d (p + 1) - d 0 ≤ ((p : ℝ) + 1) * (d (p + 1 + 1) - d (p + 1)) :=
    le_trans (lcc_left m d hd p (by omega)) (mul_le_mul_of_nonneg_left hC (by positivity))
  have hB : ((n : ℝ) + 1) * (d (p + 1 + 1) - d (p + 1)) ≤ d (p + 1 + n + 1) - d (p + 1) :=
    lcc_right m d hd n (p + 1) (by omega)
  have h3 : ((p : ℝ) + 1) * (((n : ℝ) + 1) * (d (p + 1 + 1) - d (p + 1)))
      ≤ ((p : ℝ) + 1) * (d (p + 1 + n + 1) - d (p + 1)) :=
    mul_le_mul_of_nonneg_left hB (by positivity)
  have h4 : ((n : ℝ) + 1) * (d (p + 1) - d 0)
      ≤ ((n : ℝ) + 1) * (((p : ℝ) + 1) * (d (p + 1 + 1) - d (p + 1))) :=
    mul_le_mul_of_nonneg_left hA (by positivity)
  rw [hn]
  push_cast
  linarith

/-! ### Zero propagation along the chain -/

/-- A vanishing neighbour forces a vanishing interior term. -/
lemma lcc_step_zero (m : ℕ) (K : ℝ) (a : ℕ → ℝ)
    (hconv : ∀ j, 1 ≤ j → j < m → a j ^ 2 ≤ K * (a (j - 1) * a (j + 1)))
    (i : ℕ) (h1 : 1 ≤ i) (h2 : i < m) (hz : a (i - 1) = 0 ∨ a (i + 1) = 0) :
    a i = 0 := by
  have hc := hconv i h1 h2
  have hprod : a (i - 1) * a (i + 1) = 0 := by
    rcases hz with h | h <;> simp [h]
  rw [hprod, mul_zero] at hc
  have hsq : a i ^ 2 = 0 := le_antisymm hc (sq_nonneg _)
  exact (pow_eq_zero_iff two_ne_zero).mp hsq

/-- Upward propagation of a zero. -/
lemma lcc_zero_up (m : ℕ) (K : ℝ) (a : ℕ → ℝ)
    (hconv : ∀ j, 1 ≤ j → j < m → a j ^ 2 ≤ K * (a (j - 1) * a (j + 1)))
    (j : ℕ) (hj1 : 1 ≤ j) (hz : a j = 0) : ∀ k, j + k < m → a (j + k) = 0 := by
  intro k
  induction k with
  | zero => intro _; simpa using hz
  | succ k ih =>
    intro hk
    have h0 : a (j + k) = 0 := ih (by omega)
    have h : a (j + k + 1) = 0 :=
      lcc_step_zero m K a hconv (j + k + 1) (by omega) (by omega)
        (Or.inl (by simpa using h0))
    rw [← Nat.add_assoc]
    exact h

/-- Downward propagation of a zero. -/
lemma lcc_zero_down (m : ℕ) (K : ℝ) (a : ℕ → ℝ)
    (hconv : ∀ j, 1 ≤ j → j < m → a j ^ 2 ≤ K * (a (j - 1) * a (j + 1)))
    (j : ℕ) (hjm : j < m) (hz : a j = 0) : ∀ g, g + 1 ≤ j → a (j - g) = 0 := by
  intro g
  induction g with
  | zero => intro _; simpa using hz
  | succ g ih =>
    intro hg
    have h0 : a (j - g) = 0 := ih (by omega)
    have h1 : a (j - (g + 1) + 1) = 0 := by
      rw [show j - (g + 1) + 1 = j - g by omega]
      exact h0
    exact lcc_step_zero m K a hconv (j - (g + 1)) (by omega) (by omega) (Or.inr h1)

/-- A zero at one interior index forces zeros at all interior indices. -/
lemma lcc_zero_all (m : ℕ) (K : ℝ) (a : ℕ → ℝ)
    (hconv : ∀ j, 1 ≤ j → j < m → a j ^ 2 ≤ K * (a (j - 1) * a (j + 1)))
    (j : ℕ) (hj1 : 1 ≤ j) (hjm : j < m) (hz : a j = 0)
    (i : ℕ) (hi1 : 1 ≤ i) (him : i < m) : a i = 0 := by
  rcases le_total j i with hji | hij
  · have h := lcc_zero_up m K a hconv j hj1 hz (i - j) (by omega)
    rwa [show j + (i - j) = i by omega] at h
  · have h := lcc_zero_down m K a hconv j hjm hz (j - i) (by omega)
    rwa [show j - (j - i) = i by omega] at h

/-! ### The target -/

theorem logConvexChain_proof : UnforcedLeray.Short.PartI.LogConvexChain := by
  unfold UnforcedLeray.Short.PartI.LogConvexChain
  intro m K a hK ha hconv l hl
  have hK0 : (0 : ℝ) < K := by linarith
  have hR : 0 ≤ K ^ ((l : ℝ) * ((m : ℝ) - l) / 2) * a 0 ^ (1 - (l : ℝ) / m)
      * a m ^ ((l : ℝ) / m) :=
    mul_nonneg (mul_nonneg (Real.rpow_nonneg hK0.le _) (Real.rpow_nonneg (ha 0) _))
      (Real.rpow_nonneg (ha m) _)
  rcases Nat.eq_zero_or_pos l with h0 | hl0
  · subst h0
    simp
  rcases hl.eq_or_lt with hm | hlm
  · have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    rw [hm, div_self hm0]
    simp
  have hlt : l < m := hlm
  by_cases hal0 : a l = 0
  · rw [hal0]
    exact hR
  have hal : 0 < a l := lt_of_le_of_ne (ha l) (Ne.symm hal0)
  -- every interior term is positive
  have hint : ∀ j, 1 ≤ j → j < m → 0 < a j := by
    intro j hj1 hjm
    rcases (ha j).lt_or_eq with h | h
    · exact h
    · exact absurd (lcc_zero_all m K a hconv j hj1 hjm h.symm l (by omega) hlt) hal0
  have ha0 : 0 < a 0 := by
    rcases (ha 0).lt_or_eq with h | h
    · exact h
    · exfalso
      have h1 : a 1 = 0 :=
        lcc_step_zero m K a hconv 1 le_rfl (by omega) (Or.inl (by simpa using h.symm))
      linarith [hint 1 le_rfl (by omega)]
  have ham : 0 < a m := by
    rcases (ha m).lt_or_eq with h | h
    · exact h
    · exfalso
      have h1 : a (m - 1) = 0 :=
        lcc_step_zero m K a hconv (m - 1) (by omega) (by omega)
          (Or.inr (by rw [show m - 1 + 1 = m by omega]; exact h.symm))
      linarith [hint (m - 1) (by omega) (by omega)]
  have hpos : ∀ j, j ≤ m → 0 < a j := by
    intro j hj
    rcases Nat.eq_zero_or_pos j with hj0 | hj0
    · rw [hj0]; exact ha0
    rcases hj.eq_or_lt with hjm | hjm
    · rw [hjm]; exact ham
    · exact hint j hj0 hjm
  -- logarithmic second differences
  obtain ⟨D, hD⟩ : ∃ D : ℕ → ℝ, ∀ j, D j = Real.log (a j) + (j : ℝ) ^ 2 * Real.log K / 2 :=
    ⟨fun j => Real.log (a j) + (j : ℝ) ^ 2 * Real.log K / 2, fun j => rfl⟩
  have hd : ∀ i, i + 1 + 1 ≤ m → 0 ≤ D i + D (i + 1 + 1) - 2 * D (i + 1) := by
    intro i hi
    have hc : a (i + 1) ^ 2 ≤ K * (a i * a (i + 1 + 1)) := by
      have h := hconv (i + 1) (by omega) (by omega)
      rwa [Nat.add_sub_cancel] at h
    have hp0 : 0 < a i := hpos i (by omega)
    have hp2 : 0 < a (i + 1 + 1) := hpos (i + 1 + 1) hi
    have hlog : Real.log (a (i + 1) ^ 2) ≤ Real.log (K * (a i * a (i + 1 + 1))) :=
      Real.log_le_log (pow_pos (hpos (i + 1) (by omega)) 2) hc
    rw [Real.log_pow, Real.log_mul hK0.ne' (mul_pos hp0 hp2).ne',
      Real.log_mul hp0.ne' hp2.ne'] at hlog
    rw [hD, hD, hD]
    push_cast at hlog ⊢
    linarith
  have hchord := lcc_chord m D hd l hl
  simp only [hD, Nat.cast_zero] at hchord
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr (by omega)
  have hkey : Real.log (a l) ≤ Real.log K * ((l : ℝ) * ((m : ℝ) - l) / 2)
      + Real.log (a 0) * (1 - (l : ℝ) / m) + Real.log (a m) * ((l : ℝ) / m) := by
    have eR : Real.log K * ((l : ℝ) * ((m : ℝ) - l) / 2)
        + Real.log (a 0) * (1 - (l : ℝ) / m) + Real.log (a m) * ((l : ℝ) / m)
        = (Real.log K * ((l : ℝ) * ((m : ℝ) - l) / 2) * m + ((m : ℝ) - l) * Real.log (a 0)
            + (l : ℝ) * Real.log (a m)) / m := by
      field_simp
    rw [eR, le_div_iff₀ hmR]
    linarith
  calc a l = Real.exp (Real.log (a l)) := (Real.exp_log hal).symm
    _ ≤ Real.exp (Real.log K * ((l : ℝ) * ((m : ℝ) - l) / 2)
        + Real.log (a 0) * (1 - (l : ℝ) / m) + Real.log (a m) * ((l : ℝ) / m)) :=
          Real.exp_le_exp.mpr hkey
    _ = K ^ ((l : ℝ) * ((m : ℝ) - l) / 2) * a 0 ^ (1 - (l : ℝ) / m)
        * a m ^ ((l : ℝ) / m) := by
          rw [Real.exp_add, Real.exp_add, Real.rpow_def_of_pos hK0,
            Real.rpow_def_of_pos (hpos 0 (Nat.zero_le m)),
            Real.rpow_def_of_pos (hpos m le_rfl)]

end UnforcedLeray.Short.PartI
