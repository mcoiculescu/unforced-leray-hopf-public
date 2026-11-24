import UnforcedLeray.Short.PartI.Sub.T08Statement

/-!
# `PartI:T08` leaf 8: the weights in the transport sum (pure real analysis)

Source: `the November 2 reference manuscript`, lines 344 and 349.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartI

/-- Key estimate: `(δa)^j a^{-(3+i)/2} √J_{j+1-i} √J_j ≤ a^{-2} E` for `1 ≤ i ≤ j+1`, `j ≤ N`,
where `E ≥ (δa)^m J_m` for all `m ≤ N`. Proved by squaring: the square of the left side is
`(δa)^{2j} a^{-(3+i)} J_l J_j`, and `(δa)^{2j} a⁴ a^{-(3+i)} ≤ (δa)^l (δa)^j` since `j - l = i - 1`. -/
theorem tw_key (δ a : ℝ) (J : ℕ → ℝ) (E : ℝ) (N j i : ℕ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (ha : 1 ≤ a) (hJ : ∀ j, 0 ≤ J j)
    (hE : ∀ m ≤ N, (δ * a) ^ m * J m ≤ E)
    (hi1 : 1 ≤ i) (hij : i ≤ j + 1) (hj : j ≤ N) :
    (δ * a) ^ j * (a ^ (-(3 + (i : ℝ)) / 2)) * Real.sqrt (J (j + 1 - i)) * Real.sqrt (J j)
      ≤ E / a ^ 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
  obtain ⟨l, rfl⟩ : ∃ l, j = l + m := ⟨j - m, by omega⟩
  have hl : l + m + 1 - (m + 1) = l := by omega
  rw [hl]
  have ha0 : 0 < a := by linarith
  have hδa : 0 ≤ δ * a := mul_nonneg hδ.le ha0.le
  have hx : (δ * a) ^ l * J l ≤ E := hE l (by omega)
  have hy : (δ * a) ^ (l + m) * J (l + m) ≤ E := hE (l + m) hj
  have hE0 : 0 ≤ E := le_trans (mul_nonneg (pow_nonneg hδa l) (hJ l)) hx
  -- the power of `a`: `g² a^(m+4) = 1` for `g = a^{-(3+(m+1))/2}`
  have h1 : (a ^ (-(3 + ((m + 1 : ℕ) : ℝ)) / 2)) ^ 2 = a ^ (-(3 + ((m + 1 : ℕ) : ℝ))) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ha0.le]
    congr 1
    push_cast
    ring
  have h2 : a ^ (-(3 + ((m + 1 : ℕ) : ℝ))) * a ^ (m + 4) = 1 := by
    rw [Real.rpow_neg ha0.le, show (3 + ((m + 1 : ℕ) : ℝ)) = ((m + 4 : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_natCast]
    exact inv_mul_cancel₀ (pow_ne_zero _ ha0.ne')
  have hg2 : (a ^ (-(3 + ((m + 1 : ℕ) : ℝ)) / 2)) ^ 2 * a ^ (m + 4) = 1 := by
    rw [h1]
    exact h2
  have hg0 : 0 ≤ a ^ (-(3 + ((m + 1 : ℕ) : ℝ)) / 2) := Real.rpow_nonneg ha0.le _
  -- squared inequality
  have hk : ((δ * a) ^ (l + m)) ^ 2 * (a ^ (-(3 + ((m + 1 : ℕ) : ℝ)) / 2)) ^ 2 * a ^ 4 ≤
      (δ * a) ^ l * (δ * a) ^ (l + m) := by
    have hpos : 0 < a ^ m := pow_pos ha0 m
    refine le_of_mul_le_mul_right ?_ hpos
    have hdm : (δ * a) ^ m ≤ a ^ m := by
      have : δ * a ≤ a := by nlinarith
      exact pow_le_pow_left₀ hδa this m
    calc ((δ * a) ^ (l + m)) ^ 2 * (a ^ (-(3 + ((m + 1 : ℕ) : ℝ)) / 2)) ^ 2 * a ^ 4 * a ^ m
        = ((δ * a) ^ (l + m)) ^ 2 * ((a ^ (-(3 + ((m + 1 : ℕ) : ℝ)) / 2)) ^ 2 * a ^ (m + 4)) := by
          ring
      _ = ((δ * a) ^ (l + m)) ^ 2 := by rw [hg2, mul_one]
      _ = (δ * a) ^ l * (δ * a) ^ (l + m) * (δ * a) ^ m := by
          rw [sq, pow_add (δ * a) l m]
          ring
      _ ≤ (δ * a) ^ l * (δ * a) ^ (l + m) * a ^ m :=
          mul_le_mul_of_nonneg_left hdm (mul_nonneg (pow_nonneg hδa _) (pow_nonneg hδa _))
  -- the square of the left side
  have hP2 : ((δ * a) ^ (l + m) * (a ^ (-(3 + ((m + 1 : ℕ) : ℝ)) / 2)) * Real.sqrt (J l) *
      Real.sqrt (J (l + m))) ^ 2 * a ^ 4 ≤ E * E := by
    have hsq : ((δ * a) ^ (l + m) * (a ^ (-(3 + ((m + 1 : ℕ) : ℝ)) / 2)) * Real.sqrt (J l) *
        Real.sqrt (J (l + m))) ^ 2 =
        ((δ * a) ^ (l + m)) ^ 2 * (a ^ (-(3 + ((m + 1 : ℕ) : ℝ)) / 2)) ^ 2 *
          (Real.sqrt (J l)) ^ 2 * (Real.sqrt (J (l + m))) ^ 2 := by ring
    rw [hsq, Real.sq_sqrt (hJ l), Real.sq_sqrt (hJ (l + m))]
    calc ((δ * a) ^ (l + m)) ^ 2 * (a ^ (-(3 + ((m + 1 : ℕ) : ℝ)) / 2)) ^ 2 * J l * J (l + m) * a ^ 4
        = (((δ * a) ^ (l + m)) ^ 2 * (a ^ (-(3 + ((m + 1 : ℕ) : ℝ)) / 2)) ^ 2 * a ^ 4) *
            (J l * J (l + m)) := by ring
      _ ≤ ((δ * a) ^ l * (δ * a) ^ (l + m)) * (J l * J (l + m)) :=
          mul_le_mul_of_nonneg_right hk (mul_nonneg (hJ _) (hJ _))
      _ = ((δ * a) ^ l * J l) * ((δ * a) ^ (l + m) * J (l + m)) := by ring
      _ ≤ E * E := mul_le_mul hx hy (mul_nonneg (pow_nonneg hδa _) (hJ _)) hE0
  -- conclude from the squares
  set P := (δ * a) ^ (l + m) * (a ^ (-(3 + ((m + 1 : ℕ) : ℝ)) / 2)) * Real.sqrt (J l) *
      Real.sqrt (J (l + m)) with hPdef
  have hP0 : 0 ≤ P := by
    rw [hPdef]
    exact mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hδa _) hg0) (Real.sqrt_nonneg _))
      (Real.sqrt_nonneg _)
  set T := E / a ^ 2 with hTdef
  have hT0 : 0 ≤ T := div_nonneg hE0 (by positivity)
  have hET : E = T * a ^ 2 := by
    rw [hTdef]
    field_simp
  have ha4 : 0 < a ^ 4 := pow_pos ha0 4
  have hPT2 : P ^ 2 ≤ T ^ 2 := by
    refine le_of_mul_le_mul_right ?_ ha4
    calc P ^ 2 * a ^ 4 ≤ E * E := hP2
      _ = T ^ 2 * a ^ 4 := by rw [hET]; ring
  nlinarith [hPT2, hP0, hT0]

/-- Leaf 8: the weights in the transport sum. -/
theorem transportWeightSum_proof : UnforcedLeray.Short.PartI.TransportWeightSum := by
  intro N A Cv hA hCv
  have hS : 0 ≤ ∑ i ∈ Finset.Icc 1 (N + 1), Cv i := Finset.sum_nonneg fun i _ => hCv i
  refine ⟨∑ j ∈ Finset.range (N + 1), A j * (1 + ∑ i ∈ Finset.Icc 1 (N + 1), Cv i),
    Finset.sum_nonneg fun j _ => mul_nonneg (hA j) (by linarith), ?_⟩
  intro δ a J T hδ hδ1 ha hJ hT
  have ha0 : 0 < a := by linarith
  have hδa : 0 ≤ δ * a := mul_nonneg hδ.le ha0.le
  set E := ∑ j ∈ Finset.range (N + 1), (δ * a) ^ j * J j with hEdef
  have hE : ∀ j ≤ N, (δ * a) ^ j * J j ≤ E := by
    intro j hj
    exact Finset.single_le_sum (f := fun j => (δ * a) ^ j * J j)
      (fun k _ => mul_nonneg (pow_nonneg hδa k) (hJ k)) (Finset.mem_range.2 (by omega))
  have hE0 : 0 ≤ E := Finset.sum_nonneg fun j _ => mul_nonneg (pow_nonneg hδa j) (hJ j)
  have hterm : ∀ j ∈ Finset.range (N + 1),
      (δ * a) ^ j * |T j| ≤ A j * (1 + ∑ i ∈ Finset.Icc 1 (N + 1), Cv i) * (E / a ^ 2) := by
    intro j hjmem
    have hj : j ≤ N := by
      have := Finset.mem_range.1 hjmem
      omega
    have hTj := hT j hj
    have h1 : (δ * a) ^ j * ((a ^ 2)⁻¹ * J j) ≤ E / a ^ 2 := by
      calc (δ * a) ^ j * ((a ^ 2)⁻¹ * J j) = (a ^ 2)⁻¹ * ((δ * a) ^ j * J j) := by ring
        _ ≤ (a ^ 2)⁻¹ * E := mul_le_mul_of_nonneg_left (hE j hj) (by positivity)
        _ = E / a ^ 2 := by ring
    have h2 : (δ * a) ^ j * (∑ i ∈ Finset.Icc 1 (j + 1), Cv i * a ^ (-(3 + (i : ℝ)) / 2) *
        Real.sqrt (J (j + 1 - i)) * Real.sqrt (J j)) ≤
        (∑ i ∈ Finset.Icc 1 (N + 1), Cv i) * (E / a ^ 2) := by
      rw [Finset.mul_sum]
      calc ∑ i ∈ Finset.Icc 1 (j + 1), (δ * a) ^ j * (Cv i * a ^ (-(3 + (i : ℝ)) / 2) *
            Real.sqrt (J (j + 1 - i)) * Real.sqrt (J j))
          ≤ ∑ i ∈ Finset.Icc 1 (j + 1), Cv i * (E / a ^ 2) := by
            apply Finset.sum_le_sum
            intro i hi
            rw [Finset.mem_Icc] at hi
            have hk := tw_key δ a J E N j i hδ hδ1 ha hJ hE hi.1 hi.2 hj
            calc (δ * a) ^ j * (Cv i * a ^ (-(3 + (i : ℝ)) / 2) * Real.sqrt (J (j + 1 - i)) *
                  Real.sqrt (J j))
                = Cv i * ((δ * a) ^ j * (a ^ (-(3 + (i : ℝ)) / 2)) * Real.sqrt (J (j + 1 - i)) *
                  Real.sqrt (J j)) := by ring
              _ ≤ Cv i * (E / a ^ 2) := mul_le_mul_of_nonneg_left hk (hCv i)
        _ ≤ ∑ i ∈ Finset.Icc 1 (N + 1), Cv i * (E / a ^ 2) := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · exact Finset.Icc_subset_Icc le_rfl (by omega)
            · intro i _ _
              exact mul_nonneg (hCv i) (div_nonneg hE0 (by positivity))
        _ = (∑ i ∈ Finset.Icc 1 (N + 1), Cv i) * (E / a ^ 2) := by rw [Finset.sum_mul]
    calc (δ * a) ^ j * |T j| ≤ (δ * a) ^ j * (A j * ((a ^ 2)⁻¹ * J j +
          ∑ i ∈ Finset.Icc 1 (j + 1), Cv i * a ^ (-(3 + (i : ℝ)) / 2) *
            Real.sqrt (J (j + 1 - i)) * Real.sqrt (J j))) :=
          mul_le_mul_of_nonneg_left hTj (pow_nonneg hδa j)
      _ = A j * ((δ * a) ^ j * ((a ^ 2)⁻¹ * J j) + (δ * a) ^ j * (∑ i ∈ Finset.Icc 1 (j + 1),
            Cv i * a ^ (-(3 + (i : ℝ)) / 2) * Real.sqrt (J (j + 1 - i)) * Real.sqrt (J j))) := by
          ring
      _ ≤ A j * (E / a ^ 2 + (∑ i ∈ Finset.Icc 1 (N + 1), Cv i) * (E / a ^ 2)) :=
          mul_le_mul_of_nonneg_left (add_le_add h1 h2) (hA j)
      _ = A j * (1 + ∑ i ∈ Finset.Icc 1 (N + 1), Cv i) * (E / a ^ 2) := by ring
  have hsum := Finset.sum_le_sum hterm
  rw [← Finset.sum_mul] at hsum
  refine le_trans hsum (le_of_eq ?_)
  ring

end UnforcedLeray.Short.PartI
