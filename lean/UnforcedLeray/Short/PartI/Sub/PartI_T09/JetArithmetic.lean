import UnforcedLeray.Short.PartI.Sub.PartI_T09

/-!
# Part I, task `PartI:T09/8`: `JetArithmetic`

Source of record: `the November 2 reference manuscript`, lines 349-355. Pure real
analysis. With `δ = 1/(4N)`, `(δa)^i J_i ≤ E ≤ K ν⁻² a⁻⁴ e^{-b'c²/a}` gives
`√J_i ≤ C ν⁻¹ a^{-(2+i/2)} e^{-(b'/2)c²/a}` (part 1, `C = 1 + K(4N)^N`), and the interpolation
expression is at most `2C ν⁻¹ a^{-(5+j)/2} e^{-(b'/2)c²/a}` (part 2: two products of part-1 bounds,
and `c^{-1/2} a^{1/4} ≤ 1` from `a ≤ c²`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartI

/-- **Leaf 6a: exponent arithmetic of the interpolation** (`JetArithmetic`, lines 349-355). -/
theorem jetArithmetic_proof : JetArithmetic := by
  intro N j K b' hN hjN hK hb
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = 1 + K * (4 * (N : ℝ)) ^ N := ⟨_, rfl⟩
  have hN3 : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have h4pos : (0 : ℝ) < 4 * (N : ℝ) := by linarith
  have h4N : (1 : ℝ) ≤ 4 * (N : ℝ) := by linarith
  have hKN : 0 ≤ K * (4 * (N : ℝ)) ^ N := mul_nonneg hK.le (pow_nonneg h4pos.le N)
  have hC1 : 1 ≤ C := by rw [hC]; linarith
  have hC0 : 0 ≤ C := by linarith
  have hdpos : (0 : ℝ) < 1 / (4 * (N : ℝ)) := one_div_pos.2 h4pos
  refine ⟨2 * C, by linarith, ?_⟩
  intro ν c a E hν hc ha hac J hJ hE hJE
  have ha0 : 0 < a := by linarith
  have hc0 : 0 < c := by linarith
  have hν2 : 0 < ν ^ 2 := pow_pos hν 2
  obtain ⟨G, hGdef⟩ : ∃ G : ℝ, G = Real.exp (-(b' / 2 * c ^ 2 / a)) := ⟨_, rfl⟩
  have hGpos : 0 < G := by rw [hGdef]; exact Real.exp_pos _
  have hG2 : G ^ 2 = Real.exp (-(b' * c ^ 2 / a)) := by
    rw [hGdef, sq, ← Real.exp_add]; congr 1; ring
  have hG' : 0 < Real.exp (-(b' * c ^ 2 / a)) := Real.exp_pos _
  have hpos4 : 0 < ν ^ 2 * a ^ 4 := mul_pos hν2 (pow_pos ha0 4)
  have hEG : E * (ν ^ 2 * a ^ 4) ≤ K * Real.exp (-(b' * c ^ 2 / a)) := by
    calc E * (ν ^ 2 * a ^ 4)
        ≤ K / (ν ^ 2 * a ^ 4) * Real.exp (-(b' * c ^ 2 / a)) * (ν ^ 2 * a ^ 4) :=
          mul_le_mul_of_nonneg_right hE hpos4.le
      _ = K * Real.exp (-(b' * c ^ 2 / a)) := by
          rw [mul_right_comm, div_mul_cancel₀ K hpos4.ne']
  -- Part 1: the single-index bound, for every `i ≤ N`.
  have part1 : ∀ i ≤ N, Real.sqrt (J i) ≤ C * ν⁻¹ * a ^ (-(2 + (i : ℝ) / 2)) * G := by
    intro i hi
    have hdi : (0 : ℝ) < (1 / (4 * (N : ℝ))) ^ i := pow_pos hdpos i
    have hdel : (1 / (4 * (N : ℝ))) ^ i * (4 * (N : ℝ)) ^ i = 1 := by
      rw [← mul_pow, one_div, inv_mul_cancel₀ h4pos.ne', one_pow]
    have hKD : K * (4 * (N : ℝ)) ^ i ≤ C ^ 2 := by
      have h1 : (4 * (N : ℝ)) ^ i ≤ (4 * (N : ℝ)) ^ N := pow_le_pow_right₀ h4N hi
      have h2 : K * (4 * (N : ℝ)) ^ i ≤ K * (4 * (N : ℝ)) ^ N :=
        mul_le_mul_of_nonneg_left h1 hK.le
      have h3 : K * (4 * (N : ℝ)) ^ N ≤ C := by rw [hC]; linarith
      have h4 : C ≤ C ^ 2 := by nlinarith
      linarith
    have hKC : K ≤ (1 / (4 * (N : ℝ))) ^ i * C ^ 2 := by
      calc K = K * ((1 / (4 * (N : ℝ))) ^ i * (4 * (N : ℝ)) ^ i) := by rw [hdel, mul_one]
        _ = (1 / (4 * (N : ℝ))) ^ i * (K * (4 * (N : ℝ)) ^ i) := by ring
        _ ≤ (1 / (4 * (N : ℝ))) ^ i * C ^ 2 := mul_le_mul_of_nonneg_left hKD hdi.le
    have hkey : (1 / (4 * (N : ℝ))) ^ i * (J i * (ν ^ 2 * (a ^ 4 * a ^ i))) ≤
        (1 / (4 * (N : ℝ))) ^ i * (C ^ 2 * Real.exp (-(b' * c ^ 2 / a))) := by
      have hdA : ((1 / (4 * (N : ℝ))) * a) ^ i = (1 / (4 * (N : ℝ))) ^ i * a ^ i :=
        mul_pow _ _ _
      have h1 : (1 / (4 * (N : ℝ))) ^ i * a ^ i * J i ≤ E := by
        have h := hJE i hi
        rw [hdA] at h
        exact h
      have h2 : (1 / (4 * (N : ℝ))) ^ i * a ^ i * J i * (ν ^ 2 * a ^ 4) ≤
          E * (ν ^ 2 * a ^ 4) :=
        mul_le_mul_of_nonneg_right h1 hpos4.le
      have h3 : K * Real.exp (-(b' * c ^ 2 / a)) ≤
          (1 / (4 * (N : ℝ))) ^ i * (C ^ 2 * Real.exp (-(b' * c ^ 2 / a))) := by
        calc K * Real.exp (-(b' * c ^ 2 / a))
            ≤ (1 / (4 * (N : ℝ))) ^ i * C ^ 2 * Real.exp (-(b' * c ^ 2 / a)) :=
              mul_le_mul_of_nonneg_right hKC hG'.le
          _ = (1 / (4 * (N : ℝ))) ^ i * (C ^ 2 * Real.exp (-(b' * c ^ 2 / a))) := by ring
      have e1 : (1 / (4 * (N : ℝ))) ^ i * (J i * (ν ^ 2 * (a ^ 4 * a ^ i))) =
          (1 / (4 * (N : ℝ))) ^ i * a ^ i * J i * (ν ^ 2 * a ^ 4) := by ring
      rw [e1]
      exact le_trans h2 (le_trans hEG h3)
    have hmain : J i * (ν ^ 2 * (a ^ 4 * a ^ i)) ≤ C ^ 2 * Real.exp (-(b' * c ^ 2 / a)) :=
      le_of_mul_le_mul_left hkey hdi
    have hsq_a : (a ^ (-(2 + (i : ℝ) / 2))) ^ 2 = (a ^ 4 * a ^ i)⁻¹ := by
      rw [sq, ← Real.rpow_add ha0]
      have e : -(2 + (i : ℝ) / 2) + -(2 + (i : ℝ) / 2) = -((4 + i : ℕ) : ℝ) := by
        push_cast; ring
      rw [e, Real.rpow_neg ha0.le, Real.rpow_natCast, pow_add]
    have hYsq : (C * ν⁻¹ * a ^ (-(2 + (i : ℝ) / 2)) * G) ^ 2 =
        C ^ 2 * G ^ 2 / (ν ^ 2 * (a ^ 4 * a ^ i)) := by
      simp only [mul_pow, inv_pow]
      rw [hsq_a]
      ring
    have hY0 : 0 ≤ C * ν⁻¹ * a ^ (-(2 + (i : ℝ) / 2)) * G :=
      mul_nonneg (mul_nonneg (mul_nonneg hC0 (inv_nonneg.2 hν.le))
        (Real.rpow_nonneg ha0.le _)) hGpos.le
    have hJY : J i ≤ (C * ν⁻¹ * a ^ (-(2 + (i : ℝ) / 2)) * G) ^ 2 := by
      rw [hYsq, le_div_iff₀ (mul_pos hν2 (mul_pos (pow_pos ha0 4) (pow_pos ha0 i))), hG2]
      exact hmain
    exact Real.sqrt_le_iff.2 ⟨hY0, hJY⟩
  -- Part 2: the interpolation expression.
  rw [← hGdef]
  have p1 := part1 j (by omega)
  have p2 := part1 (j + 2) (by omega)
  have p3 := part1 (j + 1) (by omega)
  push_cast at p2 p3
  have hs_nn : 0 ≤ C * ν⁻¹ * a ^ (-((5 + (j : ℝ)) / 2)) * G :=
    mul_nonneg (mul_nonneg (mul_nonneg hC0 (inv_nonneg.2 hν.le))
      (Real.rpow_nonneg ha0.le _)) hGpos.le
  have hY0j : 0 ≤ C * ν⁻¹ * a ^ (-(2 + (j : ℝ) / 2)) * G :=
    mul_nonneg (mul_nonneg (mul_nonneg hC0 (inv_nonneg.2 hν.le))
      (Real.rpow_nonneg ha0.le _)) hGpos.le
  have hY0j1 : 0 ≤ C * ν⁻¹ * a ^ (-(2 + ((j : ℝ) + 1) / 2)) * G :=
    mul_nonneg (mul_nonneg (mul_nonneg hC0 (inv_nonneg.2 hν.le))
      (Real.rpow_nonneg ha0.le _)) hGpos.le
  have hY0j2 : 0 ≤ C * ν⁻¹ * a ^ (-(2 + ((j : ℝ) + 2) / 2)) * G :=
    mul_nonneg (mul_nonneg (mul_nonneg hC0 (inv_nonneg.2 hν.le))
      (Real.rpow_nonneg ha0.le _)) hGpos.le
  -- Term 1: `(√J_j √J_{j+2})^{1/2} ≤ C ν⁻¹ a^{-(5+j)/2} G`.
  have hr1 : a ^ (-(2 + (j : ℝ) / 2)) * a ^ (-(2 + ((j : ℝ) + 2) / 2)) =
      a ^ (-((5 + (j : ℝ)) / 2)) * a ^ (-((5 + (j : ℝ)) / 2)) := by
    simp only [← Real.rpow_add ha0]
    congr 1
    ring
  have hT1 : Real.sqrt (Real.sqrt (J j) * Real.sqrt (J (j + 2))) ≤
      C * ν⁻¹ * a ^ (-((5 + (j : ℝ)) / 2)) * G := by
    refine Real.sqrt_le_iff.2 ⟨hs_nn, ?_⟩
    calc Real.sqrt (J j) * Real.sqrt (J (j + 2))
        ≤ (C * ν⁻¹ * a ^ (-(2 + (j : ℝ) / 2)) * G) *
            (C * ν⁻¹ * a ^ (-(2 + ((j : ℝ) + 2) / 2)) * G) :=
          mul_le_mul p1 p2 (Real.sqrt_nonneg _) hY0j
      _ = (C * ν⁻¹ * G) ^ 2 *
            (a ^ (-(2 + (j : ℝ) / 2)) * a ^ (-(2 + ((j : ℝ) + 2) / 2))) := by ring
      _ = (C * ν⁻¹ * G) ^ 2 *
            (a ^ (-((5 + (j : ℝ)) / 2)) * a ^ (-((5 + (j : ℝ)) / 2))) := by rw [hr1]
      _ = (C * ν⁻¹ * a ^ (-((5 + (j : ℝ)) / 2)) * G) ^ 2 := by ring
  -- Term 2: `(√J_j √J_{j+1})^{1/2} ≤ C ν⁻¹ a^{1/4} a^{-(5+j)/2} G`.
  have hr2 : a ^ (-(2 + (j : ℝ) / 2)) * a ^ (-(2 + ((j : ℝ) + 1) / 2)) =
      a ^ (1 / 4 : ℝ) * a ^ (1 / 4 : ℝ) *
        (a ^ (-((5 + (j : ℝ)) / 2)) * a ^ (-((5 + (j : ℝ)) / 2))) := by
    simp only [← Real.rpow_add ha0]
    congr 1
    ring
  have hZ2 : 0 ≤ C * ν⁻¹ * a ^ (1 / 4 : ℝ) * a ^ (-((5 + (j : ℝ)) / 2)) * G :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC0 (inv_nonneg.2 hν.le))
      (Real.rpow_nonneg ha0.le _)) (Real.rpow_nonneg ha0.le _)) hGpos.le
  have hT2 : Real.sqrt (Real.sqrt (J j) * Real.sqrt (J (j + 1))) ≤
      C * ν⁻¹ * a ^ (1 / 4 : ℝ) * a ^ (-((5 + (j : ℝ)) / 2)) * G := by
    refine Real.sqrt_le_iff.2 ⟨hZ2, ?_⟩
    calc Real.sqrt (J j) * Real.sqrt (J (j + 1))
        ≤ (C * ν⁻¹ * a ^ (-(2 + (j : ℝ) / 2)) * G) *
            (C * ν⁻¹ * a ^ (-(2 + ((j : ℝ) + 1) / 2)) * G) :=
          mul_le_mul p1 p3 (Real.sqrt_nonneg _) hY0j
      _ = (C * ν⁻¹ * G) ^ 2 *
            (a ^ (-(2 + (j : ℝ) / 2)) * a ^ (-(2 + ((j : ℝ) + 1) / 2))) := by ring
      _ = (C * ν⁻¹ * G) ^ 2 *
            (a ^ (1 / 4 : ℝ) * a ^ (1 / 4 : ℝ) *
              (a ^ (-((5 + (j : ℝ)) / 2)) * a ^ (-((5 + (j : ℝ)) / 2)))) := by rw [hr2]
      _ = (C * ν⁻¹ * a ^ (1 / 4 : ℝ) * a ^ (-((5 + (j : ℝ)) / 2)) * G) ^ 2 := by ring
  -- The exponent fact `c^{-1/2} a^{1/4} ≤ 1`, from `a ≤ c²`.
  have ha14 : a ^ (1 / 4 : ℝ) ≤ c ^ (1 / 2 : ℝ) := by
    calc a ^ (1 / 4 : ℝ) ≤ (c ^ 2) ^ (1 / 4 : ℝ) := Real.rpow_le_rpow ha0.le hac (by norm_num)
      _ = c ^ (1 / 2 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hc0.le]
        norm_num
  have hcneg : c ^ (-(1 / 2 : ℝ)) * c ^ (1 / 2 : ℝ) = 1 := by
    rw [← Real.rpow_add hc0]; norm_num
  have hk : c ^ (-(1 / 2 : ℝ)) * a ^ (1 / 4 : ℝ) ≤ 1 := by
    calc c ^ (-(1 / 2 : ℝ)) * a ^ (1 / 4 : ℝ) ≤ c ^ (-(1 / 2 : ℝ)) * c ^ (1 / 2 : ℝ) :=
          mul_le_mul_of_nonneg_left ha14 (Real.rpow_nonneg hc0.le _)
      _ = 1 := hcneg
  have hT2' : c ^ (-(1 / 2 : ℝ)) * Real.sqrt (Real.sqrt (J j) * Real.sqrt (J (j + 1))) ≤
      C * ν⁻¹ * a ^ (-((5 + (j : ℝ)) / 2)) * G := by
    calc c ^ (-(1 / 2 : ℝ)) * Real.sqrt (Real.sqrt (J j) * Real.sqrt (J (j + 1)))
        ≤ c ^ (-(1 / 2 : ℝ)) * (C * ν⁻¹ * a ^ (1 / 4 : ℝ) * a ^ (-((5 + (j : ℝ)) / 2)) * G) :=
          mul_le_mul_of_nonneg_left hT2 (Real.rpow_nonneg hc0.le _)
      _ = (c ^ (-(1 / 2 : ℝ)) * a ^ (1 / 4 : ℝ)) *
            (C * ν⁻¹ * a ^ (-((5 + (j : ℝ)) / 2)) * G) := by ring
      _ ≤ 1 * (C * ν⁻¹ * a ^ (-((5 + (j : ℝ)) / 2)) * G) :=
          mul_le_mul_of_nonneg_right hk hs_nn
      _ = C * ν⁻¹ * a ^ (-((5 + (j : ℝ)) / 2)) * G := one_mul _
  have hfin : 2 * C * ν⁻¹ * a ^ (-((5 + (j : ℝ)) / 2)) * G =
      (C * ν⁻¹ * a ^ (-((5 + (j : ℝ)) / 2)) * G) + (C * ν⁻¹ * a ^ (-((5 + (j : ℝ)) / 2)) * G) := by
    ring
  have hfirst : 2 * C * ν⁻¹ * a ^ (-(2 + (j : ℝ) / 2)) * G =
      (C * ν⁻¹ * a ^ (-(2 + (j : ℝ) / 2)) * G) + (C * ν⁻¹ * a ^ (-(2 + (j : ℝ) / 2)) * G) := by
    ring
  refine ⟨?_, ?_⟩
  · linarith [p1, hY0j, hfirst]
  · rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
    linarith [hT1, hT2', hfin]

end UnforcedLeray.Short.PartI
