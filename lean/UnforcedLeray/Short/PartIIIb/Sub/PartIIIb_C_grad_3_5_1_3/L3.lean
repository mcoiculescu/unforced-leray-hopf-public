import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_5_1_3
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_5_1_3.A3a
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_5_1_3.B3b
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_5_1_3.C3c
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_5_1_3.D3d

/-!
# `PartIII-b:C/grad/3/5/1/3/3`: joint value and derivative bound of the lattice terms

Source `shorter-proof-2026-11-02.tex` 4963-4980, 5063-5079.  Assembles
`HpAJointBound` from the sibling pieces: `hpAyBound` (A3a, bounds of `A^y` and `∂_s A^y` on
`[s0,s1]`), `hpATm_eq'` (B3b/C3c closed form), `hpATm_hasFDerivAt_bound` (C3c, derivative bound),
and `hpA_gauss_absorb` (D3d, absorption of the physical Gaussian into `hpAGauss`).
-/

set_option autoImplicit false

noncomputable section

open Set Metric

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Value bound of the lattice term `hpATm` on `s0 ≤ s ≤ s1`, `‖x‖ ≤ R` (closed form of B3b,
bounds of `Nm (A^y)` from `‖A^y‖ ≤ B`, and the absorption `a ≥ 1`). -/
theorem hpATm_value_bound_L3 (as : ℝ) (χ : ℝ → ℝ) (hχ : IsSourceCutoffC χ) (ν : ℝ) (hν : 0 < ν)
    (A : ℝ → Mat3) (hA : IsAffElem as A) (s0 s1 R B : ℝ) (hs0 : 0 < s0) (hs01 : s0 ≤ s1)
    (hBd : ∀ s ∈ Set.Icc s0 s1, ‖Ay ν χ A s‖ ≤ B ∧ ‖deriv (Ay ν χ A) s‖ ≤ B) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (j : ℤ) (p : Chart), s0 ≤ p.1 → p.1 ≤ s1 → ‖p.2‖ ≤ R →
      ‖hpATm ν χ A j p‖ ≤
        K * (1 + |p.2.1 - (j : ℝ) * cOf ν|) ^ 5 *
          Real.exp (-(p.2.1 - (j : ℝ) * cOf ν) ^ 2 / (4 * ageA ν p.1)) := by
  have hB : 0 ≤ B := (norm_nonneg _).trans (hBd s0 ⟨le_rfl, hs01⟩).1
  have hR : 0 ≤ 1 + max R 0 := by linarith [le_max_right R 0]
  refine ⟨12 * B * (1 + max R 0) ^ 5, mul_nonneg (mul_nonneg (by norm_num) hB) (pow_nonneg hR 5), ?_⟩
  intro j p h1 h2 h3
  have hp : 0 < p.1 := lt_of_lt_of_le hs0 h1
  have hM : ‖Ay ν χ A p.1‖ ≤ B := (hBd p.1 ⟨h1, h2⟩).1
  have ha1 : 1 ≤ ageA ν p.1 := by unfold ageA; nlinarith [mul_pos hν hp]
  have ha : 0 < ageA ν p.1 := by linarith
  set y1 : ℝ := p.2.1 - (j : ℝ) * cOf ν with hy1
  have hN : Nm (Ay ν χ A p.1) ≤ 4 * B := Nm_le _ _ hM
  have hN0 : 0 ≤ Nm (Ay ν χ A p.1) := Nm_nonneg _
  have hW := WW_norm (ageA ν p.1) (Ay ν χ A p.1) (xj ν j p.2) ha1
  have hn0 : 0 ≤ ‖xj ν j p.2‖ := norm_nonneg _
  have hm1 : 1 ≤ 1 + ‖xj ν j p.2‖ := by linarith
  have hnle : ‖xj ν j p.2‖ ≤ (1 + ‖xj ν j p.2‖) ^ 3 := by
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 + ‖xj ν j p.2‖)
      (sub_nonneg.mpr (one_le_pow₀ hm1 (n := 2)))]
  have hWle : ‖WW (ageA ν p.1) (Ay ν χ A p.1) (xj ν j p.2)‖ ≤ 12 * B * (1 + ‖xj ν j p.2‖) ^ 3 := by
    have hA1 : Nm (Ay ν χ A p.1) * ‖xj ν j p.2‖ ≤ 4 * B * ‖xj ν j p.2‖ :=
      mul_le_mul_of_nonneg_right hN hn0
    have hA2 : Nm (Ay ν χ A p.1) * ‖xj ν j p.2‖ ^ 3 ≤ 4 * B * (1 + ‖xj ν j p.2‖) ^ 3 :=
      mul_le_mul hN (pow_le_pow_left₀ hn0 (by linarith) 3) (by positivity) (by linarith)
    have hA3 : B * ‖xj ν j p.2‖ ≤ B * (1 + ‖xj ν j p.2‖) ^ 3 :=
      mul_le_mul_of_nonneg_left hnle hB
    nlinarith [hW, hA1, hA2, hA3]
  -- the Gaussian and the inverse factor
  have hinv : (ageA ν p.1 ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ ha1 (n := 2))
  have hEE_le : EE (ageA ν p.1) (xj ν j p.2) ≤
      Real.exp (-(sq2 (xj ν j p.2)) / (4 * ageA ν p.1)) := by
    unfold EE
    exact mul_le_of_le_one_left (Real.exp_pos _).le hinv
  have hEE0 : 0 ≤ EE (ageA ν p.1) (xj ν j p.2) := by
    unfold EE; positivity
  have hnorm : ‖EE (ageA ν p.1) (xj ν j p.2) • WW (ageA ν p.1) (Ay ν χ A p.1) (xj ν j p.2)‖
      ≤ Real.exp (-(sq2 (xj ν j p.2)) / (4 * ageA ν p.1)) *
        ‖WW (ageA ν p.1) (Ay ν χ A p.1) (xj ν j p.2)‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hEE0]
    exact mul_le_mul_of_nonneg_right hEE_le (norm_nonneg _)
  -- comparison of the physical Gaussian with the `y1`-Gaussian
  have hexp : Real.exp (-(sq2 (xj ν j p.2)) / (4 * ageA ν p.1)) ≤
      Real.exp (-y1 ^ 2 / (4 * ageA ν p.1)) := by
    apply Real.exp_le_exp.mpr
    have : sq2 (xj ν j p.2) = y1 ^ 2 + p.2.2 ^ 2 := by simp [sq2, xj, hy1]
    rw [this]
    apply div_le_div_of_nonneg_right _ (by linarith)
    nlinarith [sq_nonneg p.2.2]
  -- the polynomial weight
  have hx2 : |p.2.2| ≤ R := by
    have : |p.2.2| ≤ ‖p.2‖ := by rw [← Real.norm_eq_abs]; exact norm_snd_le p.2
    linarith
  have hn : ‖xj ν j p.2‖ ≤ |y1| + max R 0 := by
    show max ‖y1‖ ‖p.2.2‖ ≤ _
    refine max_le ?_ ?_
    · rw [Real.norm_eq_abs]; linarith [le_max_right R 0]
    · rw [Real.norm_eq_abs]; linarith [le_max_left R 0, abs_nonneg y1]
  have hw : 1 + ‖xj ν j p.2‖ ≤ (1 + max R 0) * (1 + |y1|) := by
    nlinarith [le_max_right R 0, abs_nonneg y1, mul_nonneg (le_max_right R 0) (abs_nonneg y1)]
  have hw5 : (1 + ‖xj ν j p.2‖) ^ 5 ≤ ((1 + max R 0) * (1 + |y1|)) ^ 5 :=
    pow_le_pow_left₀ (by linarith) hw 5
  have hpow : (1 + ‖xj ν j p.2‖) ^ 3 ≤ (1 + ‖xj ν j p.2‖) ^ 5 :=
    pow_le_pow_right₀ hm1 (by norm_num)
  have hpow2 : (1 + ‖xj ν j p.2‖) ^ 3 ≤ (1 + max R 0) ^ 5 * (1 + |y1|) ^ 5 := by
    have := hpow.trans (hw5.trans (le_of_eq (mul_pow _ _ _)))
    exact this
  rw [hpATm_eq']
  have hE0 : 0 ≤ Real.exp (-(sq2 (xj ν j p.2)) / (4 * ageA ν p.1)) := (Real.exp_pos _).le
  calc ‖EE (ageA ν p.1) (xj ν j p.2) • WW (ageA ν p.1) (Ay ν χ A p.1) (xj ν j p.2)‖
      ≤ Real.exp (-(sq2 (xj ν j p.2)) / (4 * ageA ν p.1)) *
        ‖WW (ageA ν p.1) (Ay ν χ A p.1) (xj ν j p.2)‖ := hnorm
    _ ≤ Real.exp (-(sq2 (xj ν j p.2)) / (4 * ageA ν p.1)) *
        (12 * B * (1 + ‖xj ν j p.2‖) ^ 3) := mul_le_mul_of_nonneg_left hWle hE0
    _ ≤ Real.exp (-y1 ^ 2 / (4 * ageA ν p.1)) *
        (12 * B * ((1 + max R 0) ^ 5 * (1 + |y1|) ^ 5)) :=
        mul_le_mul hexp (mul_le_mul_of_nonneg_left hpow2 (by linarith)) (by positivity)
          (Real.exp_pos _).le
    _ = 12 * B * (1 + max R 0) ^ 5 * (1 + |y1|) ^ 5 *
          Real.exp (-y1 ^ 2 / (4 * ageA ν p.1)) := by ring

/-- `PartIII-b:C/grad/3/5/1/3/3`: the joint value and `(s,x)`-derivative bound `HpAJointBound`
of the lattice terms, with the Gaussian `hpAGauss` of degree 5 (source 4963-4980, 5063-5079). -/
theorem hpAJointBound (as : ℝ) : HpAJointBound as := by
  intro χ hχ ν hν A hA s0 s1 R hs0 hs01
  obtain ⟨B, hB0, hB⟩ := hpAyBound as χ hχ ν hν A hA s0 s1 hs0 hs01
  obtain ⟨K1, hK1, hK1'⟩ :=
    hpATm_hasFDerivAt_bound as χ hχ ν hν A hA s0 s1 R B hs0 hs01 hB
  obtain ⟨K2, hK2, hK2'⟩ := hpATm_value_bound_L3 as χ hχ ν hν A hA s0 s1 R B hs0 hs01 hB
  refine ⟨K1 + K2, by linarith, ?_⟩
  intro p h1 h2 h3 j
  have hXG := hpA_gauss_absorb ν p.1 s1 hν (by linarith [hs0, h1]) h2 (cOf ν) j p.2.1
  have hX0 : 0 ≤ (1 + |p.2.1 - (j : ℝ) * cOf ν|) ^ 5 *
      Real.exp (-(p.2.1 - (j : ℝ) * cOf ν) ^ 2 / (4 * ageA ν p.1)) := by positivity
  have hG0 : 0 ≤ hpAGauss (1 / (4 * (1 + ν * s1))) (cOf ν) j p.2.1 := hX0.trans hXG
  have hK1le : K1 ≤ K1 + K2 := by linarith
  have hK2le : K2 ≤ K1 + K2 := by linarith
  constructor
  · have h := hK2' j p h1 h2 h3
    calc ‖hpATm ν χ A j p‖
        ≤ K2 * (1 + |p.2.1 - (j : ℝ) * cOf ν|) ^ 5 *
          Real.exp (-(p.2.1 - (j : ℝ) * cOf ν) ^ 2 / (4 * ageA ν p.1)) := h
      _ = K2 * ((1 + |p.2.1 - (j : ℝ) * cOf ν|) ^ 5 *
          Real.exp (-(p.2.1 - (j : ℝ) * cOf ν) ^ 2 / (4 * ageA ν p.1))) := by ring
      _ ≤ K2 * hpAGauss (1 / (4 * (1 + ν * s1))) (cOf ν) j p.2.1 :=
          mul_le_mul_of_nonneg_left hXG hK2
      _ ≤ (K1 + K2) * hpAGauss (1 / (4 * (1 + ν * s1))) (cOf ν) j p.2.1 :=
          mul_le_mul_of_nonneg_right hK2le hG0
  · obtain ⟨-, hf⟩ := hK1' j p h1 h2 h3
    calc ‖fderiv ℝ (hpATm ν χ A j) p‖
        ≤ K1 * (1 + |p.2.1 - (j : ℝ) * cOf ν|) ^ 5 *
          Real.exp (-(p.2.1 - (j : ℝ) * cOf ν) ^ 2 / (4 * ageA ν p.1)) := hf
      _ = K1 * ((1 + |p.2.1 - (j : ℝ) * cOf ν|) ^ 5 *
          Real.exp (-(p.2.1 - (j : ℝ) * cOf ν) ^ 2 / (4 * ageA ν p.1))) := by ring
      _ ≤ K1 * hpAGauss (1 / (4 * (1 + ν * s1))) (cOf ν) j p.2.1 :=
          mul_le_mul_of_nonneg_left hXG hK1
      _ ≤ (K1 + K2) * hpAGauss (1 / (4 * (1 + ν * s1))) (cOf ν) j p.2.1 :=
          mul_le_mul_of_nonneg_right hK1le hG0

end UnforcedLeray.Short.PartIIIb.Concrete
