import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_8
import UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Proofs.FlatTermBound
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_1_5

/-!
# `PartIII-b:C/flatset/col/8`, leaf: `FlatTermDecay` (Gaussian decay of the lattice terms)

Source of record: `the November 2 reference manuscript`, lines 4594-4596, 4988,
4991. Same route as `flatTermBound` (`Proofs/FlatTermBound.lean`), but without the restriction
`|x₂| ≤ R`: the `x₂`-factor is controlled by the Gaussian `exp(-x₂²/(4a))` instead.

Split `|y|² = (x₁ - jc)² + x₂²`, `y = x_j`, `a = ageA ν s ∈ [1, a₂]`, `a₂ = 1 + ν max(s₂,s₁)`:
* `(1 + ‖y‖)³ ≤ (1 + |x₁ - jc|)³ (1 + |x₂|)³`;
* `exp(-(x₁-jc)²/(4a)) (1+|x₁-jc|)³ ≤ exp(X²/4) exp(-(jc)²/(8a₂)) (1+X)³ (1+|jc|)³`
  (`fd_x1`, `ft_exp_aux`), summable in `j` by `gp_poly_summable`;
* `(1 + x₂²) exp(-x₂²/(4a)) (1+|x₂|)³ ≤ 8 K` (`fd_x2`, `gb_poly_exp`).
-/

set_option autoImplicit false

noncomputable section

open Set

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

/-- The `x₁`-part of the exponential: `exp(-(x₁-jc)²/(4a)) ≤ exp(X²/4) exp(-(jc)²/(8 a₂))`
for `|x₁| ≤ X`, `1 ≤ a ≤ a₂ = 1 + ν s₂`. -/
lemma fd_x1 (ν s s2 X : ℝ) (x : ℝ × ℝ) (j : ℤ) (hν : 0 < ν) (hs : 0 < s) (hss : s ≤ s2)
    (hx1 : |x.1| ≤ X) :
    Real.exp (-((x.1 - (j : ℝ) * cOf ν) ^ 2) / (4 * ageA ν s)) ≤
      Real.exp (X ^ 2 / 4) * Real.exp (-(1 / (8 * (1 + ν * s2))) * (0 - (j : ℝ) * cOf ν) ^ 2) := by
  have ha1 : 1 ≤ ageA ν s := by unfold ageA; nlinarith [mul_pos hν hs]
  have ha2 : ageA ν s ≤ 1 + ν * s2 := by
    unfold ageA; nlinarith [mul_le_mul_of_nonneg_left hss hν.le]
  have ha0 : 0 < ageA ν s := by linarith
  have hX2 : x.1 ^ 2 ≤ X ^ 2 := by
    have h := pow_le_pow_left₀ (abs_nonneg x.1) hx1 2
    rwa [sq_abs] at h
  have hXX : 0 ≤ X ^ 2 := sq_nonneg X
  have hS : (0 - (j : ℝ) * cOf ν) ^ 2 / 2 - X ^ 2 ≤ (x.1 - (j : ℝ) * cOf ν) ^ 2 := by
    nlinarith [sq_nonneg (2 * x.1 - (j : ℝ) * cOf ν), hX2]
  have hp0 : 0 ≤ 1 / (4 * ageA ν s) := div_nonneg zero_le_one (by linarith)
  have hp : 1 / (4 * ageA ν s) ≤ 1 / 4 :=
    one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hq : 1 / (8 * (1 + ν * s2)) ≤ (1 / (4 * ageA ν s)) / 2 := by
    have h1 : 1 / (8 * (1 + ν * s2)) ≤ 1 / (8 * ageA ν s) :=
      one_div_le_one_div_of_le (by linarith) (by linarith)
    have h2 : (1 / (4 * ageA ν s)) / 2 = 1 / (8 * ageA ν s) := by
      rw [div_div]; congr 1; ring
    rw [h2]; exact h1
  have aux := ft_exp_aux (1 / (4 * ageA ν s)) (1 / (8 * (1 + ν * s2)))
    ((x.1 - (j : ℝ) * cOf ν) ^ 2) (0 - (j : ℝ) * cOf ν) (X ^ 2) hp0 hp hq hS hXX
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have e1 : -((x.1 - (j : ℝ) * cOf ν) ^ 2) / (4 * ageA ν s)
      = -(1 / (4 * ageA ν s)) * (x.1 - (j : ℝ) * cOf ν) ^ 2 := by
    ring
  rw [e1]
  linarith [aux]

/-- The `x₂`-part: `(1 + x₂²) exp(-x₂²/(4a)) (1+|x₂|)³ ≤ 8 K`, where `K` bounds
`(1+t²)⁴ exp(-t²/(4a₂))`, for `1 ≤ a ≤ a₂`. -/
lemma fd_x2 {a₂ a : ℝ} (ha : 1 ≤ a) (haa : a ≤ a₂) (K : ℝ)
    (hK : ∀ t : ℝ, (1 + t ^ 2) ^ 4 * Real.exp (-(1 / (4 * a₂)) * t ^ 2) ≤ K) (t : ℝ) :
    (1 + t ^ 2) * (Real.exp (-(t ^ 2) / (4 * a)) * (1 + |t|) ^ 3) ≤ 8 * K := by
  have ha0 : 0 < a := by linarith
  have ha₂0 : 0 < a₂ := by linarith
  have hexp : Real.exp (-(t ^ 2) / (4 * a)) ≤ Real.exp (-(1 / (4 * a₂)) * t ^ 2) := by
    apply Real.exp_le_exp.mpr
    have h1 : 1 / (4 * a₂) ≤ 1 / (4 * a) :=
      one_div_le_one_div_of_le (by linarith) (by linarith)
    have h2 : 0 ≤ t ^ 2 := sq_nonneg t
    have h3 : -(t ^ 2) / (4 * a) = -(1 / (4 * a)) * t ^ 2 := by ring
    rw [h3]
    nlinarith [mul_le_mul_of_nonneg_right h1 h2]
  have hcube : (1 + |t|) ^ 3 ≤ 8 * (1 + t ^ 2) ^ 3 := by
    have hb : 1 + |t| ≤ 2 * (1 + t ^ 2) := by
      nlinarith [sq_abs t, sq_nonneg (|t| - 1), abs_nonneg t]
    have h := pow_le_pow_left₀ (by positivity) hb 3
    calc (1 + |t|) ^ 3 ≤ (2 * (1 + t ^ 2)) ^ 3 := h
      _ = 8 * (1 + t ^ 2) ^ 3 := by ring
  calc (1 + t ^ 2) * (Real.exp (-(t ^ 2) / (4 * a)) * (1 + |t|) ^ 3)
      ≤ (1 + t ^ 2) * (Real.exp (-(1 / (4 * a₂)) * t ^ 2) * (8 * (1 + t ^ 2) ^ 3)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact mul_le_mul hexp hcube (by positivity) (Real.exp_pos _).le
    _ = 8 * ((1 + t ^ 2) ^ 4 * Real.exp (-(1 / (4 * a₂)) * t ^ 2)) := by ring
    _ ≤ 8 * K := mul_le_mul_of_nonneg_left (hK t) (by norm_num)

/-- A fixed polynomial-times-Gaussian bound: `(1+t²)⁴ exp(-α t²) ≤ K` for `α > 0`. -/
lemma fd_poly4 (α : ℝ) (hα : 0 < α) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t : ℝ, (1 + t ^ 2) ^ 4 * Real.exp (-α * t ^ 2) ≤ K := by
  obtain ⟨K, hK0, hK⟩ := gb_poly_exp α hα 4
  refine ⟨K, hK0, fun t => (hK t).trans ?_⟩
  exact mul_le_of_le_one_right hK0
    (Real.exp_le_one_iff.mpr (by nlinarith [mul_nonneg hα.le (sq_nonneg t)]))

/-- The `x₁`-factor and the norm: `(1 + ‖x_j‖)³ ≤ (1 + |x₁ - jc|)³ (1 + |x₂|)³`. -/
lemma fd_norm (ν : ℝ) (j : ℤ) (x : ℝ × ℝ) :
    (1 + ‖xj ν j x‖) ^ 3 ≤ (1 + |x.1 - (j : ℝ) * cOf ν|) ^ 3 * (1 + |x.2|) ^ 3 := by
  have e : ‖xj ν j x‖ = max |x.1 - (j : ℝ) * cOf ν| |x.2| := by
    rw [Prod.norm_def]; simp [xj, Real.norm_eq_abs]
  rw [e, ← mul_pow]
  apply pow_le_pow_left₀ (by positivity)
  rcases le_total |x.1 - (j : ℝ) * cOf ν| |x.2| with h | h
  · rw [max_eq_right h]
    nlinarith [mul_nonneg (abs_nonneg (x.1 - (j : ℝ) * cOf ν)) (abs_nonneg x.2),
      abs_nonneg (x.1 - (j : ℝ) * cOf ν), abs_nonneg x.2]
  · rw [max_eq_left h]
    nlinarith [mul_nonneg (abs_nonneg (x.1 - (j : ℝ) * cOf ν)) (abs_nonneg x.2),
      abs_nonneg (x.1 - (j : ℝ) * cOf ν), abs_nonneg x.2]

/-- **Decaying domination of the lattice terms** (source 4988, 4991: Gaussian decay). -/
theorem flatTermDecay : FlatTermDecay := by
  intro ν s₁ s₂ X₀ Bb hν hs₁
  have hA2 : 0 < 1 + ν * max s₂ s₁ := by
    nlinarith [mul_pos hν hs₁, mul_le_mul_of_nonneg_left (le_max_right s₂ s₁) hν.le]
  have hα4 : 0 < 1 / (4 * (1 + ν * max s₂ s₁)) := div_pos one_pos (by linarith)
  have hβ : 0 < 1 / (8 * (1 + ν * max s₂ s₁)) := div_pos one_pos (by linarith)
  have hc : 0 < cOf ν := by
    unfold cOf; exact inv_pos.mpr (pow_pos hν 2)
  obtain ⟨K, hK0, hK⟩ := fd_poly4 _ hα4
  refine ⟨fun j => (13 * Bb * (Real.exp (|X₀| ^ 2 / 4) * (1 + |X₀|) ^ 3 * (8 * K))) *
      ((1 + |0 - (j : ℝ) * cOf ν|) ^ 3 *
        Real.exp (-(1 / (8 * (1 + ν * max s₂ s₁))) * (0 - (j : ℝ) * cOf ν) ^ 2)), ?_, ?_⟩
  · exact (gp_poly_summable 0 (1 / (8 * (1 + ν * max s₂ s₁))) (cOf ν) hβ hc).mul_left _
  · intro s hs B hB x hx1 j
    dsimp only
    have hsp : 0 < s := lt_of_lt_of_le hs₁ hs.1
    have hss : s ≤ max s₂ s₁ := hs.2.trans (le_max_left _ _)
    have hBb : 0 ≤ Bb := (abs_nonneg _).trans (hB 0 0)
    have h13 : 0 ≤ 13 * Bb := by linarith
    have ha1 : 1 ≤ ageA ν s := by unfold ageA; nlinarith [mul_pos hν hsp]
    have ha2 : ageA ν s ≤ 1 + ν * max s₂ s₁ := by
      unfold ageA; nlinarith [mul_le_mul_of_nonneg_left hss hν.le]
    have hX1 : |x.1| ≤ |X₀| := hx1.trans (le_abs_self X₀)
    have hT := ft_term_pt ν s Bb B hν hsp hB x j
    have hsplit : Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) =
        Real.exp (-((x.1 - (j : ℝ) * cOf ν) ^ 2) / (4 * ageA ν s)) *
          Real.exp (-(x.2 ^ 2) / (4 * ageA ν s)) := by
      rw [← Real.exp_add]; congr 1; simp only [sq2, xj]; ring
    have hE1 := fd_x1 ν s (max s₂ s₁) |X₀| x j hν hsp hss hX1
    have hu : |x.1 - (j : ℝ) * cOf ν| ≤ |x.1| + |0 - (j : ℝ) * cOf ν| := by
      have h1 := abs_sub x.1 ((j : ℝ) * cOf ν)
      rw [zero_sub, abs_neg]; exact h1
    have hY1 : 1 + |x.1 - (j : ℝ) * cOf ν| ≤ (1 + |X₀|) * (1 + |0 - (j : ℝ) * cOf ν|) := by
      nlinarith [abs_nonneg X₀, abs_nonneg (0 - (j : ℝ) * cOf ν),
        mul_nonneg (abs_nonneg X₀) (abs_nonneg (0 - (j : ℝ) * cOf ν))]
    have hY1' : (1 + |x.1 - (j : ℝ) * cOf ν|) ^ 3 ≤
        ((1 + |X₀|) * (1 + |0 - (j : ℝ) * cOf ν|)) ^ 3 :=
      pow_le_pow_left₀ (by positivity) hY1 3
    have hX2 := fd_x2 ha1 ha2 K hK x.2
    have hP1le : Real.exp (-((x.1 - (j : ℝ) * cOf ν) ^ 2) / (4 * ageA ν s)) *
        (1 + |x.1 - (j : ℝ) * cOf ν|) ^ 3 ≤
        Real.exp (|X₀| ^ 2 / 4) * (1 + |X₀|) ^ 3 *
          ((1 + |0 - (j : ℝ) * cOf ν|) ^ 3 *
            Real.exp (-(1 / (8 * (1 + ν * max s₂ s₁))) * (0 - (j : ℝ) * cOf ν) ^ 2)) := by
      calc Real.exp (-((x.1 - (j : ℝ) * cOf ν) ^ 2) / (4 * ageA ν s)) *
            (1 + |x.1 - (j : ℝ) * cOf ν|) ^ 3
          ≤ (Real.exp (|X₀| ^ 2 / 4) * Real.exp (-(1 / (8 * (1 + ν * max s₂ s₁))) *
              (0 - (j : ℝ) * cOf ν) ^ 2)) *
              ((1 + |X₀|) * (1 + |0 - (j : ℝ) * cOf ν|)) ^ 3 :=
            mul_le_mul hE1 hY1' (by positivity) (by positivity)
        _ = Real.exp (|X₀| ^ 2 / 4) * (1 + |X₀|) ^ 3 *
              ((1 + |0 - (j : ℝ) * cOf ν|) ^ 3 *
                Real.exp (-(1 / (8 * (1 + ν * max s₂ s₁))) * (0 - (j : ℝ) * cOf ν) ^ 2)) := by
          ring
    have hchain : 13 * Bb * (Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) *
          (1 + ‖xj ν j x‖) ^ 3) ≤
        13 * Bb * ((Real.exp (-((x.1 - (j : ℝ) * cOf ν) ^ 2) / (4 * ageA ν s)) *
            (1 + |x.1 - (j : ℝ) * cOf ν|) ^ 3) *
          (Real.exp (-(x.2 ^ 2) / (4 * ageA ν s)) * (1 + |x.2|) ^ 3)) := by
      rw [hsplit]
      refine mul_le_mul_of_nonneg_left ?_ h13
      have hE : 0 ≤ Real.exp (-((x.1 - (j : ℝ) * cOf ν) ^ 2) / (4 * ageA ν s)) *
          Real.exp (-(x.2 ^ 2) / (4 * ageA ν s)) := by positivity
      calc Real.exp (-((x.1 - (j : ℝ) * cOf ν) ^ 2) / (4 * ageA ν s)) *
            Real.exp (-(x.2 ^ 2) / (4 * ageA ν s)) * (1 + ‖xj ν j x‖) ^ 3
          ≤ Real.exp (-((x.1 - (j : ℝ) * cOf ν) ^ 2) / (4 * ageA ν s)) *
            Real.exp (-(x.2 ^ 2) / (4 * ageA ν s)) *
            ((1 + |x.1 - (j : ℝ) * cOf ν|) ^ 3 * (1 + |x.2|) ^ 3) :=
            mul_le_mul_of_nonneg_left (fd_norm ν j x) hE
        _ = (Real.exp (-((x.1 - (j : ℝ) * cOf ν) ^ 2) / (4 * ageA ν s)) *
            (1 + |x.1 - (j : ℝ) * cOf ν|) ^ 3) *
            (Real.exp (-(x.2 ^ 2) / (4 * ageA ν s)) * (1 + |x.2|) ^ 3) := by ring
    rw [le_div_iff₀ (by positivity)]
    calc ‖emb (fderiv ℝ (Vj ν s j) x (merApply B (xj ν j x))) + mv B (emb (Vj ν s j x))‖
            * (1 + x.2 ^ 2)
        ≤ (13 * Bb * ((Real.exp (-((x.1 - (j : ℝ) * cOf ν) ^ 2) / (4 * ageA ν s)) *
            (1 + |x.1 - (j : ℝ) * cOf ν|) ^ 3) *
          (Real.exp (-(x.2 ^ 2) / (4 * ageA ν s)) * (1 + |x.2|) ^ 3))) * (1 + x.2 ^ 2) :=
          mul_le_mul_of_nonneg_right (hT.trans hchain) (by positivity)
      _ = 13 * Bb * ((Real.exp (-((x.1 - (j : ℝ) * cOf ν) ^ 2) / (4 * ageA ν s)) *
            (1 + |x.1 - (j : ℝ) * cOf ν|) ^ 3) *
          ((1 + x.2 ^ 2) * (Real.exp (-(x.2 ^ 2) / (4 * ageA ν s)) * (1 + |x.2|) ^ 3))) := by
          ring
      _ ≤ 13 * Bb * ((Real.exp (|X₀| ^ 2 / 4) * (1 + |X₀|) ^ 3 *
            ((1 + |0 - (j : ℝ) * cOf ν|) ^ 3 *
              Real.exp (-(1 / (8 * (1 + ν * max s₂ s₁))) * (0 - (j : ℝ) * cOf ν) ^ 2))) *
            (8 * K)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hP1le hX2 (by positivity) (by positivity)) h13
      _ = (13 * Bb * (Real.exp (|X₀| ^ 2 / 4) * (1 + |X₀|) ^ 3 * (8 * K))) *
            ((1 + |0 - (j : ℝ) * cOf ν|) ^ 3 *
              Real.exp (-(1 / (8 * (1 + ν * max s₂ s₁))) * (0 - (j : ℝ) * cOf ν) ^ 2)) := by
          ring

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
