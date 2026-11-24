import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_2
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.HpPsiTermSummable.Gauss
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.FATermSummable

/-!
# `PartIII-b:C/flatset/col/2`, leaf 3: uniform Gaussian domination of the lattice terms

Source of record: `the November 2 reference manuscript`, lines 4988, 4991.

Route. For `s ∈ [s₁, s₂]` (so `1 ≤ a = 1 + νs ≤ a₂ = 1 + ν max(s₂, s₁)`), with `y = x_j`,
`Y = ‖y‖`, `E = exp(-|y|²/(4a))`, `κ = (a²)⁻¹`:
* `‖fderiv V_j x (B y)‖ ≤ κ E (1 + Y²/a) · 4Bb·Y` and `‖B V_j‖ ≤ 9Bb · κ E Y`, so the term is
  `≤ 13 Bb · E (1+Y)³` (`ft_alg`, `ft_term_pt`);
* `E ≤ exp(X²/4) exp(-(jc)²/(8 a₂))` for `|x₁| ≤ X` (`ft_E_bound`, from `(x₁ - jc)² ≥ (jc)²/2 - X²`);
* `(1+Y)³ ≤ (1+X+R)³ (1+|jc|)³` (`ft_Y_bound`);
* `j ↦ (1+|jc|)³ exp(-(jc)²/(8a₂))` is summable (`gp_poly_summable`, with `t = 0`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

/-- Elementary algebra for the bound of one lattice term. -/
lemma ft_alg (κ E a Y F V Bb : ℝ) (_hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1) (hE0 : 0 ≤ E) (ha1 : 1 ≤ a)
    (hY : 0 ≤ Y) (hBb : 0 ≤ Bb)
    (hF : F ≤ κ * E * (1 + Y ^ 2 / a) * (4 * Bb * Y)) (hV : V ≤ 9 * Bb * (κ * E * Y)) :
    F + V ≤ 13 * Bb * (E * (1 + Y) ^ 3) := by
  have ha0 : 0 < a := by linarith
  have hq : 0 ≤ Y ^ 2 / a := div_nonneg (sq_nonneg Y) ha0.le
  have hq1 : 1 + Y ^ 2 / a ≤ (1 + Y) ^ 2 := by
    have h := div_le_self (sq_nonneg Y) ha1
    nlinarith
  have hq2 : κ * E * (1 + Y ^ 2 / a) ≤ E * (1 + Y) ^ 2 := by
    calc κ * E * (1 + Y ^ 2 / a) ≤ 1 * E * (1 + Y) ^ 2 :=
          mul_le_mul (mul_le_mul_of_nonneg_right hκ1 hE0) hq1 (by linarith) (by linarith)
      _ = E * (1 + Y) ^ 2 := by ring
  have h4 : 0 ≤ 4 * Bb * Y := mul_nonneg (mul_nonneg (by norm_num) hBb) hY
  have hF2 : F ≤ E * (1 + Y) ^ 2 * (4 * Bb * Y) := hF.trans (mul_le_mul_of_nonneg_right hq2 h4)
  have h3 : (1 + Y) ^ 2 * Y ≤ (1 + Y) ^ 3 := by nlinarith [sq_nonneg (1 + Y)]
  have hF3 : E * (1 + Y) ^ 2 * (4 * Bb * Y) ≤ 4 * Bb * (E * (1 + Y) ^ 3) := by
    calc E * (1 + Y) ^ 2 * (4 * Bb * Y) = 4 * Bb * (E * ((1 + Y) ^ 2 * Y)) := by ring
      _ ≤ 4 * Bb * (E * (1 + Y) ^ 3) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 hE0) (by linarith)
  have hY3 : Y ≤ (1 + Y) ^ 3 := by
    nlinarith [mul_nonneg hY hY, mul_nonneg (mul_nonneg hY hY) hY]
  have hkEY : κ * E * Y ≤ E * (1 + Y) ^ 3 := by
    calc κ * E * Y ≤ 1 * E * Y := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hκ1 hE0) hY
      _ = E * Y := by ring
      _ ≤ E * (1 + Y) ^ 3 := mul_le_mul_of_nonneg_left hY3 hE0
  have hV2 : V ≤ 9 * Bb * (E * (1 + Y) ^ 3) :=
    hV.trans (mul_le_mul_of_nonneg_left hkEY (by linarith))
  calc F + V ≤ 4 * Bb * (E * (1 + Y) ^ 3) + 9 * Bb * (E * (1 + Y) ^ 3) :=
        add_le_add (hF2.trans hF3) hV2
    _ = 13 * Bb * (E * (1 + Y) ^ 3) := by ring

/-- Pointwise bound of one lattice term, in terms of `E = exp(-|x_j|²/(4a))` and `Y = ‖x_j‖`. -/
lemma ft_term_pt (ν s Bb : ℝ) (B : Mat3) (hν : 0 < ν) (hs : 0 < s)
    (hB : ∀ a b, |B a b| ≤ Bb) (x : ℝ × ℝ) (j : ℤ) :
    ‖emb (fderiv ℝ (Vj ν s j) x (merApply B (xj ν j x))) + mv B (emb (Vj ν s j x))‖ ≤
      13 * Bb * (Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) * (1 + ‖xj ν j x‖) ^ 3) := by
  have ha : 0 < ageA ν s := by unfold ageA; nlinarith [mul_pos hν hs]
  have ha1 : 1 ≤ ageA ν s := by unfold ageA; nlinarith [mul_pos hν hs]
  have hBb : 0 ≤ Bb := (abs_nonneg _).trans (hB 0 0)
  have hS4 : |B 0 0| + |B 0 2| + |B 2 0| + |B 2 2| ≤ 4 * Bb := by
    linarith [hB 0 0, hB 0 2, hB 2 0, hB 2 2]
  have hS9 : ∑ i, ∑ k, |B i k| ≤ 9 * Bb := by
    simp only [Fin.sum_univ_three]
    linarith [hB 0 0, hB 0 1, hB 0 2, hB 1 0, hB 1 1, hB 1 2, hB 2 0, hB 2 1, hB 2 2]
  have hS0 : 0 ≤ ∑ i, ∑ k, |B i k| :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun k _ => abs_nonneg _
  have hY : 0 ≤ ‖xj ν j x‖ := norm_nonneg _
  have hEnn : 0 ≤ Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) := (Real.exp_pos _).le
  have hκ0 : 0 ≤ (ageA ν s ^ 2)⁻¹ := inv_nonneg.mpr (sq_nonneg _)
  have hκ1 : (ageA ν s ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ ha1)
  have hwB : ‖merApply B (xj ν j x)‖ ≤ 4 * Bb * ‖xj ν j x‖ :=
    (gp_merApply_norm_le B (xj ν j x)).trans (mul_le_mul_of_nonneg_right hS4 hY)
  have hq0 : 0 ≤ 1 + ‖xj ν j x‖ ^ 2 / ageA ν s := by
    have := div_nonneg (sq_nonneg ‖xj ν j x‖) ha.le
    linarith
  have hD := gp_fderiv_Vj_norm ν s ha j x (merApply B (xj ν j x))
  have hF : ‖fderiv ℝ (Vj ν s j) x (merApply B (xj ν j x))‖ ≤
      (ageA ν s ^ 2)⁻¹ * Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) *
        (1 + ‖xj ν j x‖ ^ 2 / ageA ν s) * (4 * Bb * ‖xj ν j x‖) :=
    hD.trans (mul_le_mul_of_nonneg_left hwB
      (mul_nonneg (mul_nonneg hκ0 hEnn) hq0))
  have hV : ‖mv B (emb (Vj ν s j x))‖ ≤
      9 * Bb * ((ageA ν s ^ 2)⁻¹ * Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) * ‖xj ν j x‖) := by
    rw [← gp_Vj_norm_eq ν s j x]
    exact ((fa_mv_norm_le B _).trans (mul_le_mul_of_nonneg_left (fa_emb_norm_le _) hS0)).trans
      (mul_le_mul_of_nonneg_right hS9 (norm_nonneg _))
  have key := ft_alg ((ageA ν s ^ 2)⁻¹) (Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)))
    (ageA ν s) ‖xj ν j x‖ ‖fderiv ℝ (Vj ν s j) x (merApply B (xj ν j x))‖
    ‖mv B (emb (Vj ν s j x))‖ Bb hκ0 hκ1 hEnn ha1 hY hBb hF hV
  exact (norm_add_le _ _).trans (((add_le_add (fa_emb_norm_le _) le_rfl)).trans key)

/-- Exponent comparison: `exp(-|x_j|²/(4a)) ≤ exp(X²/4) exp(-(jc)²/(8 a₂))`. -/
lemma ft_exp_aux (p q S u X2 : ℝ) (hp0 : 0 ≤ p) (hp : p ≤ 1 / 4) (hq : q ≤ p / 2)
    (hS : u ^ 2 / 2 - X2 ≤ S) (hX2 : 0 ≤ X2) : -p * S ≤ X2 / 4 - q * u ^ 2 := by
  nlinarith [mul_le_mul_of_nonneg_left hS hp0, mul_nonneg (sub_nonneg.2 hq) (sq_nonneg u),
    mul_nonneg (sub_nonneg.2 hp) hX2]

lemma ft_E_bound (ν s s2 X : ℝ) (x : ℝ × ℝ) (j : ℤ) (hν : 0 < ν) (hs : 0 < s) (hss : s ≤ s2)
    (hx1 : |x.1| ≤ X) :
    Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) ≤
      Real.exp (X ^ 2 / 4) * Real.exp (-(1 / (8 * (1 + ν * s2))) * (0 - (j : ℝ) * cOf ν) ^ 2) := by
  have ha1 : 1 ≤ ageA ν s := by unfold ageA; nlinarith [mul_pos hν hs]
  have ha2 : ageA ν s ≤ 1 + ν * s2 := by
    unfold ageA; nlinarith [mul_le_mul_of_nonneg_left hss hν.le]
  have ha0 : 0 < ageA ν s := by linarith
  have hX2 : x.1 ^ 2 ≤ X ^ 2 := by
    have h := pow_le_pow_left₀ (abs_nonneg x.1) hx1 2
    rwa [sq_abs] at h
  have hXX : 0 ≤ X ^ 2 := sq_nonneg X
  have hS : (0 - (j : ℝ) * cOf ν) ^ 2 / 2 - X ^ 2 ≤ sq2 (xj ν j x) := by
    show (0 - (j : ℝ) * cOf ν) ^ 2 / 2 - X ^ 2 ≤ (x.1 - (j : ℝ) * cOf ν) ^ 2 + x.2 ^ 2
    nlinarith [sq_nonneg (x.1 + (x.1 - (j : ℝ) * cOf ν)), sq_nonneg x.2, hX2]
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
    (sq2 (xj ν j x)) (0 - (j : ℝ) * cOf ν) (X ^ 2) hp0 hp hq hS hXX
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have e1 : -(sq2 (xj ν j x)) / (4 * ageA ν s) = -(1 / (4 * ageA ν s)) * sq2 (xj ν j x) := by
    ring
  rw [e1]
  linarith [aux]

/-- The `Y`-bound: `(1 + ‖x_j‖)³ ≤ (1 + X + R)³ (1 + |jc|)³` for `|x₁| ≤ X`, `|x₂| ≤ R`. -/
lemma ft_Y_bound (ν X R : ℝ) (x : ℝ × ℝ) (j : ℤ) (hX : 0 ≤ X) (hR : 0 ≤ R)
    (hx1 : |x.1| ≤ X) (hx2 : |x.2| ≤ R) :
    (1 + ‖xj ν j x‖) ^ 3 ≤ (1 + X + R) ^ 3 * (1 + |0 - (j : ℝ) * cOf ν|) ^ 3 := by
  have hn : ‖xj ν j x‖ ≤ X + R + |0 - (j : ℝ) * cOf ν| := by
    have e : |0 - (j : ℝ) * cOf ν| = |(j : ℝ) * cOf ν| := by rw [zero_sub, abs_neg]
    rw [Prod.norm_def]
    apply max_le
    · rw [Real.norm_eq_abs]
      show |x.1 - (j : ℝ) * cOf ν| ≤ _
      have h1 := abs_sub x.1 ((j : ℝ) * cOf ν)
      linarith [abs_nonneg ((j : ℝ) * cOf ν)]
    · rw [Real.norm_eq_abs]
      show |x.2| ≤ _
      have := abs_nonneg (0 - (j : ℝ) * cOf ν)
      linarith
  have h1 : 1 + ‖xj ν j x‖ ≤ (1 + X + R) * (1 + |0 - (j : ℝ) * cOf ν|) := by
    nlinarith [abs_nonneg (0 - (j : ℝ) * cOf ν), mul_nonneg (add_nonneg hX hR)
      (abs_nonneg (0 - (j : ℝ) * cOf ν))]
  calc (1 + ‖xj ν j x‖) ^ 3 ≤ ((1 + X + R) * (1 + |0 - (j : ℝ) * cOf ν|)) ^ 3 :=
        pow_le_pow_left₀ (by positivity) h1 3
    _ = (1 + X + R) ^ 3 * (1 + |0 - (j : ℝ) * cOf ν|) ^ 3 := by ring

theorem flatTermBound : FlatTermBound := by
  intro ν s₁ s₂ R X₀ Bb hν hs₁
  have hm : s₁ ≤ max s₂ s₁ := le_max_right _ _
  have hs2pos : 0 < 1 + ν * max s₂ s₁ := by nlinarith [mul_pos hν hs₁]
  have hα : 0 < 1 / (8 * (1 + ν * max s₂ s₁)) := div_pos one_pos (by linarith)
  have hc : 0 < cOf ν := by
    unfold cOf; exact inv_pos.mpr (pow_pos hν 2)
  refine ⟨fun j => (13 * Bb * Real.exp (|X₀| ^ 2 / 4) * (1 + |X₀| + |R|) ^ 3) *
      ((1 + |0 - (j : ℝ) * cOf ν|) ^ 3 *
        Real.exp (-(1 / (8 * (1 + ν * max s₂ s₁))) * (0 - (j : ℝ) * cOf ν) ^ 2)), ?_, ?_⟩
  · exact (gp_poly_summable 0 (1 / (8 * (1 + ν * max s₂ s₁))) (cOf ν) hα hc).mul_left _
  · intro s hs B hB x hx1 hx2 j
    have hsp : 0 < s := lt_of_lt_of_le hs₁ hs.1
    have hss : s ≤ max s₂ s₁ := hs.2.trans (le_max_left _ _)
    have hBb : 0 ≤ Bb := (abs_nonneg _).trans (hB 0 0)
    have hT := ft_term_pt ν s Bb B hν hsp hB x j
    have hE := ft_E_bound ν s (max s₂ s₁) |X₀| x j hν hsp hss (hx1.trans (le_abs_self _))
    have hY := ft_Y_bound ν |X₀| |R| x j (abs_nonneg _) (abs_nonneg _)
      (hx1.trans (le_abs_self _)) (hx2.trans (le_abs_self _))
    calc ‖emb (fderiv ℝ (Vj ν s j) x (merApply B (xj ν j x))) + mv B (emb (Vj ν s j x))‖
        ≤ 13 * Bb * (Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) * (1 + ‖xj ν j x‖) ^ 3) := hT
      _ ≤ 13 * Bb * ((Real.exp (|X₀| ^ 2 / 4) *
            Real.exp (-(1 / (8 * (1 + ν * max s₂ s₁))) * (0 - (j : ℝ) * cOf ν) ^ 2)) *
            ((1 + |X₀| + |R|) ^ 3 * (1 + |0 - (j : ℝ) * cOf ν|) ^ 3)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hE hY (by positivity) (by positivity))
            (by linarith)
      _ = (13 * Bb * Real.exp (|X₀| ^ 2 / 4) * (1 + |X₀| + |R|) ^ 3) *
            ((1 + |0 - (j : ℝ) * cOf ν|) ^ 3 *
              Real.exp (-(1 / (8 * (1 + ν * max s₂ s₁))) * (0 - (j : ℝ) * cOf ν) ^ 2)) := by
          ring

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
