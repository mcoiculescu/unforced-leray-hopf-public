import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineFields
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.HpPsiTermSummable.Gauss

/-!
# `C/inst/2`: summability of the lattice terms of `f_A` (source 4963-4970, 4978)

For fixed `ν, s > 0` and `x`, the `j`-th term of `f_A` is
`emb (DV_j(x)(B_mer x_j)) + B V_j(x)` with the fixed matrix `B = Bmat ν μ χ A s`; it is bounded by a
constant times `(1 + |q - jc|)³ e^{-(q - jc)²/(4a)}`, which is summable over `j ∈ ℤ`.
Helpers `gp_*` are in `ReturnInst/HpPsiTermSummable/Gauss.lean`; the sup-norm bounds for `emb` and
`mv` are proved here.
-/

set_option autoImplicit false

noncomputable section

open Set

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- `‖emb v‖ ≤ ‖v‖` (the embedding `(v₁, v₂) ↦ (v₁, 0, v₂)` is a sup-norm contraction). -/
lemma fa_emb_norm_le (v : ℝ × ℝ) : ‖emb v‖ ≤ ‖v‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg v)).2 (fun i => ?_)
  fin_cases i
  · show ‖v.1‖ ≤ ‖v‖
    exact norm_fst_le v
  · show ‖(0 : ℝ)‖ ≤ ‖v‖
    simp
  · show ‖v.2‖ ≤ ‖v‖
    exact norm_snd_le v

/-- Operator bound for `mv B` on `Vec3`. -/
lemma fa_mv_norm_le (B : Mat3) (w : Vec3) : ‖mv B w‖ ≤ (∑ i, ∑ j, |B i j|) * ‖w‖ := by
  have hnn : 0 ≤ ‖w‖ := norm_nonneg w
  have hw : ∀ j, |w j| ≤ ‖w‖ := fun j => by
    rw [← Real.norm_eq_abs]; exact norm_le_pi_norm w j
  have hK : 0 ≤ ∑ i, ∑ j, |B i j| :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg hK hnn)).2 (fun i => ?_)
  rw [Real.norm_eq_abs]
  have h1 : |mv B w i| ≤ (∑ j, |B i j|) * ‖w‖ := by
    show |∑ j, B i j * w j| ≤ _
    rw [Finset.sum_mul]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hw j) (abs_nonneg _)
  have h2 : ∑ j, |B i j| ≤ ∑ i', ∑ j, |B i' j| :=
    Finset.single_le_sum (f := fun i' => ∑ j, |B i' j|)
      (fun i' _ => Finset.sum_nonneg fun j _ => abs_nonneg _) (Finset.mem_univ i)
  exact h1.trans (mul_le_mul_of_nonneg_right h2 hnn)

/-- Bound for the `f_A` lattice term `emb(DV_j(x)(B x_j)) + B V_j(x)` with a fixed matrix `B`. -/
lemma fa_term_bound (ν s : ℝ) (ha : 0 < ageA ν s) (B : Mat3) (x : ℝ × ℝ) :
    ∃ K : ℝ, ∀ j : ℤ,
      ‖emb (fderiv ℝ (Vj ν s j) x (merApply B (xj ν j x))) + mv B (emb (Vj ν s j x))‖ ≤
        K * ((1 + |x.1 - (j : ℝ) * cOf ν|) ^ 3 *
          Real.exp (-(1 / (4 * ageA ν s)) * (x.1 - (j : ℝ) * cOf ν) ^ 2)) := by
  have hK0 : 0 ≤ |B 0 0| + |B 0 2| + |B 2 0| + |B 2 2| := by positivity
  have hKB : 0 ≤ ∑ i, ∑ j, |B i j| := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
  have hκ : 0 ≤ (ageA ν s ^ 2)⁻¹ := by positivity
  have hia : 0 ≤ (ageA ν s)⁻¹ := inv_nonneg.mpr ha.le
  refine ⟨((|B 0 0| + |B 0 2| + |B 2 0| + |B 2 2|) * (1 + (ageA ν s)⁻¹) + ∑ i, ∑ j, |B i j|)
    * (ageA ν s ^ 2)⁻¹ * (1 + |x.2|) ^ 3, fun j => ?_⟩
  have hE0 : 0 ≤ Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) := (Real.exp_pos _).le
  have hyn : 0 ≤ ‖xj ν j x‖ := norm_nonneg _
  have hq : 0 ≤ 1 + ‖xj ν j x‖ ^ 2 / ageA ν s := by
    have := div_nonneg (sq_nonneg ‖xj ν j x‖) ha.le; linarith
  have hpos : 0 ≤ (ageA ν s ^ 2)⁻¹ * Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) *
      (1 + ‖xj ν j x‖ ^ 2 / ageA ν s) := mul_nonneg (mul_nonneg hκ hE0) hq
  have hemb1 := fa_emb_norm_le (fderiv ℝ (Vj ν s j) x (merApply B (xj ν j x)))
  have hF : ‖fderiv ℝ (Vj ν s j) x (merApply B (xj ν j x))‖ ≤
      (ageA ν s ^ 2)⁻¹ * Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) *
        (1 + ‖xj ν j x‖ ^ 2 / ageA ν s) *
        ((|B 0 0| + |B 0 2| + |B 2 0| + |B 2 2|) * ‖xj ν j x‖) :=
    (gp_fderiv_Vj_norm ν s ha j x (merApply B (xj ν j x))).trans
      (mul_le_mul_of_nonneg_left (gp_merApply_norm_le B _) hpos)
  have hmv : ‖mv B (emb (Vj ν s j x))‖ ≤ (∑ i, ∑ j', |B i j'|) *
      ((ageA ν s ^ 2)⁻¹ * Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) * ‖xj ν j x‖) := by
    rw [← gp_Vj_norm_eq ν s j x]
    exact (fa_mv_norm_le B _).trans (mul_le_mul_of_nonneg_left (fa_emb_norm_le _) hKB)
  have h3 : ‖xj ν j x‖ * ((|B 0 0| + |B 0 2| + |B 2 0| + |B 2 2|) *
      (1 + ‖xj ν j x‖ ^ 2 / ageA ν s) + ∑ i, ∑ j', |B i j'|)
      ≤ ((|B 0 0| + |B 0 2| + |B 2 0| + |B 2 2|) * (1 + (ageA ν s)⁻¹) + ∑ i, ∑ j', |B i j'|) *
        (1 + ‖xj ν j x‖) ^ 3 := by
    have hzc : ‖xj ν j x‖ ≤ (1 + ‖xj ν j x‖) ^ 3 := by
      nlinarith [mul_nonneg hyn hyn, mul_nonneg (mul_nonneg hyn hyn) hyn]
    have hz3 : ‖xj ν j x‖ ^ 3 ≤ (1 + ‖xj ν j x‖) ^ 3 := pow_le_pow_left₀ hyn (by linarith) 3
    have hK0' : 0 ≤ |B 0 0| + |B 0 2| + |B 2 0| + |B 2 2| := hK0
    calc ‖xj ν j x‖ * ((|B 0 0| + |B 0 2| + |B 2 0| + |B 2 2|) *
          (1 + ‖xj ν j x‖ ^ 2 / ageA ν s) + ∑ i, ∑ j', |B i j'|)
        = (|B 0 0| + |B 0 2| + |B 2 0| + |B 2 2|) * (‖xj ν j x‖ + ‖xj ν j x‖ ^ 3 * (ageA ν s)⁻¹)
          + (∑ i, ∑ j', |B i j'|) * ‖xj ν j x‖ := by ring
      _ ≤ (|B 0 0| + |B 0 2| + |B 2 0| + |B 2 2|) * ((1 + ‖xj ν j x‖) ^ 3 +
            (1 + ‖xj ν j x‖) ^ 3 * (ageA ν s)⁻¹) + (∑ i, ∑ j', |B i j'|) * (1 + ‖xj ν j x‖) ^ 3 := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_left (add_le_add hzc (mul_le_mul_of_nonneg_right hz3 hia)) hK0'
          · exact mul_le_mul_of_nonneg_left hzc hKB
      _ = ((|B 0 0| + |B 0 2| + |B 2 0| + |B 2 2|) * (1 + (ageA ν s)⁻¹) +
            ∑ i, ∑ j', |B i j'|) * (1 + ‖xj ν j x‖) ^ 3 := by ring
  have h4 : (1 + ‖xj ν j x‖) ^ 3 ≤ (1 + |x.2|) ^ 3 * (1 + |x.1 - (j : ℝ) * cOf ν|) ^ 3 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (gp_one_add_norm ν j x) 3
  have hEb : Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s))
      ≤ Real.exp (-(1 / (4 * ageA ν s)) * (x.1 - (j : ℝ) * cOf ν) ^ 2) :=
    gp_exp_le ν s ha j x
  have hKc : 0 ≤ (ageA ν s ^ 2)⁻¹ * Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) := mul_nonneg hκ hE0
  have h1a : 0 ≤ 1 + (ageA ν s)⁻¹ := by linarith
  have hQ : 0 ≤ ((|B 0 0| + |B 0 2| + |B 2 0| + |B 2 2|) * (1 + (ageA ν s)⁻¹) +
      ∑ i, ∑ j', |B i j'|) * (ageA ν s ^ 2)⁻¹ * (1 + |x.2|) ^ 3 * (1 + |x.1 - (j : ℝ) * cOf ν|) ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (add_nonneg (mul_nonneg hK0 h1a) hKB) hκ)
      (by positivity)) (by positivity)
  calc ‖emb (fderiv ℝ (Vj ν s j) x (merApply B (xj ν j x))) + mv B (emb (Vj ν s j x))‖
      ≤ ‖emb (fderiv ℝ (Vj ν s j) x (merApply B (xj ν j x)))‖ + ‖mv B (emb (Vj ν s j x))‖ :=
        norm_add_le _ _
    _ ≤ (ageA ν s ^ 2)⁻¹ * Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) *
          (1 + ‖xj ν j x‖ ^ 2 / ageA ν s) * ((|B 0 0| + |B 0 2| + |B 2 0| + |B 2 2|) * ‖xj ν j x‖) +
        (∑ i, ∑ j', |B i j'|) * ((ageA ν s ^ 2)⁻¹ * Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) *
          ‖xj ν j x‖) := add_le_add (hemb1.trans hF) hmv
    _ = ((ageA ν s ^ 2)⁻¹ * Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s))) *
          (‖xj ν j x‖ * ((|B 0 0| + |B 0 2| + |B 2 0| + |B 2 2|) *
            (1 + ‖xj ν j x‖ ^ 2 / ageA ν s) + ∑ i, ∑ j', |B i j'|)) := by ring
    _ ≤ ((ageA ν s ^ 2)⁻¹ * Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s))) *
          (((|B 0 0| + |B 0 2| + |B 2 0| + |B 2 2|) * (1 + (ageA ν s)⁻¹) +
            ∑ i, ∑ j', |B i j'|) * (1 + ‖xj ν j x‖) ^ 3) :=
        mul_le_mul_of_nonneg_left h3 hKc
    _ ≤ ((ageA ν s ^ 2)⁻¹ * Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s))) *
          (((|B 0 0| + |B 0 2| + |B 2 0| + |B 2 2|) * (1 + (ageA ν s)⁻¹) +
            ∑ i, ∑ j', |B i j'|) * ((1 + |x.2|) ^ 3 * (1 + |x.1 - (j : ℝ) * cOf ν|) ^ 3)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h4 (by
          have : 0 ≤ (|B 0 0| + |B 0 2| + |B 2 0| + |B 2 2|) * (1 + (ageA ν s)⁻¹) := by
            apply mul_nonneg hK0; linarith
          linarith)) hKc
    _ = (((|B 0 0| + |B 0 2| + |B 2 0| + |B 2 2|) * (1 + (ageA ν s)⁻¹) +
            ∑ i, ∑ j', |B i j'|) * (ageA ν s ^ 2)⁻¹ * (1 + |x.2|) ^ 3 *
          (1 + |x.1 - (j : ℝ) * cOf ν|) ^ 3) *
          Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) := by ring
    _ ≤ (((|B 0 0| + |B 0 2| + |B 2 0| + |B 2 2|) * (1 + (ageA ν s)⁻¹) +
            ∑ i, ∑ j', |B i j'|) * (ageA ν s ^ 2)⁻¹ * (1 + |x.2|) ^ 3 *
          (1 + |x.1 - (j : ℝ) * cOf ν|) ^ 3) *
          Real.exp (-(1 / (4 * ageA ν s)) * (x.1 - (j : ℝ) * cOf ν) ^ 2) :=
        mul_le_mul_of_nonneg_left hEb hQ
    _ = (((|B 0 0| + |B 0 2| + |B 2 0| + |B 2 2|) * (1 + (ageA ν s)⁻¹) +
            ∑ i, ∑ j', |B i j'|) * (ageA ν s ^ 2)⁻¹ * (1 + |x.2|) ^ 3) *
          ((1 + |x.1 - (j : ℝ) * cOf ν|) ^ 3 *
            Real.exp (-(1 / (4 * ageA ν s)) * (x.1 - (j : ℝ) * cOf ν) ^ 2)) := by ring

theorem fATermSummable : FATermSummable := by
  intro nu mu χ A s x hν hs
  have ha : 0 < ageA nu s := by
    unfold ageA
    nlinarith [mul_pos hν hs]
  have hc : 0 < cOf nu := by
    unfold cOf
    exact inv_pos.mpr (pow_pos hν 2)
  have hα : 0 < 1 / (4 * ageA nu s) := div_pos one_pos (by linarith)
  obtain ⟨K, hK⟩ := fa_term_bound nu s ha (Bmat nu mu χ A s) x
  have hS := gp_poly_summable x.1 (1 / (4 * ageA nu s)) (cOf nu) hα hc
  refine Summable.of_norm_bounded (hS.mul_left K) (fun j => ?_)
  unfold fATerm
  exact hK j

end UnforcedLeray.Short.PartIIIb.Concrete
