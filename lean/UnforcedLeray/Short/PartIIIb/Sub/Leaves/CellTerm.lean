import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_inst_9_3
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.FATermSummable

/-!
# `PartIII-b:C/inst/9/3` leaf 1a: pointwise bound of the merid term of `f_A` (source 4963-4979, 5063-5079)

For `0 < ν ≤ 1`, `0 < s ≤ 1.1/ν` (so `a = 1 + νs ∈ [1, 2.1]`), the merid projection of the `j`-th
term `(B_mer x_j)·∇V_j + B V_j` is bounded by `68 · |B| (1 + |x_j|²)² e^{-|x_j|²/(4a)}`.

Ingredients: the explicit derivative bound `gp_fderiv_Vj_norm`, the operator bounds for `mv`,
`merApply`, `emb`, and `‖merOf v‖ ≤ 2‖v‖` (a Euclidean norm on two coordinates of the sup norm).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- `|B i j| ≤ |B|` (Frobenius norm). -/
lemma fAc_abs_le_frob (B : Mat3) (i j : Fin 3) : |B i j| ≤ frob B := by
  unfold frob
  apply Real.abs_le_sqrt
  have h1 : B i j ^ 2 ≤ ∑ j', B i j' ^ 2 :=
    Finset.single_le_sum (f := fun j' => B i j' ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ j)
  have h2 : ∑ j', B i j' ^ 2 ≤ ∑ i', ∑ j', B i' j' ^ 2 :=
    Finset.single_le_sum (f := fun i' => ∑ j', B i' j' ^ 2)
      (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ i)
  linarith

/-- `‖merOf v‖ ≤ 2 ‖v‖`. -/
lemma fAc_merOf_norm_le (v : Vec3) : ‖merOf v‖ ≤ 2 * ‖v‖ := by
  unfold merOf
  rw [EuclideanSpace.norm_eq]
  have a0 : ‖v 0‖ ≤ ‖v‖ := norm_le_pi_norm v 0
  have a2 : ‖v 2‖ ≤ ‖v‖ := norm_le_pi_norm v 2
  have hn : 0 ≤ ‖v‖ := norm_nonneg v
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  simp only [Fin.sum_univ_two]
  have e0 : ‖(!₂[v 0, v 2] : UnforcedLeray.Axi.Merid) 0‖ = ‖v 0‖ := rfl
  have e1 : ‖(!₂[v 0, v 2] : UnforcedLeray.Axi.Merid) 1‖ = ‖v 2‖ := rfl
  rw [e0, e1]
  nlinarith [mul_le_mul a0 a0 (norm_nonneg _) hn, mul_le_mul a2 a2 (norm_nonneg _) hn]

/-- `‖X‖² ≤ 2 |X|²` for the sup norm on `ℝ × ℝ`. -/
lemma fAc_norm_sq_le (X : ℝ × ℝ) : ‖X‖ ^ 2 ≤ 2 * sq2 X := by
  have h1 : ‖X‖ ≤ |X.1| + |X.2| := by
    rw [Prod.norm_def]
    apply max_le <;> simp only [Real.norm_eq_abs] <;> linarith [abs_nonneg X.1, abs_nonneg X.2]
  have h2 : ‖X‖ ^ 2 ≤ (|X.1| + |X.2|) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  have h3 : (|X.1| + |X.2|) ^ 2 ≤ 2 * (X.1 ^ 2 + X.2 ^ 2) := by
    nlinarith [sq_abs X.1, sq_abs X.2, sq_nonneg (|X.1| - |X.2|)]
  have h4 : sq2 X = X.1 ^ 2 + X.2 ^ 2 := rfl
  rw [h4]
  linarith

/-- The scalar estimate behind the constant `68`. -/
lemma fAc_scalar (κ E r s F S1 S9 a : ℝ) (hκ0 : 0 ≤ κ) (hκ : κ ≤ 1) (hE : 0 ≤ E)
    (hr : 0 ≤ r) (hs : 0 ≤ s) (hr2 : r ^ 2 ≤ 2 * s) (hF : 0 ≤ F)
    (hS1 : 0 ≤ S1) (hS1F : S1 ≤ 4 * F) (hS9 : 0 ≤ S9) (hS9F : S9 ≤ 9 * F) (ha1 : 1 ≤ a) :
    κ * E * (1 + r ^ 2 / a) * (S1 * r) + S9 * (κ * E * r) ≤ 34 * F * (1 + s) ^ 2 * E := by
  have hr' : r ≤ 2 * (1 + s) := by nlinarith
  have hq : 1 + r ^ 2 / a ≤ 2 * (1 + s) := by
    have : r ^ 2 / a ≤ r ^ 2 := div_le_self (sq_nonneg r) ha1
    nlinarith
  have t1a : κ * E * (1 + r ^ 2 / a) ≤ 1 * E * (2 * (1 + s)) :=
    mul_le_mul (mul_le_mul_of_nonneg_right hκ hE) hq
      (by positivity) (by positivity)
  have t1b : S1 * r ≤ (4 * F) * (2 * (1 + s)) := mul_le_mul hS1F hr' hr (by positivity)
  have t1 := mul_le_mul t1a t1b (by positivity) (by positivity)
  have t2a : κ * E * r ≤ 1 * E * (2 * (1 + s)) := by
    have h := mul_le_mul_of_nonneg_right hκ (mul_nonneg hE hr)
    have h' : E * r ≤ E * (2 * (1 + s)) := mul_le_mul_of_nonneg_left hr' hE
    nlinarith
  have t2 : S9 * (κ * E * r) ≤ (9 * F) * (1 * E * (2 * (1 + s))) :=
    mul_le_mul hS9F t2a (by positivity) (by positivity)
  have key2 : (9 * F) * (1 * E * (2 * (1 + s))) ≤ 18 * F * (1 + s) ^ 2 * E := by
    nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hF hE) hs) (by positivity : (0 : ℝ) ≤ 1 + s)]
  have e1 : 1 * E * (2 * (1 + s)) * ((4 * F) * (2 * (1 + s))) = 16 * F * (1 + s) ^ 2 * E := by
    ring
  nlinarith [t1, t2, key2, e1]

theorem fAcTermPointwise : FAcTermPointwise := by
  refine ⟨68, by norm_num, ?_⟩
  intro ν s B j x hν hν1 hs hsT
  have ha0 : 0 < ageA ν s := by unfold ageA; nlinarith [mul_pos hν hs]
  have ha1 : 1 ≤ ageA ν s := by unfold ageA; nlinarith [mul_pos hν hs]
  have hκ0 : 0 ≤ (ageA ν s ^ 2)⁻¹ := by positivity
  have hκ : (ageA ν s ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by nlinarith)
  have hD := gp_fderiv_Vj_norm ν s ha0 j x (merApply B (xj ν j x))
  have hM := gp_merApply_norm_le B (xj ν j x)
  have hVn := gp_Vj_norm_eq ν s j x
  have hmv := fa_mv_norm_le B (emb (Vj ν s j x))
  have he1 := fa_emb_norm_le (fderiv ℝ (Vj ν s j) x (merApply B (xj ν j x)))
  have he2 := fa_emb_norm_le (Vj ν s j x)
  have hE0 : 0 ≤ Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) := (Real.exp_pos _).le
  have hr0 : 0 ≤ ‖xj ν j x‖ := norm_nonneg _
  have hS1 : 0 ≤ |B 0 0| + |B 0 2| + |B 2 0| + |B 2 2| := by positivity
  have hS9 : 0 ≤ ∑ i, ∑ j', |B i j'| :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j' _ => abs_nonneg _
  have hS1F : |B 0 0| + |B 0 2| + |B 2 0| + |B 2 2| ≤ 4 * frob B := by
    linarith [fAc_abs_le_frob B 0 0, fAc_abs_le_frob B 0 2, fAc_abs_le_frob B 2 0,
      fAc_abs_le_frob B 2 2]
  have hS9F : ∑ i, ∑ j', |B i j'| ≤ 9 * frob B := by
    simp only [Fin.sum_univ_three]
    linarith [fAc_abs_le_frob B 0 0, fAc_abs_le_frob B 0 1, fAc_abs_le_frob B 0 2,
      fAc_abs_le_frob B 1 0, fAc_abs_le_frob B 1 1, fAc_abs_le_frob B 1 2,
      fAc_abs_le_frob B 2 0, fAc_abs_le_frob B 2 1, fAc_abs_le_frob B 2 2]
  have hFr : 0 ≤ frob B := Real.sqrt_nonneg _
  -- the derivative part
  have hDb : ‖fderiv ℝ (Vj ν s j) x (merApply B (xj ν j x))‖ ≤
      ((ageA ν s ^ 2)⁻¹ * Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) *
        (1 + ‖xj ν j x‖ ^ 2 / ageA ν s)) *
        ((|B 0 0| + |B 0 2| + |B 2 0| + |B 2 2|) * ‖xj ν j x‖) := by
    refine hD.trans ?_
    have hc0 : 0 ≤ (ageA ν s ^ 2)⁻¹ * Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) *
        (1 + ‖xj ν j x‖ ^ 2 / ageA ν s) :=
      mul_nonneg (mul_nonneg hκ0 hE0)
        (add_nonneg zero_le_one (div_nonneg (sq_nonneg _) ha0.le))
    exact mul_le_mul_of_nonneg_left hM hc0
  -- the multiplier part
  have hVb : ‖mv B (emb (Vj ν s j x))‖ ≤
      (∑ i, ∑ j', |B i j'|) * ((ageA ν s ^ 2)⁻¹ * Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) *
        ‖xj ν j x‖) := by
    refine hmv.trans ?_
    rw [← hVn]
    exact mul_le_mul_of_nonneg_left (he2) hS9
  have hT : ‖emb (fderiv ℝ (Vj ν s j) x (merApply B (xj ν j x))) +
      mv B (emb (Vj ν s j x))‖ ≤
      ‖fderiv ℝ (Vj ν s j) x (merApply B (xj ν j x))‖ + ‖mv B (emb (Vj ν s j x))‖ :=
    (norm_add_le _ _).trans (add_le_add he1 le_rfl)
  have hsc := fAc_scalar ((ageA ν s ^ 2)⁻¹) (Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)))
    ‖xj ν j x‖ (sq2 (xj ν j x)) (frob B) (|B 0 0| + |B 0 2| + |B 2 0| + |B 2 2|)
    (∑ i, ∑ j', |B i j'|) (ageA ν s) hκ0 hκ hE0 hr0 (by unfold sq2; positivity)
    (fAc_norm_sq_le _) hFr hS1 hS1F hS9 hS9F ha1
  have hmerge := fAc_merOf_norm_le
    (emb (fderiv ℝ (Vj ν s j) x (merApply B (xj ν j x))) + mv B (emb (Vj ν s j x)))
  unfold fAcTerm
  have hfin : ‖merOf (emb (fderiv ℝ (Vj ν s j) x (merApply B (xj ν j x))) +
      mv B (emb (Vj ν s j x)))‖ ≤ 2 * (34 * frob B * (1 + sq2 (xj ν j x)) ^ 2 *
        Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s))) := by
    refine hmerge.trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    refine hT.trans ?_
    have h2 := add_le_add hDb hVb
    have h3 := hsc
    linarith
  calc _ ≤ 2 * (34 * frob B * (1 + sq2 (xj ν j x)) ^ 2 *
        Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s))) := hfin
    _ = 68 * frob B * (1 + sq2 (xj ν j x)) ^ 2 *
        Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) := by ring

end UnforcedLeray.Short.PartIIIb.Concrete
