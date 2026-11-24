import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_inst_10_3
import UnforcedLeray.Short.PartIIIb.Sub.Leaves.EAcHessUnif
import UnforcedLeray.Short.PartIIIb.Sub.Leaves.EAcMgradUnif
import UnforcedLeray.Short.PartIIIb.Sub.Leaves.CellTerm

/-!
# `PartIII-b:C/inst/10/3/3`: pointwise bound of the meridional part of the `j`-th term (source 5063-5079)

`eAcTerm = 2 B V_j + 2ν hessContr C V_j - (C + Cᵀ) ∇p_j`. Each piece is bounded by the operator
bounds `fa_mv_norm_le`, `fa_emb_norm_le`, the entrywise bound `fAc_abs_le_frob`, the uniform
second-derivative bound `hessVjUnif`, the uniform gradient bound `mgradPjUnif`, and
`fAc_merOf_norm_le`. The Gaussian factor is `(1 + |x_j|²)² e^{-|x_j|²/(4a)}`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- A `3 × 3` matrix with entries bounded by `c` has `∑ |M i j| ≤ 9 c`. -/
lemma eAcSum3x3_le (M : Mat3) (c : ℝ) (h : ∀ i j, |M i j| ≤ c) :
    ∑ i, ∑ j, |M i j| ≤ 9 * c := by
  simp only [Fin.sum_univ_three]
  linarith [h 0 0, h 0 1, h 0 2, h 1 0, h 1 1, h 1 2, h 2 0, h 2 1, h 2 2]

theorem eAcTermPointwise : EAcTermPointwise := by
  obtain ⟨K, hK0, hK⟩ := hessVjUnif
  obtain ⟨K', hK'0, hK'⟩ := mgradPjUnif
  unfold EAcTermPointwise
  refine ⟨2 * (18 + 8 * K + 18 * K'), by linarith, ?_⟩
  intro ν s B C j x hν hν1 hs hsT
  have ha1 : 1 ≤ ageA ν s := by unfold ageA; nlinarith [mul_pos hν hs]
  have ha0 : 0 < ageA ν s := by linarith
  have ha2 : 1 ≤ ageA ν s ^ 2 := by nlinarith
  have hinv : (ageA ν s ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ ha2
  have hE0 : 0 ≤ Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) := (Real.exp_pos _).le
  have hX : 0 ≤ (1 + sq2 (xj ν j x)) ^ 2 * Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) :=
    mul_nonneg (by positivity) hE0
  have hfB : 0 ≤ frob B := Real.sqrt_nonneg _
  have hfC : 0 ≤ frob C := Real.sqrt_nonneg _
  -- sup norm of x_j against the polynomial weight
  have hxn : ‖xj ν j x‖ ≤ (1 + sq2 (xj ν j x)) ^ 2 := by
    have hn2 := mu_norm_sq_le (xj ν j x)
    have hQ := mu_sq2_nonneg (xj ν j x)
    nlinarith [sq_nonneg (‖xj ν j x‖ - 1 / 2), hn2, hQ, sq_nonneg (sq2 (xj ν j x))]
  -- ‖V_j‖ ≤ (1+|x_j|²)² e^{-|x_j|²/(4a)}
  have hVG : ‖Vj ν s j x‖ ≤
      (1 + sq2 (xj ν j x)) ^ 2 * Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) := by
    rw [gp_Vj_norm_eq]
    have h1 : (ageA ν s ^ 2)⁻¹ * Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) ≤
        1 * Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) :=
      mul_le_mul_of_nonneg_right hinv hE0
    calc (ageA ν s ^ 2)⁻¹ * Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) * ‖xj ν j x‖
        ≤ (1 * Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s))) * (1 + sq2 (xj ν j x)) ^ 2 :=
          mul_le_mul h1 hxn (norm_nonneg _) (by positivity)
      _ = (1 + sq2 (xj ν j x)) ^ 2 * Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) := by ring
  -- the multiplier term `2 B V_j`
  have hSB : ∑ i, ∑ j', |B i j'| ≤ 9 * frob B :=
    eAcSum3x3_le B _ (fun i j' => fAc_abs_le_frob B i j')
  have h9B : 0 ≤ 9 * frob B := mul_nonneg (by norm_num) hfB
  have hmvB : ‖mv B (emb (Vj ν s j x))‖ ≤
      9 * frob B * ((1 + sq2 (xj ν j x)) ^ 2 * Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s))) :=
    calc ‖mv B (emb (Vj ν s j x))‖ ≤ (∑ i, ∑ j', |B i j'|) * ‖emb (Vj ν s j x)‖ :=
          fa_mv_norm_le B _
      _ ≤ (9 * frob B) * ‖Vj ν s j x‖ :=
          mul_le_mul hSB (fa_emb_norm_le _) (norm_nonneg _) h9B
      _ ≤ (9 * frob B) * ((1 + sq2 (xj ν j x)) ^ 2 * Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s))) :=
          mul_le_mul_of_nonneg_left hVG h9B
  have hT1 : ‖(2 : ℝ) • mv B (emb (Vj ν s j x))‖ ≤
      2 * (9 * frob B * ((1 + sq2 (xj ν j x)) ^ 2 * Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)))) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact mul_le_mul_of_nonneg_left hmvB (by norm_num)
  -- the Hessian term `2ν hessContr C V_j`
  have hterm : ∀ a b : Fin 2,
      ‖C (mi a) (mi b) • fderiv ℝ (fun y => fderiv ℝ (Vj ν s j) y (ei b)) x (ei a)‖ ≤
        frob C * (K * ((1 + sq2 (xj ν j x)) ^ 2 * Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)))) := by
    intro a b
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul (fAc_abs_le_frob C _ _) (hK ν s hν hν1 hs hsT j x a b) (norm_nonneg _) hfC
  have hHess : ‖hessContr C (Vj ν s j) x‖ ≤
      4 * (frob C * (K * ((1 + sq2 (xj ν j x)) ^ 2 * Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s))))) := by
    unfold hessContr
    refine (fa_emb_norm_le _).trans ?_
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum fun a _ => norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => hterm a b).trans ?_
    simp only [Fin.sum_univ_two]
    linarith
  have hT2 : ‖(2 * ν) • hessContr C (Vj ν s j) x‖ ≤
      8 * (frob C * (K * ((1 + sq2 (xj ν j x)) ^ 2 * Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s))))) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith : (0 : ℝ) < 2 * ν)]
    have hm := mul_le_mul_of_nonneg_right hν1 (norm_nonneg (hessContr C (Vj ν s j) x))
    nlinarith [hHess, hm, norm_nonneg (hessContr C (Vj ν s j) x)]
  -- the gradient term `(C + Cᵀ) ∇p_j`
  have hMC : ∀ i j' : Fin 3, |(fun a b => C a b + C b a) i j'| ≤ 2 * frob C := by
    intro i j'
    show |C i j' + C j' i| ≤ 2 * frob C
    have := abs_add_le (C i j') (C j' i)
    linarith [fAc_abs_le_frob C i j', fAc_abs_le_frob C j' i]
  have hSM : ∑ i, ∑ j', |(fun a b => C a b + C b a) i j'| ≤ 9 * (2 * frob C) :=
    eAcSum3x3_le _ _ hMC
  have h18 : 0 ≤ 9 * (2 * frob C) := by linarith
  have hT3 : ‖mv (fun a b => C a b + C b a) (emb (mgrad (pj ν s j) x))‖ ≤
      9 * (2 * frob C) * (K' * ((1 + sq2 (xj ν j x)) ^ 2 * Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)))) :=
    calc ‖mv (fun a b => C a b + C b a) (emb (mgrad (pj ν s j) x))‖
        ≤ (∑ i, ∑ j', |(fun a b => C a b + C b a) i j'|) * ‖emb (mgrad (pj ν s j) x)‖ :=
          fa_mv_norm_le _ _
      _ ≤ (9 * (2 * frob C)) * ‖mgrad (pj ν s j) x‖ :=
          mul_le_mul hSM (fa_emb_norm_le _) (norm_nonneg _) h18
      _ ≤ (9 * (2 * frob C)) * (K' * ((1 + sq2 (xj ν j x)) ^ 2 * Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)))) :=
          mul_le_mul_of_nonneg_left (hK' ν s hν hν1 hs hsT j x) h18
  -- the full term
  have hnorm : ‖eAcTerm ν s B C j x‖ ≤
      2 * (9 * frob B * ((1 + sq2 (xj ν j x)) ^ 2 * Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)))) +
        8 * (frob C * (K * ((1 + sq2 (xj ν j x)) ^ 2 * Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s))))) +
      9 * (2 * frob C) * (K' * ((1 + sq2 (xj ν j x)) ^ 2 * Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)))) := by
    unfold eAcTerm
    exact (norm_sub_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add hT1 hT2)) hT3)
  have hmer : ‖merOf (eAcTerm ν s B C j x)‖ ≤ 2 * ‖eAcTerm ν s B C j x‖ :=
    fAc_merOf_norm_le _
  refine hmer.trans ?_
  have hP0 : 0 ≤ (1 + sq2 (xj ν j x)) ^ 2 * Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) := hX
  nlinarith [mul_le_mul_of_nonneg_left hnorm (by norm_num : (0 : ℝ) ≤ 2),
    mul_nonneg (mul_nonneg hK0 hfB) hX, mul_nonneg (mul_nonneg hK'0 hfB) hX,
    mul_nonneg hfC hX, mul_nonneg (mul_nonneg hK0 hfC) hX]

end UnforcedLeray.Short.PartIIIb.Concrete
