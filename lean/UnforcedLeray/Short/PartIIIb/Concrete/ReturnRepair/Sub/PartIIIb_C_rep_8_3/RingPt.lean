import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_3.Defs

/-!
# `PartIII-b:C/rep/8/3/2/4`: the pointwise size of the affine expression (source 5466-5483)

`ringAffGen` is bounded pointwise by `12(|B||w| + ν|A^y||D²w| + |A^y||∇q|)` (Frobenius norms),
using `|M_ij| ≤ frob M`, the sup-norm bound `‖mv M v‖ ≤ 3K‖v‖` for entries bounded by `K`, and
`‖merOf u‖ ≤ 2‖u‖`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Each entry of a matrix is bounded by its Frobenius norm. -/
theorem rp_entry_le_frob (C : Mat3) (i j : Fin 3) : |C i j| ≤ frob C := by
  unfold frob
  have h1 : C i j ^ 2 ≤ ∑ i', ∑ j', C i' j' ^ 2 := by
    calc C i j ^ 2 ≤ ∑ j', C i j' ^ 2 :=
          Finset.single_le_sum (f := fun j' => C i j' ^ 2) (fun k _ => sq_nonneg _)
            (Finset.mem_univ j)
      _ ≤ ∑ i', ∑ j', C i' j' ^ 2 :=
          Finset.single_le_sum (f := fun i' => ∑ j', C i' j' ^ 2)
            (fun k _ => Finset.sum_nonneg (fun l _ => sq_nonneg _)) (Finset.mem_univ i)
  calc |C i j| = Real.sqrt (C i j ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (∑ i', ∑ j', C i' j' ^ 2) := Real.sqrt_le_sqrt h1

/-- A matrix with entries bounded by `K` acts on the sup norm with constant `3K`. -/
theorem rp_mv_norm_le (C : Mat3) (K : ℝ) (hK : ∀ i j, |C i j| ≤ K) (v : Vec3) :
    ‖mv C v‖ ≤ 3 * K * ‖v‖ := by
  have hv : ∀ j, |v j| ≤ ‖v‖ := fun j => by
    rw [← Real.norm_eq_abs]; exact norm_le_pi_norm v j
  have hK0 : 0 ≤ K := le_trans (abs_nonneg _) (hK 0 0)
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg (mul_nonneg (by norm_num) hK0) (norm_nonneg _))).2
    (fun i => ?_)
  rw [Real.norm_eq_abs]
  unfold mv
  calc |∑ j, C i j * v j| ≤ ∑ j, |C i j * v j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin 3, K * ‖v‖ := Finset.sum_le_sum (fun j _ => by
          rw [abs_mul]; exact mul_le_mul (hK i j) (hv j) (abs_nonneg _) hK0)
    _ = 3 * K * ‖v‖ := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          push_cast; ring

/-- The embedding `(v₁, v₂) ↦ (v₁, 0, v₂)` does not increase the norm. -/
theorem rp_emb_norm_le (v : ℝ × ℝ) : ‖emb v‖ ≤ ‖v‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 (fun i => ?_)
  fin_cases i
  · simpa [emb] using norm_fst_le v
  · simp [emb, norm_nonneg]
  · simpa [emb] using norm_snd_le v

/-- Embedded meridional vectors under a bounded matrix. -/
theorem rp_mv_emb_le (C : Mat3) (K : ℝ) (hK : ∀ i j, |C i j| ≤ K) (v : ℝ × ℝ) :
    ‖mv C (emb v)‖ ≤ 3 * K * ‖v‖ := by
  have hK0 : 0 ≤ K := le_trans (abs_nonneg _) (hK 0 0)
  exact (rp_mv_norm_le C K hK (emb v)).trans
    (mul_le_mul_of_nonneg_left (rp_emb_norm_le v) (mul_nonneg (by norm_num) hK0))

/-- The contracted Hessian is bounded by the Frobenius norm times the flat Hessian size. -/
theorem rp_hessContr_norm_le (A : Mat3) (V : ℝ × ℝ → ℝ × ℝ) (x : ℝ × ℝ) :
    ‖hessContr A V x‖ ≤ frob A * flatHessNorm V x := by
  unfold hessContr flatHessNorm
  have h2 : ∀ a b : Fin 2,
      ‖A (mi a) (mi b) • fderiv ℝ (fun y => fderiv ℝ V y (ei b)) x (ei a)‖ ≤
        frob A * ‖fderiv ℝ (fun y => fderiv ℝ V y (ei b)) x (ei a)‖ := by
    intro a b
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (rp_entry_le_frob _ _ _) (norm_nonneg _)
  calc ‖emb (∑ a : Fin 2, ∑ b : Fin 2,
          A (mi a) (mi b) • fderiv ℝ (fun y => fderiv ℝ V y (ei b)) x (ei a))‖
      ≤ ‖∑ a : Fin 2, ∑ b : Fin 2,
          A (mi a) (mi b) • fderiv ℝ (fun y => fderiv ℝ V y (ei b)) x (ei a)‖ :=
        rp_emb_norm_le _
    _ ≤ ∑ a : Fin 2, ‖∑ b : Fin 2,
          A (mi a) (mi b) • fderiv ℝ (fun y => fderiv ℝ V y (ei b)) x (ei a)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ a : Fin 2, ∑ b : Fin 2,
          ‖A (mi a) (mi b) • fderiv ℝ (fun y => fderiv ℝ V y (ei b)) x (ei a)‖ :=
        Finset.sum_le_sum (fun a _ => norm_sum_le _ _)
    _ ≤ ∑ a : Fin 2, ∑ b : Fin 2,
          frob A * ‖fderiv ℝ (fun y => fderiv ℝ V y (ei b)) x (ei a)‖ :=
        Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun b _ => h2 a b))
    _ = frob A * ∑ a : Fin 2, ∑ b : Fin 2,
          ‖fderiv ℝ (fun y => fderiv ℝ V y (ei b)) x (ei a)‖ := by
        simp only [Finset.mul_sum]

/-- `‖merOf u‖ ≤ 2‖u‖` (the two meridional components of a sup-norm vector). -/
theorem rp_merOf_norm_le (u : Vec3) : ‖merOf u‖ ≤ 2 * ‖u‖ := by
  have h0 : ‖u 0‖ ≤ ‖u‖ := norm_le_pi_norm u 0
  have h2 : ‖u 2‖ ≤ ‖u‖ := norm_le_pi_norm u 2
  unfold merOf
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  have e0 : |u 0| ≤ ‖u‖ := by rw [← Real.norm_eq_abs]; exact h0
  have e2 : |u 2| ≤ ‖u‖ := by rw [← Real.norm_eq_abs]; exact h2
  have a0 : u 0 ^ 2 ≤ ‖u‖ ^ 2 := by
    nlinarith [sq_abs (u 0), mul_le_mul e0 e0 (abs_nonneg _) (norm_nonneg _)]
  have a2 : u 2 ^ 2 ≤ ‖u‖ ^ 2 := by
    nlinarith [sq_abs (u 2), mul_le_mul e2 e2 (abs_nonneg _) (norm_nonneg _)]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Real.norm_eq_abs,
    sq_abs]
  nlinarith [a0, a2, sq_nonneg ‖u‖]

/-- **Pointwise size of the affine expression** (`RingAffGenPt`, source 5466-5483). -/
theorem ringAffGenPt : RingAffGenPt := by
  intro ν μ χf A w q s x hν
  have hfB : 0 ≤ frob (Bmat ν μ χf A s) := Real.sqrt_nonneg _
  have hfA : 0 ≤ frob (Ay ν χf A s) := Real.sqrt_nonneg _
  have hH : 0 ≤ flatHessNorm (w s) x :=
    Finset.sum_nonneg (fun a _ => Finset.sum_nonneg (fun b _ => norm_nonneg _))
  have hSym : ∀ i j, |(fun a b => Ay ν χf A s a b + Ay ν χf A s b a) i j| ≤
      2 * frob (Ay ν χf A s) := fun i j => by
    have h1 := rp_entry_le_frob (Ay ν χf A s) i j
    have h2 := rp_entry_le_frob (Ay ν χf A s) j i
    have h3 := abs_add_le (Ay ν χf A s i j) (Ay ν χf A s j i)
    show |Ay ν χf A s i j + Ay ν χf A s j i| ≤ 2 * frob (Ay ν χf A s)
    linarith
  have h2ν : (0 : ℝ) ≤ 2 * ν := by linarith
  have hT1 : ‖(2 : ℝ) • mv (Bmat ν μ χf A s) (emb (w s x))‖ ≤
      6 * (frob (Bmat ν μ χf A s) * ‖w s x‖) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    have := rp_mv_emb_le (Bmat ν μ χf A s) (frob (Bmat ν μ χf A s))
      (fun i j => rp_entry_le_frob _ i j) (w s x)
    linarith
  have hT2 : ‖(2 * ν) • hessContr (Ay ν χf A s) (w s) x‖ ≤
      2 * ν * (frob (Ay ν χf A s) * flatHessNorm (w s) x) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg h2ν]
    exact mul_le_mul_of_nonneg_left (rp_hessContr_norm_le _ _ _) h2ν
  have hT3 : ‖mv (fun a b => Ay ν χf A s a b + Ay ν χf A s b a) (emb (mgrad (q s) x))‖ ≤
      6 * (frob (Ay ν χf A s) * ‖mgrad (q s) x‖) := by
    have := rp_mv_emb_le _ (2 * frob (Ay ν χf A s)) hSym (mgrad (q s) x)
    linarith
  have hu : ‖ringAffGen ν μ χf A w q s x‖ ≤
      6 * (frob (Bmat ν μ χf A s) * ‖w s x‖) +
        2 * ν * (frob (Ay ν χf A s) * flatHessNorm (w s) x) +
        6 * (frob (Ay ν χf A s) * ‖mgrad (q s) x‖) := by
    unfold ringAffGen
    exact (norm_sub_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add hT1 hT2)) hT3)
  have hm := rp_merOf_norm_le (ringAffGen ν μ χf A w q s x)
  have hνA : 0 ≤ ν * (frob (Ay ν χf A s) * flatHessNorm (w s) x) :=
    mul_nonneg hν (mul_nonneg hfA hH)
  nlinarith [hm, hu, hνA, mul_nonneg hfB (norm_nonneg (w s x)),
    mul_nonneg hfA (norm_nonneg (mgrad (q s) x))]

end UnforcedLeray.Short.PartIIIb.Concrete
