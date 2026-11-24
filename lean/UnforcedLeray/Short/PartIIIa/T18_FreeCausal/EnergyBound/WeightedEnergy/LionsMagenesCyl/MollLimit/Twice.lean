import UnforcedLeray.Short.PartIIIa.Sub.T18_3_1_3_3

/-!
# Part III-a, `PartIII-a:T18/3/1/3/3/5` (`MollLimit`): the twice mollified field converges

Source of record: `the November 2 reference manuscript` lines 3427-3440 and
3541-3552. For `f ∈ L²(cell)`, `J_k J_k f → f` in `L²(cell)`.

Proof: with `d_k = J_k f - f` and `h_k = d_k` (an `L²(cell)` field), linearity gives
`J_k J_k f - f = J_k h_k + d_k`. Then `‖a + b‖² ≤ 2‖a‖² + 2‖b‖²`, the contraction
`∫|J_k h_k|² ≤ ∫|h_k|² = ∫|d_k|²` bounds the first term, and `E_k ≤ 4 ∫|d_k|² → 0`
(`squeeze_zero`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

lemma lmTw_sq_integrable {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℂ}
    (hf : MemLp f 2 μ) : Integrable (fun x => ‖f x‖ ^ 2) μ := by
  have h := hf.integrable_norm_rpow (p := 2) two_ne_zero (by norm_num)
  simpa [Real.rpow_two] using h

/-- `‖a + b‖² ≤ 2‖a‖² + 2‖b‖²`. -/
lemma lmTw_norm_add_sq_le (a b : ℂ) : ‖a + b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  have h1 : ‖a + b‖ ≤ ‖a‖ + ‖b‖ := norm_add_le a b
  have h2 := mul_self_le_mul_self (norm_nonneg _) h1
  nlinarith [sq_nonneg (‖a‖ - ‖b‖)]

/-- Integrability of the squared vector norm of an `L²(cell)` field. -/
lemma lmTw_vec_integrable {c : ℝ} {g : LMSpField} (hg : LMCellL2 c g) :
    Integrable (fun x => ∑ i : Fin 2, ‖g x i‖ ^ 2) (volume.restrict (B0579.cell c)) :=
  integrable_finsetSum _ (fun i _ => lmTw_sq_integrable (f := fun x => g x i) (hg i))

/-- **Twice mollified convergence** (SP 3427-3440, 3541-3552): `J_k J_k f → f` in `L²(cell)`. -/
theorem lmMoll_twice_tendsto {c : ℝ} {J : ℕ → LMSpField → LMSpField} (hJ : IsLMMollifier c J)
    {f : LMSpField} (hf : LMCellL2 c f) :
    Tendsto (fun k : ℕ => ∫ x in B0579.cell c, ∑ i : Fin 2, ‖J k (J k f) x i - f x i‖ ^ 2) atTop
      (𝓝 0) := by
  -- the difference field `d_k = J_k f - f` and its mollification `J_k d_k`
  have hd : ∀ k, LMCellL2 c (fun x i => J k f x i - f x i) := fun k i =>
    ((hJ.memL2 k f hf) i).sub (hf i)
  have hJg : ∀ k, LMCellL2 c (J k f) := fun k => hJ.memL2 k f hf
  have hsplit : ∀ k, J k (fun x i => J k f x i - f x i) =
      fun x i => J k (J k f) x i - J k f x i := by
    intro k
    have e1 : (fun x i => J k f x i - f x i) =
        (fun x i => J k f x i + (-1 : ℂ) * f x i) := by
      funext x i
      ring
    have hg : LMCellL2 c (fun x i => (-1 : ℂ) * f x i) := fun i => (hf i).const_mul _
    rw [e1, hJ.add k (J k f) (fun x i => (-1 : ℂ) * f x i) (hJg k) hg, hJ.smul k (-1) f hf]
    funext x i
    simp only [neg_one_mul]
    ring
  have hdec : ∀ k x i, J k (J k f) x i - f x i =
      J k (fun y j => J k f y j - f y j) x i + (J k f x i - f x i) := by
    intro k x i
    rw [hsplit k]
    ring
  -- pointwise and integrated estimates
  have hpt : ∀ k x, ∑ i : Fin 2, ‖J k (J k f) x i - f x i‖ ^ 2 ≤
      2 * ∑ i : Fin 2, ‖J k (fun y j => J k f y j - f y j) x i‖ ^ 2 +
        2 * ∑ i : Fin 2, ‖J k f x i - f x i‖ ^ 2 := by
    intro k x
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum (fun i _ => ?_)
    rw [hdec k x i]
    exact lmTw_norm_add_sq_le _ _
  have hL : ∀ k, LMCellL2 c (fun x i => J k (J k f) x i - f x i) := fun k i =>
    ((hJ.memL2 k (J k f) (hJg k)) i).sub (hf i)
  have hint : ∀ k, ∫ x in B0579.cell c, ∑ i : Fin 2, ‖J k (J k f) x i - f x i‖ ^ 2 ≤
      4 * ∫ x in B0579.cell c, ∑ i : Fin 2, ‖J k f x i - f x i‖ ^ 2 := by
    intro k
    have hA : ∫ x in B0579.cell c, ∑ i : Fin 2, ‖J k (fun y j => J k f y j - f y j) x i‖ ^ 2 ≤
        ∫ x in B0579.cell c, ∑ i : Fin 2, ‖J k f x i - f x i‖ ^ 2 :=
      hJ.contr k _ (hd k)
    have hI1 : Integrable (fun x => ∑ i : Fin 2, ‖J k (fun y j => J k f y j - f y j) x i‖ ^ 2)
        (volume.restrict (B0579.cell c)) :=
      lmTw_vec_integrable (hJ.memL2 k _ (hd k))
    have hI2 : Integrable (fun x => ∑ i : Fin 2, ‖J k f x i - f x i‖ ^ 2)
        (volume.restrict (B0579.cell c)) :=
      lmTw_vec_integrable (hd k)
    have hLint := lmTw_vec_integrable (hL k)
    have hE : ∫ x in B0579.cell c, ∑ i : Fin 2, ‖J k (J k f) x i - f x i‖ ^ 2 ≤
        ∫ x in B0579.cell c, (2 * ∑ i : Fin 2, ‖J k (fun y j => J k f y j - f y j) x i‖ ^ 2 +
          2 * ∑ i : Fin 2, ‖J k f x i - f x i‖ ^ 2) :=
      integral_mono hLint ((hI1.const_mul 2).add (hI2.const_mul 2)) (fun x => hpt k x)
    rw [integral_add (hI1.const_mul 2) (hI2.const_mul 2), integral_const_mul,
      integral_const_mul] at hE
    linarith
  have hlim : Tendsto (fun k : ℕ => 4 * ∫ x in B0579.cell c, ∑ i : Fin 2,
      ‖J k f x i - f x i‖ ^ 2) atTop (𝓝 0) := by
    have := (hJ.tendsto f hf).const_mul 4
    rw [mul_zero] at this
    exact this
  refine squeeze_zero (fun k => ?_) (fun k => hint k) hlim
  exact integral_nonneg (fun x => Finset.sum_nonneg fun i _ => sq_nonneg _)

end UnforcedLeray.Short.IIIa
