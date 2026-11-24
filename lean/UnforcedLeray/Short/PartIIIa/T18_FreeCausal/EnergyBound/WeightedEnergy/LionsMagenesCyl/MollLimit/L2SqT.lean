import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.WeightedEnergy.LionsMagenesCyl.MollLimit.L2Sq

/-!
# Part III-a, `PartIII-a:T18/3/1/3/3/3` (`MollLimit`): convergence of squared tensor norms

Source of record: `the November 2 reference manuscript` lines 3427-3440 and
3541-3552. Tensor (column-wise) version of `lm_tendsto_vsq`: if the columns `T_{·j}` of `T_k`
converge to those of `T₀` in `L²(cell)` (`∫_cell ∑ᵢ ‖T_k - T₀‖²_{ij} → 0` for each `j`), then
`∫_cell |T_k|²_{tensor} → ∫_cell |T₀|²_{tensor}`.

Proof: `tnorm2 S ^ 2 = ∑ⱼ vnorm2 (S_{·j}) ^ 2`, split both integrals over `j`
(`integral_finset_sum`, each column is integrable by `lmV_sq_integrable`), and apply
`lm_tendsto_vsq` to each column.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- `tnorm2 S ^ 2 = ∑ⱼ vnorm2 (S_{·j}) ^ 2` (columnwise decomposition of the tensor norm). -/
lemma lmT_tnorm2_sq (S : Fin 2 → Fin 2 → ℂ) :
    tnorm2 S ^ 2 = ∑ j : Fin 2, vnorm2 (fun i => S i j) ^ 2 := by
  unfold tnorm2
  rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _)]
  simp only [lmV_vnorm2_sq]
  exact Finset.sum_comm

/-- Integrability of the squared norm of a column of a tensor field in `L²(cell)`. -/
lemma lmT_col_integrable {c : ℝ} {S : ℝ × ℝ → Fin 2 → Fin 2 → ℂ}
    (hS : ∀ j : Fin 2, LMCellL2 c (fun x i => S x i j)) (j : Fin 2) :
    Integrable (fun x => vnorm2 (fun i => S x i j) ^ 2) (volume.restrict (B0579.cell c)) := by
  simp only [lmV_vnorm2_sq]
  apply integrable_finset_sum
  intro i _
  exact lmV_sq_integrable (hS j i)

/-- **Convergence of squared tensor norms** (SP 3427-3440, 3541-3552): column-wise
`L²(cell)`-convergence `T_k → T₀` implies `∫_cell |T_k|² → ∫_cell |T₀|²`. -/
theorem lm_tendsto_tsq {c : ℝ} {T : ℕ → ℝ × ℝ → Fin 2 → Fin 2 → ℂ} {T₀ : ℝ × ℝ → Fin 2 → Fin 2 → ℂ}
    (hT : ∀ k j, LMCellL2 c (fun x i => T k x i j)) (hT₀ : ∀ j, LMCellL2 c (fun x i => T₀ x i j))
    (h : ∀ j, Tendsto (fun k : ℕ => ∫ x in B0579.cell c, ∑ i : Fin 2, ‖T k x i j - T₀ x i j‖ ^ 2)
      atTop (𝓝 0)) :
    Tendsto (fun k : ℕ => ∫ x in B0579.cell c, tnorm2 (T k x) ^ 2) atTop
      (𝓝 (∫ x in B0579.cell c, tnorm2 (T₀ x) ^ 2)) := by
  have hk : ∀ k : ℕ, (fun x => tnorm2 (T k x) ^ 2) =
      fun x => ∑ j : Fin 2, vnorm2 (fun i => T k x i j) ^ 2 :=
    fun k => funext fun x => lmT_tnorm2_sq (T k x)
  have hk₀ : (fun x => tnorm2 (T₀ x) ^ 2) =
      fun x => ∑ j : Fin 2, vnorm2 (fun i => T₀ x i j) ^ 2 :=
    funext fun x => lmT_tnorm2_sq (T₀ x)
  have hsplit : ∀ k : ℕ, ∫ x in B0579.cell c, tnorm2 (T k x) ^ 2 =
      ∑ j : Fin 2, ∫ x in B0579.cell c, vnorm2 (fun i => T k x i j) ^ 2 := by
    intro k
    rw [hk k]
    exact integral_finset_sum _ (fun j _ => lmT_col_integrable (fun j => hT k j) j)
  have hsplit₀ : ∫ x in B0579.cell c, tnorm2 (T₀ x) ^ 2 =
      ∑ j : Fin 2, ∫ x in B0579.cell c, vnorm2 (fun i => T₀ x i j) ^ 2 := by
    rw [hk₀]
    exact integral_finset_sum _ (fun j _ => lmT_col_integrable hT₀ j)
  have hfun : (fun k : ℕ => ∫ x in B0579.cell c, tnorm2 (T k x) ^ 2) =
      fun k : ℕ => ∑ j : Fin 2, ∫ x in B0579.cell c, vnorm2 (fun i => T k x i j) ^ 2 :=
    funext hsplit
  rw [hfun, hsplit₀]
  exact tendsto_finset_sum _ (fun j _ => lm_tendsto_vsq (a := fun k x i => T k x i j)
    (a₀ := fun x i => T₀ x i j) (fun k => hT k j) (hT₀ j) (h j))

end UnforcedLeray.Short.IIIa
