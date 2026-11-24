import UnforcedLeray.Short.PartIIIa.Sub.T18_3_1_3_3

/-!
# Part III-a, `PartIII-a:T18/3/1/3/3/9` (`MollLimit`): domination of `E_k`, `N_k`

Source of record: `the November 2 reference manuscript` lines 3427-3440 and
3541-3552. On a good slice, `0 ≤ E_k ≤ E` and `0 ≤ N_k ≤ N` (`LMMollDomEN`).
Contraction (`IsLMMollifier.contr`) on `b(s)` gives `E_k ≤ E`; on each column `G(s)_{·j}` of the
weak gradient, after `lmMoll_pd_eq`, gives `N_k ≤ N` after summing over `j`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- `vnorm2 v ^ 2 = ∑ i ‖v i‖²`. -/
lemma domEN_vnorm2_sq (v : Fin 2 → ℂ) : vnorm2 v ^ 2 = ∑ i : Fin 2, ‖v i‖ ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _))

/-- `tnorm2 T ^ 2 = ∑ i ∑ j ‖T i j‖²`. -/
lemma domEN_tnorm2_sq (T : Fin 2 → Fin 2 → ℂ) :
    tnorm2 T ^ 2 = ∑ i : Fin 2, ∑ j : Fin 2, ‖T i j‖ ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg _)))

/-- For `f ∈ L²(cell)`, `x ↦ ∑ i ‖f x i‖²` is integrable on the cell. -/
lemma domEN_integrable_sum {c : ℝ} {f : LMSpField} (hf : LMCellL2 c f) :
    Integrable (fun x => ∑ i : Fin 2, ‖f x i‖ ^ 2) (volume.restrict (B0579.cell c)) := by
  refine integrable_finsetSum Finset.univ (fun i _ => ?_)
  exact (memLp_two_iff_integrable_sq_norm (hf i).aestronglyMeasurable).mp (hf i)

/-- **Domination of `E_k`, `N_k`**: on a good slice, `0 ≤ E_k(s) ≤ E(s)` and `0 ≤ N_k(s) ≤ N(s)`. -/
theorem lmMollDomEN : LMMollDomEN := by
  intro c ν μ F b G hD J hJ s hs hgs k
  unfold LMGoodSlice at hgs
  obtain ⟨hb, hcol, -⟩ := hgs
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact integral_nonneg (fun x => sq_nonneg _)
  · unfold LMMollE energyE
    simp only [domEN_vnorm2_sq]
    exact hJ.contr k (fun y => b (s, y)) hb
  · exact integral_nonneg (fun x => sq_nonneg _)
  · -- pointwise: the columns of `∇J_k b(s)` are `J_k G(s)_{·j}`
    have hA : ∀ (x : ℝ × ℝ) (i j : Fin 2),
        LMPd j (fun y => LMMollU J b k s y i) x = J k (fun y i' => G (s, y) i' j) x i :=
      fun x i j => lmMoll_pd_eq (f := fun y => b (s, y)) (g := fun j y i => G (s, y) i j) hJ hb
        hcol (fun i' j' => hD.sol.weakGrad s hs i' j') k i j x
    have hT : ∀ x : ℝ × ℝ, tnorm2 (fun i j => LMPd j (fun y => LMMollU J b k s y i) x) ^ 2 =
        ∑ j : Fin 2, ∑ i : Fin 2, ‖J k (fun y i' => G (s, y) i' j) x i‖ ^ 2 := by
      intro x
      rw [domEN_tnorm2_sq]
      simp only [hA]
      exact Finset.sum_comm
    have hNeq : LMMollN c J b k s = ∫ x in B0579.cell c, ∑ j : Fin 2, ∑ i : Fin 2,
        ‖J k (fun y i' => G (s, y) i' j) x i‖ ^ 2 := by
      unfold LMMollN
      exact integral_congr_ae (ae_of_all _ (fun x => hT x))
    have hint : ∀ j : Fin 2, Integrable (fun x => ∑ i : Fin 2,
        ‖J k (fun y i' => G (s, y) i' j) x i‖ ^ 2) (volume.restrict (B0579.cell c)) :=
      fun j => domEN_integrable_sum (hJ.memL2 k _ (hcol j))
    have hL : ∫ x in B0579.cell c, ∑ j : Fin 2, ∑ i : Fin 2,
        ‖J k (fun y i' => G (s, y) i' j) x i‖ ^ 2
        = ∑ j : Fin 2, ∫ x in B0579.cell c, ∑ i : Fin 2,
          ‖J k (fun y i' => G (s, y) i' j) x i‖ ^ 2 :=
      integral_finsetSum Finset.univ (fun j _ => hint j)
    have hRHS : energyN c G s = ∑ j : Fin 2, ∫ x in B0579.cell c, ∑ i : Fin 2,
        ‖G (s, x) i j‖ ^ 2 := by
      have hI : ∫ x in B0579.cell c, ∑ j : Fin 2, ∑ i : Fin 2, ‖G (s, x) i j‖ ^ 2
          = ∑ j : Fin 2, ∫ x in B0579.cell c, ∑ i : Fin 2, ‖G (s, x) i j‖ ^ 2 :=
        integral_finsetSum Finset.univ (fun j _ => domEN_integrable_sum (hcol j))
      unfold energyN
      simp only [domEN_tnorm2_sq]
      rw [← hI]
      exact integral_congr_ae (ae_of_all _ (fun x => Finset.sum_comm))
    have hbd : ∀ j : Fin 2, ∫ x in B0579.cell c, ∑ i : Fin 2,
        ‖J k (fun y i' => G (s, y) i' j) x i‖ ^ 2 ≤ ∫ x in B0579.cell c, ∑ i : Fin 2,
          ‖G (s, x) i j‖ ^ 2 :=
      fun j => hJ.contr k _ (hcol j)
    rw [hNeq, hL, hRHS]
    exact Finset.sum_le_sum (fun j _ => hbd j)

end UnforcedLeray.Short.IIIa
