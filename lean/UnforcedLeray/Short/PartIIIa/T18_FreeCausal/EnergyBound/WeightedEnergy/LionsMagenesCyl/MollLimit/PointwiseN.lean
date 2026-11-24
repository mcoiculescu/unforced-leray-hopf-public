import UnforcedLeray.Short.PartIIIa.Sub.T18_3_1_3_3
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.WeightedEnergy.LionsMagenesCyl.MollLimit.L2SqT

/-!
# Part III-a, `PartIII-a:T18/3/1/3/3/7` (`MollLimit`): pointwise limit of `N_k`

Source of record: `the November 2 reference manuscript` lines 3427-3440 and
3541-3552. On a good slice `s > 0`, `N_k(s) = ∫_cell |∇J_k b(s)|² → N(s) = ∫_cell |G(s)|²`.

Proof: `lmMoll_pd_eq` gives `∂_j (J_k b(s))_i = (J_k G(s)_{·j})_i` pointwise, so the integrand of
`N_k` is the squared tensor norm of the columns `J_k G(s)_{·j}`; then `lm_tendsto_tsq` applies,
since `J_k G(s)_{·j} → G(s)_{·j}` in `L²(cell)` by `IsLMMollifier.tendsto`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- **Pointwise limit of `N_k`** (SP 3541-3552, `k → ∞`): on a good slice `s > 0`,
`N_k(s) → N(s)`. -/
theorem lmMollPointwiseN : LMMollPointwiseN := by
  intro c ν μ F b G hD J hJ s hs hg
  have hf : LMCellL2 c (fun y => b (s, y)) := hg.1
  have hgj : ∀ j : Fin 2, LMCellL2 c (fun y i => G (s, y) i j) := hg.2.1
  have hpd : ∀ (k : ℕ) (x : ℝ × ℝ) (i j : Fin 2),
      LMPd j (fun y => LMMollU J b k s y i) x = J k (fun z i' => G (s, z) i' j) x i :=
    fun k x i j => lmMoll_pd_eq (f := fun y => b (s, y)) (g := fun j z i' => G (s, z) i' j)
      hJ hf hgj (fun i j => hD.sol.weakGrad s hs i j) k i j x
  have hN : ∀ k : ℕ, LMMollN c J b k s =
      ∫ x in B0579.cell c, tnorm2 (fun i j => J k (fun z i' => G (s, z) i' j) x i) ^ 2 := by
    intro k
    unfold LMMollN
    congr 1
    funext x
    simp only [hpd]
  have hT : ∀ (k : ℕ) (j : Fin 2), LMCellL2 c (fun x i => J k (fun z i' => G (s, z) i' j) x i) :=
    fun k j => hJ.memL2 k _ (hgj j)
  have hT₀ : ∀ j : Fin 2, LMCellL2 c (fun x i => G (s, x) i j) := hgj
  have h : ∀ j : Fin 2, Tendsto (fun k : ℕ => ∫ x in B0579.cell c, ∑ i : Fin 2,
      ‖J k (fun z i' => G (s, z) i' j) x i - G (s, x) i j‖ ^ 2) atTop (𝓝 0) :=
    fun j => hJ.tendsto _ (hgj j)
  have key := lm_tendsto_tsq (c := c)
    (T := fun k x i j => J k (fun z i' => G (s, z) i' j) x i)
    (T₀ := fun x i j => G (s, x) i j) hT hT₀ h
  have e1 : (fun k : ℕ => LMMollN c J b k s) =
      fun k : ℕ => ∫ x in B0579.cell c, tnorm2 (fun i j => J k (fun z i' => G (s, z) i' j) x i) ^ 2 :=
    funext hN
  show Tendsto (fun k : ℕ => LMMollN c J b k s) atTop
    (𝓝 (∫ x in B0579.cell c, tnorm2 (G (s, x)) ^ 2))
  rw [e1]
  exact key

end UnforcedLeray.Short.IIIa
