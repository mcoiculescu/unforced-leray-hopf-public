import UnforcedLeray.Short.PartIIIa.Sub.T18_3_1_3_3
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.WeightedEnergy.LionsMagenesCyl.MollLimit.Pair
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.WeightedEnergy.LionsMagenesCyl.MollLimit.Twice

/-!
# Part III-a, `PartIII-a:T18/3/1/3/3/8` (`MollLimit`): pointwise limit of `R_k`

Source of record: `the November 2 reference manuscript` lines 3427-3440 and
3541-3552. On a good slice `s > 0`, `R_k(s) = ∫_cell Re⟨F(s), ∇J_k² b(s)⟩ → R(s)`.

Proof: `lmMoll_pd2_eq` gives `∂_j (J_k J_k b(s))_i = (J_k J_k G(s)_{·j})_i` pointwise, so the
integrand of `R_k` is the real pairing of `F(s)` with the columns `J_k J_k G(s)_{·j}`; then
`lm_tendsto_tpair` applies, with `J_k J_k G(s)_{·j} → G(s)_{·j}` in `L²(cell)` by
`lmMoll_twice_tendsto`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- **Pointwise limit of `R_k`** (SP 3541-3552, `k → ∞`): on a good slice `s > 0`,
`R_k(s) → R(s)`. -/
theorem lmMollPointwiseR (hS : LMSmoothWeakPd) : LMMollPointwiseR := by
  intro c ν μ F b G hD J hJ s hs hg
  have hf : LMCellL2 c (fun y => b (s, y)) := hg.1
  have hgj : ∀ j : Fin 2, LMCellL2 c (fun y i => G (s, y) i j) := hg.2.1
  have hpd : ∀ (k : ℕ) (x : ℝ × ℝ) (i j : Fin 2),
      LMPd j (fun y => J k (LMMollU J b k s) y i) x =
        J k (J k (fun z i' => G (s, z) i' j)) x i :=
    fun k x i j => lmMoll_pd2_eq hS hD.pos_c hJ (f := fun y => b (s, y))
      (g := fun j z i' => G (s, z) i' j) hf hgj (fun i j => hD.sol.weakGrad s hs i j) k i j x
  have hR : ∀ k : ℕ, LMMollR c J F b k s = ∫ x in B0579.cell c, ∑ i : Fin 2, ∑ j : Fin 2,
      ((F (s, x) i j).re * (J k (J k (fun z i' => G (s, z) i' j)) x i).re +
        (F (s, x) i j).im * (J k (J k (fun z i' => G (s, z) i' j)) x i).im) := by
    intro k
    unfold LMMollR
    congr 1
    funext x
    simp only [hpd]
  have hT : ∀ (k : ℕ) (j : Fin 2),
      LMCellL2 c (fun x i => J k (J k (fun z i' => G (s, z) i' j)) x i) :=
    fun k j => hJ.memL2 k _ (hJ.memL2 k _ (hgj j))
  have hT₀ : ∀ j : Fin 2, LMCellL2 c (fun x i => G (s, x) i j) := hgj
  have hH : ∀ j : Fin 2, LMCellL2 c (fun x i => F (s, x) i j) := hg.2.2
  have h : ∀ j : Fin 2, Tendsto (fun k : ℕ => ∫ x in B0579.cell c, ∑ i : Fin 2,
      ‖J k (J k (fun z i' => G (s, z) i' j)) x i - G (s, x) i j‖ ^ 2) atTop (𝓝 0) :=
    fun j => lmMoll_twice_tendsto hJ (hgj j)
  have key := lm_tendsto_tpair (c := c)
    (T := fun k x i j => J k (J k (fun z i' => G (s, z) i' j)) x i)
    (T₀ := fun x i j => G (s, x) i j) (H := fun x i j => F (s, x) i j) hT hT₀ hH h
  show Tendsto (fun k : ℕ => LMMollR c J F b k s) atTop
    (𝓝 (∫ x in B0579.cell c, ∑ i : Fin 2, ∑ j : Fin 2,
      ((F (s, x) i j).re * (G (s, x) i j).re + (F (s, x) i j).im * (G (s, x) i j).im)))
  simp only [hR]
  exact key

end UnforcedLeray.Short.IIIa
