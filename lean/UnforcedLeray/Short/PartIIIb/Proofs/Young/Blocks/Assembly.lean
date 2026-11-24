import UnforcedLeray.Short.PartIIIb.Concrete.YoungBlocks
import UnforcedLeray.Short.PartIIIb.Proofs.Young.Blocks.Ybe1
import UnforcedLeray.Short.PartIIIb.Proofs.Young.Blocks.Ybe2
import UnforcedLeray.Short.PartIIIb.Proofs.Young.Blocks.Ybe3
import UnforcedLeray.Short.PartIIIb.Proofs.Young.Blocks.Ybe4

/-!
# Assembly of the four block estimates into `YoungBlockEstimates` (source 4376-4411)

The four parts `YBE1`..`YBE4` (`Ybe1.lean`..`Ybe4.lean`) are combined: the constant is the maximum of
the four constants and the index is the maximum of the four indices. Each part is monotone in its
constant because `ν n > 0` and the norms are nonnegative.
-/

set_option autoImplicit false

noncomputable section

open Filter Topology Set MeasureTheory

namespace UnforcedLeray.Short.PartIIIb

namespace ConcreteYF

theorem blocksFromRetained_of_gronwall (pk : ℕ → YoungPkg) (ν : ℕ → ℝ) (lam κ : ℂ) (Sg α : ℝ)
    (δ : ℕ → ℝ) (hGr : ConcreteYF.BlockGronwall) :
    ConcreteYF.BlocksFromRetained pk ν lam κ Sg α δ := by
  unfold ConcreteYF.BlocksFromRetained ConcreteYF.YoungBlockEstimates
  intro hS
  obtain ⟨C1, N1, h1⟩ := ybe1_holds pk ν lam κ Sg α δ hGr hS
  obtain ⟨C2, N2, h2⟩ := ybe2_holds pk ν lam κ Sg α δ hGr hS
  obtain ⟨C3, N3, h3⟩ := ybe3_holds pk ν lam κ Sg α δ hGr hS
  obtain ⟨C4, N4, h4⟩ := ybe4_holds pk ν lam κ Sg α δ hGr hS
  have hν : ∀ n, 0 ≤ ν n := fun n => (hS.hyp.1 n).le
  refine ⟨max (max C1 C2) (max C3 C4), max (max N1 N2) (max N3 N4), ?_⟩
  intro n hn t ht
  have hn1 : N1 ≤ n := le_trans (le_trans (le_max_left N1 N2) (le_max_left _ _)) hn
  have hn2 : N2 ≤ n := le_trans (le_trans (le_max_right N1 N2) (le_max_left _ _)) hn
  have hn3 : N3 ≤ n := le_trans (le_trans (le_max_left N3 N4) (le_max_right _ _)) hn
  have hn4 : N4 ≤ n := le_trans (le_trans (le_max_right N3 N4) (le_max_right _ _)) hn
  have hc1 : C1 ≤ max (max C1 C2) (max C3 C4) := le_trans (le_max_left C1 C2) (le_max_left _ _)
  have hc2 : C2 ≤ max (max C1 C2) (max C3 C4) := le_trans (le_max_right C1 C2) (le_max_left _ _)
  have hc3 : C3 ≤ max (max C1 C2) (max C3 C4) := le_trans (le_max_left C3 C4) (le_max_right _ _)
  have hc4 : C4 ≤ max (max C1 C2) (max C3 C4) := le_trans (le_max_right C3 C4) (le_max_right _ _)
  have hνn := hν n
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i j
    refine (h1 n hn1 t ht i j).trans ?_
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hc1 hνn) (norm_nonneg _)
  · intro j
    refine (h2 n hn2 t ht j).trans ?_
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hc2 hνn) (norm_nonneg _)
  · intro i y
    refine (h3 n hn3 t ht i y).trans ?_
    have hy : 0 ≤ ‖y‖ := norm_nonneg _
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hc3 hνn) (norm_nonneg _)) hy
  · refine (h4 n hn4 t ht).trans ?_
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hc4 hνn) (norm_nonneg _)

end ConcreteYF

end UnforcedLeray.Short.PartIIIb
