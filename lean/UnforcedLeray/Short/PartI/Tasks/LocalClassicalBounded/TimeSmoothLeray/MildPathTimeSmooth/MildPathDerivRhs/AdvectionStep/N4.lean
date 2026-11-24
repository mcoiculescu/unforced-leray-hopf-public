import UnforcedLeray.Short.PartI.Sub.PartI_T02_1_4_4_1_2

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec toVec)
open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.TrainB

/-- Splitting a sum over words of length `≤ k + 1` by the empty word and the first letter. -/
theorem sum_idx_succ {n k : ℕ} {G : Type*} [AddCommMonoid G] (f : Sob.Idx n (k + 1) → G) :
    ∑ α : Sob.Idx n (k + 1), f α =
      f Sob.Idx.zero + ∑ i : Fin n, ∑ β : Sob.Idx n k, f (Sob.Idx.cons i β) := by
  rw [Fintype.sum_sigma, Fin.sum_univ_succ]
  congr 1
  · have : IsEmpty (Fin ((0 : Fin (k + 2)) : ℕ)) := ⟨fun i => Fin.elim0 i⟩
    rw [Fintype.sum_unique]
    congr 1
  · simp only [Fintype.sum_sigma]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Fintype.sum_prod_type' (fun (i : Fin n) (c : Fin j → Fin n) =>
      f (Sob.Idx.cons i ⟨j, c⟩))]
    exact (Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin ((j : ℕ) + 1) => Fin n))
      _ _ (fun p => rfl)).symm

/-- Elementary bound: `X² = A² + a² + b²` with `A ≤ B` gives `X ≤ B + (a + b)`. -/
theorem aux_bound (X A B a b : ℝ) (hX0 : 0 ≤ X) (hX : X ^ 2 = A ^ 2 + (a ^ 2 + b ^ 2))
    (hAB : A ≤ B) (hA0 : 0 ≤ A) (ha : 0 ≤ a) (hb : 0 ≤ b) : X ≤ B + (a + b) := by
  have hB0 : 0 ≤ B := le_trans hA0 hAB
  have hsq : X ^ 2 ≤ (B + (a + b)) ^ 2 := by
    nlinarith [mul_nonneg hB0 ha, mul_nonneg hB0 hb, mul_nonneg ha hb,
      mul_le_mul hAB hAB hA0 hB0]
  exact (sq_le_sq₀ hX0 (by positivity)).mp hsq

/-- **Lemma N4 (norm bound one level up).** -/
theorem cylSobNormSucc : CylSobNormSucc := by
  intro c m x
  have hn := Sob.W.norm_sq x
  rw [sum_idx_succ] at hn
  have hpart : ∀ i : Fin 2, ‖Sob.W.partialDeriv (k := m) i x‖ ^ 2 =
      ∑ β : Sob.Idx 2 m, ‖Sob.W.deriv (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ Cyl.Vec2 m 2 β
        (Sob.W.partialDeriv (k := m) i x)‖ ^ 2 := fun i => Sob.W.norm_sq _
  have hsplit : ‖x‖ ^ 2 = ‖Sob.W.deriv (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ Cyl.Vec2 (m + 1) 2
      Sob.Idx.zero x‖ ^ 2 + ∑ i : Fin 2, ‖Sob.W.partialDeriv (k := m) i x‖ ^ 2 := by
    rw [hn]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hpart i]
    rfl
  have hB : ‖Sob.W.deriv (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ Cyl.Vec2 m 2 Sob.Idx.zero
      (Sob.W.restrict (Nat.le_succ m) x)‖ ^ 2 ≤
        ‖(Sob.W.restrict (Nat.le_succ m) x : Cyl.H ℝ Cyl.Vec2 c 0 m)‖ ^ 2 := by
    rw [Sob.W.norm_sq]
    exact Finset.single_le_sum (f := fun β => ‖Sob.W.deriv (Sob.cylinder c)
      (Cyl.ρwW c ^ (0 : ℝ)) ℝ Cyl.Vec2 m 2 β (Sob.W.restrict (Nat.le_succ m) x)‖ ^ 2)
      (fun β _ => by positivity) (Finset.mem_univ _)
  have hz : Sob.W.deriv (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ Cyl.Vec2 m 2 Sob.Idx.zero
      (Sob.W.restrict (Nat.le_succ m) x) =
      Sob.W.deriv (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ Cyl.Vec2 (m + 1) 2 Sob.Idx.zero x :=
    rfl
  rw [hz] at hB
  have hA : ‖Sob.W.deriv (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ Cyl.Vec2 (m + 1) 2
      Sob.Idx.zero x‖ ≤ ‖(Sob.W.restrict (Nat.le_succ m) x : Cyl.H ℝ Cyl.Vec2 c 0 m)‖ :=
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hB
  rw [Fin.sum_univ_two] at hsplit
  rw [Fin.sum_univ_two]
  exact aux_bound _ _ _ _ _ (norm_nonneg _) hsplit hA (norm_nonneg _)
    (norm_nonneg _) (norm_nonneg _)

end UnforcedLeray.Short.PartI
