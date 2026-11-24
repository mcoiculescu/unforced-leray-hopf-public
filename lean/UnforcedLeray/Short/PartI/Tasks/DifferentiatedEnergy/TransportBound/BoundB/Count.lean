import UnforcedLeray.Short.PartI.Sub.PartI_T08_7_2_3
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.ForcingIBP
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.ErrJetL2.VelocityJetL2.EnergyIneq.AdvCommutator

/-!
# Part I, task `PartI:T08/7/2/3/3` (`JTBCount`): counting bound

Source: `the November 2 reference manuscript` lines 352-358.

Pure combinatorics for nonnegative reals. For `w ∈ wordsOfLength j` and `p ∈ wacSplits w`,
`|p.1| + |p.2| = j`, so the weight `M (|p.2|+1)` has index `i = |p.2|+1 ∈ [1, j+1]` and
`|p.1| = j+1-i`. Each factor `√(I p.1 m)` is at most `√(S_{j+1-i})` and `√(I w k)` at most
`√(S_j)`, where `S_s = ∑_{a ∈ wordsOfLength s} ∑_m I a m`. Hence every summand is at most the
whole right-hand sum `R`. There are at most `2^j · 2 · 2^j · 2` summands, so the left side is at
most `4 · 2^j · 2^j · R`, a constant depending only on `j`. (No Cauchy-Schwarz is needed.)
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff Topology

namespace UnforcedLeray.Short.PartI

theorem jbc_card (l : ℕ) : (wordsOfLength l).card ≤ 2 ^ l := by
  unfold wordsOfLength
  refine Finset.card_image_le.trans ?_
  simp

/-- A list sum of values bounded by `c` is at most `length · c`. -/
theorem jbc_list_le {α : Type*} (φ : α → ℝ) (c : ℝ) :
    ∀ L : List α, (∀ p ∈ L, φ p ≤ c) → (L.map φ).sum ≤ (L.length : ℝ) * c
  | [], _ => by simp
  | x :: L, h => by
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have h1 := h x (by simp)
    have h2 := jbc_list_le φ c L (fun y hy => h y (by simp [hy]))
    push_cast
    linarith

theorem jtBCount_proof : UnforcedLeray.Short.PartI.JTBCount := by
  intro j
  refine ⟨4 * (2 ^ j * 2 ^ j), by positivity, ?_⟩
  intro M I hM hI
  obtain ⟨R, hRdef⟩ : ∃ R : ℝ, R = ∑ i ∈ Finset.Icc 1 (j + 1),
      M i * Real.sqrt (∑ a ∈ wordsOfLength (j + 1 - i), ∑ m : Fin 2, I a m) *
        Real.sqrt (∑ w ∈ wordsOfLength j, ∑ k : Fin 2, I w k) := ⟨_, rfl⟩
  rw [← hRdef]
  have hR0 : 0 ≤ R := by
    rw [hRdef]
    exact Finset.sum_nonneg fun i _ =>
      mul_nonneg (mul_nonneg (hM i) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
  -- a single factor is bounded by the full sum over words of its length
  have hA : ∀ (a : List Bool) (s : ℕ) (m : Fin 2), a.length = s →
      I a m ≤ ∑ b ∈ wordsOfLength s, ∑ m' : Fin 2, I b m' := by
    intro a s m ha
    have hmem : a ∈ wordsOfLength s := ForcingIBP.mem_wordsOfLength_iff'.2 ha
    calc I a m ≤ ∑ m' : Fin 2, I a m' :=
          Finset.single_le_sum (f := fun m' => I a m') (fun m' _ => hI a m') (Finset.mem_univ m)
      _ ≤ ∑ b ∈ wordsOfLength s, ∑ m' : Fin 2, I b m' :=
          Finset.single_le_sum (f := fun b => ∑ m' : Fin 2, I b m')
            (fun b _ => Finset.sum_nonneg fun m' _ => hI b m') hmem
  -- each summand of one split term, for one word `w` of length `j`, is at most `2 R`
  have hterm : ∀ (w : List Bool), w.length = j → ∀ k : Fin 2, ∀ p ∈ wacSplits w,
      ∑ m : Fin 2, M (p.2.length + 1) * Real.sqrt (I p.1 m) * Real.sqrt (I w k) ≤ 2 * R := by
    intro w hw k p hp
    have hl := wac_splits_len_sum w p hp
    have hg : p.2.length + 1 ∈ Finset.Icc 1 (j + 1) :=
      Finset.mem_Icc.2 ⟨by omega, by omega⟩
    have hsplit : j + 1 - (p.2.length + 1) = p.1.length := by omega
    have hIw : I w k ≤ ∑ b ∈ wordsOfLength j, ∑ m' : Fin 2, I b m' := hA w j k hw
    have hIp : ∀ m : Fin 2, I p.1 m ≤
        ∑ b ∈ wordsOfLength (j + 1 - (p.2.length + 1)), ∑ m' : Fin 2, I b m' := fun m => by
      rw [hsplit]
      exact hA p.1 p.1.length m rfl
    have hper : ∀ m : Fin 2, M (p.2.length + 1) * Real.sqrt (I p.1 m) * Real.sqrt (I w k) ≤ R := by
      intro m
      have h1 : Real.sqrt (I p.1 m) ≤
          Real.sqrt (∑ b ∈ wordsOfLength (j + 1 - (p.2.length + 1)), ∑ m' : Fin 2, I b m') :=
        Real.sqrt_le_sqrt (hIp m)
      have h2 : Real.sqrt (I w k) ≤ Real.sqrt (∑ b ∈ wordsOfLength j, ∑ m' : Fin 2, I b m') :=
        Real.sqrt_le_sqrt hIw
      have h3 : M (p.2.length + 1) * Real.sqrt (I p.1 m) * Real.sqrt (I w k) ≤
          M (p.2.length + 1) *
            Real.sqrt (∑ b ∈ wordsOfLength (j + 1 - (p.2.length + 1)), ∑ m' : Fin 2, I b m') *
          Real.sqrt (∑ b ∈ wordsOfLength j, ∑ m' : Fin 2, I b m') :=
        mul_le_mul (mul_le_mul_of_nonneg_left h1 (hM _)) h2 (Real.sqrt_nonneg _)
          (mul_nonneg (hM _) (Real.sqrt_nonneg _))
      have h4 : M (p.2.length + 1) *
            Real.sqrt (∑ b ∈ wordsOfLength (j + 1 - (p.2.length + 1)), ∑ m' : Fin 2, I b m') *
          Real.sqrt (∑ b ∈ wordsOfLength j, ∑ m' : Fin 2, I b m') ≤ R := by
        rw [hRdef]
        exact Finset.single_le_sum
          (f := fun i => M i * Real.sqrt (∑ a ∈ wordsOfLength (j + 1 - i), ∑ m' : Fin 2, I a m') *
            Real.sqrt (∑ w ∈ wordsOfLength j, ∑ k : Fin 2, I w k))
          (fun i _ => mul_nonneg (mul_nonneg (hM i) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))
          hg
      exact h3.trans h4
    calc ∑ m : Fin 2, M (p.2.length + 1) * Real.sqrt (I p.1 m) * Real.sqrt (I w k)
        ≤ ∑ m : Fin 2, R := Finset.sum_le_sum fun m _ => hper m
      _ = 2 * R := by rw [Fin.sum_univ_two]; ring
  -- the list sum for one word and one component
  have hlist : ∀ (w : List Bool), w.length = j → ∀ k : Fin 2,
      ((wacSplits w).map (fun p => ∑ m : Fin 2,
        M (p.2.length + 1) * Real.sqrt (I p.1 m) * Real.sqrt (I w k))).sum ≤ 2 ^ j * (2 * R) := by
    intro w hw k
    have := jbc_list_le (fun p => ∑ m : Fin 2,
        M (p.2.length + 1) * Real.sqrt (I p.1 m) * Real.sqrt (I w k)) (2 * R) (wacSplits w)
      (fun p hp => hterm w hw k p hp)
    rw [wac_splits_length, hw] at this
    push_cast at this
    exact this
  have hcard : ((wordsOfLength j).card : ℝ) ≤ 2 ^ j := by
    have := jbc_card j
    exact_mod_cast this
  calc ∑ w ∈ wordsOfLength j, ∑ k : Fin 2,
        ((wacSplits w).map (fun p => ∑ m : Fin 2,
          M (p.2.length + 1) * Real.sqrt (I p.1 m) * Real.sqrt (I w k))).sum
      ≤ ∑ w ∈ wordsOfLength j, ∑ k : Fin 2, (2 ^ j * (2 * R)) :=
        Finset.sum_le_sum fun w hw => Finset.sum_le_sum fun k _ =>
          hlist w (ForcingIBP.mem_wordsOfLength_iff'.1 hw) k
    _ = ((wordsOfLength j).card : ℝ) * (2 * (2 ^ j * (2 * R))) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          Nat.cast_ofNat]
    _ ≤ 2 ^ j * (2 * (2 ^ j * (2 * R))) :=
        mul_le_mul_of_nonneg_right hcard
          (mul_nonneg (by norm_num) (mul_nonneg (by positivity) (mul_nonneg (by norm_num) hR0)))
    _ = 4 * (2 ^ j * 2 ^ j) * R := by ring

end UnforcedLeray.Short.PartI
