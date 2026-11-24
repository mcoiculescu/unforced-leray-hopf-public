import UnforcedLeray.Short.PartI.Sub.PartI_TrainHeatFixed
import UnforcedLeray.Short.PartI.Tasks.TrainHeatFixed.JointFromMixed1D.Words

/-!
# Part I, task `PartI:HF/7`, target `jointFromMixed1D`: the full derivative from the mixed ones

Source of record: `the November 2 reference manuscript`, lines 427-435 (fixed
parameters; the derivative budget is not restricted). The Prop is `JointFromMixed1D` in
`Sub/PartI_TrainHeatFixed.lean` (B2, generic calculus).

Proof. Expand the `i`-th derivative on coordinate words (`norm_iteratedFDeriv_le_sum`, with
`2^i` words). Each word is, up to permutation, `∂_η^{a} ∂_s^{b}` with `a + b = i`
(`dW_perm`, from the count of letters), and this is the iterated one-variable derivative
`iteratedDeriv (i - b) (η ↦ iteratedDeriv b (s ↦ f s η) y.1) y.2` (`dW_replicate_ee_es`).
So each word term is at most the sum over `b`, and `K = 2^i`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Real
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Short.PartI.MixedDeriv

/-- **Target** `jointFromMixed1D`: the full derivative from the mixed ones (`JointFromMixed1D`). -/
theorem jointFromMixed1D : UnforcedLeray.Short.PartI.JointFromMixed1D := by
  intro i
  refine ⟨2 ^ i, by positivity, ?_⟩
  intro f hf y hy
  have hmem : y ∈ Ioi (0 : ℝ) ×ˢ (univ : Set ℝ) := ⟨hy, mem_univ _⟩
  have hword : ∀ r : Fin i → Bool,
      |iteratedFDeriv ℝ i (fun x : ℝ × ℝ => f x.1 x.2) y (fun k => bas (r k))| ≤
        ∑ ℓ ∈ Finset.range (i + 1),
          |iteratedDeriv (i - ℓ) (fun e => iteratedDeriv ℓ (fun t => f t e) y.1) y.2| := by
    intro r
    obtain ⟨lb, hlb⟩ : ∃ lb : List Bool, lb = List.ofFn r := ⟨_, rfl⟩
    obtain ⟨a, ha⟩ : ∃ a : ℕ, a = lb.count false := ⟨_, rfl⟩
    obtain ⟨b, hb⟩ : ∃ b : ℕ, b = lb.count true := ⟨_, rfl⟩
    have hperm : lb.Perm (List.replicate a false ++ List.replicate b true) := by
      rw [List.perm_iff_count]
      intro x
      cases x <;> simp [ha, hb, List.count_replicate, List.count_append]
    have hlen : i = a + b := by
      have h := hperm.length_eq
      simp only [List.length_append, List.length_replicate, hlb, List.length_ofFn] at h
      omega
    have hperm2 : (List.ofFn fun k => bas (r k)).Perm
        (List.replicate a (0, 1) ++ List.replicate b (1, 0)) := by
      have h0 : (List.ofFn fun k => bas (r k)) = lb.map bas := by
        rw [hlb, List.map_ofFn]
        rfl
      rw [h0]
      have h1 := hperm.map bas
      simpa [List.map_append, List.map_replicate, bas] using h1
    have hd := dW_perm isOpen_halfPlane hf hperm2 y hmem
    have hL := dW_ofFn_eq isOpen_halfPlane hf i (fun k => bas (r k)) y hmem
    have h1 : dW (List.replicate a (0, 1) ++ List.replicate b (1, 0))
        (fun x : ℝ × ℝ => f x.1 x.2) y =
        iteratedDeriv a (fun e => iteratedDeriv b (fun t => f t e) y.1) y.2 :=
      dW_replicate_ee_es hf a b y.1 y.2 hy
    have key : iteratedFDeriv ℝ i (fun x : ℝ × ℝ => f x.1 x.2) y (fun k => bas (r k)) =
        iteratedDeriv a (fun e => iteratedDeriv b (fun t => f t e) y.1) y.2 := by
      rw [← hL, hd, h1]
    have hab : i - b = a := by omega
    have hbmem : b ∈ Finset.range (i + 1) := Finset.mem_range.2 (by omega)
    calc |iteratedFDeriv ℝ i (fun x : ℝ × ℝ => f x.1 x.2) y (fun k => bas (r k))|
        = |iteratedDeriv a (fun e => iteratedDeriv b (fun t => f t e) y.1) y.2| := by
          rw [key]
      _ = |iteratedDeriv (i - b) (fun e => iteratedDeriv b (fun t => f t e) y.1) y.2| := by
          rw [hab]
      _ ≤ ∑ ℓ ∈ Finset.range (i + 1),
            |iteratedDeriv (i - ℓ) (fun e => iteratedDeriv ℓ (fun t => f t e) y.1) y.2| :=
          Finset.single_le_sum (f := fun ℓ =>
            |iteratedDeriv (i - ℓ) (fun e => iteratedDeriv ℓ (fun t => f t e) y.1) y.2|)
            (fun ℓ _ => abs_nonneg _) hbmem
  calc ‖iteratedFDeriv ℝ i (fun x : ℝ × ℝ => f x.1 x.2) y‖
      ≤ ∑ r : Fin i → Bool, |iteratedFDeriv ℝ i (fun x : ℝ × ℝ => f x.1 x.2) y
          (fun k => bas (r k))| := norm_iteratedFDeriv_le_sum _ i y
    _ ≤ ∑ r : Fin i → Bool, ∑ ℓ ∈ Finset.range (i + 1),
          |iteratedDeriv (i - ℓ) (fun e => iteratedDeriv ℓ (fun t => f t e) y.1) y.2| :=
        Finset.sum_le_sum (fun r _ => hword r)
    _ = 2 ^ i * ∑ ℓ ∈ Finset.range (i + 1),
          |iteratedDeriv (i - ℓ) (fun e => iteratedDeriv ℓ (fun t => f t e) y.1) y.2| := by
        simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = 2 ^ i * ∑ ℓ ∈ Finset.range (i + 1),
          ‖iteratedDeriv (i - ℓ) (fun e => iteratedDeriv ℓ (fun t => f t e) y.1) y.2‖ := by
        simp only [Real.norm_eq_abs]

end UnforcedLeray.Short.PartI
