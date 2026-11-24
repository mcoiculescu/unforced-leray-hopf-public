import Mathlib.Analysis.Calculus.ContDiff.Bounds
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_4_2.Sub.PartIIIb_IIIb_D2_4_2_1_3

/-!
# Leibniz bound for `PsiProfileGaussBound` (task `PartIII-b:IIIb-D2/4/2/1/3/3`)

Source of record: `the November 2 reference manuscript` lines 4963-4991.
Pure analysis: the Leibniz rule for `iteratedFDeriv` of a product of `C²` functions on the open
set `Ioi 0 ×ˢ univ`, combined with the pointwise bounds of the two factors, for `k ≤ 2`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem leibnizMulBound_proof : LeibnizMulBound := by
  intro f g G s0 N₁ N₂ C₁ C₂ hs0 hG hf hg hfb hgb
  refine ⟨4 * |C₁| * |C₂|, fun p hp k hk => ?_⟩
  have hUo : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := isOpen_Ioi.prod isOpen_univ
  have hpU : p ∈ (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) :=
    ⟨lt_of_lt_of_le (by positivity) hp.1, mem_univ _⟩
  have hGp : 0 ≤ G p := hG p
  have hX : (0 : ℝ) ≤ (1 + ‖p.2‖) ^ N₁ := by positivity
  have hY : (0 : ℝ) ≤ (1 + ‖p.2‖) ^ N₂ := by positivity
  -- Pointwise bound on the derivatives of `f`.
  have hfi : ∀ i ∈ Finset.range (k + 1),
      ‖iteratedFDerivWithin ℝ i f (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) p‖ ≤
        |C₁| * ((1 + ‖p.2‖) ^ N₁ * G p) := by
    intro i hi
    have hik : i ≤ 2 := by have := Finset.mem_range.1 hi; omega
    rw [iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := f) i hUo hpU]
    have hnn : 0 ≤ (1 + ‖p.2‖) ^ N₁ * G p := mul_nonneg hX hGp
    calc ‖iteratedFDeriv ℝ i f p‖ ≤ C₁ * (1 + ‖p.2‖) ^ N₁ * G p := hfb p hp i hik
      _ = C₁ * ((1 + ‖p.2‖) ^ N₁ * G p) := by ring
      _ ≤ |C₁| * ((1 + ‖p.2‖) ^ N₁ * G p) := mul_le_mul_of_nonneg_right (le_abs_self C₁) hnn
  -- Pointwise bound on the derivatives of `g`.
  have hgj : ∀ j ∈ Finset.range (k + 1),
      ‖iteratedFDerivWithin ℝ j g (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) p‖ ≤
        |C₂| * (1 + ‖p.2‖) ^ N₂ := by
    intro j hj
    have hjk : j ≤ 2 := by have := Finset.mem_range.1 hj; omega
    rw [iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := g) j hUo hpU]
    calc ‖iteratedFDeriv ℝ j g p‖ ≤ C₂ * (1 + ‖p.2‖) ^ N₂ := hgb p hp j hjk
      _ ≤ |C₂| * (1 + ‖p.2‖) ^ N₂ := mul_le_mul_of_nonneg_right (le_abs_self C₂) hY
  -- Leibniz rule on the open set.
  have hmul := norm_iteratedFDerivWithin_mul_le (𝕜 := ℝ) (f := f) (g := g) hf hg
    hUo.uniqueDiffOn hpU (n := k) (by exact_mod_cast hk)
  have e : iteratedFDeriv ℝ k (fun q => f q * g q) p =
      iteratedFDerivWithin ℝ k (fun q => f q * g q) (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) p :=
    (iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := fun q => f q * g q) k hUo hpU).symm
  rw [e]
  have hsum : ∑ i ∈ Finset.range (k + 1),
      (k.choose i : ℝ) * ‖iteratedFDerivWithin ℝ i f (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) p‖ *
        ‖iteratedFDerivWithin ℝ (k - i) g (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) p‖ ≤
      ∑ i ∈ Finset.range (k + 1),
        (k.choose i : ℝ) * (|C₁| * ((1 + ‖p.2‖) ^ N₁ * G p)) * (|C₂| * (1 + ‖p.2‖) ^ N₂) := by
    apply Finset.sum_le_sum
    intro i hi
    have hA := hfi i hi
    have hB := hgj (k - i) (Finset.mem_range.2 (by have := Finset.mem_range.1 hi; omega))
    have hc : (0 : ℝ) ≤ (k.choose i : ℝ) := by positivity
    have hb : 0 ≤ (k.choose i : ℝ) * (|C₁| * ((1 + ‖p.2‖) ^ N₁ * G p)) :=
      mul_nonneg hc (mul_nonneg (abs_nonneg _) (mul_nonneg hX hGp))
    exact mul_le_mul (mul_le_mul_of_nonneg_left hA hc) hB (norm_nonneg _) hb
  have hterm : ∀ i ∈ Finset.range (k + 1),
      (k.choose i : ℝ) * (|C₁| * ((1 + ‖p.2‖) ^ N₁ * G p)) * (|C₂| * (1 + ‖p.2‖) ^ N₂) =
        (k.choose i : ℝ) * (|C₁| * |C₂| * ((1 + ‖p.2‖) ^ (N₁ + N₂) * G p)) := by
    intro i _
    rw [pow_add]
    ring
  have hs2 : (∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ)) = (2 : ℝ) ^ k := by
    exact_mod_cast Nat.sum_range_choose k
  have hrhs : ∑ i ∈ Finset.range (k + 1),
      (k.choose i : ℝ) * (|C₁| * ((1 + ‖p.2‖) ^ N₁ * G p)) * (|C₂| * (1 + ‖p.2‖) ^ N₂) =
        (2 : ℝ) ^ k * (|C₁| * |C₂| * ((1 + ‖p.2‖) ^ (N₁ + N₂) * G p)) := by
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul, hs2]
  have h4 : (2 : ℝ) ^ k ≤ 4 := by
    interval_cases k <;> norm_num
  have hK0 : (0 : ℝ) ≤ |C₁| * |C₂| * ((1 + ‖p.2‖) ^ (N₁ + N₂) * G p) :=
    mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      (mul_nonneg (by positivity) hGp)
  calc ‖iteratedFDerivWithin ℝ k (fun q => f q * g q) (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) p‖
      ≤ ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) *
          ‖iteratedFDerivWithin ℝ i f (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) p‖ *
          ‖iteratedFDerivWithin ℝ (k - i) g (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) p‖ := hmul
    _ ≤ ∑ i ∈ Finset.range (k + 1),
        (k.choose i : ℝ) * (|C₁| * ((1 + ‖p.2‖) ^ N₁ * G p)) * (|C₂| * (1 + ‖p.2‖) ^ N₂) := hsum
    _ = (2 : ℝ) ^ k * (|C₁| * |C₂| * ((1 + ‖p.2‖) ^ (N₁ + N₂) * G p)) := hrhs
    _ ≤ 4 * (|C₁| * |C₂| * ((1 + ‖p.2‖) ^ (N₁ + N₂) * G p)) :=
        mul_le_mul_of_nonneg_right h4 hK0
    _ = 4 * |C₁| * |C₂| * (1 + ‖p.2‖) ^ (N₁ + N₂) * G p := by ring

end UnforcedLeray.Short.PartIIIb.Concrete
