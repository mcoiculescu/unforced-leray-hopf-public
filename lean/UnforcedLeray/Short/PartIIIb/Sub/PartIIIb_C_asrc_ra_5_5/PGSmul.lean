import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_5_5
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Data.Nat.Choose.Sum

/-!
# `PartIII-b:C/asrc/ra/5/5` : polynomial growth is stable under scalar multiplication

Toolkit lemma for `PolyGrowth`: the product `f p • P p` of a scalar function of polynomial
growth and a vector function of polynomial growth again has polynomial growth (Leibniz rule
`norm_iteratedFDerivWithin_smul_le` on the open set `Ioi 0 ×ˢ univ`, with `∑ choose = 2^m ≤ 2^n`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem polyGrowth_smul {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (n : ℕ)
    (f : ℝ × (ℝ × ℝ) → ℝ) (P : ℝ × (ℝ × ℝ) → E) (hf : PolyGrowth n f) (hP : PolyGrowth n P) :
    PolyGrowth n (fun p => f p • P p) := by
  obtain ⟨hfc, hfb⟩ := hf
  obtain ⟨hPc, hPb⟩ := hP
  refine ⟨hfc.smul hPc, fun s0 s1 hs0 hs01 => ?_⟩
  obtain ⟨C1, N1, hC1, hf1⟩ := hfb s0 s1 hs0 hs01
  obtain ⟨C2, N2, hC2, hP1⟩ := hPb s0 s1 hs0 hs01
  refine ⟨2 ^ n * (C1 * C2), N1 + N2, mul_nonneg (by positivity) (mul_nonneg hC1 hC2),
    fun m hm s hs x => ?_⟩
  have hS : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := isOpen_Ioi.prod isOpen_univ
  have hsS : (s, x) ∈ Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)) :=
    ⟨lt_of_lt_of_le hs0 hs.1, mem_univ _⟩
  have hmn : (m : WithTop ℕ∞) ≤ (n : WithTop ℕ∞) := by exact_mod_cast hm
  have hq : 0 ≤ 1 + sq2 x := by
    unfold sq2
    positivity
  have hK : 0 ≤ (C1 * (1 + sq2 x) ^ N1) * (C2 * (1 + sq2 x) ^ N2) :=
    mul_nonneg (mul_nonneg hC1 (pow_nonneg hq _)) (mul_nonneg hC2 (pow_nonneg hq _))
  have hconvf : ∀ i : ℕ, iteratedFDerivWithin ℝ i f (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) (s, x) =
      iteratedFDeriv ℝ i f (s, x) := fun i => iteratedFDerivWithin_of_isOpen i hS hsS
  have hconvP : ∀ i : ℕ, iteratedFDerivWithin ℝ i P (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) (s, x) =
      iteratedFDeriv ℝ i P (s, x) := fun i => iteratedFDerivWithin_of_isOpen i hS hsS
  rw [← iteratedFDerivWithin_of_isOpen m hS hsS]
  refine (norm_iteratedFDerivWithin_smul_le hfc hPc hS.uniqueDiffOn hsS hmn).trans ?_
  have hterm : ∀ i ∈ Finset.range (m + 1),
      (m.choose i : ℝ) * ‖iteratedFDerivWithin ℝ i f (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) (s, x)‖ *
          ‖iteratedFDerivWithin ℝ (m - i) P (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) (s, x)‖ ≤
        (m.choose i : ℝ) * ((C1 * (1 + sq2 x) ^ N1) * (C2 * (1 + sq2 x) ^ N2)) := by
    intro i hi
    have hi' : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [hconvf i, hconvP (m - i), mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    exact mul_le_mul (hf1 i (le_trans hi' hm) s hs x) (hP1 (m - i) (by omega) s hs x)
      (norm_nonneg _) (mul_nonneg hC1 (pow_nonneg hq _))
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.sum_mul]
  have hsum : ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) = 2 ^ m := by
    exact_mod_cast Nat.sum_range_choose m
  rw [hsum, pow_add]
  have hp : (2 : ℝ) ^ m ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hm
  exact (mul_le_mul_of_nonneg_right hp hK).trans_eq (by ring)

end UnforcedLeray.Short.PartIIIb.Concrete
