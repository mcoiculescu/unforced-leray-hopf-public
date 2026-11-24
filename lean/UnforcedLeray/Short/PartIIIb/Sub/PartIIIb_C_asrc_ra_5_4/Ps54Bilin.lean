import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_5_4
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Data.Nat.Choose.Sum

/-!
# `ps54_bilin`: bilinear closure of the polynomial class `PS54`

Source of record: `the November 2 reference manuscript` lines 4963-4981, 4978.
A bilinear map applied to two `PS54` families is `PS54`: the Leibniz bound
`norm_iteratedFDerivWithin_le_of_bilinear` on the open set `Ioi 0 ×ˢ univ` gives the derivative
bounds, and the polynomial exponents add.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem ps54_bilin {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (B : E →L[ℝ] F →L[ℝ] G) (n : ℕ) (f : ℝ × (ℝ × ℝ) → E) (g : ℝ × (ℝ × ℝ) → F)
    (hf : PS54 n f) (hg : PS54 n g) : PS54 n (fun p => B (f p) (g p)) := by
  obtain ⟨hfC, hfB⟩ := hf
  obtain ⟨hgC, hgB⟩ := hg
  have hU : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := isOpen_Ioi.prod isOpen_univ
  refine ⟨?_, ?_⟩
  · exact (B.contDiff.comp_contDiffOn hfC).clm_apply hgC
  · intro s0 s1 hs0 hs01
    obtain ⟨Cf, Nf, hCf, hfb⟩ := hfB s0 s1 hs0 hs01
    obtain ⟨Cg, Ng, hCg, hgb⟩ := hgB s0 s1 hs0 hs01
    refine ⟨‖B‖ * (2 ^ n) * (Cf * Cg), Nf + Ng,
      mul_nonneg (mul_nonneg (norm_nonneg B) (by positivity)) (mul_nonneg hCf hCg), ?_⟩
    intro m hm s hs x
    have hsU : (0 : ℝ) < s := lt_of_lt_of_le hs0 hs.1
    have hx : (s, x) ∈ (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := ⟨hsU, mem_univ x⟩
    have hq0 : (0 : ℝ) ≤ 1 + sq2 x := by
      unfold sq2; positivity
    have hm' : (m : WithTop ℕ∞) ≤ ((n : ℕ) : WithTop ℕ∞) := by exact_mod_cast hm
    have h := B.norm_iteratedFDerivWithin_le_of_bilinear hfC hgC hU.uniqueDiffOn hx hm'
    have e0 : iteratedFDerivWithin ℝ m (fun p => B (f p) (g p)) (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)))
        (s, x) = iteratedFDeriv ℝ m (fun p => B (f p) (g p)) (s, x) :=
      iteratedFDerivWithin_of_isOpen m hU hx
    have e1 : ∀ i : ℕ, iteratedFDerivWithin ℝ i f (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) (s, x)
        = iteratedFDeriv ℝ i f (s, x) := fun i => iteratedFDerivWithin_of_isOpen i hU hx
    have e2 : ∀ i : ℕ, iteratedFDerivWithin ℝ i g (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) (s, x)
        = iteratedFDeriv ℝ i g (s, x) := fun i => iteratedFDerivWithin_of_isOpen i hU hx
    rw [e0] at h
    simp only [e1, e2] at h
    have hbound : ∀ i ∈ Finset.range (m + 1),
        ‖iteratedFDeriv ℝ i f (s, x)‖ * ‖iteratedFDeriv ℝ (m - i) g (s, x)‖
          ≤ Cf * Cg * (1 + sq2 x) ^ (Nf + Ng) := by
      intro i hi
      have hi' : i < m + 1 := Finset.mem_range.mp hi
      have h1 : ‖iteratedFDeriv ℝ i f (s, x)‖ ≤ Cf * (1 + sq2 x) ^ Nf :=
        hfb i (by omega) s hs x
      have h2 : ‖iteratedFDeriv ℝ (m - i) g (s, x)‖ ≤ Cg * (1 + sq2 x) ^ Ng :=
        hgb (m - i) (by omega) s hs x
      calc ‖iteratedFDeriv ℝ i f (s, x)‖ * ‖iteratedFDeriv ℝ (m - i) g (s, x)‖
          ≤ (Cf * (1 + sq2 x) ^ Nf) * (Cg * (1 + sq2 x) ^ Ng) :=
            mul_le_mul h1 h2 (norm_nonneg _) (mul_nonneg hCf (pow_nonneg hq0 _))
        _ = Cf * Cg * (1 + sq2 x) ^ (Nf + Ng) := by rw [pow_add]; ring
    have hK0 : (0 : ℝ) ≤ Cf * Cg * (1 + sq2 x) ^ (Nf + Ng) :=
      mul_nonneg (mul_nonneg hCf hCg) (pow_nonneg hq0 _)
    have hsum : ∑ i ∈ Finset.range (m + 1),
        (m.choose i : ℝ) * ‖iteratedFDeriv ℝ i f (s, x)‖ * ‖iteratedFDeriv ℝ (m - i) g (s, x)‖
          ≤ ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * (Cf * Cg * (1 + sq2 x) ^ (Nf + Ng)) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (hbound i hi) (Nat.cast_nonneg _)
    have hc : ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) = 2 ^ m := by
      exact_mod_cast Nat.sum_range_choose m
    have hfinal : ∑ i ∈ Finset.range (m + 1),
        (m.choose i : ℝ) * ‖iteratedFDeriv ℝ i f (s, x)‖ * ‖iteratedFDeriv ℝ (m - i) g (s, x)‖
          ≤ 2 ^ n * (Cf * Cg * (1 + sq2 x) ^ (Nf + Ng)) := by
      calc _ ≤ ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * (Cf * Cg * (1 + sq2 x) ^ (Nf + Ng)) :=
            hsum
        _ = 2 ^ m * (Cf * Cg * (1 + sq2 x) ^ (Nf + Ng)) := by rw [← Finset.sum_mul, hc]
        _ ≤ 2 ^ n * (Cf * Cg * (1 + sq2 x) ^ (Nf + Ng)) :=
            mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hm) hK0
    calc ‖iteratedFDeriv ℝ m (fun p => B (f p) (g p)) (s, x)‖
        ≤ ‖B‖ * ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * ‖iteratedFDeriv ℝ i f (s, x)‖
            * ‖iteratedFDeriv ℝ (m - i) g (s, x)‖ := h
      _ ≤ ‖B‖ * (2 ^ n * (Cf * Cg * (1 + sq2 x) ^ (Nf + Ng))) :=
            mul_le_mul_of_nonneg_left hfinal (norm_nonneg B)
      _ = ‖B‖ * (2 ^ n) * (Cf * Cg) * (1 + sq2 x) ^ (Nf + Ng) := by ring

end UnforcedLeray.Short.PartIIIb.Concrete
