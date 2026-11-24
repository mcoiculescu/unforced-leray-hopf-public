import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_5_4

/-!
# `PartIII-b:C/asrc/ra/5/4` task 2 : bilinear products of `GP54` and `PS54` are in `GP54`

Source of record: `the November 2 reference manuscript` lines 4963-4981, 4978.
Smoothness: `B ∘ f` is `C^n` and `clm_apply` with `g`.  Bounds: the Leibniz estimate
`‖D^m (B f g)‖ ≤ ‖B‖ ∑_i C(m,i) ‖D^i f‖ ‖D^{m-i} g‖` on the open set `Ioi 0 ×ˢ univ`, with
`‖D^i f‖ ≤ C₁ (1+|x|²)^{N₁} e^{-|x|²/(κ a(s₁))}` and `‖D^j g‖ ≤ C₂ (1+|x|²)^{N₂}`.
The product has `N = N₁ + N₂`, constant `‖B‖ C₁ C₂ 2^n`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem gp54_bilin {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G] (B : E →L[ℝ] F →L[ℝ] G) (κ ν : ℝ) (n : ℕ) (f : ℝ × (ℝ × ℝ) → E) (g : ℝ × (ℝ × ℝ) → F) (hf : GP54 κ ν n f) (hg : PS54 n g) : GP54 κ ν n (fun p => B (f p) (g p)) := by
  obtain ⟨hfC, hfB⟩ := hf
  obtain ⟨hgC, hgB⟩ := hg
  have hS : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := isOpen_Ioi.prod isOpen_univ
  have hU : UniqueDiffOn ℝ (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := hS.uniqueDiffOn
  refine ⟨?_, ?_⟩
  · exact (B.contDiff.comp_contDiffOn hfC).clm_apply hgC
  · intro s0 s1 hs0 hs01
    obtain ⟨C1, N1, hC1, hb1⟩ := hfB s0 s1 hs0 hs01
    obtain ⟨C2, N2, hC2, hb2⟩ := hgB s0 s1 hs0 hs01
    refine ⟨‖B‖ * C1 * C2 * 2 ^ n, N1 + N2, mul_nonneg (mul_nonneg (mul_nonneg (norm_nonneg B) hC1) hC2) (by positivity), ?_⟩
    intro m hmn s hs x
    have hsp : 0 < s := lt_of_lt_of_le hs0 hs.1
    have hmem : (s, x) ∈ Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)) := ⟨hsp, mem_univ _⟩
    have key := ContinuousLinearMap.norm_iteratedFDerivWithin_le_of_bilinear B hfC hgC hU hmem
      (n := m) (by exact_mod_cast hmn)
    have eF : ∀ k : ℕ, iteratedFDerivWithin ℝ k f (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) (s, x)
        = iteratedFDeriv ℝ k f (s, x) := fun k => iteratedFDerivWithin_of_isOpen k hS hmem
    have eG : ∀ k : ℕ, iteratedFDerivWithin ℝ k g (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) (s, x)
        = iteratedFDeriv ℝ k g (s, x) := fun k => iteratedFDerivWithin_of_isOpen k hS hmem
    have eP : ∀ k : ℕ, iteratedFDerivWithin ℝ k (fun y => B (f y) (g y))
        (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) (s, x)
        = iteratedFDeriv ℝ k (fun y => B (f y) (g y)) (s, x) :=
      fun k => iteratedFDerivWithin_of_isOpen k hS hmem
    simp only [eF, eG, eP] at key
    have hr : 0 ≤ sq2 x := by unfold sq2; positivity
    have hK1 : 0 ≤ (1 + sq2 x) ^ N1 := pow_nonneg (by linarith) _
    have hK2 : 0 ≤ (1 + sq2 x) ^ N2 := pow_nonneg (by linarith) _
    have hE : 0 ≤ Real.exp (-(sq2 x) / (κ * ageA ν s1)) := (Real.exp_pos _).le
    have hterm : ∀ i ∈ Finset.range (m + 1),
        (m.choose i : ℝ) * ‖iteratedFDeriv ℝ i f (s, x)‖ * ‖iteratedFDeriv ℝ (m - i) g (s, x)‖ ≤
          (m.choose i : ℝ) * (C1 * (1 + sq2 x) ^ N1 * Real.exp (-(sq2 x) / (κ * ageA ν s1))) *
            (C2 * (1 + sq2 x) ^ N2) := by
      intro i hi
      have hi' : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left (hb1 i (le_trans hi' hmn) s hs x) (Nat.cast_nonneg _)
      · exact hb2 (m - i) (le_trans (Nat.sub_le m i) hmn) s hs x
      · exact norm_nonneg _
      · exact mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (mul_nonneg hC1 hK1) hE)
    have hsum : ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) *
        (C1 * (1 + sq2 x) ^ N1 * Real.exp (-(sq2 x) / (κ * ageA ν s1))) *
          (C2 * (1 + sq2 x) ^ N2)
        = (2 : ℝ) ^ m * ((C1 * (1 + sq2 x) ^ N1 * Real.exp (-(sq2 x) / (κ * ageA ν s1))) *
          (C2 * (1 + sq2 x) ^ N2)) := by
      have hc : ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) = (2 : ℝ) ^ m := by
        exact_mod_cast Nat.sum_range_choose m
      rw [← Finset.sum_mul, ← Finset.sum_mul, hc]
      ring
    have hX : 0 ≤ (C1 * (1 + sq2 x) ^ N1 * Real.exp (-(sq2 x) / (κ * ageA ν s1))) *
          (C2 * (1 + sq2 x) ^ N2) :=
      mul_nonneg (mul_nonneg (mul_nonneg hC1 hK1) hE) (mul_nonneg hC2 hK2)
    have h2 : (2 : ℝ) ^ m ≤ (2 : ℝ) ^ n := pow_le_pow_right₀ (by norm_num) hmn
    refine le_trans key ?_
    refine le_trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm) (norm_nonneg B)) ?_
    rw [hsum]
    have e2 : ‖B‖ * ((2 : ℝ) ^ m * ((C1 * (1 + sq2 x) ^ N1 * Real.exp (-(sq2 x) / (κ * ageA ν s1))) *
          (C2 * (1 + sq2 x) ^ N2)))
        ≤ ‖B‖ * ((2 : ℝ) ^ n * ((C1 * (1 + sq2 x) ^ N1 * Real.exp (-(sq2 x) / (κ * ageA ν s1))) *
          (C2 * (1 + sq2 x) ^ N2))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h2 hX) (norm_nonneg B)
    refine le_trans e2 (le_of_eq ?_)
    rw [pow_add]
    ring

end UnforcedLeray.Short.PartIIIb.Concrete
