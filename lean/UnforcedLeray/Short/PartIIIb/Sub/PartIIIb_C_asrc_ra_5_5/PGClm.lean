import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_5_5

/-!
# `PartIII-b:C/asrc/ra/5/5` : polynomial growth is stable under a continuous linear map

Used for `PhpA` in `GhpA = e^{-|y|²/(4a)} • PhpA`: `L ∘ P` keeps `PolyGrowth`
(composition with a continuous linear map commutes with the derivatives).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem polyGrowth_clm {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (n : ℕ) (L : E →L[ℝ] F)
    (P : ℝ × (ℝ × ℝ) → E) (hP : PolyGrowth n P) : PolyGrowth n (fun p => L (P p)) := by
  obtain ⟨hcd, hb⟩ := hP
  refine ⟨L.contDiff.comp_contDiffOn hcd, ?_⟩
  intro s0 s1 hs0 hs01
  obtain ⟨C, N, hC, hbd⟩ := hb s0 s1 hs0 hs01
  refine ⟨‖L‖ * C, N, by positivity, ?_⟩
  intro m hm s hs x
  have hmem : (s, x) ∈ Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)) :=
    ⟨lt_of_lt_of_le hs0 hs.1, trivial⟩
  have hopen : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) :=
    isOpen_Ioi.prod isOpen_univ
  have hat : ContDiffAt ℝ (n : WithTop ℕ∞) P (s, x) :=
    hcd.contDiffAt (hopen.mem_nhds hmem)
  have hn : ((m : ℕ) : WithTop ℕ∞) ≤ (n : WithTop ℕ∞) := by exact_mod_cast hm
  have h1 := L.norm_iteratedFDeriv_comp_left (f := P) (x := (s, x)) (N := (n : WithTop ℕ∞))
    (n := m) hat hn
  have h2 := hbd m hm s hs x
  calc ‖iteratedFDeriv ℝ m (fun p => L (P p)) (s, x)‖
      ≤ ‖L‖ * ‖iteratedFDeriv ℝ m P (s, x)‖ := h1
    _ ≤ ‖L‖ * (C * (1 + sq2 x) ^ N) := mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
    _ = ‖L‖ * C * (1 + sq2 x) ^ N := by ring

end UnforcedLeray.Short.PartIIIb.Concrete
