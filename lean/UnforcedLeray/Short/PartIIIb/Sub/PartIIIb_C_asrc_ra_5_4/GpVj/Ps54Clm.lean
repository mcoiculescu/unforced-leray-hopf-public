import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_5_4

/-!
# `PartIII-b:C/asrc/ra/5/4/11` helper : post-composition with a continuous linear map preserves `PS54`

Source of record: `the November 2 reference manuscript` lines 4963-4981, 4978.
This is the `PS54` analogue of `gp54_clm` (`GpClm.lean`): the polynomial bounds pass to `L ∘ f`
with constant `‖L‖ * C` and the same exponent `N`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem ps54_clm {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E →L[ℝ] F) (n : ℕ) (f : ℝ × (ℝ × ℝ) → E) (hf : PS54 n f) : PS54 n (fun p => L (f p)) := by
  obtain ⟨hC, hB⟩ := hf
  refine ⟨L.contDiff.comp_contDiffOn hC, ?_⟩
  intro s0 s1 hs0 hs01
  obtain ⟨C, N, hC0, hbd⟩ := hB s0 s1 hs0 hs01
  refine ⟨‖L‖ * C, N, mul_nonneg (norm_nonneg _) hC0, fun m hm s hs x => ?_⟩
  have hp : (s, x) ∈ Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)) :=
    ⟨lt_of_lt_of_le hs0 hs.1, trivial⟩
  have hda : ContDiffAt ℝ ((n : ℕ) : WithTop ℕ∞) f (s, x) :=
    hC.contDiffAt ((isOpen_Ioi.prod isOpen_univ).mem_nhds hp)
  have h1 := L.norm_iteratedFDeriv_comp_left hda (by exact_mod_cast hm)
  calc ‖iteratedFDeriv ℝ m (fun p => L (f p)) (s, x)‖
      ≤ ‖L‖ * ‖iteratedFDeriv ℝ m f (s, x)‖ := h1
    _ ≤ ‖L‖ * (C * (1 + sq2 x) ^ N) :=
        mul_le_mul_of_nonneg_left (hbd m hm s hs x) (norm_nonneg _)
    _ = ‖L‖ * C * (1 + sq2 x) ^ N := by ring

end UnforcedLeray.Short.PartIIIb.Concrete
