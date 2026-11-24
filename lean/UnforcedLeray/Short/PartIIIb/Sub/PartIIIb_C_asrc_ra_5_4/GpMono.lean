import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_5_4

/-!
# `PartIII-b:C/asrc/ra/5/4/6`: `GP54` is monotone in the derivative order

Source of record: `the November 2 reference manuscript` lines 4963-4981, 4978.
A `C^n` function is `C^m` for `m ≤ n`, and the derivative bounds of order `≤ n` restrict to
those of order `≤ m`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem gp54_mono {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (κ ν : ℝ) (n m : ℕ) (hmn : m ≤ n) (f : ℝ × (ℝ × ℝ) → E) (hf : GP54 κ ν n f) : GP54 κ ν m f := by
  obtain ⟨hC, hB⟩ := hf
  refine ⟨hC.of_le (by exact_mod_cast hmn), ?_⟩
  intro s0 s1 hs0 hs01
  obtain ⟨C, N, hC0, hbd⟩ := hB s0 s1 hs0 hs01
  exact ⟨C, N, hC0, fun k hk => hbd k (le_trans hk hmn)⟩

end UnforcedLeray.Short.PartIIIb.Concrete
