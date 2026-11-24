import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_1_2.Reduce
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_1_4.Of

/-!
# `FlatForceClosed` (decomposition of `PartIII-b:C/flatset/col/1/2`, leaf 1)

Source of record `the November 2 reference manuscript`: 4594-4596, 4976.

The components of `f_A` at a point `x = (q, η)` are minus the lattice sums of `ftF1`, `ftF2`
(`fMer_components`, `Sub/PartIII-b_C_flatset_col_1_4/Of.lean`).  That lemma proves the
coordinate-wise `tsum` identity via `ft_fTerm_closed` and summability of the lattice terms
(Gaussian bounds), so the statement at a general `x` is its instance at `(x.1, x.2)`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

theorem flatForceClosed : FlatForceClosed := by
  intro ν μ χ A s hν hs x
  obtain ⟨q, η⟩ := x
  exact fMer_components ν μ χ A s hν hs q η

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
