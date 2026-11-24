import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_3_2_dec
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_3_2_3_2.Main

/-!
# `pepsC0SliceDivFreeAE` (task `PartIII-b:C/flatset/col/7/1/1/2/4/2/3/2/3/2`)

Source `the November 2 reference manuscript` 1650-1656, 1676.

For `b ∈ solenoidalHC 0 c`, a.e. slice `b_s` is weakly divergence free against every cylinder test.
The proof: (i) the test `χ(s) ψ(q,η)` in the Fubini identity gives `∫ χ(s) s^(-3/2) g_ψ(s) ds = 0`,
so `s^(-3/2) g_ψ` vanishes a.e. (fundamental lemma on `(0,∞)`, `Core.lean`); (ii) a countable
family of tests, dense in the uniform norm on `[0,c] × [-N,N]` for each `N`, makes the null set
independent of `ψ` (`Sep.lean`, `Slice.lean`, `Main.lean`); the helper files live in the folder
`PartIII-b_C_flatset_col_7_1_1_2_4_2_3_2_3_2/`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

theorem pepsC0SliceDivFreeAE : PepsC0SliceDivFreeAE := by
  intro c hc b hb
  exact hj3_main hc b hb

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
