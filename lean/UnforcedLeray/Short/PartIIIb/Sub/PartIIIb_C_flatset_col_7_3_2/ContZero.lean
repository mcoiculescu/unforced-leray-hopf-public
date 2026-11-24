import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_3_2_2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_3_2_2.StrongContZero

/-!
# `PartIII-b:C/flatset/col/7/3/2/2` (`t0_contZero`): right-continuity of the pairing at `0`

Source `the November 2 reference manuscript` 1650-1656. Proof: `t0_contZero_of`
applied to the strong continuity `t0_strong_cont_zero`.
-/

set_option autoImplicit false

noncomputable section

open UnforcedLeray.B0220 (HSpace measureH Profile)
open UnforcedLeray.B0223 (MeridC)
open UnforcedLeray.Short.PartIIa (IsMeridTest)

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

theorem t0_contZero (c ν : ℝ) (hc : 0 < c) (g : HSpace c MeridC) (ζ : Profile → MeridC)
    (hζ : IsMeridTest c ζ) :
    ContinuousWithinAt
      (fun s : ℝ => pairH c (UnforcedLeray.B0224.T0 hc ν s g : Profile → MeridC) ζ) (Set.Ici 0) 0 :=
  t0_contZero_of t0_strong_cont_zero c ν hc g ζ hζ

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

end
