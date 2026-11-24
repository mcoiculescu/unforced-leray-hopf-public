import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_3_2_2_1_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_3_2_2_1_1.Dense
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_3_2_2_1_1.Conv

/-!
# Strong continuity at age `0` of the age dilation `D_{e^{-s}}` on `H`

Source `the November 2 reference manuscript` lines 1650-1656.

The reduction `tendsto_dilH_exp_neg_zero_of` (density class `DilDenseGood`, convergence on the
class `DilGoodConv`) is proved in `Sub/PartIII-b_C_flatset_col_7_3_2_2_1_1.lean`; the two analytic
inputs are supplied by `dilDenseGood_holds` (Dense.lean) and `dilGoodConv_holds` (Conv.lean).
-/

set_option autoImplicit false

noncomputable section

theorem tendsto_dilH_exp_neg_zero (c : ℝ) (g : UnforcedLeray.B0220.HSpace c UnforcedLeray.B0223.MeridC) : Filter.Tendsto (fun s : ℝ => UnforcedLeray.B0224.dilH (Real.exp_pos (-s)) g) (nhdsWithin 0 (Set.Ici 0)) (nhds g) :=
  UnforcedLeray.Short.PartIIIb.Concrete.DilStrong.tendsto_dilH_exp_neg_zero_of
    (fun c hc => UnforcedLeray.Short.PartIIIb.Concrete.DilStrong.dilDenseGood_holds c hc)
    (fun c hc => UnforcedLeray.Short.PartIIIb.Concrete.DilStrong.dilGoodConv_holds c hc) c g

end
