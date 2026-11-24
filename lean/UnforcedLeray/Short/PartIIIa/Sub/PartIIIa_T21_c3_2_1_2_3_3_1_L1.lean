import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_regime
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_2_3_3_1_1_A
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_2_3_3_1_1_B

theorem movSolTestedDuhamelSmall :
    UnforcedLeray.Short.IIIa.ComplMildTestedSplit.MovSolTestedDuhamelSmall :=
  UnforcedLeray.Short.IIIa.ComplMildTestedSplit.Regime.movSolTestedDuhamelSmall_of'
    UnforcedLeray.Short.IIIa.ComplMildTestedSplit.movSolExistsSmall
    UnforcedLeray.Short.IIIa.ComplMildTestedSplit.movSolDuhamelOfSmall
