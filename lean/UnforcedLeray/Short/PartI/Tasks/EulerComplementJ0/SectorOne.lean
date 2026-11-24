import UnforcedLeray.Short.PartI.Sub.PartI_S15
import UnforcedLeray.Lib.ComplexODEC.SectorOne
import UnforcedLeray.Lib.PlanarSpectralB.SimpleProj

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Real
open scoped ENNReal ComplexConjugate ContDiff Topology

namespace UnforcedLeray.Short.PartI

theorem sectorOneStableAll : SectorOneStableAll := by
  intro M hM n hn z w hz hw
  rcases Int.natAbs_eq_iff.1 hn with h | h
  · -- n = 1
    have hn1 : n = 1 := by exact_mod_cast h
    subst hn1
    exact UnforcedLeray.ComplexODEC.sector_one_eigen_eq_zero hM hz hw
  · -- n = -1: conjugate to sector 1
    have hn1 : n = -1 := by exact_mod_cast h
    subst hn1
    have hstar := UnforcedLeray.Planar.Lsec_star_eigen hM hw
    rw [neg_neg] at hstar
    have hre : 0 < (starRingEnd ℂ z).re := by simpa using hz
    have hs := UnforcedLeray.ComplexODEC.sector_one_eigen_eq_zero hM hre hstar
    by_contra hne
    exact UnforcedLeray.Planar.star_ne_zero_prof hne hs

end UnforcedLeray.Short.PartI
