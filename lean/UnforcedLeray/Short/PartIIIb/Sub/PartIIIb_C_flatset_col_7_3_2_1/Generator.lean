import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_3_2_1.ComplexAdjoint
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_3_2_1.AdjDeriv

/-!
# Generator identity `d/dt ⟨T₀(t)g, ζ⟩_H = ⟨T₀(t)g, A₀*ζ⟩_H` (`ν > 0`)

Source `the November 2 reference manuscript` 1650-1656. The proof combines the
complex adjoint identity `t0_complex_adjoint` and the strong derivative `t0adj_strong_deriv`
through `t0_generator_of` of `Sub/PartIII-b_C_flatset_col_7_3_2_1.lean`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped InnerProductSpace

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.B0220 (HSpace measureH Profile)
open UnforcedLeray.B0223 (MeridC)
open UnforcedLeray.Short.PartIIa (IsMeridTest)

theorem t0_generator (c ν : ℝ) (hc : 0 < c) (hν : 0 < ν) (g : HSpace c MeridC) (ζ : Profile → MeridC) (hζ : IsMeridTest c ζ) (t : ℝ) (ht : 0 < t) : HasDerivAt (fun s : ℝ => pairH c (UnforcedLeray.B0224.T0 hc ν s g : Profile → MeridC) ζ) (pairH c (UnforcedLeray.B0224.T0 hc ν t g : Profile → MeridC) (A0adj ν ζ)) t :=
  t0_generator_of t0_complex_adjoint t0adj_strong_deriv c ν hc hν g ζ hζ t ht

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
