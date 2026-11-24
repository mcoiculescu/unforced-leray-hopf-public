import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_1
import UnforcedLeray.Short.PartIIIa.Compose
import UnforcedLeray.Cons.L2.BackgroundConcrete.GraphStateSymmetry
import UnforcedLeray.Cons.L2.BackgroundConcrete.Operators
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.Defs

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **Leaf `RbFacts`** (source 2031, 2522-2523, 2664-2713): the repair `r_b = p.corr z` of the exact
split is axisymmetric without swirl, `2c/R`-periodic in `τ`, and a.e.-strongly measurable. -/
theorem rbFacts : RbFacts := by
  intro Pl K L S hsplit hP
  obtain ⟨z, -, -, hrb, -⟩ := hsplit.state
  have hperiod : (L.params Pl).period = 2 * L.ε * cOf L.ν := rfl
  have hP1 : (L.params Pl).period ≤ 1 := by rw [hperiod]; exact hP
  have hshift : 2 * cOf L.ν / L.ε⁻¹ = (L.params Pl).period := by
    rw [hperiod, div_inv_eq_mul]; ring
  refine ⟨fun τ => ?_, fun τ y => ?_, fun τ => ?_⟩
  · rw [hrb]
    exact axiNoSwirlPt_of_ae
      ((UnforcedLeray.Short.IIIa.corr_continuous (L.params Pl) hP1 z).comp (continuous_const.prodMk continuous_id))
      ((L.params Pl).corr_isAxisymmetricNoSwirl hP1 z τ)
  · rw [hrb, hshift]
    exact congrFun ((L.params Pl).corr_periodic z τ) y
  · rw [hrb]
    exact ((UnforcedLeray.Short.IIIa.corr_continuous (L.params Pl) hP1 z).comp
      (continuous_const.prodMk continuous_id)).aestronglyMeasurable

end UnforcedLeray.Short.PartIIIb.Concrete
