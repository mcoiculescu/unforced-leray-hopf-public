import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Inverses.Leaves
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.TruncMemY

/-!
# `Y_2` is a linear space (source 1341-1344)

Proof of `YrSub`: the difference is the sum of `w` and `(-1) • w'`, and the latter lies in
`Y_2` by the bounded-multiplier lemma `isInYr_smul_of_bdd`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

theorem yrSub : YrSub := by
  intro P w w' hP hw hw'
  have hneg : UnforcedLeray.Short.IIb.IsInYr P 2 (fun x => (-1 : ℝ) • w' x) :=
    isInYr_smul_of_bdd hP (a := fun _ => (-1 : ℝ)) (M := 1) aestronglyMeasurable_const
      (fun _ => by norm_num) (Filter.Eventually.of_forall fun _ => rfl) hw'
  exact isInYr_add2 hP (F := w - w') (u := w) (v := fun x => (-1 : ℝ) • w' x)
    (fun x => by simp [sub_eq_add_neg]) hw hneg

end UnforcedLeray.Short.PartIIIb.Concrete
