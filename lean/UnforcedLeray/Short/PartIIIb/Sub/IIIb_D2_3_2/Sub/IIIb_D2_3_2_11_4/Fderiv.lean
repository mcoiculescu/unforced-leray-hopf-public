import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.Sub.IIIb_D2_3_2_11_4

/-!
# Chain rule for equivariant fields (`PartIII-b:IIIb-D2/3/2/11/4`, source 121-124, 6314-6316)

`fderivEqv_proved`: if a differentiable field `F` commutes with a linear isometry `g`, then
its derivative is equivariant, `D F (g y) (g v) = g (D F y v)`.  Proof: `F ∘ g = g ∘ F`, so the
two chain-rule expressions for the derivative of this composite agree (`HasFDerivAt.unique`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem fderivEqv_proved : FderivEqv := by
  intro g F hF hG y v
  have hFun : F ∘ (g : Space → Space) = (g : Space → Space) ∘ F := funext fun x => hG x
  have hA : HasFDerivAt ((g : Space → Space) ∘ F)
      (g.toContinuousLinearEquiv.toContinuousLinearMap.comp (fderiv ℝ F y)) y :=
    g.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.comp y (hF y).hasFDerivAt
  have hB : HasFDerivAt (F ∘ (g : Space → Space))
      ((fderiv ℝ F ((g : Space → Space) y)).comp g.toContinuousLinearEquiv.toContinuousLinearMap) y :=
    (hF ((g : Space → Space) y)).hasFDerivAt.comp y
      g.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt
  rw [hFun] at hB
  have heq := hB.unique hA
  have h := congrArg (fun M : Space →L[ℝ] Space => M v) heq
  simpa using h

end UnforcedLeray.Short.PartIIIb.Concrete
