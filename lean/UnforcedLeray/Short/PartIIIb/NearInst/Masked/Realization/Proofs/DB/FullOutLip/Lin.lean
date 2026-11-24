import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.Proofs.DB.FullOutLip.Lin.Core

/-!
# `fullOutSubLin` (source 3611-3621, 3604-3610): linearity of `fullOut` on box tensors

`fullOut` reads the tensor through `cartLift`, which is linear (`cartLift_sub`); `sepW` is linear
in the source (`sepW_sub_fun`, integrability from `GradKL1` and the kernel sup bound); the
meridional real part and the scalar `(√s)⁻¹` are linear.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization

open UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Short.PartIIIb.NearInst

theorem merRe_sub_lin (w v : Fin 3 → ℂ) : merRe (w - v) = merRe w - merRe v := by
  ext i
  fin_cases i <;> simp [merRe]

theorem merRe_neg_sub_lin (A B : Fin 3 → ℂ) :
    merRe (-(A - B)) = merRe (-A) - merRe (-B) := by
  rw [show -(A - B) = -A - -B by abel]
  exact merRe_sub_lin _ _

/-- **Linearity** (source 3611-3621): on box tensors `fullOut` is additive in the tensor. -/
theorem fullOutSubLin : FullOutSubLin := by
  intro R c ν μ hR hc hν hμ f g hf hg x
  have hfun : NearInst.cartLift R c (fun p => f p - g p) =
      fun τ' z => NearInst.cartLift R c f τ' z - NearInst.cartLift R c g τ' z :=
    funext fun τ' => funext fun z => LinAux.cartLift_sub R c f g τ' z
  unfold NearInst.Masked.fullOut
  rw [hfun, LinAux.sepW_sub_fun ν μ hν hμ _ _ (LinAux.goodT_of_box R c hR f hf)
    (LinAux.goodT_of_box R c hR g hg) (chartY R x) (chartTau R x), merRe_neg_sub_lin, smul_sub]

end UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization
