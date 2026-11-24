import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_cancelOrg

/-!
# `EarlyPartThin`: the early part of a thin stress is thin (source 4163-4166)

`χ_o` acts componentwise (`chiOStr`), and `thinPart T = (T₁, 0)`, so `χ_o (thinPart T)` again has
zero repair component and `thinPart` fixes it.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

variable {c mZ ρb γ ν : ℝ}

theorem thinPart_thinPart_eq (T : StrG c mZ ρb γ ν) :
    thinPart (thinPart T) = thinPart T := by
  apply (WithLp.prodContinuousLinearEquiv 1 ℝ (Lp (α := Chart) Ten3 2 (gainZ1Measure c mZ γ ν))
    (Lp (α := Chart) Ten3 2 (gainHTMeasure c ρb γ ν))).injective
  simp [thinPart]

theorem thinPart_chiOStr_thinPart_eq {χ : ℝ → ℝ} (hχ : IsOutwardCutoff χ)
    (T : StrG c mZ ρb γ ν) :
    thinPart (chiOStr c mZ ρb γ ν hχ (thinPart T)) = chiOStr c mZ ρb γ ν hχ (thinPart T) := by
  apply (WithLp.prodContinuousLinearEquiv 1 ℝ (Lp (α := Chart) Ten3 2 (gainZ1Measure c mZ γ ν))
    (Lp (α := Chart) Ten3 2 (gainHTMeasure c ρb γ ν))).injective
  simp [thinPart, chiOStr]

theorem earlyPartThin : EarlyPartThin := by
  intro c mZ ρb γ ν χ hχ T
  rw [map_sub, thinPart_thinPart_eq, thinPart_chiOStr_thinPart_eq hχ]

end UnforcedLeray.Short.PartIIIb.Concrete
