import UnforcedLeray.Short.PartIIIb.Concrete.ReturnOps.Targets

/-!
# `C/ret/11`: `χ_o` multiplies both stress components pointwise (source 4163-4166)
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem chiOStrApply : ChiOStrApply := by
  intro c mZ ρb γ ν χ hχ T
  constructor
  · exact NearInst.mulBdd_apply_ae (E := Ten3) (μ := gainZ1Measure c mZ γ ν)
      (cutFun χ ν) (cutFun_measurable hχ ν) 1 (cutFun_bound hχ ν) (WithLp.fst T)
  · exact NearInst.mulBdd_apply_ae (E := Ten3) (μ := gainHTMeasure c ρb γ ν)
      (cutFun χ ν) (cutFun_measurable hχ ν) 1 (cutFun_bound hχ ν) (WithLp.snd T)

end UnforcedLeray.Short.PartIIIb.Concrete
