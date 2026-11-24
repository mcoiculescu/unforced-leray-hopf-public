import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_4_1
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_4_2

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem hhatSolenoidal_of {c mZ ρb γ ν : ℝ} {Aff : Type} [NormedAddCommGroup Aff]
    [NormedSpace ℝ Aff] [CompleteSpace Aff] (B : ReturnBase c mZ ρb γ ν Aff)
    {ι : Aff →ₗ[ℝ] (ℝ → Mat3)} {χf : ℝ → ℝ} {μ ε as : ℝ} (hχf : IsSourceCutoffC χf)
    (hι : ∀ A, IsAffElem as (ι A)) (hc : 0 < c) (hcν : c = cOf ν) (hν : 0 < ν) (hε : 0 < ε)
    (hAff : IsAffinePinned B ι χf μ ε) : HhatSolenoidal B ε := by
  intro A φ hφ
  rw [hhatTransfer_of B hc hcν hν hε hAff A φ hφ]
  exact hhatChartSolenoidal_of hχf hι hc hcν hν hε A φ hφ

end UnforcedLeray.Short.PartIIIb.Concrete
