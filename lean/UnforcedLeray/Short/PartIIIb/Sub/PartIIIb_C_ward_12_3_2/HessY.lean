import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_2
import UnforcedLeray.Short.PartIIa.Tasks.F06GraphBound

/-!
# `BgCorrHessY`: the distributional gradients `g_j` of `g_j ∈ D_p` lie in `Y_p`

Task `PartIII-b:C/ward/12/3/2/1`.  Source of record
`the November 2 reference manuscript`
(source 2552-2559, graph bound 1351-1362).  Each `g_j ∈ D_p` is an element of the common body
domain at `r = q0E`, so `bg:common-body-graph` (`commonBodyGraphBound`) gives a gradient in `Y_p`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace
open UnforcedLeray.Cons.C03.Concrete (Params)

/-- **`PartIII-b:C/ward/12/3/2/1`**: every `∂_l g_j` exists in `Y_p`. -/
theorem bgCorrHessY : BgCorrHessY := by
  intro lam q hq dm dp hdm
  refine ⟨dm ^ 3 / 12, by positivity, ?_⟩
  intro p d hreg hν hmode z hPE g hg
  have hP1 : p.period ≤ 1 := bgCorr_period_le_one hreg hν
  have hGall : ∀ j : Fin 3, ∃ G : Fin 3 → Yq p.period UnforcedLeray.B0412.q0E,
      UnforcedLeray.Short.PartIIa.HasGrad
        (g j : Yq p.period UnforcedLeray.B0412.q0E) G := by
    intro j
    obtain ⟨_, _, hC⟩ := UnforcedLeray.Short.PartIIa.commonBodyGraphBound
      UnforcedLeray.B0412.q0E q0E_gt_one2 q0E_lt_three2
    obtain ⟨G, hG, _⟩ := hC p.period hP1 p.ν p.ν_pos 0
      (by simpa using gammaR_q0E_pos2) (g j)
    exact ⟨G, hG⟩
  choose G hG using hGall
  exact ⟨G, fun j l => hG j l⟩

end UnforcedLeray.Short.PartIIIb.Concrete
