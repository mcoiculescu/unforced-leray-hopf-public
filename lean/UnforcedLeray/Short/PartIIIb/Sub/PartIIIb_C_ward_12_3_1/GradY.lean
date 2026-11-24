import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.Bg.YoungW2.Corr.Sub
import UnforcedLeray.Short.PartIIa.Tasks.F06GraphBound
import UnforcedLeray.Cons.L2.BackgroundConcrete.Spaces
import UnforcedLeray.Units.B0412

/-!
# `BgCorrGradY` (source 2533 "Dw in Y_p is already known", 1351-1362)

Task `PartIII-b:C/ward/12/3/1/1`.  Source of record
`the November 2 reference manuscript`.

The correction `w = wOf z` lies in `X_{q₀} ⊆ D_{q₀}` (`cw_mem_X`, `X_le_D`).  The common
body graph bound at `μ = 0` (admissible since `γ_{q₀} > 0`) then gives a distributional
gradient `g` of `w` in `Y_{q₀}`.  The shift is `ν₀ = dm³/12`, which yields `P ≤ 1`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem bgCorrGradY : BgCorrGradY := by
  intro lam q hq dm dp hdm
  refine ⟨dm ^ 3 / 12, by positivity, ?_⟩
  intro p d hreg hν hmode z hPE
  have hP1 : p.period ≤ 1 := bgCorr_period_le_one hreg hν
  have hw : p.wOf z ∈ UnforcedLeray.B0412.X p.period p.ν UnforcedLeray.B0412.q0E :=
    UnforcedLeray.Cons.C03.Concrete.cw_mem_X z
  have hD : p.wOf z ∈ UnforcedLeray.B0411.D p.period p.ν UnforcedLeray.B0412.q0E :=
    UnforcedLeray.B0412.X_le_D hw
  obtain ⟨C, -, hB⟩ := UnforcedLeray.Short.PartIIa.commonBodyGraphBound
    UnforcedLeray.B0412.q0E q0E_gt_one q0E_lt_three
  obtain ⟨g, hg, -⟩ := hB p.period hP1 p.ν p.ν_pos 0 (by simpa using gammaR_q0E_pos)
    ⟨p.wOf z, hD⟩
  exact ⟨g, hg⟩

end UnforcedLeray.Short.PartIIIb.Concrete
