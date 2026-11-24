import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_1.Duhamel

/-!
# Periodicity of the Duhamel integral (`DuhamelPeriodic`)

`duhamel ν μ G (s, (q + c, η)) = duhamel ν μ G (s, (q, η))` for `s > 0`.
The integrand at fixed `σ` is `planeHeat (ν (s-σ)) (fun z => G (σ, z) i) (q,η)`; the periodicity of
`G` in `q` (`IsDriving.2.1`) makes the planar heat of the slice `c`-periodic
(`B0224.isPeriodic_planeHeat`), so the integrands agree pointwise and `integral_congr` applies.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

theorem duhamelPeriodic : DuhamelPeriodic := by
  intro c ν μ G hG s q η _hs
  funext i
  unfold duhamel
  apply intervalIntegral.integral_congr
  intro σ _hσ
  simp only
  congr 1
  have hper : UnforcedLeray.Cyl.IsPeriodic c (fun z : ℝ × ℝ => ((G (σ, z) i : ℝ) : ℂ)) := by
    intro z
    simp only [hG.2.1 σ z.1 z.2]
  have key := UnforcedLeray.B0224.isPeriodic_planeHeat (θ := ν * (s - σ)) hper (q, η)
  exact key

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
