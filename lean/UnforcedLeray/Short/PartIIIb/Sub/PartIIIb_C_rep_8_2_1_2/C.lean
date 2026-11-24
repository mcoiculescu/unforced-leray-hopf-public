import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_1_2

/-!
# `ChartId`: the similarity chart inverts `(chartTau, chartY)` (`PartIII-b:C/rep/8/2/1/2`, (C))

Source `the November 2 reference manuscript`,
lines 2073-2075 (`s = R²/ϱ²`, `ξ = Rτ/2 - (R/2) log s`, `η = R y₃/ϱ`).
At `y = (R/√s, 0, η/√s)` one has `ϱ y = R/√s`, so `age = s`, `trans = η`, `phase = q`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Axi

theorem chartId : ChartId := by
  intro R p hR hp0
  have hs : 0 < Real.sqrt p.1 := Real.sqrt_pos.2 hp0
  have hsne : Real.sqrt p.1 ≠ 0 := hs.ne'
  have hRne : R ≠ 0 := hR.ne'
  have h0 : NearInst.chartY R p 0 = R / Real.sqrt p.1 := by
    simp [NearInst.chartY]
  have h1 : NearInst.chartY R p 1 = 0 := by
    simp [NearInst.chartY]
  have h2 : NearInst.chartY R p 2 = p.2.2 / Real.sqrt p.1 := by
    simp [NearInst.chartY]
  have hϱ : ϱ (NearInst.chartY R p) = R / Real.sqrt p.1 := by
    unfold ϱ
    rw [h0, h1, show (R / Real.sqrt p.1) ^ 2 + (0 : ℝ) ^ 2 = (R / Real.sqrt p.1) ^ 2 by ring]
    exact Real.sqrt_sq (div_nonneg hR.le hs.le)
  have hage : UnforcedLeray.Axi.age R (NearInst.chartY R p) = p.1 := by
    unfold UnforcedLeray.Axi.age
    rw [hϱ, div_pow, Real.sq_sqrt hp0.le]
    field_simp
  have htr : UnforcedLeray.Axi.trans R (NearInst.chartY R p) = p.2.2 := by
    unfold UnforcedLeray.Axi.trans
    rw [hϱ, h2]
    field_simp
  have hph : phase R (NearInst.chartTau R p) (NearInst.chartY R p) = p.2.1 := by
    unfold UnforcedLeray.Axi.phase NearInst.chartTau
    rw [hage]
    field_simp
    ring
  unfold UnforcedLeray.Axi.chart
  exact Prod.ext hage (Prod.ext hph htr)

end UnforcedLeray.Short.PartIIIb.Concrete
