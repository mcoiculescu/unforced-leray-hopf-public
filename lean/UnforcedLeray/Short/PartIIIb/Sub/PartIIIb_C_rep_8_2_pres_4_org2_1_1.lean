import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_4_org2_1_org
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GELinSub.rawSmoothBdd_Sub.Sub.RingLiftOffAxis_Sub.RingLiftPtJet

/-!
# Organizer task `PartIII-b:C/rep/8/2/pres/4/org2/1/1`: `ringLiftChartPt`

Source `the November 2 reference manuscript` 1206-1222 (ring chart `s = R²/ρ²`,
`q`, `η = R y₃/ρ`), 2360-2366. Chart-point form of the proved `RingLiftPtJet`: at `y = chartY R x`,
`τ = chartTau R x`, the chart round trip `chart R τ y = x` gives `age R y = x.1` and
`trans R y = x.2.2`, and `y` is off the axis.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology UnforcedLeray.Axi
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Local copy of the chart-point facts of the similarity point `y = chartY R p`, `s = p.1 > 0`
(the same statement as `fe_chartY_facts`, re-proved here to avoid the import conflict). -/
private theorem rlc_chartY_facts {R : ℝ} (hR : 0 < R) (p : Chart) (hp : 0 < p.1) :
    NearInst.chartY R p 0 = R / Real.sqrt p.1 ∧ NearInst.chartY R p 1 = 0 ∧
      ϱ (NearInst.chartY R p) = R / Real.sqrt p.1 ∧
      Axi.age R (NearInst.chartY R p) = p.1 := by
  have hs : 0 < Real.sqrt p.1 := Real.sqrt_pos.2 hp
  have hy0 : NearInst.chartY R p 0 = R / Real.sqrt p.1 := by simp [NearInst.chartY]
  have hy1 : NearInst.chartY R p 1 = 0 := by simp [NearInst.chartY]
  have hϱ : ϱ (NearInst.chartY R p) = R / Real.sqrt p.1 := by
    unfold ϱ
    rw [hy0, hy1, show (R / Real.sqrt p.1) ^ 2 + (0 : ℝ) ^ 2 = (R / Real.sqrt p.1) ^ 2 by ring]
    exact Real.sqrt_sq (div_nonneg hR.le hs.le)
  refine ⟨hy0, hy1, hϱ, ?_⟩
  have hR0 : R ≠ 0 := hR.ne'
  unfold Axi.age
  rw [hϱ, div_pow, Real.sq_sqrt hp.le]
  field_simp

/-- Local copy of the chart round trip `chart R (chartTau R p) (chartY R p) = p` (`s = p.1 > 0`). -/
private theorem rlc_chart_roundtrip {R : ℝ} (hR : 0 < R) (p : Chart) (hp : 0 < p.1) :
    Axi.chart R (NearInst.chartTau R p) (NearInst.chartY R p) = p := by
  obtain ⟨hy0, hy1, hϱ, hage⟩ := rlc_chartY_facts hR p hp
  have hs : 0 < Real.sqrt p.1 := Real.sqrt_pos.2 hp
  have hR0 : R ≠ 0 := hR.ne'
  have hsq : Real.sqrt p.1 ≠ 0 := hs.ne'
  have htrans : Axi.trans R (NearInst.chartY R p) = p.2.2 := by
    unfold Axi.trans
    rw [hϱ, show NearInst.chartY R p 2 = p.2.2 / Real.sqrt p.1 by simp [NearInst.chartY]]
    field_simp
  have hphase : Axi.phase R (NearInst.chartTau R p) (NearInst.chartY R p) = p.2.1 := by
    unfold Axi.phase NearInst.chartTau
    rw [hage]
    field_simp
    ring
  unfold Axi.chart
  rw [hage, hphase, htrans]

theorem ringLiftChartPt : RingLiftChartPt := by
  intro j
  obtain ⟨C, k, hC, h⟩ := ringLiftPtJet j
  refine ⟨C, k, hC, ?_⟩
  intro R b hR hb x hx
  have hR0 : 0 < R := lt_of_lt_of_le one_pos hR
  have hyF := rlc_chartY_facts hR0 x hx
  have hrt := rlc_chart_roundtrip hR0 x hx
  have hy : NearInst.chartY R x ∉ axis := by
    intro hmem
    have h0 : NearInst.chartY R x 0 = 0 := hmem.1
    rw [hyF.1] at h0
    exact (div_pos hR0 (Real.sqrt_pos.2 hx)).ne' h0
  have hage : Axi.age R (NearInst.chartY R x) = x.1 := hyF.2.2.2
  have htrans : Axi.trans R (NearInst.chartY R x) = x.2.2 := by
    have h2 := congrArg (fun p : Chart => p.2.2) hrt
    exact h2
  have hb' := (h R (NearInst.chartTau R x) b hR hb).2 (NearInst.chartY R x) hy
  rw [hrt, hage, htrans] at hb'
  exact hb'

end UnforcedLeray.Short.PartIIIb.Concrete
