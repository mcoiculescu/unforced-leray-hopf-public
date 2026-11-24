import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_1_1

/-!
# Ring-chart bridge at azimuth zero (`PartIII-b:C/rep/8/2/1/1/1`)

Source `the November 2 reference manuscript` lines 2073-2077, 5460-5461.
At the chart point `p = (s,(q,η))` with `s > 0` and `R = ε⁻¹`, the point `y = chartY R p` is off the
axis and the ring chart returns `p`; the raw lift is `√s (b₀ e_r + b₁ e_z)` with `e_r = e₁`,
`e_z = e₃` at azimuth zero.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Blueprint.Planar (PlanarData)

/-- `ϱ(chartY R p) = R/√s`. -/
theorem ringBridge_varrho {R : ℝ} (hR : 0 < R) {p : Chart} (hs : 0 < p.1) :
    UnforcedLeray.Axi.ϱ (NearInst.chartY R p) = R / Real.sqrt p.1 := by
  have h : 0 < R / Real.sqrt p.1 := div_pos hR (Real.sqrt_pos.2 hs)
  unfold UnforcedLeray.Axi.ϱ NearInst.chartY
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  rw [show (R / Real.sqrt p.1) ^ 2 + 0 ^ 2 = (R / Real.sqrt p.1) ^ 2 by ring]
  exact Real.sqrt_sq h.le

theorem ringBridge_y0 {R : ℝ} {p : Chart} :
    NearInst.chartY R p 0 = R / Real.sqrt p.1 := by
  simp [NearInst.chartY]

theorem ringBridge_y1 {R : ℝ} {p : Chart} :
    NearInst.chartY R p 1 = 0 := by
  simp [NearInst.chartY]

theorem ringBridge_y2 {R : ℝ} {p : Chart} :
    NearInst.chartY R p 2 = p.2.2 / Real.sqrt p.1 := by
  simp [NearInst.chartY]

theorem ringBridge_off_axis {R : ℝ} (hR : 0 < R) {p : Chart} (hs : 0 < p.1) :
    NearInst.chartY R p ∉ UnforcedLeray.Axi.axis := by
  rintro ⟨h0, -⟩
  rw [ringBridge_y0] at h0
  exact (div_pos hR (Real.sqrt_pos.2 hs)).ne' h0

theorem ringBridge_age {R : ℝ} (hR : 0 < R) {p : Chart} (hs : 0 < p.1) :
    UnforcedLeray.Axi.age R (NearInst.chartY R p) = p.1 := by
  have hR0 : R ≠ 0 := hR.ne'
  have hsq : 0 < Real.sqrt p.1 := Real.sqrt_pos.2 hs
  unfold UnforcedLeray.Axi.age
  rw [ringBridge_varrho hR hs, div_pow, Real.sq_sqrt hs.le]
  field_simp

theorem ringBridge_phase {R : ℝ} (hR : 0 < R) {p : Chart} (hs : 0 < p.1) :
    UnforcedLeray.Axi.phase R (NearInst.chartTau R p) (NearInst.chartY R p) = p.2.1 := by
  have hR0 : R ≠ 0 := hR.ne'
  unfold UnforcedLeray.Axi.phase NearInst.chartTau
  rw [ringBridge_age hR hs]
  field_simp
  ring

theorem ringBridge_trans {R : ℝ} (hR : 0 < R) {p : Chart} (hs : 0 < p.1) :
    UnforcedLeray.Axi.trans R (NearInst.chartY R p) = p.2.2 := by
  have hR0 : R ≠ 0 := hR.ne'
  have hsq : 0 < Real.sqrt p.1 := Real.sqrt_pos.2 hs
  unfold UnforcedLeray.Axi.trans
  rw [ringBridge_varrho hR hs, ringBridge_y2]
  field_simp

theorem ringBridge_chart {R : ℝ} (hR : 0 < R) {p : Chart} (hs : 0 < p.1) :
    UnforcedLeray.Axi.chart R (NearInst.chartTau R p) (NearInst.chartY R p) = p := by
  unfold UnforcedLeray.Axi.chart
  rw [ringBridge_age hR hs, ringBridge_phase hR hs, ringBridge_trans hR hs]

theorem ringBridge_eR_zero {R : ℝ} (hR : 0 < R) {p : Chart} (hs : 0 < p.1) :
    UnforcedLeray.Axi.eR (NearInst.chartY R p) 0 = 1 := by
  rw [UnforcedLeray.Axi.eR_apply_zero, ringBridge_varrho hR hs, ringBridge_y0]
  exact div_self (div_pos hR (Real.sqrt_pos.2 hs)).ne'

theorem ringBridge_eR_one {R : ℝ} {p : Chart} :
    UnforcedLeray.Axi.eR (NearInst.chartY R p) 1 = 0 := by
  rw [UnforcedLeray.Axi.eR_apply_one, ringBridge_y1]
  simp

theorem ringBridge_frame {R : ℝ} (hR : 0 < R) {p : Chart} (hs : 0 < p.1) (b0 b1 : ℝ) :
    b0 • UnforcedLeray.Axi.eR (NearInst.chartY R p) + b1 • UnforcedLeray.Axi.e3 =
      vecSp ![b0, 0, b1] := by
  ext i
  fin_cases i
  · simp [ringBridge_eR_zero hR hs, vecSp]
  · simp [ringBridge_y1, vecSp]
  · simp [vecSp]

/-- **The ring-chart bridge** (source 2073-2077, 5460-5461). -/
theorem ringChartBridge : RingChartBridge := by
  intro Pl L p hp
  have hR : 0 < L.ε⁻¹ := inv_pos.2 L.ε_pos
  have hY : NearInst.chartY L.ε⁻¹ p ∉ UnforcedLeray.Axi.axis := ringBridge_off_axis hR hp
  have hraw : rawU Pl L (NearInst.chartTau L.ε⁻¹ p) (NearInst.chartY L.ε⁻¹ p) =
      UnforcedLeray.Axi.Nv L.ε⁻¹ (UnforcedLeray.Cons.C03.rawProfile L.ε L.train.v L.train.ψ)
        (NearInst.chartTau L.ε⁻¹ p) (NearInst.chartY L.ε⁻¹ p) :=
    UnforcedLeray.Cons.C03.Concrete.Params.raw_eq_off_axis (L.params Pl)
      (NearInst.chartTau L.ε⁻¹ p) (NearInst.chartY L.ε⁻¹ p) hY
  rw [hraw]
  unfold UnforcedLeray.Axi.Nv
  rw [ringBridge_chart hR hp, ringBridge_age hR hp, UnforcedLeray.Axi.frameL_apply]
  rw [ringBridge_frame hR hp]

end UnforcedLeray.Short.PartIIIb.Concrete

end
