import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.TransTable.ThinChart.Core2
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_1.ChartPhysL2
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.Org.YThinTrans

/-!
# `RepChart/Chart`: chart-to-physical for the repair multiplication (source 2683-2689, 2698-2713)

`multMaj R V f p = s⁻¹ · G(τ(p), y(p))` with `G(τ,y) = |V_mer(τ, (ϱ y, 0, y₃))| f(τ,y)`, so
`ρ_b^{-1/2}‖multMaj‖_{H_T}` is bounded by `ρ_b^{-1/2}π^{-1/2}R⁻¹‖G‖_{L²_τL²}` (`chartPhysL2`).
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

namespace RC

/-- The meridional norm of `V(τ, ·)` at the half-plane point `(ϱ y, 0, y₃)`: an axisymmetric
function of `y`. -/
def merTr (V : ℝ → Space → Space) (τ : ℝ) (y : Space) : ℝ :=
  ‖(WithLp.toLp 2 ![V τ (!₂[ϱ y, 0, y 2]) 0, V τ (!₂[ϱ y, 0, y 2]) 2] :
    EuclideanSpace ℝ (Fin 2))‖

theorem norm_chartCoeff {R : ℝ} (hR : 0 < R) (V : ℝ → Space → Space) {p : Chart} (hs : 0 < p.1) :
    ‖IIIa.chartCoeff R V p‖ = (Real.sqrt p.1)⁻¹ *
      merTr V (NearInst.chartTau R p) (NearInst.chartY R p) := by
  have hsq : 0 < Real.sqrt p.1 := Real.sqrt_pos.2 hs
  unfold IIIa.chartCoeff merTr
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hsq.le)]
  congr 2
  have h2 : (NearInst.chartY R p) 2 = p.2.2 / Real.sqrt p.1 := by
    simp [NearInst.chartY]
  have h1 : (!₂[ϱ (NearInst.chartY R p), 0, (NearInst.chartY R p) 2] : Space) =
      !₂[R / Real.sqrt p.1, 0, p.2.2 / Real.sqrt p.1] := by
    rw [ϱ_chartY hR hs, h2]
  rw [h1]
  rfl

theorem multMaj_eq {R : ℝ} (hR : 0 < R) (V : ℝ → Space → Space) (f : ℝ → Space → ℝ≥0∞)
    {p : Chart} (hs : 0 < p.1) :
    multMaj R V f p = ENNReal.ofReal p.1⁻¹ *
      (ENNReal.ofReal (merTr V (NearInst.chartTau R p) (NearInst.chartY R p)) *
        f (NearInst.chartTau R p) (NearInst.chartY R p)) := by
  have hsq : 0 < Real.sqrt p.1 := Real.sqrt_pos.2 hs
  unfold multMaj
  rw [norm_chartCoeff hR V hs, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
  congr 2
  have h : (Real.sqrt p.1)⁻¹ * (Real.sqrt p.1)⁻¹ = p.1⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt hs.le]
  calc (Real.sqrt p.1)⁻¹ * merTr V (NearInst.chartTau R p) (NearInst.chartY R p) *
        (Real.sqrt p.1)⁻¹
      = (Real.sqrt p.1)⁻¹ * (Real.sqrt p.1)⁻¹ *
        merTr V (NearInst.chartTau R p) (NearInst.chartY R p) := by ring
    _ = _ := by rw [h]

end RC

end UnforcedLeray.Short.PartIIIb.Concrete

end
