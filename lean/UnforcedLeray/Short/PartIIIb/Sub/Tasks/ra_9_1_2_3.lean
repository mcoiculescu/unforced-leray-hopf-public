import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.Sub.GeoDTasks
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.RAGeoFE
import UnforcedLeray.Short.PartIIIb.Sub.Tasks.ra_9_1_2_1
import UnforcedLeray.Short.PartIIIb.Sub.Tasks.ra_9_1_2_2

/-!
# `PartIII-b:C/asrc/ra/9/1/2/3` : `RingDmuRule` from the ring-chart rules

Source: `the November 2 reference manuscript` lines 5034-5039, 4979-4980.

Proof outline. For `q.1 > 0` put `τ = chartTau R q`, `y = chartY R q` (so `chart R τ y = q`,
`y ∉ axis`). Then `physDmu ν μ (Nv R b) τ y` equals `Nv R G τ y` for the explicit profile
`G = s∂_s b + μ b - ν s·Lp b`, by `ringT0Rule` and `ringLapRule`; `coefOf` inverts the lift
(`fe_coefOf_Nv`), and the remaining identity is algebra.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest Params)

/-- The profile `G` with `Nv R G τ y = physDmu ν μ (Nv R b) τ y` off the axis
(`s∂_s b + μ b - ν s·(Δ_{q,η} b - 2ε K1(∂_q b) + ε² K1(K1 b) - ε² b_r e_r)`, `ε = R⁻¹`). -/
def ringDmuG (R ν μ : ℝ) (b : Chart → Merid) : Chart → Merid :=
  fun p => p.1 • UnforcedLeray.Axi.dS b p + μ • b p - ν • (p.1 • (lapQE b p
    - (2 * R⁻¹) • K1 (UnforcedLeray.Axi.dQ b) p + (R⁻¹) ^ 2 • K1 (K1 b) p
    - (R⁻¹) ^ 2 • erProj (b p)))

/-- Pointwise identity at the chart point of `q` (with `q.1 > 0`). -/
theorem ringDmu_pt {R : ℝ} (hR : 0 < R) (ν μ : ℝ) (b : Chart → Merid)
    (hb : ContDiffOn ℝ 2 b (Ioi 0 ×ˢ univ)) (q : Chart) (hq : 0 < q.1) :
    physDmu ν μ (Nv R b) (NearInst.chartTau R q) (NearInst.chartY R q) =
      Nv R (ringDmuG R ν μ b) (NearInst.chartTau R q) (NearInst.chartY R q) := by
  have hrt := fe_chart_roundtrip hR q hq
  obtain ⟨hy0, hy1, hϱ, hage⟩ := fe_chartY_facts hR q hq
  have hϱne : ϱ (NearInst.chartY R q) ≠ 0 := by
    rw [hϱ]
    exact div_ne_zero hR.ne' (Real.sqrt_pos.2 hq).ne'
  have hyax : NearInst.chartY R q ∉ axis := fun h => hϱne ((mem_axis_iff _).1 h)
  have hdiff : DifferentiableAt ℝ b (Axi.chart R (NearInst.chartTau R q) (NearInst.chartY R q)) := by
    rw [hrt]
    have hopen : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) :=
      isOpen_Ioi.prod isOpen_univ
    exact (hb.differentiableOn (by norm_num)).differentiableAt
      (hopen.mem_nhds ⟨hq, mem_univ _⟩)
  have h0 := ringT0Rule R hR b (NearInst.chartTau R q) (NearInst.chartY R q) hyax hdiff
  have h1 := ringLapRule R hR b hb (NearInst.chartTau R q) (NearInst.chartY R q) hyax
  have hA : physDmu ν μ (Nv R b) (NearInst.chartTau R q) (NearInst.chartY R q)
      = Nv R (fun p => p.1 • UnforcedLeray.Axi.dS b p) (NearInst.chartTau R q) (NearInst.chartY R q)
        + μ • Nv R b (NearInst.chartTau R q) (NearInst.chartY R q)
        - ν • Nv R (fun p => p.1 • (lapQE b p - (2 * R⁻¹) • K1 (UnforcedLeray.Axi.dQ b) p
            + (R⁻¹) ^ 2 • K1 (K1 b) p - (R⁻¹) ^ 2 • erProj (b p)))
          (NearInst.chartTau R q) (NearInst.chartY R q) := by
    unfold physDmu
    linear_combination (norm := module) h0 - ν • h1
  rw [hA]
  simp only [Nv, ringDmuG, map_add, map_sub, map_smul]
  module

theorem ringDmuRule : RingDmuRule := by
  intro R ν μ hR b hb q hq
  have hc := ringDmu_pt hR ν μ b hb q hq
  have hcoef : coefOf R (physDmu ν μ (Nv R b)) q
      = coefOf R (fun τ y => Nv R (ringDmuG R ν μ b) τ y) q := by
    unfold coefOf
    rw [hc]
  have hq0 : q.1 ≠ 0 := hq.ne'
  have hμ : q.1 • ((μ / q.1) • b q) = μ • b q := by
    rw [smul_smul, show q.1 * (μ / q.1) = μ from by field_simp]
  rw [hcoef, fe_coefOf_Nv hR _ q hq]
  simp only [ringDmuG, Dc, ringRem, smul_add, smul_sub, hμ]
  module
