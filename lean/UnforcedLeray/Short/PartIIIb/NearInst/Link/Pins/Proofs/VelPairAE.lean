import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_pins_4
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.StressPairAE

/-!
# `VelPairAE` (source 1640-1641, 2666-2668, 2683)

The velocity pairing `Φ ↦ ⟨Φ, 𝒩_v G⟩` sees only the a.e. class of the chart field `G` for the
weight `ageμ c (-3/2)`.  The argument is that of `StressPairAE`: a null set of `ageμ c (-3/2)` is a
null set of `ageμ c (-5/2)` (absolute continuity of the age measures), its preimage under the ring
chart is null for `dτ dy` on `(0, P] × ℝ³` (`stressPairAE_null`), and `𝒩_v G` at `(τ, y)` only
reads `G` at `chartOf R c y τ` (the cell representative enters through `perExt`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.NearInst

open MeasureTheory UnforcedLeray.Axi UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.B0220 (HSpace measureH Profile)
open UnforcedLeray.B0223 (MeridC)
open Set
open scoped ENNReal

/-- The chart `perExt` agreement: `𝒩_v` reads the chart field at `chartOf R c y τ`. -/
theorem perExt_chart_congr {R c : ℝ} (hR : 0 < R) (hc : 0 < c) (G G' : Chart → Merid)
    (τ : ℝ) (y : Space) (h : G (chartOf R c y τ) = G' (chartOf R c y τ)) :
    perExt c G (UnforcedLeray.Axi.chart R τ y) = perExt c G' (UnforcedLeray.Axi.chart R τ y) := by
  rw [chartOf_eq_ring R c hR hc y τ] at h
  exact h

/-- Pointwise: equal chart values at the ring chart point give equal physical velocities. -/
theorem velPhys_congr_chart {R c : ℝ} (hR : 0 < R) (hc : 0 < c) (G G' : Chart → Merid)
    (x : ℝ × Space) (h : G (chartOf R c x.2 x.1) = G' (chartOf R c x.2 x.1)) :
    velPhys R c G x = velPhys R c G' x := by
  simp only [velPhys, UnforcedLeray.Axi.Nv]
  rw [perExt_chart_congr hR hc G G' x.1 x.2 h]

/-- **The velocity pairing sees only the a.e. class of the chart field** (source 1640-1641,
2666-2668, 2683; same argument as `StressPairAE`, weight `ageμ c (-3/2)`). -/
theorem velPairAE : VelPairAE := by
  intro c ε hc hε G G' hG Φ
  have hR : 0 < ε⁻¹ := inv_pos.2 hε
  have hP : 2 * ε * c = 2 * c / ε⁻¹ := by field_simp
  obtain ⟨N, hsub, hNm, hN0⟩ := exists_measurable_superset_of_null
    (s := {p | G p ≠ G' p}) (μ := ageμ c (-3 / 2)) (ae_iff.1 hG)
  have hN5 : ageμ c (-5 / 2) N = 0 := ageμ_absCont c (-5 / 2) (-3 / 2) hN0
  have hnull := stressPairAE_null ε⁻¹ c (2 * ε * c) hR hc hP N hNm hN5
  have hae := Measure.ae_ae_of_ae_prod hnull
  unfold pairF phaseInt
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [hae] with t ht
  refine integral_congr_ae ?_
  filter_upwards [ht] with y hy
  have hGG : G (chartOf ε⁻¹ c y t) = G' (chartOf ε⁻¹ c y t) := by
    by_contra h
    exact hy (hsub h)
  have hv : velPhys ε⁻¹ c G (t, y) = velPhys ε⁻¹ c G' (t, y) :=
    velPhys_congr_chart hR hc G G' (t, y) hGG
  simp only [hv]

end UnforcedLeray.Short.PartIIIb.NearInst
