import UnforcedLeray.Short.PartIIb.Tasks.FlatUnique.HeatStream.HeatEq.RhsCpd
import UnforcedLeray.Short.PartIIb.Tasks.FlatUnique.HeatStream.HeatEq.TauDeriv
import UnforcedLeray.Short.PartIIb.Tasks.FlatUnique.HeatStream.HeatEq.AgeIntegral

/-!
# Part II-b, leaf `PartII-b:T11/3/4` (`HeatConvEq`): the heat equation for a nice stream

Source of record: `the November 2 reference manuscript`, lines 1923-1927 (the heat
semigroup `e^{ν τ Δ}` commutes with the spatial derivatives and solves `∂_τ = ν Δ`).

For `τ = x.1 > 0`, `cpd 0 H = ν ∫ (∂_θG)_{ντ} ζ(· - w)` (`hce_cpd0`), the age derivative splits into
the two second spatial derivatives of `G` (`hce_age_integral`, two Gaussian integrations by parts per
coordinate), and the spatial side `ν (cpd 1² + cpd 2²) H = ν (H_{∂_q²ζ} + H_{∂_η²ζ})`
(`hce_spatial_side`) is the same pair of heat flows.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.IIb

/-- **Leaf `PartII-b:T11/3/4`** (the heat equation `∂_τ H = ν (∂_q² + ∂_η²) H` for a nice stream
and `τ > 0`). -/
theorem heatConvEq : UnforcedLeray.Short.IIb.HeatConvEq := by
  intro c ν ζ hc hν hζ x hx
  rw [hce_cpd0 hc hν hζ hx, hce_spatial_side hc hν hζ hx,
    hce_age_integral (mul_pos hν hx) hc hζ x.2]
  have h1 : heatStreamH ν (qDer (qDer ζ)) x =
      ∫ w : ℝ × ℝ, UnforcedLeray.B0284.heatKernel2 (ν * x.1) w * qDer (qDer ζ) (x.2 - w) := by
    unfold heatStreamH
    rw [if_pos hx]
  have h2 : heatStreamH ν (etaDer (etaDer ζ)) x =
      ∫ w : ℝ × ℝ, UnforcedLeray.B0284.heatKernel2 (ν * x.1) w * etaDer (etaDer ζ) (x.2 - w) := by
    unfold heatStreamH
    rw [if_pos hx]
  rw [h1, h2]

end UnforcedLeray.Short.IIb
