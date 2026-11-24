import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_4_1
import UnforcedLeray.Short.PartIIb.Sub.YqOfFields_a
import UnforcedLeray.Short.PartIIb.Sub.YqOfFields_b
import UnforcedLeray.Short.PartIIb.Sub.YqOfFields_c

/-!


Source of record: `the November 2 reference manuscript`, lines 1478-1480 and 2370-2383.

Assembled from the three leaves:
* `yqOfFields_slices` (a): a strongly measurable a.e.-equal version `W'` with the same norm and
  a.e. periodicity on slices;
* `yqOfFields_exists` (b): `W'` is represented by some `F : Yq P q0E`;
* `yqOfFields_norm` (c): `‖F‖ = (phaseLpNorm P bgp W').toReal`.

The slices of `W` agree a.e. with those of `W'` (`Measure.ae_ae_of_ae_prod`), so `F` also represents `W`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.Blueprint UnforcedLeray.PhaseSpace
  UnforcedLeray.B0411 UnforcedLeray.B0412

/-- **Packaging leaf** (SP 1478-1480, 2370-2383): a field in `Y_p` has a representative in `Y_{q₀}`
with the same norm. -/
theorem yqOfFields : UnforcedLeray.Short.IIb.YqOfFields := by
  intro P _ W hW
  obtain ⟨W', hsm, hE, hper, hnorm, hfin⟩ := yqOfFields_slices P W hW
  obtain ⟨F, hF⟩ := yqOfFields_exists P W' hsm hper hfin
  have hWslice : ∀ᵐ τ : ℝ, (fun y => W (τ, y)) =ᵐ[volume] (fun y => W' (τ, y)) := by
    have h2 : ∀ᵐ τ : ℝ, ∀ᵐ y : Space, W' (τ, y) = W (τ, y) := by
      refine Measure.ae_ae_of_ae_prod (p := fun z : ℝ × Space => W' z = W z) ?_
      rw [← Measure.volume_eq_prod]
      exact hE
    filter_upwards [h2] with τ hτ
    filter_upwards [hτ] with y hy
    exact hy.symm
  refine ⟨F, ⟨hW.meas, ?_⟩, ?_⟩
  · filter_upwards [hWslice, hF.slice] with τ h1 h2
    exact h1.trans h2
  · rw [yqOfFields_norm P W' F hF, hnorm]

end UnforcedLeray.Short.IIb
