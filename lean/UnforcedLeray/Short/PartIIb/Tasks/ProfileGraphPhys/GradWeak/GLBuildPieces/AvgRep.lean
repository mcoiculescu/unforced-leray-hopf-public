import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T10_7_1_1_3

/-!
# `PartII-b:T10/7/1/1/3` piece: `gl_avgRep` (profile representation of a measurable equivariant field)

Source of record: `the November 2 reference manuscript` 112-116, 1912-1921.

Route: take a measurable representative `W' = hW.mk W` (`W =ᵐ W'`). The group actions
`x ↦ (x.1, g x.2)` for `g = rotZ θ` and `g = reflY` preserve volume, so the a.e. equivariance of
`W` transfers to `W'`. Then `glAvgLift` applied to `W'` gives the representation with the measurable
angular averages `A = avgR W'`, `B = avgZ W'`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology

theorem gl_avgRep : UnforcedLeray.Short.IIb.GLAvgRep := by
  intro W hW hE
  -- a volume-preserving action of the form `x ↦ (x.1, g x.2)` for a linear isometry `g`
  have hT : ∀ g : UnforcedLeray.Space ≃ₗᵢ[ℝ] UnforcedLeray.Space,
      MeasurePreserving (fun x : ℝ × UnforcedLeray.Space => (x.1, g x.2)) volume volume := by
    intro g
    rw [Measure.volume_eq_prod]
    exact (MeasurePreserving.id volume).prod g.measurePreserving
  have hEq : W =ᵐ[volume] hW.mk W := hW.ae_eq_mk
  have hWm : Measurable (hW.mk W) := hW.stronglyMeasurable_mk.measurable
  have hE' : UnforcedLeray.Short.IIb.GLEquivar (hW.mk W) := by
    obtain ⟨hrot, hrefl⟩ := hE
    refine ⟨fun θ => ?_, ?_⟩
    · have h1 : ∀ᵐ x : ℝ × UnforcedLeray.Space ∂volume,
          W (x.1, UnforcedLeray.Axi.rotZ θ x.2) = hW.mk W (x.1, UnforcedLeray.Axi.rotZ θ x.2) :=
        (hT (UnforcedLeray.Axi.rotZ θ)).quasiMeasurePreserving.ae hEq
      filter_upwards [h1, hrot θ, hEq] with x h1x h2x h3x
      rw [← h1x, h2x, h3x]
    · have h1 : ∀ᵐ x : ℝ × UnforcedLeray.Space ∂volume,
          W (x.1, UnforcedLeray.Axi.reflY x.2) = hW.mk W (x.1, UnforcedLeray.Axi.reflY x.2) :=
        (hT UnforcedLeray.Axi.reflY).quasiMeasurePreserving.ae hEq
      filter_upwards [h1, hrefl, hEq] with x h1x h2x h3x
      rw [← h1x, h2x, h3x]
  have hlift := UnforcedLeray.Short.IIb.glAvgLift hWm hE'
  refine ⟨UnforcedLeray.Axi.avgR (hW.mk W), UnforcedLeray.Axi.avgZ (hW.mk W),
    UnforcedLeray.Axi.measurable_avgR hWm, UnforcedLeray.Axi.measurable_avgZ hWm, ?_⟩
  filter_upwards [hEq, hlift] with x h1 h2
  rw [h1]
  exact h2

#print axioms gl_avgRep
