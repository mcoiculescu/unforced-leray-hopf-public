import UnforcedLeray.Short.Spine.Sub.SP_CAN4_5

/-!
# Spine leaf 4: a.e. equality of continuous functions is equality on `(0, ∞)`

Proves the Prop `UnforcedLeray.Short.Spine.AeEqOfContinuousOn` of `Sub/SP_CAN4_5.lean` exactly as
stated. Source: `the November 2 reference manuscript` line 1086 (`SmoothRepresentativeEquation`
cut into its leaves; this leaf is the last one used in the assembly).

Proof. `xGMeasure` is `volume.restrict (Ioi 0)` with a positive density, so the Lebesgue restriction
`volume.restrict (Ioi 0)` is absolutely continuous with respect to `xGMeasure` (`B0012.restrict_ac`).
Hence `f =ᵐ[xGMeasure] g` gives `f =ᵐ[volume.restrict (Ioi 0)] g`. Since `Ioi 0` is open and `f`, `g`
are continuous on it, `MeasureTheory.Measure.eqOn_open_of_ae_eq` gives `EqOn f g (Ioi 0)`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ContDiff Topology

namespace UnforcedLeray.Short.Spine

open UnforcedLeray.B0010 Blueprint.Planar ComplexODEC UnforcedLeray.Cons.C01
open UnforcedLeray.Cons.G3b

/-- **Leaf 4, a.e. equality of continuous functions is equality on `(0, ∞)`.** -/
theorem aeEqOfContinuousOn_proof : UnforcedLeray.Short.Spine.AeEqOfContinuousOn := by
  intro f g hf hg hfg r hr
  -- `volume.restrict (Ioi 0) ≪ xGMeasure`, so the a.e. equality transfers to the Lebesgue restriction
  have hae : f =ᵐ[volume.restrict (Ioi (0 : ℝ))] g :=
    UnforcedLeray.B0012.restrict_ac.ae_le hfg
  exact MeasureTheory.Measure.eqOn_open_of_ae_eq hae isOpen_Ioi hf hg (Set.mem_Ioi.2 hr)

end UnforcedLeray.Short.Spine

end
