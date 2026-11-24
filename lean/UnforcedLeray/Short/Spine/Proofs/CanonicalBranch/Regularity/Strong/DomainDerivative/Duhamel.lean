import UnforcedLeray.Short.Spine.Sub.SP_CAN4_2_1
import UnforcedLeray.Short.Spine.Proofs.CanonicalBranch.Regularity.Smoothing.Step.Helpers

/-!
# Spine: Duhamel identity for a mild `V` on the negative side (task `Spine:SP-CAN/4/2/1/1`)

Source: `the November 2 reference manuscript` line 1086 and lines 1134-1145.

For `0 < θ ≤ θ''`, the forward Duhamel identity `MildLevelStepHelp.mild_decomp`
(`V θ = e^{(log θ'' - log θ) D} V θ'' + ∫_θ^{θ''} e^{(log v - log θ) D} L₀ V(v) dv`) is
rewritten with the substitution `u = -v` (`intervalIntegral.integral_comp_neg`), which turns the
integral over `[θ, θ'']` into the integral over `[-θ'', -θ]` of the integrand at `-u`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology

namespace UnforcedLeray.Short.Spine

open UnforcedLeray.B0010 Blueprint.Planar ComplexODEC UnforcedLeray.Cons.C01
open UnforcedLeray.Cons.G3b

/-- **Duhamel identity for a mild `V`** (shorter proof lines 1134-1145): `V θ` is the Duhamel
expression over `[-θ'', -θ]`. -/
theorem mdDuhamel : MDDuhamel := by
  intro V hV θ θ'' hθ hθθ''
  have key := MildLevelStepHelp.mild_decomp hV hθ hθθ''
  have h2 : (∫ u in (-θ'')..(-θ),
      B0123.expD (Real.log (-u) - Real.log θ) (B0012.L0 (V (-u))))
      = ∫ v in θ..θ'', B0123.expD (Real.log v - Real.log θ) (B0012.L0 (V v)) := by
    have := intervalIntegral.integral_comp_neg (a := -θ'') (b := -θ)
      (f := fun v : ℝ => B0123.expD (Real.log v - Real.log θ) (B0012.L0 (V v)))
    simpa only [neg_neg] using this
  rw [key, h2]

end UnforcedLeray.Short.Spine
