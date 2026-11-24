import UnforcedLeray.Short.Spine.Sub.SP_CAN4_1

/-!
# Spine: `MildContinuous` (leaf 4 of task `Spine:SP-CAN/4/1`)

Target: `UnforcedLeray.Short.Spine.MildContinuous` (`Short/Spine/Sub/SP_CAN4_1.lean`): a mild
solution `V` (`V θ = S θ θ' (V θ')` for `0 < θ ≤ θ'`) is continuous into `X_G` on `(0, ∞)`.

Source of record: `the November 2 reference manuscript`, line 1086 ("smooth for
positive `θ`").

Proof. Fix `θ₀ > 0`, put `ε = θ₀/2` and `θ₁ = θ₀ + 1`. On `Icc ε θ₁` the curve `V` agrees with
`θ ↦ S θ θ₁ (V θ₁)`, which is continuous there by `Cons.G3b.continuousOn_S_left`. Hence `V` is
continuous on `Icc ε θ₁`, a neighbourhood of `θ₀`, so `V` is continuous at `θ₀`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ContDiff Topology

namespace UnforcedLeray.Short.Spine

open UnforcedLeray.B0010 Blueprint.Planar ComplexODEC UnforcedLeray.Cons.C01
open UnforcedLeray.Cons.G3b

/-- **Leaf 4, strong continuity in `X_G`**: a mild solution is continuous into `X_G` on `(0, ∞)`. -/
theorem mildContinuous_proof : UnforcedLeray.Short.Spine.MildContinuous := by
  intro V hV θ₀ hθ₀
  have hθ₀' : (0 : ℝ) < θ₀ := hθ₀
  have hc := continuousOn_S_left (θ₁ := θ₀ + 1) (half_pos hθ₀') (V (θ₀ + 1))
  have heq : EqOn V (fun θ => S θ (θ₀ + 1) (V (θ₀ + 1))) (Icc (θ₀ / 2) (θ₀ + 1)) := by
    intro θ hθ
    exact hV θ (θ₀ + 1) ((half_pos hθ₀').trans_le hθ.1) hθ.2
  have hmem : Icc (θ₀ / 2) (θ₀ + 1) ∈ 𝓝 θ₀ := Icc_mem_nhds (by linarith) (by linarith)
  exact ((hc.congr heq).continuousAt hmem).continuousWithinAt

end UnforcedLeray.Short.Spine

end
