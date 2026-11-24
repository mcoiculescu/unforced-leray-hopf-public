import UnforcedLeray.Short.PartI.Sub.PartI_C08_1

/-!
# `PartI:C08/1/1`: proof of `MildOnPosContinuous`

Source `the November 2 reference manuscript`,
lines 1094-1125.  A mild curve `V'` on `(0, ∞)` satisfies `V' θ = S θ x' (V' x')` for every
`x' ≥ θ`; continuity on `[b, ∞)` follows from strong continuity of `θ ↦ S θ x' y` on `[b, x']`
(`Cons.G3b.continuousOn_S_left`), localized at each point.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartI

open UnforcedLeray Set

theorem mildOnPosContinuous_proof : UnforcedLeray.Short.PartI.MildOnPosContinuous := by
  intro b V' hb hV
  refine continuousOn_of_locally_continuousOn fun x hx => ?_
  have hbx : b ≤ x := hx
  refine ⟨Ioo (b / 2) (x + 1), isOpen_Ioo, ⟨by linarith, by linarith⟩, ?_⟩
  have hg : ContinuousOn (fun θ => Cons.G3b.S θ (x + 1) (V' (x + 1))) (Icc b (x + 1)) :=
    Cons.G3b.continuousOn_S_left hb _
  have hsub : Ici b ∩ Ioo (b / 2) (x + 1) ⊆ Icc b (x + 1) := fun θ hθ =>
    ⟨hθ.1, (hθ.2).2.le⟩
  refine (hg.mono hsub).congr fun θ hθ => ?_
  have hθb : b ≤ θ := hθ.1
  have hθx : θ ≤ x + 1 := (hθ.2).2.le
  exact hV θ (x + 1) (by linarith) hθx

end UnforcedLeray.Short.PartI
