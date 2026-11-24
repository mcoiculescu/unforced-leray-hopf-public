import UnforcedLeray.Short.PartI.Sub.PartI_C07_1_1
import UnforcedLeray.Short.PartI.Tasks.FullMildUnique.Gronwall
import UnforcedLeray.Short.PartI.Tasks.FullMildUnique.Key

/-!
# `PartI:C07/1/1/1`: Gronwall uniqueness for the full Duhamel equation

Source `the November 2 reference manuscript` lines 1094-1125 ("uniqueness follows
from the bounded coupling maps and Gronwall"). A continuous solution `V` of `FullMildEq b V` on
`[b, ∞)` equals `S θ θ' (V θ')`: the difference `D θ = ‖V θ - S θ θ' (V θ')‖` satisfies
`D θ ≤ ‖L₀‖ ∫_θ^{θ'} D`, so `D = 0` by `FullMildUniqueHelp.gronwall_le_zero`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartI

open UnforcedLeray MeasureTheory Set

theorem fullMildUnique : UnforcedLeray.Short.PartI.FullMildUnique := by
  intro b V hb hV hE θ θ' hbθ hθθ'
  have hVc : ContinuousOn V (Icc b θ') := hV.mono Icc_subset_Ici_self
  have hSc : ContinuousOn (fun s => Cons.G3b.S s θ' (V θ')) (Icc b θ') :=
    Cons.G3b.continuousOn_S_left hb (V θ')
  have hD : ContinuousOn (fun s => ‖V s - Cons.G3b.S s θ' (V θ')‖) (Icc b θ') :=
    (hVc.sub hSc).norm
  have hle := FullMildUniqueHelp.gronwall_le_zero (D := fun s => ‖V s - Cons.G3b.S s θ' (V θ')‖)
    (a := b) (c := θ') (K := ‖B0012.L0‖) (norm_nonneg _) hD (fun s _ => norm_nonneg _)
    (fun s hs => FullMildUniqueHelp.key_norm_le b hb V hV hE hs.1 hs.2)
  have h0 : ‖V θ - Cons.G3b.S θ θ' (V θ')‖ ≤ 0 := hle θ ⟨hbθ, hθθ'⟩
  have h1 : ‖V θ - Cons.G3b.S θ θ' (V θ')‖ = 0 := le_antisymm h0 (norm_nonneg _)
  exact sub_eq_zero.mp (norm_eq_zero.mp h1)

end UnforcedLeray.Short.PartI
