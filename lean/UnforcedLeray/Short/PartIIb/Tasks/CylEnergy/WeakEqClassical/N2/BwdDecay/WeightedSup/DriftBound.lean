import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T22_2_3_2_1
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.WeakEqClassical.N2.BwdDecay.WeightedSup.DriftBound.VcSup

/-!
# `BwdDriftBound` (SP 2085-2093): the train drift is bounded on `[0, Σ/ν] × ℝ²`.

`|v - V_c| ≤ δ` (`TrainClose.abs_sub_le`) and `|V_c| ≤ M` (`Vc_sup_all_c`).
-/

set_option autoImplicit false

noncomputable section

open Set

namespace UnforcedLeray.Short.IIb

theorem bwdDriftBound : UnforcedLeray.Short.IIb.BwdDriftBound := by
  intro Sg ν c δ hSg hν hc hδ tr htr
  obtain ⟨M, hM⟩ := Vc_sup_all_c Sg ν c hSg hν hc
  have hM0 : 0 ≤ M :=
    le_trans (abs_nonneg _) (hM 0 le_rfl (by positivity) (0, 0) 0)
  refine ⟨M + δ, by linarith, fun r hr x => ?_⟩
  have key : ∀ k : Fin 2, |tr.v r x k| ≤ M + δ := fun k => by
    have h1 := htr.abs_sub_le hc hr.1 hr.2 x k
    have h2 := hM r hr.1 hr.2 x k
    have h3 := abs_sub_abs_le_abs_sub (tr.v r x k) (Train.Vc ν c r x k)
    linarith
  exact ⟨key 0, key 1⟩

end UnforcedLeray.Short.IIb
