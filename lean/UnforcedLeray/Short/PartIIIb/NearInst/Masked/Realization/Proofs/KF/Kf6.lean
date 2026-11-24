import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.Sub1

/-!
# `KF6`: phase bookkeeping for the periodic cell representative (source 3618-3619)

For `s : ℝ/Pℤ` and `t : ℝ`, the cell representatives `b = (toCell P (0, s - t)).2` and
`a = (toCell P (0, s)).2` both lie in `(0, P]` and represent the same class: `b ≡ a - t` in
`ℝ/Pℤ`. So `b = a - t + nP` for some `n : ℤ`, and `P`-periodicity of `T` in `τ` gives
`T b = T (a - t)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization

/-- The cell representative reduces back to the phase in `ℝ/Pℤ`. -/
theorem kf6_coe_toCell (P : ℝ) [Fact (0 < P)] (u : AddCircle P) :
    (((UnforcedLeray.B0223.toCell P (0, u)).2 : ℝ) : AddCircle P) = u :=
  AddCircle.coe_equivIoc

/-- **KF6** (phase bookkeeping). -/
theorem kf6 : KF6 := by
  unfold KF6
  intro P _ T hT s t
  have hdiff : (((UnforcedLeray.B0223.toCell P (0, s - (t : AddCircle P))).2 -
      ((UnforcedLeray.B0223.toCell P (0, s)).2 - t) : ℝ) : AddCircle P) = 0 := by
    rw [AddCircle.coe_sub, AddCircle.coe_sub, kf6_coe_toCell, kf6_coe_toCell]
    exact sub_self _
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff P).mp hdiff
  rw [zsmul_eq_mul] at hn
  have hb : (UnforcedLeray.B0223.toCell P (0, s - (t : AddCircle P))).2 =
      (UnforcedLeray.B0223.toCell P (0, s)).2 - t + (n : ℝ) * P := by
    linarith
  have hper : Function.Periodic T P := fun τ => funext fun z => hT τ z
  have hk := hper.int_mul n ((UnforcedLeray.B0223.toCell P (0, s)).2 - t)
  rw [hb]
  exact hk

end UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization
