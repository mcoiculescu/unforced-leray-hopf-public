import UnforcedLeray.Short.PartIIb.Sub.R1_7

/-!
# Part II-b, task `PartII-b:R1/7`, leaf `TrainPressureSmooth`: the train pressure profile is smooth
at positive age

Proves `UnforcedLeray.Short.IIb.TrainPressureSmooth` (defined in `Sub/R1_7.lean`). Source of record:
`the November 2 reference manuscript`, lines 258-288 (the train is a global smooth
solution, with bounded smooth pressure).

Proof idea. The profile `trainProfile T.p` is `g ∘ A`, where `g (z) = T.p z.1 z.2` is smooth on
`Ici 0 ×ˢ univ` by the field `T.isTrain.smooth_p`, and `A (x) = (x.2.2, (x.1, x.2.1))` is a
polynomial (hence smooth) coordinate change that sends the age domain `{0 < x.2.2}` into
`Ici 0 ×ˢ univ`.

No hypotheses are added to the statement.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.IIb

/-- **`TrainPressureSmooth`.** The pressure profile of a train is `C^∞` on the age domain. -/
theorem trainPressureSmooth : UnforcedLeray.Short.IIb.TrainPressureSmooth := by
  unfold TrainPressureSmooth
  intro nu c T
  -- the field of the train, smooth on `[0, ∞) × ℝ²`
  have hP : ContDiffOn ℝ ∞ (fun z : ℝ × (ℝ × ℝ) => T.p z.1 z.2) (Ici (0 : ℝ) ×ˢ univ) :=
    T.isTrain.smooth_p
  -- the coordinate change `(q, (η, s)) ↦ (s, (q, η))` is smooth
  have hA : ContDiff ℝ ∞ (fun x : UnforcedLeray.B0184.ProfilePoint => (x.2.2, (x.1, x.2.1))) := by
    fun_prop
  -- and it maps the age domain into `[0, ∞) × ℝ²`
  have hmaps : MapsTo (fun x : UnforcedLeray.B0184.ProfilePoint => (x.2.2, (x.1, x.2.1)))
      UnforcedLeray.B0185.ageDomain (Ici (0 : ℝ) ×ˢ univ) := by
    intro x hx
    have hx' : (0 : ℝ) < x.2.2 := hx
    exact ⟨Set.mem_Ici.mpr hx'.le, Set.mem_univ _⟩
  have hcomp := hP.comp hA.contDiffOn hmaps
  exact hcomp

end UnforcedLeray.Short.IIb

end
