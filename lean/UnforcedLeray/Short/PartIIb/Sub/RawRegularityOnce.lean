import UnforcedLeray.Short.PartIIb.Sub.G1
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_4_1_Fields
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GELinSub.rawSmoothBdd_Sub.Lemmas

/-!
# Smoothness of the raw field, proved once (organizer `ORG:ward/raw-regularity-once`)

Source `the November 2 reference manuscript`
lines 1214, 1305-1325 (the similarity lift `U_R` of the train is smooth through the axis, with
bounded derivatives) and 2042-2046 (`V_0 = U_raw` is that lift).

The joint smoothness of `(τ, y) ↦ U_raw(τ, y)` has one proof: `PartIIIb.Concrete.RawJointSmooth`
(task `PartIII-b:C/ward/12/3/1/2/6/1/1`, from `RingLiftSmoothReal`, from `IIb.RingLiftSmoothExt`
of task `PartII-b:R1/6`, from `PartII-a:R06`). The two Part II-b forms are consequences:

* `IIb.RawContDiff` (`Sub/G1.lean`): each phase slice `p.raw τ` is `C^∞`, a slice of a jointly
  smooth map;
* `IIb.RawJointSmooth` (`Sub/PartII-b_G4_4_1_Fields.lean`): the same joint smoothness over the
  inlet template `InletPiece`, whose data `Sig, lam, q, i` it does not use.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

open scoped ContDiff
open UnforcedLeray.Cons.C03.Concrete

/-- `PartIIIb.Concrete.RawJointSmooth → RawContDiff`: slices of the jointly smooth raw field.
Composed with `PartIIIb.Concrete.rawJointSmooth` by task `PartII-b:G1/4`. -/
theorem rawContDiff_of_concreteJoint
    (h : UnforcedLeray.Short.PartIIIb.Concrete.RawJointSmooth) : RawContDiff := by
  intro dm dp hdm
  obtain ⟨ν₀, hν₀, H⟩ := h dm dp hdm
  refine ⟨ν₀, hν₀, fun p d hreg hν τ => ?_⟩
  have hc : ContDiff ℝ ∞
      ((fun x : ℝ × UnforcedLeray.Space => p.raw x.1 x.2) ∘ fun y : UnforcedLeray.Space => (τ, y)) :=
    (H p d hreg hν).comp (contDiff_prodMk_right τ)
  have heq : ((fun x : ℝ × UnforcedLeray.Space => p.raw x.1 x.2) ∘
      fun y : UnforcedLeray.Space => (τ, y)) = p.raw τ := by
    funext y
    simp only [Function.comp_apply]
  rw [heq] at hc
  exact hc

/-- `PartIIIb.Concrete.RawJointSmooth → RawJointSmooth` (the inlet data are not used).
Composed with `PartIIIb.Concrete.rawJointSmooth` by task `PartII-b:G4/4/1/1/2`. -/
theorem rawJointSmooth_of_concreteJoint
    (h : UnforcedLeray.Short.PartIIIb.Concrete.RawJointSmooth) : RawJointSmooth := by
  intro _ _ _ _ _ dm dp hdm
  obtain ⟨ν₀, hν₀, H⟩ := h dm dp hdm
  exact ⟨ν₀, hν₀, fun p d hreg hν _ _ _ => H p d hreg hν⟩

end UnforcedLeray.Short.IIb
