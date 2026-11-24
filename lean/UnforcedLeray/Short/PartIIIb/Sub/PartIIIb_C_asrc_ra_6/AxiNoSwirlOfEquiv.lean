import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_6
import UnforcedLeray.Cons.L2.PencilConcrete.Meridional

/-!
# `PartIII-b:C/asrc/ra/6/5` : `AxiNoSwirlOfEquiv`

Source of record: `the November 2 reference manuscript` 121-124 (axisymmetry without
swirl is invariance under the linear isometries fixing `e₃`), 4161.

A field `F` equivariant under every linear isometry fixing `e₃` is axisymmetric without swirl:
for `y` off the axis, the rotation about `e₃` taking `meridPt y` to `y` transports `F τ (meridPt y)`
to `F τ y`, and the reflection `y₁ ↦ -y₁` fixes `meridPt y`, forcing the azimuthal component
of `F τ (meridPt y)` to vanish.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem axiNoSwirlOfEquiv : AxiNoSwirlOfEquiv := by
  intro F hF τ y _ hy
  have hcs : (y 0 / ϱ y) ^ 2 + (y 1 / ϱ y) ^ 2 = 1 := eR_sq_sum hy
  have hrot : UnforcedLeray.FixesAxis
      (UnforcedLeray.Blueprint.C07.PencilConcrete.rotation (y 0 / ϱ y) (y 1 / ϱ y) hcs) :=
    (UnforcedLeray.Blueprint.C07.PencilConcrete.rotation_fixesAxis _ _ hcs).axis
  have hrefl : UnforcedLeray.FixesAxis UnforcedLeray.Blueprint.C07.PencilConcrete.reflection :=
    UnforcedLeray.Blueprint.C07.PencilConcrete.reflection_fixesAxis.axis
  have hgp : UnforcedLeray.Blueprint.C07.PencilConcrete.rotation (y 0 / ϱ y) (y 1 / ϱ y) hcs
      (meridPt y) = y := by
    have hϱ : ϱ y ≠ 0 := ϱ_ne_zero hy
    ext i
    fin_cases i
    · simp [UnforcedLeray.Blueprint.C07.PencilConcrete.rotation_apply, meridPt]
      field_simp
    · simp [UnforcedLeray.Blueprint.C07.PencilConcrete.rotation_apply, meridPt]
      field_simp
    · simp [UnforcedLeray.Blueprint.C07.PencilConcrete.rotation_apply, meridPt]
  have hfix : UnforcedLeray.Blueprint.C07.PencilConcrete.reflection (meridPt y) = meridPt y := by
    ext i
    fin_cases i <;> simp [UnforcedLeray.Blueprint.C07.PencilConcrete.reflection_apply, meridPt]
  have h1 := hF _ hrefl τ (meridPt y)
  rw [hfix] at h1
  have hF1 : F τ (meridPt y) 1 = 0 := by
    have := congrArg (fun v => v 1) h1
    simp [UnforcedLeray.Blueprint.C07.PencilConcrete.reflection_apply] at this
    linarith
  have hFy : F τ y = UnforcedLeray.Blueprint.C07.PencilConcrete.rotation (y 0 / ϱ y) (y 1 / ϱ y) hcs
      (F τ (meridPt y)) := by
    have h2 := hF _ hrot τ (meridPt y)
    rw [hgp] at h2
    exact h2
  rw [hFy]
  ext i
  fin_cases i
  · simp [UnforcedLeray.Blueprint.C07.PencilConcrete.rotation_apply, frameL_apply, eR, hor, hF1]
    ring
  · simp [UnforcedLeray.Blueprint.C07.PencilConcrete.rotation_apply, frameL_apply, eR, hor, hF1]
    ring
  · simp [UnforcedLeray.Blueprint.C07.PencilConcrete.rotation_apply, frameL_apply, e3, coordinateVector]

end UnforcedLeray.Short.PartIIIb.Concrete
