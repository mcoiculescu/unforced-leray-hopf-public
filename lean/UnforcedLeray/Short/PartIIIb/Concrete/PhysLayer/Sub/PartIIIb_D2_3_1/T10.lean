import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_3_1.T5
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.Defs

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-! Pointwise axisymmetry without swirl (`AxiNoSwirlPt`, invariance under all orthogonal maps fixing
`e₃`, source 121-124) gives the frame form of `AxiNoSwirl` (source 2666-2668).  Rotations about
`e₃` carry the point `y` to its meridional point, and the reflection `y₁ ↦ -y₁` fixes that point,
so the `e_y` component of the trace vanishes; `bx_frame_vec` then gives the frame lift. -/

theorem axiNoSwirl_of_pt (U : ℝ → SpatialField) (h : ∀ τ, AxiNoSwirlPt (U τ)) : AxiNoSwirl U := by
  intro τ y _ hy
  have hp0 : 0 < meridPt y 0 := ϱ_pos hy
  have hp1 : meridPt y 1 = 0 := rfl
  -- rotation by `arg (y₀ + i y₁)` about `e₃` carries the meridional point to `y`
  have hrot : rotZ (Complex.arg ⟨y 0, y 1⟩) (U τ (meridPt y)) = U τ y := by
    have hm : (rotZ (Complex.arg ⟨y 0, y 1⟩)).symm y = meridPt y := by
      rw [LinearIsometryEquiv.symm_apply_eq]
      exact (bx_meridPt_rot_eq y).symm
    have hh := h τ (rotZ (Complex.arg ⟨y 0, y 1⟩)) (fixesAxis_rotZ _) y
    rwa [hm] at hh
  -- the reflection `y₁ ↦ -y₁` fixes the meridional point, so the `e_y` component vanishes
  have hU1 : U τ (meridPt y) 1 = 0 := by
    have hfix : reflY.symm (meridPt y) = meridPt y := by
      rw [LinearIsometryEquiv.symm_apply_eq]
      ext i
      fin_cases i <;> simp [reflY_apply, reflFun, meridPt]
    have hh := h τ reflY fixesAxis_reflY (meridPt y)
    rw [hfix] at hh
    have h1 := congrArg (fun v : Space => v 1) hh
    simp [reflY_apply, reflFun] at h1
    linarith
  rw [← hrot, rotZ_apply,
    bx_frame_vec (U τ (meridPt y)) (Complex.arg ⟨y 0, y 1⟩) (meridPt y) hp1 hp0 hU1,
    bx_meridPt_rot_eq y]

end UnforcedLeray.Short.PartIIIb.Concrete
