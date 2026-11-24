import UnforcedLeray.Units.B0579

/-!
# Directional derivatives of cylinder tests (helper for `kerVelSmooth`)

For a cylinder test `φ` and a vector `v`, the function `x ↦ fderiv φ x v` is again a cylinder test
(the proof of `B0579.IsCylTest.pd` with the direction `dir j` replaced by `v`). A test vanishes
together with its derivative on the open set `|x.2| > R` where it vanishes for `|x.2| > R`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- The derivative of `φ` in the direction `v`, as a real function. -/
def kvsDirDer (φ : ℝ × ℝ → ℝ) (v : ℝ × ℝ) : ℝ × ℝ → ℝ := fun x => fderiv ℝ φ x v

theorem kvsDirDer_isCylTest {c : ℝ} {φ : ℝ × ℝ → ℝ} (hφ : UnforcedLeray.B0579.IsCylTest c φ)
    (v : ℝ × ℝ) : UnforcedLeray.B0579.IsCylTest c (kvsDirDer φ v) where
  smooth := ((contDiff_infty_iff_fderiv.1 hφ.smooth).2).clm_apply contDiff_const
  periodic x := by
    have hfun : (fun y : ℝ × ℝ => φ (y + ((c, 0) : ℝ × ℝ))) = φ := by
      funext y
      have hy : y + ((c, 0) : ℝ × ℝ) = (y.1 + c, y.2) := by ext <;> simp
      rw [hy]
      exact hφ.periodic y
    have h := fderiv_comp_add_right (𝕜 := ℝ) (f := φ) (x := x) ((c, 0) : ℝ × ℝ)
    rw [hfun] at h
    have hx : x + ((c, 0) : ℝ × ℝ) = (x.1 + c, x.2) := by ext <;> simp
    rw [hx] at h
    simp only [kvsDirDer]
    rw [← h]
  band := by
    obtain ⟨R, hR⟩ := hφ.band
    refine ⟨R, fun x hx => ?_⟩
    have hU : IsOpen {y : ℝ × ℝ | R < |y.2|} := isOpen_lt continuous_const continuous_snd.abs
    have hev : φ =ᶠ[𝓝 x] fun _ => (0 : ℝ) :=
      Filter.eventually_of_mem (hU.mem_nhds hx) fun y hy => hR y hy
    simp only [kvsDirDer]
    rw [hev.fderiv_eq]
    simp

/-- The derivative of a function vanishing on `|x.2| > R` vanishes there. -/
theorem kvsFderiv_eq_zero {φ : ℝ × ℝ → ℝ} {R : ℝ} (hR : ∀ x : ℝ × ℝ, R < |x.2| → φ x = 0)
    {x : ℝ × ℝ} (hx : R < |x.2|) : fderiv ℝ φ x = 0 := by
  have hU : IsOpen {y : ℝ × ℝ | R < |y.2|} := isOpen_lt continuous_const continuous_snd.abs
  have hev : φ =ᶠ[𝓝 x] fun _ => (0 : ℝ) :=
    Filter.eventually_of_mem (hU.mem_nhds hx) fun y hy => hR y hy
  rw [hev.fderiv_eq]
  simp

end UnforcedLeray.Short.IIIa
