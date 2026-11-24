import UnforcedLeray.Short.PartIIIb.Concrete.SourceL
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.XmtReflect

set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open UnforcedLeray.Short.PartIIIb.Concrete.XmtRefl

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- A map commuting with the reflection `reflY` has vanishing `(i,j)` entry of its derivative at a
fixed point of the reflection, when the reflection signs of `i` and `j` differ (source 4797-4800). -/
theorem azimuthal_entry_zero (X : Vec3 → Vec3) (hX : ∀ y, X (reflY y) = reflY (X y))
    (y0 : Vec3) (hy0 : reflY y0 = y0) (i j : Fin 3) (hij : sg i * sg j = -1) :
    fderiv ℝ X y0 (Pi.single j 1) i = 0 := by
  have h1 : fderiv ℝ (⇑reflL ∘ X) y0 = (reflL : Vec3 →L[ℝ] Vec3).comp (fderiv ℝ X y0) :=
    ContinuousLinearEquiv.comp_fderiv reflL
  have h2 : fderiv ℝ (X ∘ ⇑reflL) y0 = (fderiv ℝ X (reflL y0)).comp (reflL : Vec3 →L[ℝ] Vec3) :=
    ContinuousLinearEquiv.comp_right_fderiv reflL
  have h3 : (X ∘ ⇑reflL) = (⇑reflL ∘ X) := funext fun y => by
    simp only [Function.comp_apply, reflL_apply]
    exact hX y
  have h4 : (fderiv ℝ X (reflL y0)).comp (reflL : Vec3 →L[ℝ] Vec3)
      = (reflL : Vec3 →L[ℝ] Vec3).comp (fderiv ℝ X y0) := by
    rw [← h2, h3, h1]
  have h5 := congrArg (fun L : Vec3 →L[ℝ] Vec3 => L (Pi.single j 1)) h4
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, reflL_apply, hy0] at h5
  rw [reflY_single j, map_smul] at h5
  have h6 := congrFun h5 i
  simp only [Pi.smul_apply, smul_eq_mul, reflY_apply_idx] at h6
  have hne : sg j - sg i ≠ 0 := by
    intro h
    have e : sg j = sg i := by linarith
    rw [e] at hij
    linarith [sg_sq i]
  have hm : (sg j - sg i) * fderiv ℝ X y0 (Pi.single j 1) i = 0 := by
    linear_combination h6
  exact (mul_eq_zero.1 hm).resolve_left hne

/-- Source 4797-4799: `𝓛T` has no entry with exactly one azimuthal index, at every `s > 0`. -/
theorem sourceLAzimuthal (c mZ ρb γ ν ε μ : ℝ) (χo χy : ℝ → ℝ) :
    SourceLAzimuthal c mZ ρb γ ν ε μ χo χy := by
  intro _ _ _ T s hs
  have key : ∀ i j, LjFun c mZ ρb γ ν ε μ χo χy T s i j =
      fderiv ℝ (Xmt c ν ε μ χo χy (thinRep T)) ![ε⁻¹ / Real.sqrt s, 0, 0] (Pi.single j 1) i := by
    intro i j
    unfold LjFun Lpt
    rw [if_pos hs]
  have hX : ∀ y : Vec3, Xmt c ν ε μ χo χy (thinRep T) (reflY y)
      = reflY (Xmt c ν ε μ χo χy (thinRep T) y) :=
    fun y => xmtReflect c ν ε μ χo χy (thinRep T) y
  have hy0 : reflY (![ε⁻¹ / Real.sqrt s, 0, 0] : Vec3) = ![ε⁻¹ / Real.sqrt s, 0, 0] := by
    funext i
    fin_cases i <;> simp [reflY]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [key]
    exact azimuthal_entry_zero _ hX _ hy0 0 1 (by rw [sg_zero, sg_one]; norm_num)
  · rw [key]
    exact azimuthal_entry_zero _ hX _ hy0 1 0 (by rw [sg_one, sg_zero]; norm_num)
  · rw [key]
    exact azimuthal_entry_zero _ hX _ hy0 1 2 (by rw [sg_one, sg_two]; norm_num)
  · rw [key]
    exact azimuthal_entry_zero _ hX _ hy0 2 1 (by rw [sg_two, sg_one]; norm_num)

end UnforcedLeray.Short.PartIIIb.Concrete
