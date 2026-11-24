import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_5_3
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.EATermSummable.Mgrad

/-!
# `PartIII-b:C/asrc/ra/5/3/2` : `GpsiA = e^{-|y|²/(2a)} • PpsiA` (source 4963-4968)

`p_0(s, y) = -a⁻³ e^{-|y|²/(2a)}` (since `x_0 = y`), with
`∇p_0(y) = a⁻⁴ e^{-|y|²/(2a)} y`, which gives the factorisation of `GpsiA`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- `x_0 = y`. -/
lemma gA_xj_zero (ν : ℝ) (y : ℝ × ℝ) : xj ν 0 y = y := by
  simp [xj]

/-- Directional derivative of `p_0` at `y`. -/
lemma gA_fderiv_pj0 (ν s : ℝ) (y v : ℝ × ℝ) :
    fderiv ℝ (pj ν s 0) y v =
      (ageA ν s ^ 3)⁻¹ * Real.exp (-(sq2 y) / (2 * ageA ν s)) *
        ((y.1 * v.1 + y.2 * v.2) / ageA ν s) := by
  rw [mg_fderiv_pj]
  simp only [gA_xj_zero]
  ring

/-- `∇p_0(y) = (a⁻³ e^{-|y|²/(2a)} / a) • y`. -/
lemma gA_mgrad_pj0 (ν s : ℝ) (y : ℝ × ℝ) :
    mgrad (pj ν s 0) y =
      ((ageA ν s ^ 3)⁻¹ * Real.exp (-(sq2 y) / (2 * ageA ν s)) / ageA ν s) • y := by
  unfold mgrad
  simp only [gA_fderiv_pj0]
  ext <;> simp [ei, smul_eq_mul] <;> ring

/-- (N-fd) `GpsiA = e^{-|y|²/(2a)} • PpsiA`. -/
theorem gpsiA_eq_proof : GpsiA_eq := by
  intro ν χ A p
  unfold GpsiA PpsiA
  rw [gA_mgrad_pj0]
  simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  have h4 : (ageA ν p.1 ^ 4)⁻¹ = (ageA ν p.1 ^ 3)⁻¹ * (ageA ν p.1)⁻¹ := by
    rw [show ageA ν p.1 ^ 4 = ageA ν p.1 ^ 3 * ageA ν p.1 by ring, mul_inv]
  rw [h4]
  ring

end UnforcedLeray.Short.PartIIIb.Concrete
