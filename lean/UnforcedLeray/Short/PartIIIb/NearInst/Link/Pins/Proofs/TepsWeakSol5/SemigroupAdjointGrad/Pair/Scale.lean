import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_pins_3_5_4_4

/-!
# Leaf S2: scaling and evenness (`AdjSpatialScale`)

Source `the November 2 reference manuscript`
1339-1362, 3346-3352.  With `c = e^{t/2} > 0`:
`∫ G_a(cy - u) A(y) dy = e^{-3t/2} ∫ G_a(w) A(e^{-t/2}(u - w)) dw`.

Proof: `y = c⁻¹ v` (`Measure.integral_comp_smul`, factor `|(c⁻¹)^3|⁻¹ = c^3`), then
`v = u - w` (`integral_sub_left_eq_self`) and evenness `G_a(-w) = G_a(w)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set

namespace UnforcedLeray.Short.PartIIIb.NearInst

open UnforcedLeray.Gaussian (Euc gaussKernel)
open UnforcedLeray.PhaseSpace

theorem adjSpatialScale : AdjSpatialScale := by
  intro a t ha A hA hR u
  set c : ℝ := Real.exp (t / 2) with hc
  have hcpos : 0 < c := Real.exp_pos _
  -- the integrand after the substitution `y = c⁻¹ • v`
  set g : Space → CVec3 := fun y => gaussKernel 3 a (c • y - u) • A y with hg
  set h : Space → CVec3 := fun v => gaussKernel 3 a (v - u) • A (c⁻¹ • v) with hh
  have hgh : (fun v : Space => g (c⁻¹ • v)) = h := by
    funext v
    simp only [hg, hh]
    rw [smul_smul, mul_inv_cancel₀ hcpos.ne', one_smul]
  have hscale : ∫ v, h v = |((c⁻¹) ^ 3)⁻¹| • ∫ y, g y := by
    rw [← hgh]
    have := MeasureTheory.Measure.integral_comp_smul (volume : Measure Space) g c⁻¹
    simpa [finrank_euclideanSpace_fin] using this
  have habs : |((c⁻¹) ^ 3)⁻¹| = c ^ 3 := by
    rw [abs_of_pos (by positivity)]
    simp
  have hexp : (Real.exp (-(3 * t / 2)) : ℝ) = (c ^ 3)⁻¹ := by
    rw [hc, ← Real.exp_nat_mul, ← Real.exp_neg]
    congr 1
    push_cast
    ring
  have hexpInv : Real.exp (-t / 2) = c⁻¹ := by
    rw [hc, ← Real.exp_neg]
    congr 1
    ring
  -- `∫ g = (c^3)⁻¹ • ∫ h`
  have hgint : ∫ y, g y = (Real.exp (-(3 * t / 2)) : ℝ) • ∫ v, h v := by
    rw [hscale, habs, hexp, smul_smul, inv_mul_cancel₀ (by positivity), one_smul]
  -- the left side of the target is `∫ g`, after unfolding
  have hLHS : ∫ y, gaussKernel 3 a (c • y - u) • A y = ∫ y, g y := rfl
  rw [hLHS, hgint]
  congr 1
  -- `∫ h = ∫ G_a(w) A(c⁻¹(u - w)) dw`
  have hsub : ∫ v, h v = ∫ w, h (u - w) := (integral_sub_left_eq_self h volume u).symm
  rw [hsub, hexpInv]
  congr 1
  funext w
  simp only [hh]
  rw [show u - w - u = -w by abel, UnforcedLeray.Gaussian.gaussKernel_neg]
