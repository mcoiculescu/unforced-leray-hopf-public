import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.OuterGen.Transp.Deriv.Defs

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.NearInst

open UnforcedLeray.B0223

theorem odAdd : OD_Add := by
  unfold OD_Add
  intro P _ h hh s t hs ht Ψ
  have hpos : ∀ r : ℝ, 0 < (Real.exp (r / 2))⁻¹ := fun r => inv_pos.2 (Real.exp_pos _)
  have hE : ∀ r : ℝ, Real.exp r = Real.exp (r / 2) ^ 2 := fun r => by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hdh : ∀ (a φ : ℝ), 0 < a → ∀ u : XC P,
      dilN a (heatC φ u) = heatC (φ / a ^ 2) (dilN a u) := by
    intro a φ ha u
    have ha0 : a ≠ 0 := ha.ne'
    have h1 := heatC_dilN ha (φ / a ^ 2) u
    have hφ : a ^ 2 * (φ / a ^ 2) = φ := by field_simp
    rw [hφ] at h1
    exact h1.symm
  have hsc : ((Real.exp (-(s + t) / 4) : ℝ) : ℂ) =
      ((Real.exp (-s / 4) : ℝ) : ℂ) * ((Real.exp (-t / 4) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    congr 2
    ring
  unfold outerTransp
  simp only [map_smul]
  rw [smul_smul, hsc]
  congr 1
  have hA_s : 0 ≤ h * (Real.exp s - 1) := heatTime_nonneg hh hs
  have hA_t : 0 ≤ h * (Real.exp t - 1) := heatTime_nonneg hh ht
  have hB : 0 ≤ h * (Real.exp t - 1) / ((Real.exp (s / 2))⁻¹) ^ 2 :=
    div_nonneg hA_t (sq_nonneg _)
  have hcoef : h * (Real.exp s - 1) + h * (Real.exp t - 1) / ((Real.exp (s / 2))⁻¹) ^ 2
      = h * (Real.exp (s + t) - 1) := by
    have hEs : Real.exp (s / 2) ≠ 0 := (Real.exp_pos _).ne'
    rw [Real.exp_add, hE s]
    field_simp
    ring
  have hdil : (Real.exp (s / 2))⁻¹ * (Real.exp (t / 2))⁻¹ = (Real.exp ((s + t) / 2))⁻¹ := by
    rw [← mul_inv, ← Real.exp_add]
    congr 2
    ring
  rw [← transC_dilN (hpos s) (-t), heatC_transC, ← transC_add, ← neg_add,
    hdh _ _ (hpos s), ← heatC_add hA_s hB, dilN_mul (hpos s) (hpos t), hcoef, hdil]

end UnforcedLeray.Short.PartIIIb.NearInst
