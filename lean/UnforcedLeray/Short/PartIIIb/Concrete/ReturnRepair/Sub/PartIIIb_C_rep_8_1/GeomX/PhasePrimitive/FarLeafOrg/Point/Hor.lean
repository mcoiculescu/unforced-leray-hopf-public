import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomX.PhasePrimitive.FarLeafOrg.Defs

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete.FarLeafOrg

open UnforcedLeray

/-- horizontal norm -/
def hor (v : Space) : ℝ := Real.sqrt (v 0 ^ 2 + v 1 ^ 2)

lemma hor_eq (v : Space) : hor v = ‖(⟨v 0, v 1⟩ : ℂ)‖ := by
  rw [Complex.norm_eq_sqrt_sq_add_sq]; rfl

lemma hor_sub (a b : Space) (l : ℝ) (hl : 0 ≤ l) : hor a ≤ hor (a - l • b) + l * hor b := by
  rw [hor_eq, hor_eq, hor_eq]
  have e : (⟨a 0, a 1⟩ : ℂ) = (⟨(a - l • b) 0, (a - l • b) 1⟩ : ℂ) + (l : ℂ) * (⟨b 0, b 1⟩ : ℂ) := by
    apply Complex.ext <;> simp
  have h := norm_add_le (⟨(a - l • b) 0, (a - l • b) 1⟩ : ℂ) ((l : ℂ) * (⟨b 0, b 1⟩ : ℂ))
  rw [← e, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hl] at h
  exact h

lemma hor_smul (c : ℝ) (hc : 0 ≤ c) (v : Space) : hor (c • v) = c * hor v := by
  unfold hor
  have : (c • v) 0 ^ 2 + (c • v) 1 ^ 2 = c ^ 2 * (v 0 ^ 2 + v 1 ^ 2) := by simp; ring
  rw [this, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc]

lemma norm_sq_eq (v : Space) : ‖v‖ = Real.sqrt (v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2) := by
  rw [EuclideanSpace.norm_eq]
  simp [Fin.sum_univ_three]

lemma hor_le_norm (v : Space) : hor v ≤ ‖v‖ := by
  rw [norm_sq_eq]
  exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (v 2)])

lemma norm_le_hor (v : Space) : ‖v‖ ≤ hor v + |v 2| := by
  rw [norm_sq_eq]
  unfold hor
  have h1 := Real.sqrt_nonneg (v 0 ^ 2 + v 1 ^ 2)
  have h2 := Real.sq_sqrt (show 0 ≤ v 0 ^ 2 + v 1 ^ 2 by positivity)
  apply Real.sqrt_le_iff.2
  refine ⟨by positivity, ?_⟩
  nlinarith [sq_abs (v 2), abs_nonneg (v 2)]

end UnforcedLeray.Short.PartIIIb.Concrete.FarLeafOrg
end
