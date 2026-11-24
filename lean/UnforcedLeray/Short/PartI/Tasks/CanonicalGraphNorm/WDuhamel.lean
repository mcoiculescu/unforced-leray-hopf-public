import UnforcedLeray.Short.PartI.Sub.PartI_C10
import UnforcedLeray.Short.Spine.Proofs.CanonicalBranch.Mild.Duhamel

set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open scoped ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray UnforcedLeray.B0123

/-- The Duhamel identity for `W = e^{λθ}θ^κ V_can`, and its continuity on `(0,∞)`. -/
theorem wDuh_of_canonical {lam κ : ℂ} {V : ℝ → B0010.XG} (hV : IsCanonicalSolution V) :
    WDuh lam κ (fun θ : ℝ => Complex.exp (lam * θ) • (θ : ℂ) ^ κ • V θ) ∧
      ContinuousOn (fun θ : ℝ => Complex.exp (lam * θ) • (θ : ℂ) ^ κ • V θ) (Set.Ioi 0) := by
  refine ⟨?_, ?_⟩
  · intro θ θ' hθ hθθ'
    have hd := Spine.CanonicalMild.canonical_duhamel hV hθ hθθ'
    have hθ' : 0 < θ' := lt_of_lt_of_le hθ hθθ'
    have hs : ∀ v : ℝ, 0 < v → Complex.exp (lam * v) * (v : ℂ) ^ κ ≠ 0 := by
      intro v hv
      refine mul_ne_zero (Complex.exp_ne_zero _) ?_
      rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hv.ne')]
      exact Complex.exp_ne_zero _
    have hscal : ∀ v : ℝ, 0 < v → cfac lam κ θ v * (Complex.exp (lam * v) * (v : ℂ) ^ κ)
        = Complex.exp (lam * θ) * (θ : ℂ) ^ κ := by
      intro v hv
      unfold cfac
      rw [mul_assoc, inv_mul_cancel₀ (hs v hv), mul_one]
    have hpt : ∀ v ∈ uIcc θ θ', cfac lam κ θ v •
        expD (Real.log v - Real.log θ) (B0012.L0 (Complex.exp (lam * v) • (v : ℂ) ^ κ • V v))
          = (Complex.exp (lam * θ) * (θ : ℂ) ^ κ) •
            expD (Real.log v - Real.log θ) (B0012.L0 (V v)) := by
      intro v hv
      rw [uIcc_of_le hθθ'] at hv
      have hv0 : 0 < v := lt_of_lt_of_le hθ hv.1
      rw [smul_smul, map_smul, map_smul, smul_smul, hscal v hv0]
    have hint : ∫ v in θ..θ', cfac lam κ θ v •
        expD (Real.log v - Real.log θ) (B0012.L0 (Complex.exp (lam * v) • (v : ℂ) ^ κ • V v))
          = (Complex.exp (lam * θ) * (θ : ℂ) ^ κ) •
            ∫ v in θ..θ', expD (Real.log v - Real.log θ) (B0012.L0 (V v)) := by
      rw [intervalIntegral.integral_congr hpt, intervalIntegral.integral_smul]
    have hfirst : cfac lam κ θ θ' • expD (Real.log θ' - Real.log θ)
        (Complex.exp (lam * θ') • (θ' : ℂ) ^ κ • V θ')
          = (Complex.exp (lam * θ) * (θ : ℂ) ^ κ) • expD (Real.log θ' - Real.log θ) (V θ') := by
      rw [smul_smul, map_smul, smul_smul, hscal θ' hθ']
    have hLHS : Complex.exp (lam * θ) • (θ : ℂ) ^ κ • V θ
        = (Complex.exp (lam * θ) * (θ : ℂ) ^ κ) • V θ := smul_smul _ _ _
    dsimp only
    rw [hLHS, hfirst, hint, hd, smul_add]
  · have h1 : ContinuousOn (fun θ : ℝ => Complex.exp (lam * θ)) (Set.Ioi 0) :=
      (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).continuousOn
    have h2 : ContinuousOn (fun θ : ℝ => (θ : ℂ) ^ κ) (Set.Ioi 0) := fun θ hθ =>
      (Complex.continuousAt_ofReal_cpow_const θ κ
        (Or.inr (Set.mem_Ioi.mp hθ).ne')).continuousWithinAt
    have h3 : ContinuousOn V (Set.Ioi 0) := hV.smooth.continuousOn
    exact h1.smul (h2.smul h3)

end UnforcedLeray.Short.PartI
