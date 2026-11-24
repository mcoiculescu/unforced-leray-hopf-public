import UnforcedLeray.Analysis.Sturm.L2TestPairing
import NonUniqueEuler.P.Infra.Sobolev.WeakDeriv

/-! # Algebra and uniqueness for the actual L² weak derivative graph -/
noncomputable section
open MeasureTheory Set
namespace UnforcedLeray.Sturm
open NonUniqueEuler.Sob

theorem hasWeakDerivOn_L2_sub {vs : List ℝ} {u v du dv : ComplexL2}
    (hu : HasWeakDerivOn univ vs (u : ℝ → ℂ) (du : ℝ → ℂ))
    (hv : HasWeakDerivOn univ vs (v : ℝ → ℂ) (dv : ℝ → ℂ)) :
    HasWeakDerivOn univ vs ((u - v : ComplexL2) : ℝ → ℂ)
      ((du - dv : ComplexL2) : ℝ → ℂ) := by
  intro φ hφ
  have hu' : testPairing (iterDirDeriv vs φ) (hφ.iterDirDeriv vs) u =
      (-1 : ℂ) ^ vs.length * testPairing φ hφ du := by
    simpa only [testPairing_apply] using hu φ hφ
  have hv' : testPairing (iterDirDeriv vs φ) (hφ.iterDirDeriv vs) v =
      (-1 : ℂ) ^ vs.length * testPairing φ hφ dv := by
    simpa only [testPairing_apply] using hv φ hφ
  rw [← testPairing_apply (iterDirDeriv vs φ) (hφ.iterDirDeriv vs),
    ← testPairing_apply φ hφ, map_sub, map_sub, hu', hv', mul_sub]

theorem hasWeakDerivOn_L2_smul {vs : List ℝ} {u du : ComplexL2}
    (hu : HasWeakDerivOn univ vs (u : ℝ → ℂ) (du : ℝ → ℂ)) (c : ℂ) :
    HasWeakDerivOn univ vs ((c • u : ComplexL2) : ℝ → ℂ)
      ((c • du : ComplexL2) : ℝ → ℂ) := by
  intro φ hφ
  have hu' : testPairing (iterDirDeriv vs φ) (hφ.iterDirDeriv vs) u =
      (-1 : ℂ) ^ vs.length * testPairing φ hφ du := by
    simpa only [testPairing_apply] using hu φ hφ
  rw [← testPairing_apply (iterDirDeriv vs φ) (hφ.iterDirDeriv vs),
    ← testPairing_apply φ hφ, map_smul, map_smul, hu']
  simp only [smul_eq_mul]
  ring

/-- The standard local distributional uniqueness theorem identifies L²
weak derivatives as actual equal L² classes. -/
theorem weakDerivative_L2_unique {vs : List ℝ} {u du dv : ComplexL2}
    (hu : HasWeakDerivOn univ vs (u : ℝ → ℂ) (du : ℝ → ℂ))
    (hv : HasWeakDerivOn univ vs (u : ℝ → ℂ) (dv : ℝ → ℂ)) : du = dv := by
  have h := HasWeakDerivOn.ae_eq isOpen_univ
    (((Lp.memLp du).locallyIntegrable (by norm_num)).locallyIntegrableOn univ)
    (((Lp.memLp dv).locallyIntegrable (by norm_num)).locallyIntegrableOn univ) hu hv
  apply Lp.ext
  filter_upwards [h] with x hx
  exact hx (mem_univ x)

end UnforcedLeray.Sturm
