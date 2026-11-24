import UnforcedLeray.Short.PartIIa.Calc.JetClass

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIa.Jet

open UnforcedLeray.B0184 UnforcedLeray.B0185 UnforcedLeray.B0188 UnforcedLeray.B0190

theorem lm_diff {f : ProfilePoint → ℝ} {x : ProfilePoint}
    (hf : ContDiffOn ℝ ∞ f {y : ProfilePoint | 0 < y.2.2})
    (hx : x ∈ {y : ProfilePoint | 0 < y.2.2}) : DifferentiableAt ℝ f x :=
  (hf.contDiffAt (isOpen_late.mem_nhds hx)).differentiableAt (by simp)

theorem lm_pE_mul (f g : ProfilePoint → ℝ) (x : ProfilePoint)
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    partialEta (f * g) x = partialEta f x * g x + f x * partialEta g x := by
  show fderiv ℝ (f * g) x eηDir = fderiv ℝ f x eηDir * g x + f x * fderiv ℝ g x eηDir
  rw [fderiv_mul hf hg]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem lm_pQ_mul (f g : ProfilePoint → ℝ) (x : ProfilePoint)
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    partialQ (f * g) x = partialQ f x * g x + f x * partialQ g x := by
  show fderiv ℝ (f * g) x eqDir = fderiv ℝ f x eqDir * g x + f x * fderiv ℝ g x eqDir
  rw [fderiv_mul hf hg]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem lm_pA_mul (f g : ProfilePoint → ℝ) (x : ProfilePoint)
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    partialAge (f * g) x = partialAge f x * g x + f x * partialAge g x := by
  show fderiv ℝ (f * g) x esDir = fderiv ℝ f x esDir * g x + f x * fderiv ℝ g x esDir
  rw [fderiv_mul hf hg]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem leibnizMul : LeibnizMul := by
  unfold LeibnizMul
  intro F G hF hG
  unfold JSmooth at hF hG
  refine ⟨?_, ?_, ?_⟩
  · intro ν c hν hc tr htr x hx
    have dF := lm_diff (hF ν c hν hc tr htr) hx
    have dG := lm_diff (hG ν c hν hc tr htr) hx
    show ageOperator (F ν c tr * G ν c tr) x =
      ageOperator (F ν c tr) x * G ν c tr x + F ν c tr x * ageOperator (G ν c tr) x
    unfold ageOperator
    rw [lm_pE_mul _ _ x dF dG, lm_pA_mul _ _ x dF dG]
    ring
  · intro ν c hν hc tr htr x hx
    have dF := lm_diff (hF ν c hν hc tr htr) hx
    have dG := lm_diff (hG ν c hν hc tr htr) hx
    show partialEta (F ν c tr * G ν c tr) x =
      partialEta (F ν c tr) x * G ν c tr x + F ν c tr x * partialEta (G ν c tr) x
    exact lm_pE_mul _ _ x dF dG
  · intro ν c hν hc tr htr x hx
    have dF := lm_diff (hF ν c hν hc tr htr) hx
    have dG := lm_diff (hG ν c hν hc tr htr) hx
    show partialQ (F ν c tr * G ν c tr) x =
      partialQ (F ν c tr) x * G ν c tr x + F ν c tr x * partialQ (G ν c tr) x
    exact lm_pQ_mul _ _ x dF dG

end UnforcedLeray.Short.PartIIa.Jet
