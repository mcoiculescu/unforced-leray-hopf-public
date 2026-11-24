import UnforcedLeray.Short.PartIIa.Calc.JetClass

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIa.Jet

open UnforcedLeray.B0184 UnforcedLeray.B0185 UnforcedLeray.B0188 UnforcedLeray.B0190

theorem lo_diff {f : ProfilePoint → ℝ} {x : ProfilePoint}
    (hf : ContDiffOn ℝ ∞ f {y : ProfilePoint | 0 < y.2.2})
    (hx : x ∈ {y : ProfilePoint | 0 < y.2.2}) : DifferentiableAt ℝ f x :=
  (hf.contDiffAt (isOpen_late.mem_nhds hx)).differentiableAt (by simp)

theorem lo_pE_add (f g : ProfilePoint → ℝ) (x : ProfilePoint)
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    partialEta (f + g) x = partialEta f x + partialEta g x := by
  show fderiv ℝ (f + g) x eηDir = fderiv ℝ f x eηDir + fderiv ℝ g x eηDir
  rw [fderiv_add hf hg, ContinuousLinearMap.add_apply]

theorem lo_pQ_add (f g : ProfilePoint → ℝ) (x : ProfilePoint)
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    partialQ (f + g) x = partialQ f x + partialQ g x := by
  show fderiv ℝ (f + g) x eqDir = fderiv ℝ f x eqDir + fderiv ℝ g x eqDir
  rw [fderiv_add hf hg, ContinuousLinearMap.add_apply]

theorem lo_pA_add (f g : ProfilePoint → ℝ) (x : ProfilePoint)
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    partialAge (f + g) x = partialAge f x + partialAge g x := by
  show fderiv ℝ (f + g) x esDir = fderiv ℝ f x esDir + fderiv ℝ g x esDir
  rw [fderiv_add hf hg, ContinuousLinearMap.add_apply]

theorem lo_pE_smul (k : ℝ) (f : ProfilePoint → ℝ) (x : ProfilePoint)
    (hf : DifferentiableAt ℝ f x) :
    partialEta (k • f) x = k * partialEta f x := by
  show fderiv ℝ (k • f) x eηDir = k * fderiv ℝ f x eηDir
  rw [fderiv_const_smul hf, smul_apply, smul_eq_mul]

theorem lo_pQ_smul (k : ℝ) (f : ProfilePoint → ℝ) (x : ProfilePoint)
    (hf : DifferentiableAt ℝ f x) :
    partialQ (k • f) x = k * partialQ f x := by
  show fderiv ℝ (k • f) x eqDir = k * fderiv ℝ f x eqDir
  rw [fderiv_const_smul hf, smul_apply, smul_eq_mul]

theorem lo_pA_smul (k : ℝ) (f : ProfilePoint → ℝ) (x : ProfilePoint)
    (hf : DifferentiableAt ℝ f x) :
    partialAge (k • f) x = k * partialAge f x := by
  show fderiv ℝ (k • f) x esDir = k * fderiv ℝ f x esDir
  rw [fderiv_const_smul hf, smul_apply, smul_eq_mul]

theorem lo_pE_cmul (c : ℝ) (f : ProfilePoint → ℝ) (x : ProfilePoint)
    (hf : DifferentiableAt ℝ f x) :
    partialEta (fun y => c * f y) x = c * partialEta f x := by
  show fderiv ℝ (fun y => c * f y) x eηDir = c * fderiv ℝ f x eηDir
  rw [fderiv_const_mul hf, smul_apply, smul_eq_mul]

theorem lo_pQ_cmul (c : ℝ) (f : ProfilePoint → ℝ) (x : ProfilePoint)
    (hf : DifferentiableAt ℝ f x) :
    partialQ (fun y => c * f y) x = c * partialQ f x := by
  show fderiv ℝ (fun y => c * f y) x eqDir = c * fderiv ℝ f x eqDir
  rw [fderiv_const_mul hf, smul_apply, smul_eq_mul]

theorem lo_pA_cmul (c : ℝ) (f : ProfilePoint → ℝ) (x : ProfilePoint)
    (hf : DifferentiableAt ℝ f x) :
    partialAge (fun y => c * f y) x = c * partialAge f x := by
  show fderiv ℝ (fun y => c * f y) x esDir = c * fderiv ℝ f x esDir
  rw [fderiv_const_mul hf, smul_apply, smul_eq_mul]

theorem linearOps : LinearOps := by
  unfold LinearOps
  intro F G hF hG k
  unfold JSmooth at hF hG
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- K (F + G)
    intro ν c hν hc tr htr x hx
    have dF := lo_diff (hF ν c hν hc tr htr) hx
    have dG := lo_diff (hG ν c hν hc tr htr) hx
    show ageOperator (F ν c tr + G ν c tr) x = ageOperator (F ν c tr) x + ageOperator (G ν c tr) x
    unfold ageOperator
    rw [lo_pE_add _ _ x dF dG, lo_pA_add _ _ x dF dG]
    ring
  · -- ∂_η (F + G)
    intro ν c hν hc tr htr x hx
    have dF := lo_diff (hF ν c hν hc tr htr) hx
    have dG := lo_diff (hG ν c hν hc tr htr) hx
    show partialEta (F ν c tr + G ν c tr) x = partialEta (F ν c tr) x + partialEta (G ν c tr) x
    exact lo_pE_add _ _ x dF dG
  · -- ∂_q (F + G)
    intro ν c hν hc tr htr x hx
    have dF := lo_diff (hF ν c hν hc tr htr) hx
    have dG := lo_diff (hG ν c hν hc tr htr) hx
    show partialQ (F ν c tr + G ν c tr) x = partialQ (F ν c tr) x + partialQ (G ν c tr) x
    exact lo_pQ_add _ _ x dF dG
  · -- K (k F)
    intro ν c hν hc tr htr x hx
    have dF := lo_diff (hF ν c hν hc tr htr) hx
    show ageOperator (k • F ν c tr) x = k * ageOperator (F ν c tr) x
    unfold ageOperator
    rw [lo_pE_smul k _ x dF, lo_pA_smul k _ x dF]
    ring
  · -- ∂_η (k F)
    intro ν c hν hc tr htr x hx
    have dF := lo_diff (hF ν c hν hc tr htr) hx
    show partialEta (k • F ν c tr) x = k * partialEta (F ν c tr) x
    exact lo_pE_smul k _ x dF
  · -- ∂_q (k F)
    intro ν c hν hc tr htr x hx
    have dF := lo_diff (hF ν c hν hc tr htr) hx
    show partialQ (k • F ν c tr) x = k * partialQ (F ν c tr) x
    exact lo_pQ_smul k _ x dF
  · -- K (ν F)
    intro ν c hν hc tr htr x hx
    have dF := lo_diff (hF ν c hν hc tr htr) hx
    show ageOperator (fun y => ν * F ν c tr y) x = ν * ageOperator (F ν c tr) x
    unfold ageOperator
    rw [lo_pE_cmul ν _ x dF, lo_pA_cmul ν _ x dF]
    ring
  · -- ∂_η (ν F)
    intro ν c hν hc tr htr x hx
    have dF := lo_diff (hF ν c hν hc tr htr) hx
    show partialEta (fun y => ν * F ν c tr y) x = ν * partialEta (F ν c tr) x
    exact lo_pE_cmul ν _ x dF
  · -- ∂_q (ν F)
    intro ν c hν hc tr htr x hx
    have dF := lo_diff (hF ν c hν hc tr htr) hx
    show partialQ (fun y => ν * F ν c tr y) x = ν * partialQ (F ν c tr) x
    exact lo_pQ_cmul ν _ x dF
  · -- K 0 = 0
    intro ν c hν hc tr htr x hx
    show ageOperator (fun _ : ProfilePoint => (0 : ℝ)) x = 0
    unfold ageOperator partialEta partialAge
    simp
  · -- ∂_η 0 = 0
    intro ν c hν hc tr htr x hx
    show partialEta (fun _ : ProfilePoint => (0 : ℝ)) x = 0
    unfold partialEta
    simp
  · -- ∂_q 0 = 0
    intro ν c hν hc tr htr x hx
    show partialQ (fun _ : ProfilePoint => (0 : ℝ)) x = 0
    unfold partialQ
    simp

end UnforcedLeray.Short.PartIIa.Jet
