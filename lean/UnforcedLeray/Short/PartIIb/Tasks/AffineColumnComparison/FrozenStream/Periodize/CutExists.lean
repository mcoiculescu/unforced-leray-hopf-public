import UnforcedLeray.Short.PartIIb.Sub.G4_2_3

/-!
# Part II-b, task `PartII-b:G4/2/3/1`: smooth cut of the harmonic part

Source of record: `the November 2 reference manuscript`, lines 2349-2358.
Take `Hc y = M * s(y) * (y₁ - i y₂)^(-2)` with `s(y) = smoothTransition(4|y|²/ρ² - 1)`:
`s = 0` on `|y| ≤ ρ/2` (so `Hc` is smooth at the pole) and `s = 1` on `|y|² > ρ²`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Complex

namespace UnforcedLeray.Short.IIb

theorem cutExists : UnforcedLeray.Short.IIb.CutExists := by
  unfold UnforcedLeray.Short.IIb.CutExists
  intro ρ M hρ
  have hρ2 : 0 < ρ ^ 2 := by positivity
  have hpow : ∀ z : ℂ, z ^ (-2 : ℤ) = (z⁻¹) ^ 2 := by
    intro z
    simp [zpow_neg, inv_pow]
  have hw : ∀ y : ℝ × ℝ, ((y.1 : ℂ) - (y.2 : ℂ) * Complex.I) = 0 → y = 0 := by
    intro y h
    have hy1 : y.1 = 0 := by simpa using congrArg Complex.re h
    have hy2 : y.2 = 0 := by simpa using congrArg Complex.im h
    simp [Prod.ext_iff, hy1, hy2]
  have hcont : Continuous (fun y : ℝ × ℝ => 4 * (y.1 ^ 2 + y.2 ^ 2) / ρ ^ 2 - 1) := by
    fun_prop
  refine ⟨fun y => M * ((Real.smoothTransition (4 * (y.1 ^ 2 + y.2 ^ 2) / ρ ^ 2 - 1) : ℝ) : ℂ)
      * (((y.1 : ℂ) - (y.2 : ℂ) * Complex.I) ^ (-2 : ℤ)), ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy : y = 0
    · subst hy
      have hev : ∀ᶠ z in 𝓝 (0 : ℝ × ℝ), 4 * (z.1 ^ 2 + z.2 ^ 2) / ρ ^ 2 - 1 < 0 :=
        hcont.continuousAt.eventually_lt continuousAt_const (by norm_num)
      have hcst : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun _ : ℝ × ℝ => (0 : ℂ)) 0 := contDiffAt_const
      refine hcst.congr_of_eventuallyEq ?_
      filter_upwards [hev] with z hz
      simp [Real.smoothTransition.zero_of_nonpos hz.le]
    · have hwne : ((y.1 : ℂ) - (y.2 : ℂ) * Complex.I) ≠ 0 := fun h => hy (hw y h)
      have h1 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : ℝ × ℝ => 4 * (z.1 ^ 2 + z.2 ^ 2) / ρ ^ 2 - 1) y := by
        fun_prop
      have hA : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun z : ℝ × ℝ => ((Real.smoothTransition (4 * (z.1 ^ 2 + z.2 ^ 2) / ρ ^ 2 - 1) : ℝ) : ℂ)) y :=
        Complex.ofRealCLM.contDiff.contDiffAt.comp y
          (Real.smoothTransition.contDiffAt.comp y h1)
      have hfst : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : ℝ × ℝ => (z.1 : ℂ)) y :=
        (Complex.ofRealCLM.contDiff.comp contDiff_fst).contDiffAt
      have hsnd : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : ℝ × ℝ => (z.2 : ℂ)) y :=
        (Complex.ofRealCLM.contDiff.comp contDiff_snd).contDiffAt
      have hw1 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun z : ℝ × ℝ => (z.1 : ℂ) - (z.2 : ℂ) * Complex.I) y :=
        hfst.sub (hsnd.mul contDiffAt_const)
      have hB : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun z : ℝ × ℝ => ((z.1 : ℂ) - (z.2 : ℂ) * Complex.I) ^ (-2 : ℤ)) y := by
        simp only [hpow]
        exact (hw1.inv hwne).pow 2
      exact (contDiffAt_const.mul hA).mul hB
  · intro y hy
    have h1 : 2 ≤ 4 * (y.1 ^ 2 + y.2 ^ 2) / ρ ^ 2 := by
      rw [le_div_iff₀ hρ2]
      nlinarith
    have h2 : Real.smoothTransition (4 * (y.1 ^ 2 + y.2 ^ 2) / ρ ^ 2 - 1) = 1 :=
      Real.smoothTransition.one_of_one_le (by linarith)
    simp [h2]

end UnforcedLeray.Short.IIb
