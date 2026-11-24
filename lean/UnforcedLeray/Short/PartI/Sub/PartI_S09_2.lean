import UnforcedLeray.Short.PartI.Sub.PartI_S09
import UnforcedLeray.Short.PartI.Tasks.AdjointEigenvectorExplicit
import UnforcedLeray.Cons.C01ReferenceChoice.Eigenpair

/-!
# Part I, task `PartI:S09/2` (`SeedQuotientSmooth`): reduction to smoothness of `greenN 2`

Source: `the November 2 reference manuscript`
lines 606-609 ("The quotients at `k = 0` are removable").
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Real
open scoped ENNReal ComplexConjugate ContDiff Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.GaussianVortex (radialOmega radialK radialOmega_smooth radialK_smooth)

/-- Leaf `PartI:S09/2/1` (lines 606-609): for `h ∈ L²(xG)` smooth on `(0,∞)`,
`r ↦ greenN 2 h r = -(1/4)(r⁻² ∫₀^r ρ³ h + r² ∫_r^∞ ρ⁻¹ h)` is smooth on `(0,∞)`
(FTC for the two integrals, whose integrability is `WProf`). -/
def GreenTwoSmooth : Prop :=
  ∀ (h : ℝ → ℂ), MemLp h 2 B0010.xGMeasure → ContDiffOn ℝ ∞ h (Ioi 0) →
    ContDiffOn ℝ ∞ (fun r : ℝ => Planar.greenN 2 h r) (Ioi 0)

theorem seedQuotientSmooth_of (h1 : GreenTwoSmooth) : SeedQuotientSmooth := by
  intro lam h hh ℓ hI hs
  have hre := hI.re_pos
  set q : B0010.XG := hh.toLp h with hq
  have hGs := h1 h hh hs
  have hΩ : ContDiff ℝ ∞ (fun r : ℝ => (radialOmega r : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp radialOmega_smooth
  have hK : ContDiff ℝ ∞ (fun r : ℝ => (radialK r : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp radialK_smooth
  have hqh : (⇑q) =ᵐ[volume.restrict (Ioi (0 : ℝ))] h :=
    B0012.restrict_ac.ae_le hh.coeFn_toLp
  have hgreen : ∀ r, Planar.greenN 2 (⇑q) r = Planar.greenN 2 h r := adjEig_greenN_congr hqh
  refine ⟨fun r => Planar.greenN 2 h r / ((radialOmega r : ℂ) - Complex.I * lam / 2), ?_, ?_, ?_⟩
  · have hD' : ContDiffOn ℝ ∞ (fun r : ℝ => ((radialOmega r : ℂ) - Complex.I * lam / 2)⁻¹) (Ioi 0) := by
      intro r _
      have hat : ContDiffAt ℝ ∞ (fun z : ℂ => z⁻¹) ((radialOmega r : ℂ) - Complex.I * lam / 2) :=
        (contDiffAt_inv ℂ (adjEig_den_ne hre _)).restrict_scalars ℝ
      exact (hat.comp_contDiffWithinAt r ((hΩ.sub contDiff_const).contDiffWithinAt))
    simpa only [div_eq_mul_inv] using hGs.mul hD'
  · intro r hr hk
    have hae : ∀ᵐ x ∂(volume.restrict (Ioi (0 : ℝ))),
        ((radialOmega x : ℂ) - Complex.I * lam / 2) * h x = (radialK x : ℂ) * Planar.greenN 2 h x := by
      have h0 := B0012.restrict_ac.ae_le (adjEig_pointwise hI.eigen)
      filter_upwards [h0, hqh] with x hx hx'
      rw [← hx', ← hgreen x]
      exact hx
    have hcont : ContinuousOn (fun x : ℝ => ((radialOmega x : ℂ) - Complex.I * lam / 2) * h x)
        (Ioi 0) :=
      ((hΩ.continuous.sub continuous_const).continuousOn).mul hs.continuousOn
    have hcont2 : ContinuousOn (fun x : ℝ => (radialK x : ℂ) * Planar.greenN 2 h x) (Ioi 0) :=
      hK.continuous.continuousOn.mul hGs.continuousOn
    have heq := Measure.eqOn_open_of_ae_eq hae isOpen_Ioi hcont hcont2 hr
    simp only at heq
    have hk' : (Blueprint.Planar.strainK r : ℂ) ≠ 0 := by exact_mod_cast hk
    rw [Cons.C01.strainK_eq] at hk' ⊢
    have hD := adjEig_den_ne hre (radialOmega r)
    simp only
    rw [div_eq_div_iff hD hk']
    linear_combination -heq
  · obtain ⟨C, hC0, hC⟩ := Planar.norm_greenN_two_le_XG
    refine ⟨2 * (C * ‖q‖) / lam.re, fun r hr1 => ?_⟩
    have hr0 : 0 < r := by linarith
    have hb := hC q r hr0
    have hmin : min r ((r ^ 2)⁻¹) ≤ (r ^ 2)⁻¹ := min_le_right _ _
    have hG : ‖Planar.greenN 2 h r‖ ≤ C * ‖q‖ * (r ^ 2)⁻¹ := by
      rw [← hgreen r]
      exact hb.trans (by gcongr)
    have hD : lam.re / 2 ≤ ‖(radialOmega r : ℂ) - Complex.I * lam / 2‖ := by
      have h1 := Complex.abs_im_le_norm ((radialOmega r : ℂ) - Complex.I * lam / 2)
      rw [adjEig_im_den, abs_neg, abs_of_pos (by linarith)] at h1
      exact h1
    have hDpos : 0 < lam.re / 2 := by linarith
    show ‖Planar.greenN 2 h r / ((radialOmega r : ℂ) - Complex.I * lam / 2)‖ ≤ _
    rw [norm_div]
    have hr2 : 0 < r ^ 2 := by positivity
    calc ‖Planar.greenN 2 h r‖ / ‖(radialOmega r : ℂ) - Complex.I * lam / 2‖
        ≤ (C * ‖q‖ * (r ^ 2)⁻¹) / (lam.re / 2) := by
          apply div_le_div₀ (by positivity) hG hDpos hD
      _ = 2 * (C * ‖q‖) / lam.re / r ^ 2 := by field_simp

end UnforcedLeray.Short.PartI
