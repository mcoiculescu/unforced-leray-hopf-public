import UnforcedLeray.Short.PartI.Sub.PartI_C06
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!


Source of record: `the November 2 reference manuscript`, lines 1106-1116
(`r_A(θ) = ∫_θ^∞ S(θ,s) QDq A(s)/s ds`, with `‖r_A(θ)‖ ≤ C θ⁻¹ ‖A‖_∞`).

Method. For `θ ≥ b > 0` the integrand `s ↦ (A(s)/s) S(θ,s)y` is continuous on `(θ,∞)` and bounded by
`(M/θ) C‖y‖ e^{-g(s-θ)}`, which is integrable. The Bochner integral is then bounded by
`(M/θ) C‖y‖ ∫_θ^∞ e^{-g(s-θ)} ds = C‖y‖M/(gθ)`. The functional `l` commutes with the integral and
kills each integrand since `l(S(θ,s)y) = 0`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray

/-- **Target `PartI:C06/3`** (source lines 1106-1114): the bound on `r_A` and `ℓ(r_A) = 0`. -/
theorem canonicalRABound : CanonicalRABound := by
  intro l b C g S hb hC hg hS y hy A M hA hM θ hθ
  have hθ0 : 0 < θ := lt_of_lt_of_le hb hθ
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM θ hθ)
  -- continuity of the integrand on `[θ,∞)`
  have hdivc : ContinuousOn (fun s : ℝ => A s / (s : ℂ)) (Ici θ) :=
    ContinuousOn.div (hA.mono (Ici_subset_Ici.2 hθ)) Complex.continuous_ofReal.continuousOn
      (fun s hs => Complex.ofReal_ne_zero.2 (lt_of_lt_of_le hθ0 hs).ne')
  have hfc : ContinuousOn (fun s : ℝ => (A s / (s : ℂ)) • S θ s y) (Ici θ) :=
    hdivc.smul (hS.cont_snd θ y hθ)
  have hmeas : AEStronglyMeasurable (fun s : ℝ => (A s / (s : ℂ)) • S θ s y)
      (volume.restrict (Ioi θ)) :=
    (hfc.mono Ioi_subset_Ici_self).aestronglyMeasurable measurableSet_Ioi
  -- the scalar tail `∫_θ^∞ e^{-g(s-θ)} ds = 1/g`
  have h1 : (fun s : ℝ => Real.exp (-(g * (s - θ)))) =
      fun s => Real.exp (g * θ) * Real.exp ((-g) * s) := by
    funext s
    rw [← Real.exp_add]
    congr 1
    ring
  have hexpI : IntegrableOn (fun s : ℝ => Real.exp (-(g * (s - θ)))) (Ioi θ) := by
    rw [h1]
    exact Integrable.const_mul (integrableOn_exp_mul_Ioi (by linarith) θ) (Real.exp (g * θ))
  have hintI : ∫ s in Ioi θ, Real.exp (-(g * (s - θ))) = 1 / g := by
    have h2 : Real.exp (g * θ) * Real.exp ((-g) * θ) = 1 := by
      rw [← Real.exp_add, show g * θ + (-g) * θ = 0 by ring, Real.exp_zero]
    rw [h1, integral_const_mul, integral_exp_mul_Ioi (by linarith) θ, neg_div_neg_eq,
      ← mul_div_assoc, h2]
  -- pointwise bound
  have hpt : ∀ s : ℝ, θ < s →
      ‖(A s / (s : ℂ)) • S θ s y‖ ≤ (M * (C * ‖y‖) / θ) * Real.exp (-(g * (s - θ))) := by
    intro s hs
    have hθs : θ ≤ s := hs.le
    have hsp : (0 : ℝ) < s := lt_trans hθ0 hs
    have hAs : ‖A s‖ ≤ M := hM s (le_trans hθ hs.le)
    have hns : ‖(s : ℂ)‖ = s := by
      rw [Complex.norm_real, Real.norm_of_nonneg hsp.le]
    have hdec := hS.decay θ s y hθ hθs hy
    have hq : ‖A s‖ / s ≤ M / θ := by
      rw [div_le_div_iff₀ hsp hθ0]
      exact mul_le_mul hAs hθs hθ0.le hM0
    rw [norm_smul, norm_div, hns]
    calc ‖A s‖ / s * ‖S θ s y‖ ≤ (M / θ) * (C * Real.exp (-(g * (s - θ))) * ‖y‖) :=
          mul_le_mul hq hdec (norm_nonneg _) (div_nonneg hM0 hθ0.le)
      _ = (M * (C * ‖y‖) / θ) * Real.exp (-(g * (s - θ))) := by ring
  have hbint : Integrable (fun s : ℝ => (M * (C * ‖y‖) / θ) * Real.exp (-(g * (s - θ))))
      (volume.restrict (Ioi θ)) :=
    Integrable.const_mul hexpI _
  have hae : ∀ᵐ s ∂(volume.restrict (Ioi θ)),
      ‖(A s / (s : ℂ)) • S θ s y‖ ≤ (M * (C * ‖y‖) / θ) * Real.exp (-(g * (s - θ))) :=
    (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun s hs => hpt s hs)
  have hint1 : IntegrableOn (fun s : ℝ => (A s / (s : ℂ)) • S θ s y) (Ioi θ) :=
    Integrable.mono' hbint hmeas hae
  refine ⟨hint1, ?_, ?_⟩
  · show ‖∫ s in Ioi θ, (A s / (s : ℂ)) • S θ s y‖ ≤ C * ‖y‖ * M / (g * θ)
    calc ‖∫ s in Ioi θ, (A s / (s : ℂ)) • S θ s y‖
        ≤ ∫ s in Ioi θ, (M * (C * ‖y‖) / θ) * Real.exp (-(g * (s - θ))) :=
          norm_integral_le_of_norm_le hbint hae
      _ = (M * (C * ‖y‖) / θ) * ∫ s in Ioi θ, Real.exp (-(g * (s - θ))) :=
          integral_const_mul _ _
      _ = (M * (C * ‖y‖) / θ) * (1 / g) := by rw [hintI]
      _ = C * ‖y‖ * M / (g * θ) := by ring
  · show l (∫ s in Ioi θ, (A s / (s : ℂ)) • S θ s y) = 0
    rw [← ContinuousLinearMap.integral_comp_comm l hint1]
    have h0 : ∫ s in Ioi θ, l ((A s / (s : ℂ)) • S θ s y) = ∫ _ in Ioi θ, (0 : ℂ) := by
      refine setIntegral_congr_fun measurableSet_Ioi (fun s hs => ?_)
      show l ((A s / (s : ℂ)) • S θ s y) = 0
      rw [map_smul, hS.ker θ s y hθ (le_of_lt hs) hy, smul_zero]
    rw [h0, integral_zero]

end UnforcedLeray.Short.PartI
