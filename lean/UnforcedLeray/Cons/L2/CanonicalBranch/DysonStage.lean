import UnforcedLeray.Cons.L2.CanonicalBranch.UniformComplement
import UnforcedLeray.Cons.L2.CanonicalBranch.CompactInteraction

/-!
# Bounded transport and scalar terms in the first Dyson stage

For `paper/main.tex`, equations `eq:st18-t00080`–`t00081`, the first bounded perturbation of
`Eβ(t,s)=exp(D∫β)` is `T−λ−βκ`, where `T=−2iΩ` is the bounded skew transport. This leaf packages
that actual coefficient as an `Evolution.BoundedPert` for measurable bounded `β`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace UnforcedLeray.Cons.G3b

open UnforcedLeray.B0010 UnforcedLeray.B0012

/-- The first-stage bounded interaction `T - λ - βκ` on a fixed time block. -/
def transportDysonPert (T : XG →L[ℂ] XG) (lam κ : ℂ) (β : ℝ → ℝ) (a b : ℝ)
    (hβ : AEStronglyMeasurable β (volume.restrict (Set.Icc a b)))
    (hβb : ∃ M : ℝ, ∀ t ∈ Set.Icc a b, |β t| ≤ M) :
    UnforcedLeray.Evolution.BoundedPert XG a b := by
  let M : ℝ := Classical.choose hβb
  have hM : ∀ t ∈ Set.Icc a b, |β t| ≤ M := Classical.choose_spec hβb
  let I : XG →L[ℂ] XG := 1
  refine ⟨fun t => T - lam • I - ((β t : ℂ) * κ) • I, ?_, ?_⟩
  · intro x
    have hβc : AEStronglyMeasurable (fun t => (β t : ℂ))
        (volume.restrict (Set.Icc a b)) :=
      Complex.continuous_ofReal.comp_aestronglyMeasurable hβ
    have hc : AEStronglyMeasurable (fun t => (β t : ℂ) * κ)
        (volume.restrict (Set.Icc a b)) :=
      (continuous_id.mul continuous_const).comp_aestronglyMeasurable hβc
    have hs : AEStronglyMeasurable (fun t => ((β t : ℂ) * κ) • x)
        (volume.restrict (Set.Icc a b)) := hc.smul aestronglyMeasurable_const
    change AEStronglyMeasurable
      (fun t => (T - lam • I) x - ((β t : ℂ) * κ) • x)
      (volume.restrict (Set.Icc a b))
    exact aestronglyMeasurable_const.sub hs
  · refine ⟨‖T‖ + ‖lam‖ * ‖I‖ + (max M 0 * ‖κ‖) * ‖I‖, fun t ht => ?_⟩
    have hβnorm : ‖(β t : ℂ)‖ ≤ max M 0 := by
      simpa [Complex.norm_real, Real.norm_eq_abs] using (hM t ht).trans (le_max_left M 0)
    have hcoef : ‖(β t : ℂ) * κ‖ ≤ max M 0 * ‖κ‖ := by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right hβnorm (norm_nonneg κ)
    calc
      ‖T - lam • I - ((β t : ℂ) * κ) • I‖ ≤ ‖T - lam • I‖ + ‖((β t : ℂ) * κ) • I‖ :=
        norm_sub_le _ _
      _ ≤ (‖T‖ + ‖lam • I‖) + (max M 0 * ‖κ‖) * ‖I‖ := by
        gcongr
        · exact norm_sub_le _ _
        · rw [norm_smul]
          exact mul_le_mul_of_nonneg_right hcoef (norm_nonneg I)
      _ ≤ (‖T‖ + ‖lam‖ * ‖I‖) + (max M 0 * ‖κ‖) * ‖I‖ := by
        gcongr
        rw [norm_smul]

/-- The first-stage interaction is measurable in operator norm, since it depends continuously on
the scalar coefficient `β(t)`. -/
theorem transportDysonPert_aestronglyMeasurable (T : XG →L[ℂ] XG) (lam κ : ℂ)
    (β : ℝ → ℝ) (a b : ℝ)
    (hβ : AEStronglyMeasurable β (volume.restrict (Set.Icc a b)))
    (hβb : ∃ M : ℝ, ∀ t ∈ Set.Icc a b, |β t| ≤ M) :
    AEStronglyMeasurable
      (fun t => (transportDysonPert T lam κ β a b hβ hβb).A t)
      (volume.restrict (Set.Icc a b)) := by
  let I : XG →L[ℂ] XG := 1
  let ψ : ℂ → XG →L[ℂ] XG := fun z => T - lam • I - (z * κ) • I
  have hψ : Continuous ψ := by fun_prop
  have hβc : AEStronglyMeasurable (fun t => (β t : ℂ))
      (volume.restrict (Set.Icc a b)) :=
    Complex.continuous_ofReal.comp_aestronglyMeasurable hβ
  change AEStronglyMeasurable (fun t => ψ (β t : ℂ))
    (volume.restrict (Set.Icc a b))
  exact hψ.comp_aestronglyMeasurable hβc

/-- The adjoint coefficient in the first-stage Dyson evolution is strongly measurable. -/
theorem transportDysonPert_adjointMeasurable (T : XG →L[ℂ] XG) (lam κ : ℂ)
    (β : ℝ → ℝ) (a b : ℝ)
    (hβ : AEStronglyMeasurable β (volume.restrict (Set.Icc a b)))
    (hβb : ∃ M : ℝ, ∀ t ∈ Set.Icc a b, |β t| ≤ M) :
    (transportDysonPert T lam κ β a b hβ hβb).AdjointMeasurable :=
  UnforcedLeray.Evolution.BoundedPert.adjointMeasurable_of_aestronglyMeasurable
    (transportDysonPert T lam κ β a b hβ hβb)
    (transportDysonPert_aestronglyMeasurable T lam κ β a b hβ hβb)

/-- The actual first-stage free family `Fβ` of the manuscript: the bounded transport and scalar
terms `−2iΩ−λ−βκ` are added by Dyson to the Gaussian diffusion evolution `Eβ`. -/
def canonicalTransportDysonFamily {a b : ℝ} (lam κ : ℂ) (β : ℝ → ℝ)
    (hβi : ∀ s t, IntervalIntegrable β volume s t)
    (hβ0 : ∀ τ, 0 ≤ β τ) (M : ℝ) (hβM : ∀ τ, |β τ| ≤ M)
    (hβsm : AEStronglyMeasurable β (volume.restrict (Set.Icc a b)))
    (hβblock : ∃ B : ℝ, ∀ t ∈ Set.Icc a b, |β t| ≤ B) :
    UnforcedLeray.Evolution.EvolutionFamily XG a b :=
  UnforcedLeray.Evolution.dyson
    (freeDiffusionFamily β hβi hβ0 M hβM)
    (transportDysonPert ((-2 * Complex.I) • omegaOp) lam κ β a b hβsm hβblock)

/-- The actual full complement evolution `Uβ`: a second bounded-perturbation Dyson series, with
compact interaction `A−P+βR_f`, on top of the concrete first-stage family `Fβ`. -/
def canonicalComplementDysonFamily {a b : ℝ} (lam κ : ℂ)
    (A P Rf : XG →L[ℂ] XG) (β : ℝ → ℝ)
    (hβi : ∀ s t, IntervalIntegrable β volume s t)
    (hβ0 : ∀ τ, 0 ≤ β τ) (M : ℝ) (hβM : ∀ τ, |β τ| ≤ M)
    (hβsm : AEStronglyMeasurable β (volume.restrict (Set.Icc a b)))
    (hβblock : ∃ B : ℝ, ∀ t ∈ Set.Icc a b, |β t| ≤ B) :
    UnforcedLeray.Evolution.EvolutionFamily XG a b :=
  UnforcedLeray.Evolution.dyson
    (canonicalTransportDysonFamily lam κ β hβi hβ0 M hβM hβsm hβblock)
    (compactInteractionPert A P Rf β a b hβsm hβblock)

end UnforcedLeray.Cons.G3b
