import UnforcedLeray.Analysis.Rayleigh.Evans.Solution
import NonUniqueEuler.P.Infra.ODE.Holo
import NonUniqueEuler.P.Infra.ODE.Param
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Holomorphy and parameter continuity of the actual Gaussian Evans function

The normalized solution is the genuine global solution of the concrete Gaussian
Rayleigh ODE. Its dependence on spectral speed and angular index follows from
proved continuous-dependence and variational-equation theorems for that solution.
These results do not assert the existence of an unstable Evans zero.
The totalized coefficient outside the upper half-plane is not identified with
the completed neutral coefficient, and no real-axis extension is asserted.
-/

noncomputable section
open Set
namespace UnforcedLeray.Rayleigh.Evans
open NonUniqueEuler.LinODE

/-- The actual normalized solution pair is holomorphic in spectral speed. -/
theorem differentiableOn_normalizedPair (α a t : ℝ) :
    DifferentiableOn ℂ (fun c => normalizedPair α a c t) upperHalfPlane :=
  differentiableOn_sol (V := fun t c => rayleighPotential α t c)
    upperHalfPlane_open (continuousOn_rayleighPotential α)
    (differentiableOn_rayleighPotential α) a (0, 1) t

theorem differentiableOn_normalizedF (α a t : ℝ) :
    DifferentiableOn ℂ (fun c => normalizedF α a c t) upperHalfPlane :=
  (differentiableOn_normalizedPair α a t).fst

theorem differentiableOn_normalizedDerivative (α a t : ℝ) :
    DifferentiableOn ℂ (fun c => normalizedDerivative α a c t) upperHalfPlane :=
  (differentiableOn_normalizedPair α a t).snd

theorem differentiableOn_evansFunction (α a b : ℝ) :
    DifferentiableOn ℂ (evansFunction α a b) upperHalfPlane :=
  differentiableOn_normalizedF α a b

theorem analyticOnNhd_normalizedPair (α a t : ℝ) :
    AnalyticOnNhd ℂ (fun c => normalizedPair α a c t) upperHalfPlane :=
  (differentiableOn_normalizedPair α a t).analyticOnNhd upperHalfPlane_open

theorem analyticOnNhd_normalizedF (α a t : ℝ) :
    AnalyticOnNhd ℂ (fun c => normalizedF α a c t) upperHalfPlane :=
  (differentiableOn_normalizedF α a t).analyticOnNhd upperHalfPlane_open

theorem analyticOnNhd_normalizedDerivative (α a t : ℝ) :
    AnalyticOnNhd ℂ (fun c => normalizedDerivative α a c t) upperHalfPlane :=
  (differentiableOn_normalizedDerivative α a t).analyticOnNhd upperHalfPlane_open

theorem analyticOnNhd_evansFunction (α a b : ℝ) :
    AnalyticOnNhd ℂ (evansFunction α a b) upperHalfPlane :=
  (differentiableOn_evansFunction α a b).analyticOnNhd upperHalfPlane_open

/-- Joint continuity in radius, angular index, and upper-half-plane spectral speed. -/
theorem continuousOn_normalizedPair_parameters (a : ℝ) :
    ContinuousOn (fun q : ℝ × (ℝ × ℂ) => normalizedPair q.2.1 a q.2.2 q.1)
      (univ ×ˢ {p : ℝ × ℂ | p.2 ∈ upperHalfPlane}) :=
  continuousOn_sol (V := fun (t : ℝ) (p : ℝ × ℂ) => rayleighPotential p.1 t p.2)
    (y₀ := fun _ => (0, 1)) continuousOn_rayleighPotential_parameters a continuousOn_const

theorem continuousOn_normalizedF_parameters (a : ℝ) :
    ContinuousOn (fun q : ℝ × (ℝ × ℂ) => normalizedF q.2.1 a q.2.2 q.1)
      (univ ×ˢ {p : ℝ × ℂ | p.2 ∈ upperHalfPlane}) :=
  (continuousOn_normalizedPair_parameters a).fst

theorem continuousOn_normalizedDerivative_parameters (a : ℝ) :
    ContinuousOn (fun q : ℝ × (ℝ × ℂ) => normalizedDerivative q.2.1 a q.2.2 q.1)
      (univ ×ˢ {p : ℝ × ℂ | p.2 ∈ upperHalfPlane}) :=
  (continuousOn_normalizedPair_parameters a).snd

/-- Continuity of the actual finite-annulus endpoint value in the two spectral parameters. -/
theorem continuousOn_evansFunction_parameters (a b : ℝ) :
    ContinuousOn (fun p : ℝ × ℂ => evansFunction p.1 a b p.2)
      {p : ℝ × ℂ | p.2 ∈ upperHalfPlane} := by
  have hg : Continuous (fun p : ℝ × ℂ => (b, p)) := continuous_const.prodMk continuous_id
  have h := (continuousOn_normalizedF_parameters a).comp
    (f := fun p : ℝ × ℂ => (b, p))
    (s := {p : ℝ × ℂ | p.2 ∈ upperHalfPlane}) hg.continuousOn
    (fun p hp => ⟨mem_univ b, hp⟩)
  exact h

/-- The complex coefficient derivative comes from its explicit Gaussian formula. -/
theorem hasDerivAt_rayleighPotential (α t : ℝ) {c : ℂ} (hc : c ∈ upperHalfPlane) :
    HasDerivAt (rayleighPotential α t)
      ((gaussianRayleighCoefficient t : ℂ) / ((Sturm.neutralOmega t : ℂ) - c) ^ 2) c := by
  have h := (hasDerivAt_const c ((α : ℂ) ^ 2)).add
    ((hasDerivAt_const c (gaussianRayleighCoefficient t : ℂ)).div
      ((hasDerivAt_const c (Sturm.neutralOmega t : ℂ)).sub (hasDerivAt_id c))
      (rayleighDenominator_ne_zero t hc))
  convert h using 1 <;> first | rfl | simp

theorem deriv_rayleighPotential (α t : ℝ) {c : ℂ} (hc : c ∈ upperHalfPlane) :
    deriv (rayleighPotential α t) c =
      (gaussianRayleighCoefficient t : ℂ) / ((Sturm.neutralOmega t : ℂ) - c) ^ 2 :=
  (hasDerivAt_rayleighPotential α t hc).deriv

/-- The actual spectral derivative solves the differentiated Rayleigh ODE, with
zero initial data and the explicit Gaussian forcing coefficient. -/
theorem normalized_spectral_variation (α a : ℝ) {c : ℂ} (hc : c ∈ upperHalfPlane) :
    IsInhomSolOn (fun t => rayleighPotential α t c)
      (fun t => ((gaussianRayleighCoefficient t : ℂ) /
        ((Sturm.neutralOmega t : ℂ) - c) ^ 2) * normalizedF α a c t) univ
      (fun t => deriv (fun z => normalizedF α a z t) c)
      (fun t => deriv (fun z => normalizedDerivative α a z t) c) ∧
      deriv (fun z => normalizedF α a z a) c = 0 ∧
      deriv (fun z => normalizedDerivative α a z a) c = 0 := by
  have h := isInhomSolOn_deriv_sol (V := fun t c => rayleighPotential α t c)
    upperHalfPlane_open (continuousOn_rayleighPotential α)
    (differentiableOn_rayleighPotential α) a (0, 1) hc
  simpa only [normalizedF, normalizedDerivative, normalizedPair,
    deriv_rayleighPotential α _ hc] using h

end UnforcedLeray.Rayleigh.Evans
