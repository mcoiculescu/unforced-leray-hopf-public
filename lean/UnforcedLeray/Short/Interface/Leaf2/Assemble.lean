import UnforcedLeray.Short.Interface.Leaf2.Calc

/-!
# Interface leaf 2, conditional assembly (task `Interface:I11`)

Source of record: `the November 2 reference manuscript`, line 180 (the mode
equation in `𝒟'(ℝ³ × ℝ/𝒯ℤ)`), with the periodization of the test in the helper Props of
`Statements.lean` (Section 2b).

`periodicModeEquationToLine_of` takes the five helper Props as hypotheses, exactly as
`l3BackgroundOfPath_of` does for Leaf 1:

* `PeriodizeIsPeriodicTest` (task `Interface:I06`): the periodization of a similarity test is a
  periodic test.
* `PeriodizeCommutes` (task `Interface:I07`): the time, spatial Laplacian and dilation derivatives
  commute with periodization.
* `PeriodicLineToSlab` (task `Interface:I08`): a periodic `𝒴₂` field against a periodized test
  transfers the line integral to the slab.
* `PeriodicCouplingTransfer` (task `Interface:I09`): the coupling pairing transfers to the slab.
* `ModeSolutionIntegrability` (task `Interface:I10`): the integrability clauses of
  `IsWeakModeSolution`.

The unconditional `periodicModeEquationToLine` (`Short/Interface/Leaf2.lean`) applies this
theorem to the five proved helpers. The target has no hypotheses; the five Props are supplied by
that application only.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.Short.Interface.Leaf2

open UnforcedLeray UnforcedLeray.Blueprint UnforcedLeray.Cons.C08

/-- One pairing term from the line to the slab: the line integral of `⟨b, g⟩` equals the slab
integral of `⟨b, Lφ⟩` once `periodizeTest P g = Lφ` pointwise. -/
theorem transfer_of_periodize (hI8 : PeriodicLineToSlab) (P : ℝ) (b : ℝ → SpatialField)
    (hP : 0 < P) (hb : B0005.IsY2 P b) (g Lφ : SpaceTime → Space)
    (hgc : Continuous g) (hgk : HasCompactSupport g)
    (hpz : ∀ z : SpaceTime, periodizeTest P g z = Lφ z) :
    IntegrableOn (fun z : SpaceTime => inner ℝ (b z.1 z.2) (Lφ z)) (periodSlab P) volume ∧
      (∫ z : SpaceTime, inner ℝ (b z.1 z.2) (g z)) =
        ∫ z in periodSlab P, inner ℝ (b z.1 z.2) (Lφ z) := by
  obtain ⟨hi, he⟩ := hI8 P b g hP hb hgc hgk
  have hfun : (fun z : SpaceTime => inner ℝ (b z.1 z.2) (periodizeTest P g z)) =
      fun z : SpaceTime => inner ℝ (b z.1 z.2) (Lφ z) := by
    funext z
    simp only [hpz z]
  rw [hfun] at hi he
  exact ⟨hi, he⟩

/-- **Conditional Leaf 2.** Given the five helper Props, the mode equation in distributions on
the period (`SolvesPeriodicModeEquation`, tested against periodic tests) gives the line equation
`IsWeakModeSolution` tested against similarity tests. -/
theorem periodicModeEquationToLine_of (hI6 : PeriodizeIsPeriodicTest)
    (hI7 : PeriodizeCommutes) (hI8 : PeriodicLineToSlab) (hI9 : PeriodicCouplingTransfer)
    (hI10 : ModeSolutionIntegrability) : PeriodicModeEquationToLine := by
  intro h σ P U dU b hP hU hb hmode
  have hb2 : B0005.IsY2 P b := isY2_of_isH1Periodic hb
  have hint : ∀ ψ : SpaceTime → Space, IsSimilarityTest ψ →
      Integrable (pairTerm b ψ) ∧ Integrable (temporalTerm b ψ) ∧
        Integrable (dilationTerm b ψ) ∧ Integrable (diffusionTerm b ψ) ∧
        (∀ᵐ τ, ∀ j : Fin 3,
          Integrable (lerayDivIntegrand (symTensorColumns (U τ) (b τ)) (slice ψ τ) j)) ∧
        Integrable (weakCoupling U b ψ) :=
    fun ψ hψ => hI10 P U dU b hP hU hb ψ hψ
  refine ⟨fun ψ hψ => (hint ψ hψ).1, fun ψ hψ => (hint ψ hψ).2.1,
    fun ψ hψ => (hint ψ hψ).2.2.1, fun ψ hψ => (hint ψ hψ).2.2.2.1,
    fun ψ hψ => (hint ψ hψ).2.2.2.2.1, fun ψ hψ => (hint ψ hψ).2.2.2.2.2, ?_⟩
  intro ψ hψ
  obtain ⟨hTc, hTk⟩ := similarity_timeDerivative_regular hψ
  obtain ⟨hDc, hDk⟩ := similarity_spatialDerivative_regular hψ
  obtain ⟨hLc, hLk⟩ := similarity_spatialLaplacian_regular hψ
  -- the periodized test and the slab form of the mode equation
  have hφ : IsPeriodicTest P (periodizeTest P ψ) := hI6 P ψ hP hψ
  have hslab := hmode (periodizeTest P ψ) hφ
  have hcoup := hI9 P U dU b hP hU hb2 ψ hψ
  -- the four pairing terms transfer from the line to the slab
  have eP := transfer_of_periodize hI8 P b hP hb2 ψ (periodizeTest P ψ)
    hψ.smooth.continuous hψ.compact (fun _ => rfl)
  have eT := transfer_of_periodize hI8 P b hP hb2 (fun w : SpaceTime => timeDerivative ψ w.1 w.2)
    (fun z : SpaceTime => timeDerivative (periodizeTest P ψ) z.1 z.2) hTc hTk
    (fun z => (hI7 P ψ hP hψ z).1.symm)
  have eD := transfer_of_periodize hI8 P b hP hb2
    (fun w : SpaceTime => spatialDerivative ψ w.1 w.2 w.2)
    (fun z : SpaceTime => spatialDerivative (periodizeTest P ψ) z.1 z.2 z.2) hDc hDk
    (fun z => (hI7 P ψ hP hψ z).2.2.symm)
  have eL := transfer_of_periodize hI8 P b hP hb2
    (fun w : SpaceTime => spatialLaplacian ψ w.1 w.2)
    (fun z : SpaceTime => spatialLaplacian (periodizeTest P ψ) z.1 z.2) hLc hLk
    (fun z => (hI7 P ψ hP hψ z).2.1.symm)
  have eP' : (∫ z, pairTerm b ψ z) = ∫ z in periodSlab P, pairTerm b (periodizeTest P ψ) z :=
    eP.2
  have eT' : (∫ z, temporalTerm b ψ z) =
      ∫ z in periodSlab P, temporalTerm b (periodizeTest P ψ) z := eT.2
  have eD' : (∫ z, dilationTerm b ψ z) =
      ∫ z in periodSlab P, dilationTerm b (periodizeTest P ψ) z := eD.2
  have eL' : (∫ z, diffusionTerm b ψ z) =
      ∫ z in periodSlab P, diffusionTerm b (periodizeTest P ψ) z := eL.2
  have iP : IntegrableOn (pairTerm b (periodizeTest P ψ)) (periodSlab P) := eP.1
  have iT : IntegrableOn (temporalTerm b (periodizeTest P ψ)) (periodSlab P) := eT.1
  have iD : IntegrableOn (dilationTerm b (periodizeTest P ψ)) (periodSlab P) := eD.1
  have iL : IntegrableOn (diffusionTerm b (periodizeTest P ψ)) (periodSlab P) := eL.1
  -- the line side: the weak mode integral, and the coupling by `I09`
  have hI := hint ψ hψ
  rw [weakModeIntegral_linear h σ b ψ hI.1 hI.2.1 hI.2.2.1 hI.2.2.2.1, hcoup, eP', eT', eD',
    eL']
  -- the slab side: the same linear combination, then the mode equation
  have hS := weakModeIntegral_linear (μ := volume.restrict (periodSlab P)) h σ b
    (periodizeTest P ψ) iP iT iD iL
  rw [hS] at hslab
  linear_combination hslab

end UnforcedLeray.Short.Interface.Leaf2
