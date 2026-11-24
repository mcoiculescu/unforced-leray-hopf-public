import UnforcedLeray.Units.B0449.GraphResolventBounded
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# B0449 overlap uniqueness for local continuous chart candidates

This leaf freezes the local patching fact separately from the resolvent source. Two continuous
candidates that represent the actual chart on their central strips agree pointwise on their open
overlap after the exact chart transition.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace UnforcedLeray.B0449

open UnforcedLeray.PhaseSpace

/-- The transition from chart coordinates at center `τ₀` to coordinates at center `τ₀ + d`. -/
def chartTransition (d : ℝ) (p : ℝ × Space) : ℝ × Space :=
  (p.1 + -d, Real.exp (-d / 2) • p.2)

/-- The open central time strip, with all spatial points. -/
def chartCentral : Set (ℝ × Space) :=
  Ioo (-(1 / 8 : ℝ)) (1 / 8) ×ˢ (Set.univ : Set Space)

/-- The overlap of two central chart domains, expressed in the first chart's coordinates. -/
def chartOverlap (d : ℝ) : Set (ℝ × Space) :=
  chartCentral ∩ chartTransition d ⁻¹' chartCentral

theorem isOpen_chartCentral : IsOpen chartCentral := by
  exact isOpen_Ioo.prod isOpen_univ

theorem isOpen_chartOverlap (d : ℝ) : IsOpen (chartOverlap d) := by
  have hT : Continuous (chartTransition d) := by
    unfold chartTransition
    fun_prop
  exact isOpen_chartCentral.inter (isOpen_chartCentral.preimage hT)

/-- Two continuous scalar candidates identified a.e. with the actual chart agree everywhere on
their chart overlap. -/
theorem local_chart_candidates_eqOn_overlap {P : ℝ} [Fact (0 < P)]
    {q : ℝ≥0∞} [Fact (1 ≤ q)] {ν : ℝ} (hν : 0 < ν) (w : Yq P q)
    (τ₀ d : ℝ) (e : CVec3) (f₀ f₁ : ℝ × Space → ℂ)
    (hf₀ : Continuous f₀) (hf₁ : Continuous f₁)
    (h₀ : f₀ =ᵐ[volume.restrict chartCentral]
      (fun p => dotL e (chartJ w ν τ₀ p)))
    (h₁ : f₁ =ᵐ[volume.restrict chartCentral]
      (fun p => dotL e (chartJ w ν (τ₀ + d) p))) :
    EqOn f₀ (fun p => f₁ (chartTransition d p)) (chartOverlap d) := by
  have hT : Continuous (chartTransition d) := by
    unfold chartTransition
    fun_prop
  have hS : MeasurableSet chartCentral := measurableSet_Ioo.prod MeasurableSet.univ
  have h₀imp : ∀ᵐ p ∂(volume : Measure (ℝ × Space)),
      p ∈ chartCentral → f₀ p = dotL e (chartJ w ν τ₀ p) := by
    exact (ae_restrict_iff' hS).mp h₀
  have h₁imp : ∀ᵐ p ∂(volume : Measure (ℝ × Space)),
      p ∈ chartCentral → f₁ p = dotL e (chartJ w ν (τ₀ + d) p) := by
    exact (ae_restrict_iff' hS).mp h₁
  have h₁trans : ∀ᵐ p ∂(volume : Measure (ℝ × Space)),
      chartTransition d p ∈ chartCentral →
        f₁ (chartTransition d p) = dotL e (chartJ w ν (τ₀ + d) (chartTransition d p)) := by
    simpa [chartTransition] using (qmp_shift (-d)).ae h₁imp
  have hrel : f₀ =ᵐ[volume.restrict (chartOverlap d)]
      (fun p => f₁ (chartTransition d p)) := by
    rw [Filter.EventuallyEq, ae_restrict_iff' (isOpen_chartOverlap d).measurableSet]
    filter_upwards [h₀imp, h₁trans] with p hp₀ hp₁ hpV
    have h₀p := hp₀ hpV.1
    have h₁p := hp₁ hpV.2
    calc
      f₀ p = dotL e (chartJ w ν τ₀ p) := h₀p
      _ = dotL e (chartJ w ν (τ₀ + d) (chartTransition d p)) := by
        simp only [chartTransition]
        rw [chartJ_shift]
        have hscalar : Real.exp (d / 2) * Real.exp (-d / 2) = 1 := by
          rw [← Real.exp_add]
          have harg : d / 2 + -d / 2 = 0 := by ring
          rw [harg, Real.exp_zero]
        rw [smul_smul, hscalar, one_smul]
        have hpair : (p.1 + -d + d, p.2) = p := by
          apply Prod.ext
          · ring
          · rfl
        rw [hpair]
      _ = f₁ (chartTransition d p) := h₁p.symm
  exact MeasureTheory.Measure.eqOn_open_of_ae_eq hrel (isOpen_chartOverlap d)
    hf₀.continuousOn (hf₁.comp_continuousOn hT.continuousOn)

end UnforcedLeray.B0449
