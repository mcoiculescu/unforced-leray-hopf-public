import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_pins_3_5_4

/-!
# `AdjL0` (task `PartIII-b:C/near/pins/3/5/4/1`)

A phase test is an `L²` test: it is smooth and periodic, and `‖φ‖² + ‖∇φ‖²` is continuous and
vanishes for `‖y‖ > R`, so it is integrable on one period `Ioc 0 P ×ˢ univ` (it is supported in the
compact set `Icc 0 P ×ˢ closedBall 0 R` there).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.NearInst

open UnforcedLeray.PhaseSpace

/-- The gradient of a scalar function vanishing for `R < ‖y‖` vanishes there too. -/
theorem fderiv_eq_zero_of_far {φ : ℝ × Space → ℂ} {R : ℝ}
    (hR : ∀ τ y, R < ‖y‖ → φ (τ, y) = 0) (p : ℝ × Space) (hp : R < ‖p.2‖) :
    fderiv ℝ φ p = 0 := by
  have hopen : IsOpen {q : ℝ × Space | R < ‖q.2‖} :=
    isOpen_lt continuous_const (continuous_norm.comp continuous_snd)
  have hev : φ =ᶠ[𝓝 p] fun _ => 0 := by
    filter_upwards [hopen.mem_nhds hp] with q hq
    exact hR q.1 q.2 hq
  rw [hev.fderiv_eq]
  simp

theorem adjL0_aux {P : ℝ} (φ : ℝ × Space → ℂ) (hφ : IsPhaseTest P φ) :
    IsL2Test P φ := by
  obtain ⟨R, hR⟩ := hφ.bounded_support
  refine ⟨hφ.smooth, hφ.periodic, ?_⟩
  set f : ℝ × Space → ℝ := fun x => ‖φ x‖ ^ 2 + ‖gradT φ x‖ ^ 2 with hf
  have hfc : Continuous f := by
    have h1 : Continuous φ := hφ.continuous
    have h2 : Continuous (gradT φ) := (hφ.gradT).continuous
    exact (h1.norm.pow 2).add (h2.norm.pow 2)
  have hfar : ∀ x : ℝ × Space, R < ‖x.2‖ → f x = 0 := by
    intro x hx
    have h1 : φ x = 0 := hR x.1 x.2 hx
    have h2 : gradT φ x = 0 := by
      simp [PhaseSpace.gradT, PhaseSpace.dy, fderiv_eq_zero_of_far hR x hx]
    simp [hf, h1, h2]
  set K : Set (ℝ × Space) := Icc (0:ℝ) P ×ˢ Metric.closedBall (0:Space) R with hKdef
  have hK : IsCompact K := isCompact_Icc.prod (isCompact_closedBall _ _)
  have hg : Integrable (K.indicator f) := by
    have : IntegrableOn f K := hfc.continuousOn.integrableOn_compact hK
    exact this.integrable_indicator hK.isClosed.measurableSet
  refine hg.integrableOn.congr_fun (fun x hx => ?_)
    (measurableSet_Ioc.prod MeasurableSet.univ)
  by_cases hxK : x ∈ K
  · rw [indicator_of_mem hxK]
  · rw [indicator_of_notMem hxK]
    have hgt : R < ‖x.2‖ := by
      by_contra hcon
      push Not at hcon
      exact hxK ⟨⟨hx.1.1.le, hx.1.2⟩, mem_closedBall_zero_iff.2 hcon⟩
    exact (hfar x hgt).symm

/-- **Leaf 0**: a phase test is an `L²` test. -/
theorem adjL0 : AdjL0 := fun P _ φ hφ => adjL0_aux φ hφ

end UnforcedLeray.Short.PartIIIb.NearInst
