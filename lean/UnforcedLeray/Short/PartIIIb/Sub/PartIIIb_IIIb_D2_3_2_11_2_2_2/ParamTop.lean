import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_3_2_11_2_2_2
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# `ParamContDiffTop` (`PartIII-b:IIIb-D2/3/2/11/2/2/2/1`, source 3604-3621)

All-order generic parametric differentiation: an induction on the order with
`hasFDerivAt_integral_of_dominated_of_fderiv_le`, the codomain generalised so that the
derivative family (valued in `E →L[ℝ] G`) is covered by the induction hypothesis.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem paramAesmIter0 {α : Type} [MeasurableSpace α] {m : Measure α} {E G : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (f : α → E → G) (x : E)
    (h : AEStronglyMeasurable (fun a => iteratedFDeriv ℝ 0 (f a) x) m) :
    AEStronglyMeasurable (fun a => f a x) m := by
  have h' := (continuousMultilinearCurryFin0 ℝ E G).continuous.comp_aestronglyMeasurable h
  refine h'.congr (Filter.Eventually.of_forall fun a => ?_)
  simp [iteratedFDeriv_zero_eq_comp]

theorem paramAesmIterFDeriv {α : Type} [MeasurableSpace α] {m : Measure α} {E G : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (f : α → E → G) (k : ℕ) (x : E)
    (h : AEStronglyMeasurable (fun a => iteratedFDeriv ℝ (k + 1) (f a) x) m) :
    AEStronglyMeasurable (fun a => iteratedFDeriv ℝ k (fun y => fderiv ℝ (f a) y) x) m := by
  have h' := (continuousMultilinearCurryRightEquiv' ℝ k E G).continuous.comp_aestronglyMeasurable h
  refine h'.congr (Filter.Eventually.of_forall fun a => ?_)
  simp [iteratedFDeriv_succ_eq_comp_right]

theorem paramNormFDeriv1 {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (f : E → G) (y : E) :
    ‖fderiv ℝ f y‖ = ‖iteratedFDeriv ℝ 1 f y‖ := by
  have h := norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (n := 0) (f := f) (x := y)
  rw [norm_iteratedFDeriv_zero] at h
  exact h

/--
valued in `E →L[ℝ] G`). -/
theorem paramContDiffOn_nat {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (n : ℕ) :
    ∀ {α : Type} [MeasurableSpace α] (m : Measure α) {G : Type} [NormedAddCommGroup G]
      [NormedSpace ℝ G] (F : α → E → G) (U : Set E) (g : ℕ → α → ℝ),
      IsOpen U → (∀ᵐ a ∂m, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (F a) U) →
      (∀ k, Integrable (g k) m) →
      (∀ k, ∀ᵐ a ∂m, ∀ x ∈ U, ‖iteratedFDeriv ℝ k (F a) x‖ ≤ g k a) →
      (∀ k, ∀ x ∈ U, AEStronglyMeasurable (fun a => iteratedFDeriv ℝ k (F a) x) m) →
      ContDiffOn ℝ (n : WithTop ℕ∞) (fun x => ∫ a, F a x ∂m) U := by
  induction n with
  | zero =>
    intro α _ m G _ _ F U g hU hF hg hbound hmeas
    rw [Nat.cast_zero, contDiffOn_zero]
    refine continuousOn_of_dominated (F := fun x a => F a x) (bound := g 0)
      (fun x hx => paramAesmIter0 F x (hmeas 0 x hx)) ?_ (hg 0) ?_
    · intro x hx
      filter_upwards [hbound 0] with a ha
      have := ha x hx
      rwa [norm_iteratedFDeriv_zero] at this
    · filter_upwards [hF] with a ha
      exact ha.continuousOn
  | succ n ih =>
    intro α _ m G _ _ F U g hU hF hg hbound hmeas
    have hIntx : ∀ x ∈ U, Integrable (fun a => F a x) m := fun x hx =>
      Integrable.mono' (hg 0) (paramAesmIter0 F x (hmeas 0 x hx))
        ((hbound 0).mono fun a ha => by
          have := ha x hx
          rwa [norm_iteratedFDeriv_zero] at this)
    have hbnd1 : ∀ᵐ a ∂m, ∀ x ∈ U, ‖fderiv ℝ (F a) x‖ ≤ g 1 a :=
      (hbound 1).mono fun a ha x hx => by
        rw [paramNormFDeriv1]
        exact ha x hx
    have hdiff1 : ∀ᵐ a ∂m, ∀ x ∈ U, HasFDerivAt (fun y => F a y) (fderiv ℝ (F a) x) x :=
      hF.mono fun a ha x hx =>
        ((ha.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hx)).hasFDerivAt
    have hmeasF' : ∀ x ∈ U, AEStronglyMeasurable (fun a => fderiv ℝ (F a) x) m := fun x hx =>
      paramAesmIter0 (fun a => fderiv ℝ (F a)) x (paramAesmIterFDeriv F 0 x (hmeas 1 x hx))
    have hHas : ∀ x ∈ U, HasFDerivAt (fun y => ∫ a, F a y ∂m) (∫ a, fderiv ℝ (F a) x ∂m) x :=
      fun x hx => hasFDerivAt_integral_of_dominated_of_fderiv_le
        (F := fun y a => F a y) (F' := fun y a => fderiv ℝ (F a) y) (bound := g 1)
        (hU.mem_nhds hx)
        (Filter.eventually_of_mem (hU.mem_nhds hx) fun y hy =>
          paramAesmIter0 F y (hmeas 0 y hy))
        (hIntx x hx) (hmeasF' x hx) hbnd1 (hg 1) hdiff1
    have hdiffU : DifferentiableOn ℝ (fun y => ∫ a, F a y ∂m) U :=
      fun x hx => (hHas x hx).differentiableAt.differentiableWithinAt
    have hder : ContDiffOn ℝ (n : WithTop ℕ∞) (fun x => ∫ a, fderiv ℝ (F a) x ∂m) U := by
      refine ih m (fun a => fderiv ℝ (F a)) U (fun k a => g (k + 1) a) hU ?_ ?_ ?_ ?_
      · exact hF.mono fun a ha => ((contDiffOn_infty_iff_fderiv_of_isOpen hU).1 ha).2
      · intro k
        exact hg (k + 1)
      · intro k
        exact (hbound (k + 1)).mono fun a ha x hx => by
          rw [norm_iteratedFDeriv_fderiv]
          exact ha x hx
      · intro k x hx
        exact paramAesmIterFDeriv F k x (hmeas (k + 1) x hx)
    rw [Nat.cast_succ]
    refine (contDiffOn_succ_iff_fderiv_of_isOpen hU).2 ⟨hdiffU, fun h => absurd h (by simp), ?_⟩
    exact hder.congr fun x hx => (hHas x hx).fderiv

theorem paramContDiffTop : ParamContDiffTop := by
  intro α _ m F U g hU _ hF hg hbound hmeas
  exact contDiffOn_infty.2 fun n => paramContDiffOn_nat n m F U g hU hF hg hbound hmeas

end UnforcedLeray.Short.PartIIIb.Concrete
