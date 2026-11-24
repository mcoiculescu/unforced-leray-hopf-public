import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_3_2_11_2_2_2.ParamTop

/-!
# Norm bound for the derivatives of a parametric integral (helper of `B4b`, source 4177-4179)

If `F a` is `C^∞` on an open `U` with `‖D^k F a (x)‖ ≤ g k a` (integrable), then
`‖D^n (∫ F a) (x)‖ ≤ ∫ g n` on `U`.  Same induction as `paramContDiffOn_nat`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem paramIterBound {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (n : ℕ) :
    ∀ {α : Type} [MeasurableSpace α] (m : Measure α) {G : Type} [NormedAddCommGroup G]
      [NormedSpace ℝ G] (F : α → E → G) (U : Set E) (g : ℕ → α → ℝ),
      IsOpen U → (∀ᵐ a ∂m, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (F a) U) →
      (∀ k, Integrable (g k) m) →
      (∀ k, ∀ᵐ a ∂m, ∀ x ∈ U, ‖iteratedFDeriv ℝ k (F a) x‖ ≤ g k a) →
      (∀ k, ∀ x ∈ U, AEStronglyMeasurable (fun a => iteratedFDeriv ℝ k (F a) x) m) →
      ∀ x ∈ U, ‖iteratedFDeriv ℝ n (fun y => ∫ a, F a y ∂m) x‖ ≤ ∫ a, g n a ∂m := by
  induction n with
  | zero =>
    intro α _ m G _ _ F U g hU hF hg hbound hmeas x hx
    rw [norm_iteratedFDeriv_zero]
    refine norm_integral_le_of_norm_le (hg 0) ?_
    filter_upwards [hbound 0] with a ha
    have := ha x hx
    rwa [norm_iteratedFDeriv_zero] at this
  | succ n ih =>
    intro α _ m G _ _ F U g hU hF hg hbound hmeas x hx
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
    have hEq : fderiv ℝ (fun y => ∫ a, F a y ∂m) =ᶠ[𝓝 x]
        fun y => ∫ a, fderiv ℝ (F a) y ∂m := by
      filter_upwards [hU.mem_nhds hx] with y hy using (hHas y hy).fderiv
    have hIH := ih m (fun a => fderiv ℝ (F a)) U (fun k a => g (k + 1) a) hU
      (hF.mono fun a ha => ((contDiffOn_infty_iff_fderiv_of_isOpen hU).1 ha).2)
      (fun k => hg (k + 1))
      (fun k => (hbound (k + 1)).mono fun a ha x hx => by
        rw [norm_iteratedFDeriv_fderiv]
        exact ha x hx)
      (fun k x hx => paramAesmIterFDeriv F k x (hmeas (k + 1) x hx)) x hx
    rw [← norm_iteratedFDeriv_fderiv, (hEq.iteratedFDeriv ℝ n).eq_of_nhds]
    exact hIH

end UnforcedLeray.Short.PartIIIb.Concrete
