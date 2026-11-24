import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GELinSub.Props

/-!
# `GELinConvTPhaseTest`: `convT V Φ` is a phase test (source 2525-2533)

Task `PartIII-b:C/ward/12/3/1/2/6/4`.  `convT V Φ = gradUT V Φ - advT (realC V) Φ` with
`(gradUT V Φ)ₖ = ∑ᵢ Φᵢ ∂ₖVᵢ` and `advT u Φ = ∑ₖ uₖ ∂ₖΦ`.  For smooth periodic `V` and a phase
test `Φ`: the components are smooth (products and sums of smooth functions, with the spatial
derivative of the jointly smooth `V` smooth by the chain rule), periodicity is inherited from
`V` and `Φ` (and their `y`-derivatives), and the support is contained in that of `Φ` and of its
`y`-derivatives.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace MeasureTheory Set
open scoped ContDiff
open UnforcedLeray.Cons.C03.Concrete (convT gradUT advT)

/-- The spatial partial derivative of a jointly smooth field is jointly smooth. -/
theorem gELinConvT_partial {F : ℝ × UnforcedLeray.Space → UnforcedLeray.Space}
    (hF : ContDiff ℝ ∞ F) (j : Fin 3) :
    ContDiff ℝ ∞ (fun x : ℝ × UnforcedLeray.Space =>
      fderiv ℝ (fun y => F (x.1, y)) x.2 (EuclideanSpace.single j 1)) := by
  have key : ∀ x : ℝ × UnforcedLeray.Space,
      fderiv ℝ (fun y => F (x.1, y)) x.2 (EuclideanSpace.single j 1) =
        fderiv ℝ F x (0, EuclideanSpace.single j 1) := by
    intro x
    have hFd : HasFDerivAt F (fderiv ℝ F x) (x.1, x.2) :=
      (hF.differentiable (by simp) x).hasFDerivAt
    have hg : HasFDerivAt (fun y : UnforcedLeray.Space => ((x.1, y) : ℝ × UnforcedLeray.Space))
        (ContinuousLinearMap.inr ℝ ℝ UnforcedLeray.Space) x.2 :=
      hasFDerivAt_prodMk_right x.1 x.2
    have hc := hFd.comp x.2 hg
    have hfd : fderiv ℝ (fun y => F (x.1, y)) x.2 =
        (fderiv ℝ F x).comp (ContinuousLinearMap.inr ℝ ℝ UnforcedLeray.Space) := hc.fderiv
    rw [hfd]
    rfl
  have hd : ContDiff ℝ ∞ (fderiv ℝ F) := hF.fderiv_right (m := ∞) (by simp)
  have hfun : (fun x : ℝ × UnforcedLeray.Space =>
      fderiv ℝ (fun y => F (x.1, y)) x.2 (EuclideanSpace.single j 1)) =
      fun x => fderiv ℝ F x (0, EuclideanSpace.single j 1) := funext key
  rw [hfun]
  exact hd.clm_apply contDiff_const

/-- Real-valued smooth functions give smooth complex-valued functions. -/
theorem gELinConvT_ofReal {f : ℝ × UnforcedLeray.Space → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (fun x => ((f x : ℝ) : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp hf

theorem gELinConvTPhaseTest : GELinConvTPhaseTest := by
  intro P V hV Φ hΦ
  obtain ⟨hVc, hVp⟩ := hV
  have hF : ContDiff ℝ ∞ (fun x : ℝ × UnforcedLeray.Space => V x.1 x.2) := hVc
  refine
    { smooth := ?_
      periodic := ?_
      bounded_support := ?_ }
  · refine (contDiff_piLp 2).2 (fun i => ?_)
    show ContDiff ℝ ∞ (fun x : ℝ × UnforcedLeray.Space => convT V Φ x i)
    have hcomp : (fun x : ℝ × UnforcedLeray.Space => convT V Φ x i) =
        fun x => (∑ l : Fin 3, Φ x l *
            ((fderiv ℝ (V x.1) x.2 (EuclideanSpace.single i 1) l : ℝ) : ℂ)) -
          ∑ k : Fin 3, ((V x.1 x.2 k : ℝ) : ℂ) * PhaseSpace.dy k Φ x i := by
      funext x
      simp [convT, gradUT, advT, UnforcedLeray.B0412.realC_apply]
    rw [hcomp]
    refine ContDiff.sub ?_ ?_
    · refine ContDiff.sum (fun l _ => ?_)
      exact ((contDiff_piLp 2).1 hΦ.smooth l).mul
        (gELinConvT_ofReal ((contDiff_piLp 2).1 (gELinConvT_partial hF i) l))
    · refine ContDiff.sum (fun k _ => ?_)
      exact (gELinConvT_ofReal ((contDiff_piLp 2).1 hF k)).mul
        ((contDiff_piLp 2).1 (hΦ.dy k).smooth i)
  · intro τ y
    have hVτ : V (τ + P) = V τ := funext (hVp τ)
    have h1 : ∀ k, PhaseSpace.dy k Φ (τ + P, y) = PhaseSpace.dy k Φ (τ, y) :=
      fun k => (hΦ.dy k).periodic τ y
    have h2 : Φ (τ + P, y) = Φ (τ, y) := hΦ.periodic τ y
    simp only [convT, gradUT, advT, UnforcedLeray.B0412.realC, hVτ, h1, h2]
  · obtain ⟨R0, hR0⟩ := hΦ.bounded_support
    have hdy : ∀ k : Fin 3, ∃ R : ℝ, ∀ τ y, R < ‖y‖ → PhaseSpace.dy k Φ (τ, y) = 0 :=
      fun k => (hΦ.dy k).bounded_support
    choose Rk hRk using hdy
    refine ⟨max R0 (∑ k, |Rk k|), fun τ y hy => ?_⟩
    have hy0 : R0 < ‖y‖ := lt_of_le_of_lt (le_max_left _ _) hy
    have hy1 : ∑ k, |Rk k| < ‖y‖ := lt_of_le_of_lt (le_max_right _ _) hy
    have hΦz : Φ (τ, y) = 0 := hR0 τ y hy0
    have hdz : ∀ k, PhaseSpace.dy k Φ (τ, y) = 0 := fun k =>
      hRk k τ y (lt_of_le_of_lt
        (le_trans (le_abs_self _)
          (Finset.single_le_sum (fun i _ => abs_nonneg (Rk i)) (Finset.mem_univ k))) hy1)
    simp [convT, gradUT, advT, hΦz, hdz] <;> rfl

end UnforcedLeray.Short.PartIIIb.Concrete
