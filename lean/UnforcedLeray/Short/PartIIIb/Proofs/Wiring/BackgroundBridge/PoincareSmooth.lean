import UnforcedLeray.Short.PartIIIb.Proofs.Wiring.Sub.PartIIIb_IIIb_D5_bridge_1
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Parametric `C^∞` regularity of the radial Poincaré potential (`PartIII-b:IIIb-D5/bridge/1`)

Source of record: `the November 2 reference manuscript`, lines 4139-4141.

Proves `ShortBgExactProfileAux.PoincareIntervalSmooth`: when `G : ℝ → SpatialField` is jointly
`C^∞` on `ℝ × Space`, the spacetime radial Poincaré potential
`(τ, y) ↦ ∫ t in (0 : ℝ)..1, ⟪G(τ, t • y), y⟫` is `C^∞` on `ℝ × Space`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal ContDiff Interval

namespace UnforcedLeray.Short.PartIIIb.Concrete.Wiring

open UnforcedLeray

private theorem contDiff_intervalIntegral_zero_one :
    ∀ (n : ℕ) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      {F : (ℝ × Space) × ℝ → E},
      ContDiff ℝ n F →
      ContDiff ℝ n (fun x : ℝ × Space => ∫ t in (0 : ℝ)..1, F (x, t))
  | 0, E, _, _, F, hF => by
    rw [Nat.cast_zero, contDiff_zero]
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun (x : ℝ × Space) (t : ℝ) => F (x, t)) hF.continuous 0 1
  | n + 1, E, _, _, F, hF => by
    have hF_succ : ContDiff ℝ ((n : WithTop ℕ∞) + 1) F := by
      simpa [Nat.cast_add, Nat.cast_one] using hF
    have hfderiv : ContDiff ℝ n (fderiv ℝ F) :=
      (contDiff_succ_iff_fderiv.mp hF_succ).2.2
    let F' : (ℝ × Space) × ℝ → ((ℝ × Space) →L[ℝ] E) :=
      fun p => (fderiv ℝ F p).comp (ContinuousLinearMap.inl ℝ (ℝ × Space) ℝ)
    have hF' : ContDiff ℝ n F' := hfderiv.clm_comp contDiff_const
    have hhas : ∀ x₀ : ℝ × Space,
        HasFDerivAt (fun x : ℝ × Space => ∫ t in (0 : ℝ)..1, F (x, t))
          (∫ t in (0 : ℝ)..1, F' (x₀, t)) x₀ := by
      intro x₀
      let s : Set (ℝ × Space) := Metric.closedBall x₀ 1
      have hs : s ∈ 𝓝 x₀ := Metric.closedBall_mem_nhds x₀ one_pos
      have hK : IsCompact (s ×ˢ Set.uIcc (0 : ℝ) 1) :=
        (isCompact_closedBall x₀ 1).prod isCompact_uIcc
      obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hF'.continuous.continuousOn
      have hF_diff : Differentiable ℝ F :=
        hF_succ.differentiable (by simp)
      refine intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
        (F := fun x t => F (x, t)) (F' := fun x t => F' (x, t)) (bound := fun _ => C)
        hs ?_ ?_ ?_ ?_ intervalIntegrable_const ?_
      · exact Eventually.of_forall fun x =>
          (hF.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
      · exact (hF.continuous.comp (continuous_const.prodMk continuous_id)).intervalIntegrable 0 1
      · exact (hF'.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
      · exact Eventually.of_forall fun t ht x hx =>
          hC (x, t) ⟨hx, Set.uIoc_subset_uIcc ht⟩
      · refine Eventually.of_forall fun t _ x _ => ?_
        have h1 : HasFDerivAt F (fderiv ℝ F (x, t)) (x, t) :=
          (hF_diff (x, t)).hasFDerivAt
        have h2 : HasFDerivAt (fun z : ℝ × Space => (z, t))
            (ContinuousLinearMap.inl ℝ (ℝ × Space) ℝ) x :=
          hasFDerivAt_prodMk_left x t
        exact h1.comp x h2
    have hdiff : Differentiable ℝ (fun x : ℝ × Space => ∫ t in (0 : ℝ)..1, F (x, t)) :=
      fun x₀ => (hhas x₀).differentiableAt
    have hfderiv_eq : fderiv ℝ (fun x : ℝ × Space => ∫ t in (0 : ℝ)..1, F (x, t)) =
        fun x₀ : ℝ × Space => ∫ t in (0 : ℝ)..1, F' (x₀, t) :=
      funext fun x₀ => (hhas x₀).fderiv
    have ih : ContDiff ℝ n (fun x₀ : ℝ × Space => ∫ t in (0 : ℝ)..1, F' (x₀, t)) :=
      contDiff_intervalIntegral_zero_one n hF'
    have h_out : ContDiff ℝ ((n : WithTop ℕ∞) + 1)
        (fun x : ℝ × Space => ∫ t in (0 : ℝ)..1, F (x, t)) := by
      rw [contDiff_succ_iff_fderiv]
      refine ⟨hdiff, ?_, ?_⟩
      · intro hω
        exact absurd hω (by simp)
      · rw [hfderiv_eq]
        exact ih
    simpa [Nat.cast_add, Nat.cast_one] using h_out

/-- **Parametric `C^∞` smoothness of `radialPoincare`** (`PartIII-b:IIIb-D5/bridge/1`). -/
theorem poincareIntervalSmooth_proof :
    UnforcedLeray.Short.PartIIIb.Concrete.Wiring.ShortBgExactProfileAux.PoincareIntervalSmooth := by
  intro G hG
  let F : (ℝ × Space) × ℝ → ℝ := fun p => inner ℝ (G p.1.1 (p.2 • p.1.2)) p.1.2
  have harg : ContDiff ℝ ∞ (fun p : (ℝ × Space) × ℝ => (p.1.1, p.2 • p.1.2)) :=
    (contDiff_fst.comp contDiff_fst).prodMk
      (contDiff_snd.smul (contDiff_snd.comp contDiff_fst))
  have hF : ContDiff ℝ ∞ F :=
    (hG.comp harg).inner ℝ (contDiff_snd.comp contDiff_fst)
  change ContDiff ℝ ∞ (fun x : ℝ × Space => ∫ t in (0 : ℝ)..1, F (x, t))
  rw [contDiff_infty]
  intro n
  exact contDiff_intervalIntegral_zero_one n (hF.of_le (by simp))

end UnforcedLeray.Short.PartIIIb.Concrete.Wiring
