import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_1_org2_smooth_6

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

/-- Derivatives of the `τ`-family of derivatives: joint continuity passes to `fderivWithin`. -/
theorem deriv_cont_aux (E G : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (U : Set E) (hU : IsOpen U) (S : Set ℝ) (F : ℝ → E → G)
    (hF : ∀ i : ℕ, ContinuousOn (fun q : ℝ × E => iteratedFDerivWithin ℝ i (F q.1) U q.2) (S ×ˢ U))
    (i : ℕ) :
    ContinuousOn (fun q : ℝ × E =>
      iteratedFDerivWithin ℝ i (fun y => fderivWithin ℝ (F q.1) U y) U q.2) (S ×ˢ U) := by
  have h := (continuousMultilinearCurryRightEquiv' ℝ i E G).continuous.comp_continuousOn
    (hF (i + 1))
  refine h.congr (fun q hq => ?_)
  simp only [Function.comp_apply]
  rw [iteratedFDerivWithin_succ_eq_comp_right hU.uniqueDiffOn hq.2]
  simp

/-- Smoothness of `fderivWithin` of a smooth function on an open set. -/
theorem deriv_smooth_aux (E G : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (U : Set E) (hU : IsOpen U) (F : E → G) (hF : ContDiffOn ℝ ∞ F U) :
    ContDiffOn ℝ ∞ (fun y => fderivWithin ℝ F U y) U :=
  hF.fderivWithin hU.uniqueDiffOn (by simp)

/-- Bilinear Leibniz joint continuity, stated for all bilinear maps and all orders. -/
theorem leibniz_aux (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (U : Set E)
    (hU : IsOpen U) (S : Set ℝ) :
    ∀ (n : ℕ) {G1 G2 G3 : Type} [NormedAddCommGroup G1] [NormedSpace ℝ G1]
      [NormedAddCommGroup G2] [NormedSpace ℝ G2] [NormedAddCommGroup G3] [NormedSpace ℝ G3]
      (B : G1 →L[ℝ] G2 →L[ℝ] G3) (A : ℝ → E → G1) (C : ℝ → E → G2),
      (∀ i : ℕ, ContinuousOn (fun q : ℝ × E => iteratedFDerivWithin ℝ i (A q.1) U q.2) (S ×ˢ U)) →
      (∀ i : ℕ, ContinuousOn (fun q : ℝ × E => iteratedFDerivWithin ℝ i (C q.1) U q.2) (S ×ˢ U)) →
      (∀ τ ∈ S, ContDiffOn ℝ ∞ (A τ) U) → (∀ τ ∈ S, ContDiffOn ℝ ∞ (C τ) U) →
      ContinuousOn (fun q : ℝ × E =>
        iteratedFDerivWithin ℝ n (fun y => B (A q.1 y) (C q.1 y)) U q.2) (S ×ˢ U) := by
  intro n
  induction n with
  | zero =>
    intro G1 G2 G3 _ _ _ _ _ _ B A C hA hC _ _
    have hA0 := hA 0
    have hC0 := hC 0
    have hAv : ContinuousOn (fun q : ℝ × E => A q.1 q.2) (S ×ˢ U) := by
      refine ((continuousMultilinearCurryFin0 ℝ E G1).continuous.comp_continuousOn hA0).congr
        (fun q _ => ?_)
      simp [iteratedFDerivWithin_zero_eq_comp]
    have hCv : ContinuousOn (fun q : ℝ × E => C q.1 q.2) (S ×ˢ U) := by
      refine ((continuousMultilinearCurryFin0 ℝ E G2).continuous.comp_continuousOn hC0).congr
        (fun q _ => ?_)
      simp [iteratedFDerivWithin_zero_eq_comp]
    have hBv : ContinuousOn (fun q : ℝ × E => B (A q.1 q.2) (C q.1 q.2)) (S ×ˢ U) :=
      (ContinuousLinearMap.continuous₂ B).comp_continuousOn (hAv.prodMk hCv)
    refine ((continuousMultilinearCurryFin0 ℝ E G3).symm.continuous.comp_continuousOn hBv).congr
      (fun q _ => ?_)
    simp [iteratedFDerivWithin_zero_eq_comp]
  | succ n IH =>
    intro G1 G2 G3 _ _ _ _ _ _ B A C hA hC hAs hCs
    have hn : ((n : ℕ) : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
    have hone : (∞ : WithTop ℕ∞) ≠ 0 := by simp
    have hA' : ∀ i : ℕ, ContinuousOn
        (fun q : ℝ × E => iteratedFDerivWithin ℝ i (fun y => fderivWithin ℝ (A q.1) U y) U q.2)
        (S ×ˢ U) := fun i => deriv_cont_aux E G1 U hU S A hA i
    have hC' : ∀ i : ℕ, ContinuousOn
        (fun q : ℝ × E => iteratedFDerivWithin ℝ i (fun y => fderivWithin ℝ (C q.1) U y) U q.2)
        (S ×ˢ U) := fun i => deriv_cont_aux E G2 U hU S C hC i
    have hAs' : ∀ τ ∈ S, ContDiffOn ℝ ∞ (fun y => fderivWithin ℝ (A τ) U y) U :=
      fun τ hτ => deriv_smooth_aux E G1 U hU (A τ) (hAs τ hτ)
    have hCs' : ∀ τ ∈ S, ContDiffOn ℝ ∞ (fun y => fderivWithin ℝ (C τ) U y) U :=
      fun τ hτ => deriv_smooth_aux E G2 U hU (C τ) (hCs τ hτ)
    have hS1 : ∀ τ ∈ S, ContDiffOn ℝ ∞
        (fun y => (B.precompR E) (A τ y) (fderivWithin ℝ (C τ) U y)) U := fun τ hτ =>
      (B.precompR E).isBoundedBilinearMap.contDiff.comp₂_contDiffOn (hAs τ hτ) (hCs' τ hτ)
    have hS2 : ∀ τ ∈ S, ContDiffOn ℝ ∞
        (fun y => (B.precompL E) (fderivWithin ℝ (A τ) U y) (C τ y)) U := fun τ hτ =>
      (B.precompL E).isBoundedBilinearMap.contDiff.comp₂_contDiffOn (hAs' τ hτ) (hCs τ hτ)
    have hP1 := IH (B.precompR E) A (fun τ y => fderivWithin ℝ (C τ) U y) hA hC' hAs hCs'
    have hP2 := IH (B.precompL E) (fun τ y => fderivWithin ℝ (A τ) U y) C hA' hC hAs' hCs
    have hpt : ∀ q ∈ S ×ˢ U,
        iteratedFDerivWithin ℝ n (fun y => fderivWithin ℝ (fun y => B (A q.1 y) (C q.1 y)) U y) U
            q.2 =
          iteratedFDerivWithin ℝ n (fun y => (B.precompR E) (A q.1 y)
              (fderivWithin ℝ (C q.1) U y)) U q.2 +
          iteratedFDerivWithin ℝ n (fun y => (B.precompL E) (fderivWithin ℝ (A q.1) U y)
              (C q.1 y)) U q.2 := by
      intro q hq
      have hτ : q.1 ∈ S := hq.1
      have hx : q.2 ∈ U := hq.2
      have hEq : EqOn (fun y => fderivWithin ℝ (fun y => B (A q.1 y) (C q.1 y)) U y)
          (fun y => (B.precompR E) (A q.1 y) (fderivWithin ℝ (C q.1) U y) +
            (B.precompL E) (fderivWithin ℝ (A q.1) U y) (C q.1 y)) U := by
        intro y hy
        exact B.fderivWithin_of_bilinear
          (((hAs q.1 hτ).differentiableOn hone) y hy)
          (((hCs q.1 hτ).differentiableOn hone) y hy)
          (hU.uniqueDiffOn y hy)
      rw [iteratedFDerivWithin_congr hEq hx n,
        fun_iteratedFDerivWithin_add_apply
          (((hS1 q.1 hτ).of_le hn).contDiffWithinAt hx)
          (((hS2 q.1 hτ).of_le hn).contDiffWithinAt hx) hU.uniqueDiffOn hx]
    have hsum : ContinuousOn (fun q : ℝ × E =>
        iteratedFDerivWithin ℝ n (fun y => fderivWithin ℝ (fun y => B (A q.1 y) (C q.1 y)) U y)
          U q.2) (S ×ˢ U) :=
      (hP1.add hP2).congr (fun q hq => hpt q hq)
    have hfinal := (continuousMultilinearCurryRightEquiv' ℝ n E G3).symm.continuous.comp_continuousOn
      hsum
    refine hfinal.congr (fun q hq => ?_)
    simp only [Function.comp_apply]
    rw [iteratedFDerivWithin_succ_eq_comp_right hU.uniqueDiffOn hq.2]
    simp

/-- **Leibniz, joint continuity.** -/
theorem prodJointCont : ProdJointCont := by
  intro A B S U hU hA hB hAs hBs n
  have hA' : ∀ i : ℕ, ContinuousOn
      (fun q : ℝ × (ℝ × (ℝ × ℝ)) => iteratedFDerivWithin ℝ i (A q.1) U q.2) (S ×ˢ U) :=
    fun i => (hA i).congr (fun q hq => iteratedFDerivWithin_of_isOpen i hU hq.2)
  have hB' : ∀ i : ℕ, ContinuousOn
      (fun q : ℝ × (ℝ × (ℝ × ℝ)) => iteratedFDerivWithin ℝ i (B q.1) U q.2) (S ×ˢ U) :=
    fun i => (hB i).congr (fun q hq => iteratedFDerivWithin_of_isOpen i hU hq.2)
  have key := leibniz_aux (ℝ × (ℝ × ℝ)) U hU S n (ContinuousLinearMap.mul ℝ ℂ) A B hA' hB' hAs hBs
  have key2 : ContinuousOn (fun q : ℝ × (ℝ × (ℝ × ℝ)) =>
      iteratedFDerivWithin ℝ n (fun y => A q.1 y * B q.1 y) U q.2) (S ×ˢ U) := by
    simpa using key
  exact key2.congr (fun q hq => (iteratedFDerivWithin_of_isOpen n hU hq.2).symm)

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
