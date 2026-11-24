import UnforcedLeray.Short.PartI.Sub.PartI_C07_1_1
import UnforcedLeray.Short.Spine.Proofs.CanonicalBranch.Mild.ExpJoint

/-!
# One-step Gronwall estimate for the full Duhamel equation (helper for `fullMildUnique`)

For `b ≤ θ ≤ θ'` with `0 < b`, and `V` solving `FullMildEq b V`, the difference of `V θ` and
`S θ θ' (V θ')` is the Duhamel integral of `L₀` applied to the difference `V - S(·, θ')V(θ')`
over `[θ, θ']`; hence its norm is bounded by `‖L₀‖ ∫_θ^{θ'} ‖V s - S s θ' (V θ')‖ ds`.
Source `the November 2 reference manuscript` lines 1094-1125.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology

namespace UnforcedLeray.Short.PartI.FullMildUniqueHelp

open UnforcedLeray.Short.PartI

theorem norm_freeU_apply_le' (t s : ℝ) (y : UnforcedLeray.B0010.XG) :
    ‖UnforcedLeray.Cons.G3b.freeU t s y‖ ≤ ‖y‖ := by
  have h1 := (UnforcedLeray.Cons.G3b.freeU t s).le_opNorm y
  have h2 := UnforcedLeray.Cons.G3b.norm_freeU_le t s
  have h3 : ‖UnforcedLeray.Cons.G3b.freeU t s‖ * ‖y‖ ≤ 1 * ‖y‖ :=
    mul_le_mul_of_nonneg_right h2 (norm_nonneg y)
  linarith

theorem key_norm_le (b : ℝ) (hb : 0 < b) (V : ℝ → UnforcedLeray.B0010.XG)
    (hV : ContinuousOn V (Ici b)) (hE : FullMildEq b V) {θ θ' : ℝ} (hbθ : b ≤ θ)
    (hθθ' : θ ≤ θ') :
    ‖V θ - UnforcedLeray.Cons.G3b.S θ θ' (V θ')‖ ≤
      ‖UnforcedLeray.B0012.L0‖ *
        ∫ s in θ..θ', ‖V s - UnforcedLeray.Cons.G3b.S s θ' (V θ')‖ := by
  have hθ0 : 0 < θ := lt_of_lt_of_le hb hbθ
  have h1 : V θ = UnforcedLeray.B0123.expD (Real.log θ' - Real.log θ) (V θ') +
      ∫ u in (-θ')..(-θ), UnforcedLeray.Cons.G3b.freeU (-θ) u
        (UnforcedLeray.B0012.L0 (V (-u))) := hE θ θ' hbθ hθθ'
  have h2 := UnforcedLeray.Cons.G3b.S_mild hθ0 hθθ' (V θ')
  have hmapsI : MapsTo (fun u : ℝ => -u) (Icc (-θ') (-θ)) (Ici b) := by
    intro u hu
    simp only [mem_Ici]
    linarith [hu.2]
  have hmapsS : MapsTo (fun u : ℝ => -u) (Icc (-θ') (-θ)) (Icc b θ') := by
    intro u hu
    simp only [mem_Icc]
    constructor <;> linarith [hu.1, hu.2]
  have hVc : ContinuousOn (fun u : ℝ => V (-u)) (Icc (-θ') (-θ)) :=
    hV.comp continuous_neg.continuousOn hmapsI
  have hSc : ContinuousOn (fun u : ℝ => UnforcedLeray.Cons.G3b.S (-u) θ' (V θ'))
      (Icc (-θ') (-θ)) :=
    (UnforcedLeray.Cons.G3b.continuousOn_S_left (θ₁ := θ') hb (V θ')).comp
      continuous_neg.continuousOn hmapsS
  have hLc : ContinuousOn (fun u : ℝ => UnforcedLeray.B0012.L0 (V (-u)))
      (Icc (-θ') (-θ)) :=
    UnforcedLeray.B0012.L0.continuous.comp_continuousOn hVc
  have hlog : ContinuousOn (fun u : ℝ => Real.log (-u) - Real.log (-(-θ)))
      (Icc (-θ') (-θ)) := by
    apply ContinuousOn.sub
    · apply ContinuousOn.log continuous_neg.continuousOn
      intro u hu
      have : 0 < -u := by linarith [hu.2]
      exact this.ne'
    · exact continuousOn_const
  have hint1 : IntervalIntegrable (fun u : ℝ => UnforcedLeray.Cons.G3b.freeU (-θ) u
      (UnforcedLeray.B0012.L0 (V (-u)))) volume (-θ') (-θ) := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le (by linarith)]
    exact UnforcedLeray.Short.Spine.CanonicalMild.continuousOn_expD_pair hlog hLc
  have hint2 := UnforcedLeray.Cons.G3b.intervalIntegrable_S_mild_integrand hθ0 hθθ' (V θ')
  have hsub : V θ - UnforcedLeray.Cons.G3b.S θ θ' (V θ') =
      ∫ u in (-θ')..(-θ), UnforcedLeray.Cons.G3b.freeU (-θ) u
        (UnforcedLeray.B0012.L0 (V (-u) - UnforcedLeray.Cons.G3b.S (-u) θ' (V θ'))) := by
    rw [h1, h2, add_sub_add_left_eq_sub, ← intervalIntegral.integral_sub hint1 hint2]
    refine intervalIntegral.integral_congr fun u _ => ?_
    simp only [map_sub]
  rw [hsub]
  have hg : ContinuousOn (fun u : ℝ => ‖UnforcedLeray.B0012.L0‖ *
      ‖V (-u) - UnforcedLeray.Cons.G3b.S (-u) θ' (V θ')‖) (Icc (-θ') (-θ)) :=
    continuousOn_const.mul ((hVc.sub hSc).norm)
  calc ‖∫ u in (-θ')..(-θ), UnforcedLeray.Cons.G3b.freeU (-θ) u
        (UnforcedLeray.B0012.L0 (V (-u) - UnforcedLeray.Cons.G3b.S (-u) θ' (V θ')))‖
      ≤ ∫ u in (-θ')..(-θ), ‖UnforcedLeray.B0012.L0‖ *
          ‖V (-u) - UnforcedLeray.Cons.G3b.S (-u) θ' (V θ')‖ := by
        apply intervalIntegral.norm_integral_le_of_norm_le (by linarith)
        · apply Filter.Eventually.of_forall
          intro u _
          refine (norm_freeU_apply_le' _ _ _).trans ?_
          exact (UnforcedLeray.B0012.L0.le_opNorm _)
        · apply ContinuousOn.intervalIntegrable
          rw [uIcc_of_le (by linarith)]
          exact hg
    _ = ‖UnforcedLeray.B0012.L0‖ *
          ∫ s in θ..θ', ‖V s - UnforcedLeray.Cons.G3b.S s θ' (V θ')‖ := by
        rw [intervalIntegral.integral_const_mul]
        congr 1
        have h3 := intervalIntegral.integral_comp_neg
          (a := -θ') (b := -θ) (f := fun s => ‖V s - UnforcedLeray.Cons.G3b.S s θ' (V θ')‖)
        simp only [neg_neg] at h3
        exact h3

end UnforcedLeray.Short.PartI.FullMildUniqueHelp
