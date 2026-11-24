import UnforcedLeray.Short.PartIIb.Sub.FlatInverseDesign
import UnforcedLeray.Short.PartIIb.Tasks.GraphTransform

/-!
# `PartII-b:F3` (`InvariantProjections.lean`): Discrete invariant projections from `BlockDichotomy`

Source of record: `the November 2 reference manuscript` (SP), lines 2172–2188
(display `short-bg:graphs` at line 2175).

Proves `dichotomyProjections_of : BlockDichotomy → DichotomyProjections` by running the forward and
backward graph recursions (`graphTransformLemma_proof`, `PartII-b:T06`) on the ball of radius
`r = 1/2` with off-diagonal tolerance `η = 1/2`. Because `BlockFactorizationData.Valid` provides
strict margins `‖a_n⁻¹‖ ≤ ½ e^{-b'L}` and `‖d_n‖ ≤ ½ e^{a'L}`, we have `A ≤ 1/2` and `A D ≤ 1/4`,
so the ball-preservation condition `A η (1 + r²) ≤ r (1 - A D)` holds with `5/16 ≤ 3/8`, the
unstable inverse satisfies `‖M_n‖ ≤ A / (1 - A η r) ≤ e^{-b'L}`, and the center block
`D_n = d_n + c_n ζ_n` satisfies `‖D_n‖ ≤ D + η r ≤ e^{a'L}`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-! ## 1. Numerical bounds for the strict-margin dichotomy parameters (`r = 1/2`, `η = 1/2`) -/

private theorem exp_neg_mul_le_one {b' L : ℝ} (hb' : 0 < b') (hL : 0 ≤ L) :
    Real.exp (-b' * L) ≤ 1 := by
  apply Real.exp_le_one_iff.2
  nlinarith

private theorem one_le_exp_mul {a' L : ℝ} (ha' : 0 < a') (hL : 0 ≤ L) :
    1 ≤ Real.exp (a' * L) := by
  apply Real.one_le_exp
  nlinarith

private theorem strict_margin_A_le_half {b' L : ℝ} (hb' : 0 < b') (hL : 0 ≤ L) :
    (1 / 2 : ℝ) * Real.exp (-b' * L) ≤ 1 / 2 := by
  have h := exp_neg_mul_le_one hb' hL
  linarith

private theorem strict_margin_AD_le_quarter {a' b' L : ℝ} (hab' : a' < b') (hL : 0 ≤ L) :
    ((1 / 2 : ℝ) * Real.exp (-b' * L)) * ((1 / 2 : ℝ) * Real.exp (a' * L)) ≤ 1 / 4 := by
  have hexp : Real.exp (-b' * L) * Real.exp (a' * L) ≤ 1 := by
    rw [← Real.exp_add]
    apply Real.exp_le_one_iff.2
    nlinarith
  calc ((1 / 2 : ℝ) * Real.exp (-b' * L)) * ((1 / 2 : ℝ) * Real.exp (a' * L))
      = (1 / 4 : ℝ) * (Real.exp (-b' * L) * Real.exp (a' * L)) := by ring
    _ ≤ (1 / 4 : ℝ) * 1 := mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = 1 / 4 := mul_one _

private theorem strict_margin_Arη_lt_one {b' L : ℝ} (hb' : 0 < b') (hL : 0 ≤ L) :
    ((1 / 2 : ℝ) * Real.exp (-b' * L)) * (1 / 2 : ℝ) * (1 / 2 : ℝ) < 1 := by
  have hA := strict_margin_A_le_half hb' hL
  linarith

private theorem strict_margin_ball_cond {a' b' L : ℝ}
    (ha' : 0 < a') (hab' : a' < b') (hL : 0 ≤ L) :
    ((1 / 2 : ℝ) * Real.exp (-b' * L)) * (1 / 2 : ℝ) * (1 + (1 / 2 : ℝ) ^ 2) ≤
      (1 / 2 : ℝ) *
        (1 - ((1 / 2 : ℝ) * Real.exp (-b' * L)) * ((1 / 2 : ℝ) * Real.exp (a' * L))) := by
  have hb' : 0 < b' := lt_trans ha' hab'
  have hA := strict_margin_A_le_half hb' hL
  have hAD := strict_margin_AD_le_quarter hab' hL
  linarith

private theorem strict_margin_inv_bound {b' L : ℝ} (hb' : 0 < b') (hL : 0 ≤ L) :
    ((1 / 2 : ℝ) * Real.exp (-b' * L)) /
        (1 - ((1 / 2 : ℝ) * Real.exp (-b' * L)) * (1 / 2 : ℝ) * (1 / 2 : ℝ)) ≤
      Real.exp (-b' * L) := by
  have hA := strict_margin_A_le_half hb' hL
  have hA_pos : 0 < Real.exp (-b' * L) := Real.exp_pos _
  have hden : (1 / 2 : ℝ) ≤ 1 - ((1 / 2 : ℝ) * Real.exp (-b' * L)) * (1 / 2 : ℝ) * (1 / 2 : ℝ) := by
    linarith
  have hden_pos :
      0 < 1 - ((1 / 2 : ℝ) * Real.exp (-b' * L)) * (1 / 2 : ℝ) * (1 / 2 : ℝ) := by linarith
  rw [div_le_iff₀ hden_pos]
  nlinarith

private theorem strict_margin_center_bound {a' L : ℝ} (ha' : 0 < a') (hL : 0 ≤ L) :
    (1 / 2 : ℝ) * Real.exp (a' * L) + (1 / 2 : ℝ) * (1 / 2 : ℝ) ≤ Real.exp (a' * L) := by
  have hexp := one_le_exp_mul ha' hL
  linarith

/-! ## 2. Abstract graph embeddings, projections, and intertwining over generic Banach spaces -/

section AbstractGraph

variable {X E F : Type}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

private theorem exists_graph_W_gen
    (ξ : E →L[ℝ] F) (ζ : F →L[ℝ] E) (hξ : ‖ξ‖ ≤ 1 / 2) (hζ : ‖ζ‖ ≤ 1 / 2) :
    ∃ W : E →L[ℝ] E,
      W * (1 - ζ.comp ξ) = 1 ∧ (1 - ζ.comp ξ) * W = 1 ∧ ‖W‖ ≤ 2 := by
  have h1_norm : ‖(1 : E →L[ℝ] E)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  have hnegζ : ‖-ζ‖ ≤ 1 / 2 := by rw [norm_neg]; exact hζ
  obtain ⟨W, hW1, hW2, hWn⟩ :=
    exists_inverse_add_comp (1 : E →L[ℝ] E) (1 : E →L[ℝ] E) (-ζ) ξ
      (mul_one 1) (mul_one 1) h1_norm hnegζ hξ (by positivity) (by positivity) (by norm_num)
  have hsub : (1 : E →L[ℝ] E) + (-ζ).comp ξ = 1 - ζ.comp ξ := by
    rw [ContinuousLinearMap.neg_comp, sub_eq_add_neg]
  rw [hsub] at hW1 hW2
  refine ⟨W, hW1, hW2, ?_⟩
  linarith

private def genEmbedU (ι : E →L[ℝ] X) (κ : F →L[ℝ] X) (ξ : E →L[ℝ] F) : E →L[ℝ] X :=
  ι + κ.comp ξ

private def genCoordU (π : X →L[ℝ] E) (ρ : X →L[ℝ] F) (ζ : F →L[ℝ] E) (W : E →L[ℝ] E) :
    X →L[ℝ] E :=
  W.comp (π - ζ.comp ρ)

private def genProjU (ι : E →L[ℝ] X) (π : X →L[ℝ] E) (κ : F →L[ℝ] X) (ρ : X →L[ℝ] F)
    (ξ : E →L[ℝ] F) (ζ : F →L[ℝ] E) (W : E →L[ℝ] E) : X →L[ℝ] X :=
  (genEmbedU ι κ ξ).comp (genCoordU π ρ ζ W)

private def genEmbedC (ι : E →L[ℝ] X) (κ : F →L[ℝ] X) (ζ : F →L[ℝ] E) : F →L[ℝ] X :=
  κ + ι.comp ζ

private def genCoordC (ρ : X →L[ℝ] F) (ξ : E →L[ℝ] F) (Pu : X →L[ℝ] E) : X →L[ℝ] F :=
  ρ - ξ.comp Pu

private theorem genCoordU_comp_genEmbedU
    (ι : E →L[ℝ] X) (π : X →L[ℝ] E) (κ : F →L[ℝ] X) (ρ : X →L[ℝ] F)
    (ξ : E →L[ℝ] F) (ζ : F →L[ℝ] E) (W : E →L[ℝ] E)
    (hπι : π.comp ι = ContinuousLinearMap.id ℝ E)
    (hρκ : ρ.comp κ = ContinuousLinearMap.id ℝ F)
    (hπκ : π.comp κ = 0) (hρι : ρ.comp ι = 0)
    (hW : W * (1 - ζ.comp ξ) = 1) :
    (genCoordU π ρ ζ W).comp (genEmbedU ι κ ξ) = ContinuousLinearMap.id ℝ E := by
  have h1 : (π - ζ.comp ρ).comp (ι + κ.comp ξ) = 1 - ζ.comp ξ := by
    apply ContinuousLinearMap.ext
    intro w
    have hπι_w := DFunLike.congr_fun hπι w
    have hπκ_w := DFunLike.congr_fun hπκ (ξ w)
    have hρι_w := DFunLike.congr_fun hρι w
    have hρκ_w := DFunLike.congr_fun hρκ (ξ w)
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
      zero_apply] at hπι_w hπκ_w hρι_w hρκ_w
    change (π (ι w + κ (ξ w))) - ζ (ρ (ι w + κ (ξ w))) = w - ζ (ξ w)
    rw [map_add, map_add, hπι_w, hπκ_w, hρι_w, hρκ_w, add_zero, zero_add]
  unfold genCoordU genEmbedU
  rw [ContinuousLinearMap.comp_assoc, h1]
  exact hW

private theorem genCoordU_comp_genEmbedC
    (ι : E →L[ℝ] X) (π : X →L[ℝ] E) (κ : F →L[ℝ] X) (ρ : X →L[ℝ] F)
    (ζ : F →L[ℝ] E) (W : E →L[ℝ] E)
    (hπι : π.comp ι = ContinuousLinearMap.id ℝ E)
    (hρκ : ρ.comp κ = ContinuousLinearMap.id ℝ F)
    (hπκ : π.comp κ = 0) (hρι : ρ.comp ι = 0) :
    (genCoordU π ρ ζ W).comp (genEmbedC ι κ ζ) = 0 := by
  have h1 : (π - ζ.comp ρ).comp (κ + ι.comp ζ) = 0 := by
    apply ContinuousLinearMap.ext
    intro v
    have hπι_v := DFunLike.congr_fun hπι (ζ v)
    have hπκ_v := DFunLike.congr_fun hπκ v
    have hρι_v := DFunLike.congr_fun hρι (ζ v)
    have hρκ_v := DFunLike.congr_fun hρκ v
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
      zero_apply] at hπι_v hπκ_v hρι_v hρκ_v
    change (π (κ v + ι (ζ v))) - ζ (ρ (κ v + ι (ζ v))) = 0
    rw [map_add, map_add, hπι_v, hπκ_v, hρι_v, hρκ_v, zero_add, add_zero, sub_self]
  unfold genCoordU genEmbedC
  rw [ContinuousLinearMap.comp_assoc, h1, ContinuousLinearMap.comp_zero]

private theorem genProjC_eq_id_sub_genProjU
    (ι : E →L[ℝ] X) (π : X →L[ℝ] E) (κ : F →L[ℝ] X) (ρ : X →L[ℝ] F)
    (ξ : E →L[ℝ] F) (ζ : F →L[ℝ] E) (W : E →L[ℝ] E)
    (hdecomp : ι.comp π + κ.comp ρ = ContinuousLinearMap.id ℝ X)
    (hW2 : (1 - ζ.comp ξ) * W = 1) :
    ContinuousLinearMap.id ℝ X - genProjU ι π κ ρ ξ ζ W =
      (genEmbedC ι κ ζ).comp (genCoordC ρ ξ (genCoordU π ρ ζ W)) := by
  apply ContinuousLinearMap.ext
  intro x
  set Pu := genCoordU π ρ ζ W
  have hWPu : Pu x - ζ (ξ (Pu x)) = π x - ζ (ρ x) :=
    DFunLike.congr_fun hW2 ((π - ζ.comp ρ) x)
  have hπ_eq : Pu x + ζ (ρ x - ξ (Pu x)) = π x := by
    calc Pu x + ζ (ρ x - ξ (Pu x))
        = (Pu x - ζ (ξ (Pu x))) + ζ (ρ x) := by rw [map_sub]; abel
      _ = (π x - ζ (ρ x)) + ζ (ρ x) := by rw [hWPu]
      _ = π x := sub_add_cancel _ _
  have hρ_eq : ξ (Pu x) + (ρ x - ξ (Pu x)) = ρ x := add_sub_cancel _ _
  have hdec_x : ι (π x) + κ (ρ x) = x := DFunLike.congr_fun hdecomp x
  have hsum : (ι (Pu x) + κ (ξ (Pu x))) + (κ (ρ x - ξ (Pu x)) + ι (ζ (ρ x - ξ (Pu x)))) = x := by
    calc (ι (Pu x) + κ (ξ (Pu x))) + (κ (ρ x - ξ (Pu x)) + ι (ζ (ρ x - ξ (Pu x))))
        = ι (Pu x + ζ (ρ x - ξ (Pu x))) + κ (ξ (Pu x) + (ρ x - ξ (Pu x))) := by
          rw [map_add, map_add]; abel
      _ = ι (π x) + κ (ρ x) := by rw [hπ_eq, hρ_eq]
      _ = x := hdec_x
  change x - (ι (Pu x) + κ (ξ (Pu x))) = κ (ρ x - ξ (Pu x)) + ι (ζ (ρ x - ξ (Pu x)))
  exact sub_eq_of_eq_add' hsum.symm

private theorem gen_block_fwd_intertwine
    (Un : X →L[ℝ] X)
    (ι₀ ι₁ : E →L[ℝ] X) (π₁ : X →L[ℝ] E) (κ₀ κ₁ : F →L[ℝ] X) (ρ₁ : X →L[ℝ] F)
    (ξ ξ' : E →L[ℝ] F) (M : E →L[ℝ] E)
    (hdec₁ : ι₁.comp π₁ + κ₁.comp ρ₁ = ContinuousLinearMap.id ℝ X)
    (hMB : M * ((π₁.comp (Un.comp ι₀)) + (π₁.comp (Un.comp κ₀)).comp ξ) = 1)
    (hξ' : ξ' = ((ρ₁.comp (Un.comp ι₀)) + (ρ₁.comp (Un.comp κ₀)).comp ξ).comp M) :
    Un.comp (genEmbedU ι₀ κ₀ ξ) =
      (genEmbedU ι₁ κ₁ ξ').comp ((π₁.comp (Un.comp ι₀)) + (π₁.comp (Un.comp κ₀)).comp ξ) := by
  set a := π₁.comp (Un.comp ι₀)
  set b := π₁.comp (Un.comp κ₀)
  set c := ρ₁.comp (Un.comp ι₀)
  set d := ρ₁.comp (Un.comp κ₀)
  set B := a + b.comp ξ
  have hπU : ∀ w : E, π₁ (Un (genEmbedU ι₀ κ₀ ξ w)) = B w := by
    intro w
    change π₁ (Un (ι₀ w + κ₀ (ξ w))) = a w + b (ξ w)
    rw [map_add, map_add]
    rfl
  have hρU : ∀ w : E, ρ₁ (Un (genEmbedU ι₀ κ₀ ξ w)) = ξ' (B w) := by
    intro w
    have hMB_w : M (B w) = w := DFunLike.congr_fun hMB w
    have hξ'_Bw : ξ' (B w) = (c + d.comp ξ) w := by
      rw [hξ']
      change (c + d.comp ξ) (M (B w)) = (c + d.comp ξ) w
      rw [hMB_w]
    rw [hξ'_Bw]
    change ρ₁ (Un (ι₀ w + κ₀ (ξ w))) = c w + d (ξ w)
    rw [map_add, map_add]
    rfl
  apply ContinuousLinearMap.ext
  intro w
  have hdec_w : ι₁ (π₁ (Un (genEmbedU ι₀ κ₀ ξ w))) + κ₁ (ρ₁ (Un (genEmbedU ι₀ κ₀ ξ w))) =
      Un (genEmbedU ι₀ κ₀ ξ w) :=
    DFunLike.congr_fun hdec₁ (Un (genEmbedU ι₀ κ₀ ξ w))
  calc Un (genEmbedU ι₀ κ₀ ξ w)
      = ι₁ (π₁ (Un (genEmbedU ι₀ κ₀ ξ w))) + κ₁ (ρ₁ (Un (genEmbedU ι₀ κ₀ ξ w))) := hdec_w.symm
    _ = ι₁ (B w) + κ₁ (ξ' (B w)) := by rw [hπU w, hρU w]
    _ = (genEmbedU ι₁ κ₁ ξ').comp B w := rfl

private theorem gen_block_bwd_intertwine
    (Un : X →L[ℝ] X)
    (ι₀ ι₁ : E →L[ℝ] X) (π₀ π₁ : X →L[ℝ] E)
    (κ₀ κ₁ : F →L[ℝ] X) (ρ₀ ρ₁ : X →L[ℝ] F)
    (ξ₀ ξ₁ : E →L[ℝ] F) (ζ₀ ζ₁ : F →L[ℝ] E) (W₀ W₁ Mb B : E →L[ℝ] E)
    (hdec₀ : ι₀.comp π₀ + κ₀.comp ρ₀ = ContinuousLinearMap.id ℝ X)
    (hπι₀ : π₀.comp ι₀ = ContinuousLinearMap.id ℝ E)
    (hρκ₀ : ρ₀.comp κ₀ = ContinuousLinearMap.id ℝ F)
    (hπκ₀ : π₀.comp κ₀ = 0) (hρι₀ : ρ₀.comp ι₀ = 0)
    (hπι₁ : π₁.comp ι₁ = ContinuousLinearMap.id ℝ E)
    (hρκ₁ : ρ₁.comp κ₁ = ContinuousLinearMap.id ℝ F)
    (hπκ₁ : π₁.comp κ₁ = 0) (hρι₁ : ρ₁.comp ι₁ = 0)
    (hW₀a : W₀ * (1 - ζ₀.comp ξ₀) = 1)
    (hW₀b : (1 - ζ₀.comp ξ₀) * W₀ = 1)
    (hW₁a : W₁ * (1 - ζ₁.comp ξ₁) = 1)
    (hMb : ((π₁.comp (Un.comp ι₀)) - ζ₁.comp (ρ₁.comp (Un.comp ι₀))) * Mb = 1)
    (hζ₀ : ζ₀ = Mb.comp (ζ₁.comp (ρ₁.comp (Un.comp κ₀)) - (π₁.comp (Un.comp κ₀))))
    (hfwd : Un.comp (genEmbedU ι₀ κ₀ ξ₀) = (genEmbedU ι₁ κ₁ ξ₁).comp B) :
    (genCoordU π₁ ρ₁ ζ₁ W₁).comp Un = B.comp (genCoordU π₀ ρ₀ ζ₀ W₀) := by
  set a := π₁.comp (Un.comp ι₀)
  set b := π₁.comp (Un.comp κ₀)
  set c := ρ₁.comp (Un.comp ι₀)
  set d := ρ₁.comp (Un.comp κ₀)
  set A_bwd := a - ζ₁.comp c
  have hAζ : ∀ v : F, A_bwd (ζ₀ v) = ζ₁ (d v) - b v := by
    intro v
    rw [hζ₀]
    change (A_bwd * Mb) ((ζ₁.comp d - b) v) = ζ₁ (d v) - b v
    rw [hMb]
    rfl
  have hraw : ∀ x : X, (π₁ - ζ₁.comp ρ₁) (Un x) = A_bwd ((π₀ - ζ₀.comp ρ₀) x) := by
    intro x
    have hdec_x : ι₀ (π₀ x) + κ₀ (ρ₀ x) = x := DFunLike.congr_fun hdec₀ x
    have h1 : (π₁ - ζ₁.comp ρ₁) (Un x) =
        (π₁ - ζ₁.comp ρ₁) (Un (ι₀ (π₀ x))) + (π₁ - ζ₁.comp ρ₁) (Un (κ₀ (ρ₀ x))) := by
      conv_lhs => rw [← hdec_x]
      rw [map_add, map_add]
    have h2 : (π₁ - ζ₁.comp ρ₁) (Un (ι₀ (π₀ x))) = A_bwd (π₀ x) := rfl
    have h3 : (π₁ - ζ₁.comp ρ₁) (Un (κ₀ (ρ₀ x))) = - A_bwd (ζ₀ (ρ₀ x)) := by
      have hz := hAζ (ρ₀ x)
      change b (ρ₀ x) - ζ₁ (d (ρ₀ x)) = - A_bwd (ζ₀ (ρ₀ x))
      rw [hz]
      abel
    rw [h1, h2, h3]
    change A_bwd (π₀ x) + - A_bwd (ζ₀ (ρ₀ x)) = A_bwd (π₀ x - ζ₀ (ρ₀ x))
    rw [map_sub, sub_eq_add_neg]
  set T : E →L[ℝ] E := W₁.comp (A_bwd.comp (1 - ζ₀.comp ξ₀))
  have hPu_T : (genCoordU π₁ ρ₁ ζ₁ W₁).comp Un = T.comp (genCoordU π₀ ρ₀ ζ₀ W₀) := by
    apply ContinuousLinearMap.ext
    intro x
    have hW₀_x : (1 - ζ₀.comp ξ₀) (W₀ ((π₀ - ζ₀.comp ρ₀) x)) = (π₀ - ζ₀.comp ρ₀) x :=
      DFunLike.congr_fun hW₀b ((π₀ - ζ₀.comp ρ₀) x)
    change W₁ ((π₁ - ζ₁.comp ρ₁) (Un x)) =
      W₁ (A_bwd ((1 - ζ₀.comp ξ₀) (W₀ ((π₀ - ζ₀.comp ρ₀) x))))
    rw [hraw x, hW₀_x]
  have hT_eq_B : T = B := by
    have hPI₀ := genCoordU_comp_genEmbedU ι₀ π₀ κ₀ ρ₀ ξ₀ ζ₀ W₀ hπι₀ hρκ₀ hπκ₀ hρι₀ hW₀a
    have hPI₁ := genCoordU_comp_genEmbedU ι₁ π₁ κ₁ ρ₁ ξ₁ ζ₁ W₁ hπι₁ hρκ₁ hπκ₁ hρι₁ hW₁a
    calc T = T.comp (ContinuousLinearMap.id ℝ E) := (ContinuousLinearMap.comp_id T).symm
      _ = T.comp ((genCoordU π₀ ρ₀ ζ₀ W₀).comp (genEmbedU ι₀ κ₀ ξ₀)) := by rw [hPI₀]
      _ = (T.comp (genCoordU π₀ ρ₀ ζ₀ W₀)).comp (genEmbedU ι₀ κ₀ ξ₀) :=
          (ContinuousLinearMap.comp_assoc _ _ _).symm
      _ = ((genCoordU π₁ ρ₁ ζ₁ W₁).comp Un).comp (genEmbedU ι₀ κ₀ ξ₀) := by rw [hPu_T]
      _ = (genCoordU π₁ ρ₁ ζ₁ W₁).comp (Un.comp (genEmbedU ι₀ κ₀ ξ₀)) :=
          ContinuousLinearMap.comp_assoc _ _ _
      _ = (genCoordU π₁ ρ₁ ζ₁ W₁).comp ((genEmbedU ι₁ κ₁ ξ₁).comp B) := by rw [hfwd]
      _ = ((genCoordU π₁ ρ₁ ζ₁ W₁).comp (genEmbedU ι₁ κ₁ ξ₁)).comp B :=
          (ContinuousLinearMap.comp_assoc _ _ _).symm
      _ = (ContinuousLinearMap.id ℝ E).comp B := by rw [hPI₁]
      _ = B := ContinuousLinearMap.id_comp B
  rw [hPu_T, hT_eq_B]

private theorem gen_block_center_intertwine
    (Un : X →L[ℝ] X)
    (ι₀ ι₁ : E →L[ℝ] X) (π₀ π₁ : X →L[ℝ] E)
    (κ₀ κ₁ : F →L[ℝ] X) (ρ₀ ρ₁ : X →L[ℝ] F)
    (ξ₁ : E →L[ℝ] F) (ζ₀ ζ₁ : F →L[ℝ] E) (W₀ W₁ B : E →L[ℝ] E)
    (hdec₁ : ι₁.comp π₁ + κ₁.comp ρ₁ = ContinuousLinearMap.id ℝ X)
    (hπι₀ : π₀.comp ι₀ = ContinuousLinearMap.id ℝ E)
    (hρκ₀ : ρ₀.comp κ₀ = ContinuousLinearMap.id ℝ F)
    (hπκ₀ : π₀.comp κ₀ = 0) (hρι₀ : ρ₀.comp ι₀ = 0)
    (hW₁b : (1 - ζ₁.comp ξ₁) * W₁ = 1)
    (hbwd : (genCoordU π₁ ρ₁ ζ₁ W₁).comp Un = B.comp (genCoordU π₀ ρ₀ ζ₀ W₀)) :
    Un.comp (genEmbedC ι₀ κ₀ ζ₀) =
      (genEmbedC ι₁ κ₁ ζ₁).comp ((ρ₁.comp (Un.comp κ₀)) + (ρ₁.comp (Un.comp ι₀)).comp ζ₀) := by
  have hPu₀_Ic₀ : (genCoordU π₀ ρ₀ ζ₀ W₀).comp (genEmbedC ι₀ κ₀ ζ₀) = 0 :=
    genCoordU_comp_genEmbedC ι₀ π₀ κ₀ ρ₀ ζ₀ W₀ hπι₀ hρκ₀ hπκ₀ hρι₀
  have hPu₁_U_Ic₀ : (genCoordU π₁ ρ₁ ζ₁ W₁).comp (Un.comp (genEmbedC ι₀ κ₀ ζ₀)) = 0 := by
    rw [← ContinuousLinearMap.comp_assoc, hbwd, ContinuousLinearMap.comp_assoc,
      hPu₀_Ic₀, ContinuousLinearMap.comp_zero]
  have hPic₁ := genProjC_eq_id_sub_genProjU ι₁ π₁ κ₁ ρ₁ ξ₁ ζ₁ W₁ hdec₁ hW₁b
  apply ContinuousLinearMap.ext
  intro v
  have hPu₁_v : genCoordU π₁ ρ₁ ζ₁ W₁ (Un (genEmbedC ι₀ κ₀ ζ₀ v)) = 0 :=
    DFunLike.congr_fun hPu₁_U_Ic₀ v
  have hPiu₁_v : genProjU ι₁ π₁ κ₁ ρ₁ ξ₁ ζ₁ W₁ (Un (genEmbedC ι₀ κ₀ ζ₀ v)) = 0 := by
    unfold genProjU
    change genEmbedU ι₁ κ₁ ξ₁ (genCoordU π₁ ρ₁ ζ₁ W₁ (Un (genEmbedC ι₀ κ₀ ζ₀ v))) = 0
    rw [hPu₁_v, map_zero]
  have hPic₁_v : Un (genEmbedC ι₀ κ₀ ζ₀ v) =
      genEmbedC ι₁ κ₁ ζ₁ (genCoordC ρ₁ ξ₁ (genCoordU π₁ ρ₁ ζ₁ W₁) (Un (genEmbedC ι₀ κ₀ ζ₀ v))) := by
    have h := DFunLike.congr_fun hPic₁ (Un (genEmbedC ι₀ κ₀ ζ₀ v))
    change Un (genEmbedC ι₀ κ₀ ζ₀ v) - genProjU ι₁ π₁ κ₁ ρ₁ ξ₁ ζ₁ W₁ (Un (genEmbedC ι₀ κ₀ ζ₀ v)) =
      genEmbedC ι₁ κ₁ ζ₁ (genCoordC ρ₁ ξ₁ (genCoordU π₁ ρ₁ ζ₁ W₁) (Un (genEmbedC ι₀ κ₀ ζ₀ v))) at h
    rw [hPiu₁_v, sub_zero] at h
    exact h
  have hPc₁_v :
      genCoordC ρ₁ ξ₁ (genCoordU π₁ ρ₁ ζ₁ W₁) (Un (genEmbedC ι₀ κ₀ ζ₀ v)) =
        ((ρ₁.comp (Un.comp κ₀)) + (ρ₁.comp (Un.comp ι₀)).comp ζ₀) v := by
    change ρ₁ (Un (κ₀ v + ι₀ (ζ₀ v))) - ξ₁ (genCoordU π₁ ρ₁ ζ₁ W₁ (Un (genEmbedC ι₀ κ₀ ζ₀ v))) =
      ρ₁ (Un (κ₀ v)) + ρ₁ (Un (ι₀ (ζ₀ v)))
    rw [hPu₁_v, map_zero, sub_zero, map_add, map_add]
  change Un (genEmbedC ι₀ κ₀ ζ₀ v) =
    genEmbedC ι₁ κ₁ ζ₁ (((ρ₁.comp (Un.comp κ₀)) + (ρ₁.comp (Un.comp ι₀)).comp ζ₀) v)
  rw [hPic₁_v, hPc₁_v]

/-! ## 3. Generic sequence construction and dichotomy bounds -/

private theorem gen_exists_sequences
    (N : ℕ) (L a' b' M_coord : ℝ)
    (ha' : 0 < a') (hab' : a' < b') (hL : 0 ≤ L) (hM_coord : 1 ≤ M_coord)
    (U : ℝ → ℝ → (X →L[ℝ] X))
    (ι : ℕ → (E →L[ℝ] X)) (π : ℕ → (X →L[ℝ] E))
    (κ : ℕ → (F →L[ℝ] X)) (ρ : ℕ → (X →L[ℝ] F))
    (ainv : ℕ → (E →L[ℝ] E))
    (hU_id : ∀ n ≤ N, U ((n : ℝ) * L) ((n : ℝ) * L) = ContinuousLinearMap.id ℝ X)
    (hU_coc : ∀ j k : ℕ, j ≤ k → k < N →
      (U (((k + 1 : ℕ) : ℝ) * L) ((k : ℝ) * L)).comp (U ((k : ℝ) * L) ((j : ℝ) * L)) =
        U (((k + 1 : ℕ) : ℝ) * L) ((j : ℝ) * L))
    (hπι : ∀ n ≤ N, (π n).comp (ι n) = ContinuousLinearMap.id ℝ E)
    (hρκ : ∀ n ≤ N, (ρ n).comp (κ n) = ContinuousLinearMap.id ℝ F)
    (hπκ : ∀ n ≤ N, (π n).comp (κ n) = 0)
    (hρι : ∀ n ≤ N, (ρ n).comp (ι n) = 0)
    (hdec : ∀ n ≤ N, (ι n).comp (π n) + (κ n).comp (ρ n) = ContinuousLinearMap.id ℝ X)
    (hcoord : ∀ n ≤ N, ‖ι n‖ ≤ M_coord ∧ ‖π n‖ ≤ M_coord ∧ ‖κ n‖ ≤ M_coord ∧ ‖ρ n‖ ≤ M_coord)
    (hainv_l : ∀ n < N, ainv n * ((π (n + 1)).comp ((U (((n + 1 : ℕ) : ℝ) * L) ((n : ℝ) * L)).comp (ι n))) = 1)
    (hainv_r : ∀ n < N, ((π (n + 1)).comp ((U (((n + 1 : ℕ) : ℝ) * L) ((n : ℝ) * L)).comp (ι n))) * ainv n = 1)
    (hainv_n : ∀ n < N, ‖ainv n‖ ≤ (1 / 2 : ℝ) * Real.exp (-b' * L))
    (hd_n : ∀ n < N, ‖(ρ (n + 1)).comp ((U (((n + 1 : ℕ) : ℝ) * L) ((n : ℝ) * L)).comp (κ n))‖ ≤
      (1 / 2 : ℝ) * Real.exp (a' * L))
    (hb_n : ∀ n < N, ‖(π (n + 1)).comp ((U (((n + 1 : ℕ) : ℝ) * L) ((n : ℝ) * L)).comp (κ n))‖ ≤ 1 / 2)
    (hc_n : ∀ n < N, ‖(ρ (n + 1)).comp ((U (((n + 1 : ℕ) : ℝ) * L) ((n : ℝ) * L)).comp (ι n))‖ ≤ 1 / 2) :
    ∃ (Iu : ℕ → (E →L[ℝ] X)) (Pu : ℕ → (X →L[ℝ] E))
      (Piu Pic : ℕ → (X →L[ℝ] X)) (Bn Mn : ℕ → (E →L[ℝ] E)),
      Iu 0 = ι 0 ∧
      (∀ n ≤ N,
        (Pu n).comp (Iu n) = ContinuousLinearMap.id ℝ E ∧
        Piu n = (Iu n).comp (Pu n) ∧
        Pic n = ContinuousLinearMap.id ℝ X - Piu n) ∧
      (∀ n ≤ N,
        ‖Iu n‖ ≤ 7 * M_coord ^ 2 ∧ ‖Pu n‖ ≤ 7 * M_coord ^ 2 ∧
        ‖Piu n‖ ≤ 7 * M_coord ^ 2 ∧ ‖Pic n‖ ≤ 7 * M_coord ^ 2) ∧
      (∀ n < N,
        Mn n * Bn n = 1 ∧ Bn n * Mn n = 1 ∧ ‖Mn n‖ ≤ Real.exp (-b' * L)) ∧
      (∀ n < N,
        (U (((n + 1 : ℕ) : ℝ) * L) ((n : ℝ) * L)).comp (Iu n) = (Iu (n + 1)).comp (Bn n) ∧
        (Pu (n + 1)).comp (U (((n + 1 : ℕ) : ℝ) * L) ((n : ℝ) * L)) = (Bn n).comp (Pu n)) ∧
      (∀ j k : ℕ, j ≤ k → k ≤ N →
        ‖(U ((k : ℝ) * L) ((j : ℝ) * L)).comp (Pic j)‖ ≤
          (7 * M_coord ^ 2) * Real.exp (a' * ((k : ℝ) * L - (j : ℝ) * L))) ∧
      (∀ j k : ℕ, j ≤ k → k ≤ N →
        ∃ M_jk : E →L[ℝ] E,
          (U ((k : ℝ) * L) ((j : ℝ) * L)).comp ((Iu j).comp M_jk) = Iu k ∧
          M_jk.comp ((Pu k).comp (U ((k : ℝ) * L) ((j : ℝ) * L))) = Pu j ∧
          ‖M_jk‖ ≤ Real.exp (-b' * ((k : ℝ) * L - (j : ℝ) * L)) ∧
          ‖(Iu j).comp (M_jk.comp (Pu k))‖ ≤
            (7 * M_coord ^ 2) * Real.exp (-b' * ((k : ℝ) * L - (j : ℝ) * L))) := by
  classical
  have hb' : 0 < b' := lt_trans ha' hab'
  let t : ℕ → ℝ := fun n => (n : ℝ) * L
  let a : ℕ → (E →L[ℝ] E) := fun n => (π (n + 1)).comp ((U (t (n + 1)) (t n)).comp (ι n))
  let b : ℕ → (F →L[ℝ] E) := fun n => (π (n + 1)).comp ((U (t (n + 1)) (t n)).comp (κ n))
  let c : ℕ → (E →L[ℝ] F) := fun n => (ρ (n + 1)).comp ((U (t (n + 1)) (t n)).comp (ι n))
  let d : ℕ → (F →L[ℝ] F) := fun n => (ρ (n + 1)).comp ((U (t (n + 1)) (t n)).comp (κ n))
  have h1_fwd : ∀ {n : ℕ} (hn : n < N) (ξn : E →L[ℝ] F) (hξn : ‖ξn‖ ≤ 1 / 2),
      ∃ M : E →L[ℝ] E,
        M * (a n + (b n).comp ξn) = 1 ∧
        (a n + (b n).comp ξn) * M = 1 ∧
        ‖M‖ ≤ Real.exp (-b' * L) ∧
        ‖(c n + (d n).comp ξn).comp M‖ ≤ 1 / 2 := by
    intro n hn ξn hξn
    have hGT := graphTransformLemma_proof E F (a n) (b n) (c n) (d n) (ainv n)
      ((1 / 2 : ℝ) * Real.exp (-b' * L)) ((1 / 2 : ℝ) * Real.exp (a' * L)) (1 / 2) (1 / 2)
      (hainv_l n hn) (hainv_r n hn) (hainv_n n hn) (hd_n n hn) (hb_n n hn) (hc_n n hn)
      (by positivity) (by positivity)
      (strict_margin_Arη_lt_one hb' hL) (strict_margin_ball_cond ha' hab' hL)
    obtain ⟨M, hM1, hM2, hMn, hξ'⟩ := hGT.1 ξn hξn
    exact ⟨M, hM1, hM2, hMn.trans (strict_margin_inv_bound hb' hL), hξ'⟩
  have h1_bwd : ∀ {n : ℕ} (hn : n < N) (ζn : F →L[ℝ] E) (hζn : ‖ζn‖ ≤ 1 / 2),
      ∃ M : E →L[ℝ] E,
        M * (a n - ζn.comp (c n)) = 1 ∧
        (a n - ζn.comp (c n)) * M = 1 ∧
        ‖M.comp (ζn.comp (d n) - b n)‖ ≤ 1 / 2 := by
    intro n hn ζn hζn
    have hGT := graphTransformLemma_proof E F (a n) (b n) (c n) (d n) (ainv n)
      ((1 / 2 : ℝ) * Real.exp (-b' * L)) ((1 / 2 : ℝ) * Real.exp (a' * L)) (1 / 2) (1 / 2)
      (hainv_l n hn) (hainv_r n hn) (hainv_n n hn) (hd_n n hn) (hb_n n hn) (hc_n n hn)
      (by positivity) (by positivity)
      (strict_margin_Arη_lt_one hb' hL) (strict_margin_ball_cond ha' hab' hL)
    obtain ⟨M, hM1, hM2, _, hζ'⟩ := hGT.2.2.1 ζn hζn
    exact ⟨M, hM1, hM2, hζ'⟩
  let stepM (n : ℕ) (ξn : E →L[ℝ] F) : E →L[ℝ] E :=
    if h : n < N ∧ ‖ξn‖ ≤ 1 / 2 then Classical.choose (h1_fwd h.1 ξn h.2) else 0
  let ξ : ℕ → (E →L[ℝ] F) :=
    Nat.rec 0 (fun n ξn =>
      if n < N ∧ ‖ξn‖ ≤ 1 / 2 then (c n + (d n).comp ξn).comp (stepM n ξn) else 0)
  let Mn : ℕ → (E →L[ℝ] E) := fun n => stepM n (ξ n)
  have hξ_norm : ∀ n : ℕ, ‖ξ n‖ ≤ 1 / 2 := by
    intro n
    induction n with
    | zero =>
      change ‖(0 : E →L[ℝ] F)‖ ≤ 1 / 2
      rw [norm_zero]; positivity
    | succ n ih =>
      change ‖if n < N ∧ ‖ξ n‖ ≤ 1 / 2 then
        (c n + (d n).comp (ξ n)).comp (stepM n (ξ n)) else 0‖ ≤ 1 / 2
      split_ifs with h
      · have hspec := Classical.choose_spec (h1_fwd h.1 (ξ n) h.2)
        have heq : stepM n (ξ n) = Classical.choose (h1_fwd h.1 (ξ n) h.2) := dif_pos h
        rw [heq]; exact hspec.2.2.2
      · rw [norm_zero]; positivity
  have hξ_step : ∀ n < N,
      Mn n * (a n + (b n).comp (ξ n)) = 1 ∧
      (a n + (b n).comp (ξ n)) * Mn n = 1 ∧
      ‖Mn n‖ ≤ Real.exp (-b' * L) ∧
      ξ (n + 1) = (c n + (d n).comp (ξ n)).comp (Mn n) := by
    intro n hn
    have hcond : n < N ∧ ‖ξ n‖ ≤ 1 / 2 := ⟨hn, hξ_norm n⟩
    have hspec := Classical.choose_spec (h1_fwd hn (ξ n) (hξ_norm n))
    have hMn_eq : Mn n = Classical.choose (h1_fwd hn (ξ n) (hξ_norm n)) := dif_pos hcond
    have hξ_succ : ξ (n + 1) = (c n + (d n).comp (ξ n)).comp (Mn n) := if_pos hcond
    rw [← hMn_eq] at hspec
    exact ⟨hspec.1, hspec.2.1, hspec.2.2.1, hξ_succ⟩
  let stepMb (n : ℕ) (ζn : F →L[ℝ] E) : E →L[ℝ] E :=
    if h : n < N ∧ ‖ζn‖ ≤ 1 / 2 then Classical.choose (h1_bwd h.1 ζn h.2) else 0
  let ζRev : ℕ → (F →L[ℝ] E) :=
    Nat.rec 0 (fun k ζk =>
      let m := N - 1 - k
      if m < N ∧ ‖ζk‖ ≤ 1 / 2 then (stepMb m ζk).comp (ζk.comp (d m) - b m) else 0)
  have hζRev_norm : ∀ k : ℕ, ‖ζRev k‖ ≤ 1 / 2 := by
    intro k
    induction k with
    | zero =>
      change ‖(0 : F →L[ℝ] E)‖ ≤ 1 / 2
      rw [norm_zero]; positivity
    | succ k ih =>
      let m := N - 1 - k
      change ‖if m < N ∧ ‖ζRev k‖ ≤ 1 / 2 then
        (stepMb m (ζRev k)).comp ((ζRev k).comp (d m) - b m) else 0‖ ≤ 1 / 2
      split_ifs with h
      · have hspec := Classical.choose_spec (h1_bwd h.1 (ζRev k) h.2)
        have heq : stepMb m (ζRev k) = Classical.choose (h1_bwd h.1 (ζRev k) h.2) := dif_pos h
        rw [heq]; exact hspec.2.2
      · rw [norm_zero]; positivity
  let ζ : ℕ → (F →L[ℝ] E) := fun n => ζRev (N - n)
  let Mb : ℕ → (E →L[ℝ] E) := fun n => stepMb n (ζ (n + 1))
  have hζ_norm : ∀ n : ℕ, ‖ζ n‖ ≤ 1 / 2 := fun n => hζRev_norm (N - n)
  have hζ_step : ∀ n < N,
      Mb n * (a n - (ζ (n + 1)).comp (c n)) = 1 ∧
      (a n - (ζ (n + 1)).comp (c n)) * Mb n = 1 ∧
      ζ n = (Mb n).comp ((ζ (n + 1)).comp (d n) - b n) := by
    intro n hn
    set k : ℕ := N - 1 - n
    have hsub_n : N - n = k + 1 := by omega
    have hsub_n1 : N - (n + 1) = k := by omega
    have hmk : N - 1 - k = n := by omega
    have hζ_n1 : ζ (n + 1) = ζRev k := by dsimp [ζ]; rw [hsub_n1]
    have hcond : n < N ∧ ‖ζ (n + 1)‖ ≤ 1 / 2 := ⟨hn, hζ_norm (n + 1)⟩
    have hspec := Classical.choose_spec (h1_bwd hn (ζ (n + 1)) hcond.2)
    have hMb_eq : Mb n = Classical.choose (h1_bwd hn (ζ (n + 1)) hcond.2) := dif_pos hcond
    have hζ_n : ζ n = (Mb n).comp ((ζ (n + 1)).comp (d n) - b n) := by
      dsimp [ζ]
      rw [hsub_n]
      change (if (N - 1 - k) < N ∧ ‖ζRev k‖ ≤ 1 / 2 then
        (stepMb (N - 1 - k) (ζRev k)).comp ((ζRev k).comp (d (N - 1 - k)) - b (N - 1 - k))
        else 0) = (Mb n).comp ((ζ (n + 1)).comp (d n) - b n)
      rw [hmk, ← hζ_n1, if_pos hcond]
    rw [← hMb_eq] at hspec
    exact ⟨hspec.1, hspec.2.1, hζ_n⟩
  have hW_ex : ∀ n : ℕ, ∃ W : E →L[ℝ] E,
      W * (1 - (ζ n).comp (ξ n)) = 1 ∧ (1 - (ζ n).comp (ξ n)) * W = 1 ∧ ‖W‖ ≤ 2 :=
    fun n => exists_graph_W_gen (ξ n) (ζ n) (hξ_norm n) (hζ_norm n)
  let W : ℕ → (E →L[ℝ] E) := fun n => Classical.choose (hW_ex n)
  have hW_spec : ∀ n : ℕ,
      W n * (1 - (ζ n).comp (ξ n)) = 1 ∧ (1 - (ζ n).comp (ξ n)) * W n = 1 ∧ ‖W n‖ ≤ 2 :=
    fun n => Classical.choose_spec (hW_ex n)
  let Iu : ℕ → (E →L[ℝ] X) := fun n => genEmbedU (ι n) (κ n) (ξ n)
  let Pu : ℕ → (X →L[ℝ] E) := fun n => genCoordU (π n) (ρ n) (ζ n) (W n)
  let Piu : ℕ → (X →L[ℝ] X) := fun n => (Iu n).comp (Pu n)
  let Pic : ℕ → (X →L[ℝ] X) := fun n => ContinuousLinearMap.id ℝ X - Piu n
  let Bn : ℕ → (E →L[ℝ] E) := fun n => a n + (b n).comp (ξ n)
  let Ic : ℕ → (F →L[ℝ] X) := fun n => genEmbedC (ι n) (κ n) (ζ n)
  let Pc : ℕ → (X →L[ℝ] F) := fun n => genCoordC (ρ n) (ξ n) (Pu n)
  let Dn : ℕ → (F →L[ℝ] F) := fun n => d n + (c n).comp (ζ n)
  have hIu_norm : ∀ n ≤ N, ‖Iu n‖ ≤ 2 * M_coord := by
    intro n hn
    have hc := hcoord n hn
    have h1 : ‖(κ n).comp (ξ n)‖ ≤ M_coord * (1 / 2) :=
      ((κ n).opNorm_comp_le (ξ n)).trans
        (mul_le_mul hc.2.2.1 (hξ_norm n) (norm_nonneg _) (by positivity))
    calc ‖Iu n‖ ≤ ‖ι n‖ + ‖(κ n).comp (ξ n)‖ := norm_add_le _ _
      _ ≤ M_coord + M_coord * (1 / 2) := add_le_add hc.1 h1
      _ ≤ 2 * M_coord := by linarith
  have hPu_norm : ∀ n ≤ N, ‖Pu n‖ ≤ 3 * M_coord := by
    intro n hn
    have hc := hcoord n hn
    have h1 : ‖(ζ n).comp (ρ n)‖ ≤ (1 / 2) * M_coord :=
      ((ζ n).opNorm_comp_le (ρ n)).trans
        (mul_le_mul (hζ_norm n) hc.2.2.2 (norm_nonneg _) (by positivity))
    have h2 : ‖π n - (ζ n).comp (ρ n)‖ ≤ (3 / 2) * M_coord := by
      calc ‖π n - (ζ n).comp (ρ n)‖ ≤ ‖π n‖ + ‖(ζ n).comp (ρ n)‖ := norm_sub_le _ _
        _ ≤ M_coord + (1 / 2) * M_coord := add_le_add hc.2.1 h1
        _ = (3 / 2) * M_coord := by ring
    calc ‖Pu n‖ ≤ ‖W n‖ * ‖π n - (ζ n).comp (ρ n)‖ := (W n).opNorm_comp_le _
      _ ≤ 2 * ((3 / 2) * M_coord) :=
          mul_le_mul (hW_spec n).2.2 h2 (norm_nonneg _) (by positivity)
      _ = 3 * M_coord := by ring
  have hIc_norm : ∀ n ≤ N, ‖Ic n‖ ≤ 2 * M_coord := by
    intro n hn
    have hc := hcoord n hn
    have h1 : ‖(ι n).comp (ζ n)‖ ≤ M_coord * (1 / 2) :=
      ((ι n).opNorm_comp_le (ζ n)).trans
        (mul_le_mul hc.1 (hζ_norm n) (norm_nonneg _) (by positivity))
    calc ‖Ic n‖ ≤ ‖κ n‖ + ‖(ι n).comp (ζ n)‖ := norm_add_le _ _
      _ ≤ M_coord + M_coord * (1 / 2) := add_le_add hc.2.2.1 h1
      _ ≤ 2 * M_coord := by linarith
  have hPc_norm : ∀ n ≤ N, ‖Pc n‖ ≤ 3 * M_coord := by
    intro n hn
    have hc := hcoord n hn
    have h1 : ‖(ξ n).comp (Pu n)‖ ≤ (1 / 2) * (3 * M_coord) :=
      ((ξ n).opNorm_comp_le (Pu n)).trans
        (mul_le_mul (hξ_norm n) (hPu_norm n hn) (norm_nonneg _) (by positivity))
    calc ‖Pc n‖ ≤ ‖ρ n‖ + ‖(ξ n).comp (Pu n)‖ := norm_sub_le (ρ n) ((ξ n).comp (Pu n))
      _ ≤ M_coord + (1 / 2) * (3 * M_coord) := add_le_add hc.2.2.2 h1
      _ ≤ 3 * M_coord := by linarith
  have hIntertwine : ∀ n < N,
      (U (t (n + 1)) (t n)).comp (Iu n) = (Iu (n + 1)).comp (Bn n) ∧
      (Pu (n + 1)).comp (U (t (n + 1)) (t n)) = (Bn n).comp (Pu n) := by
    intro n hn
    have hfwd := gen_block_fwd_intertwine (U (t (n + 1)) (t n))
      (ι n) (ι (n + 1)) (π (n + 1)) (κ n) (κ (n + 1)) (ρ (n + 1))
      (ξ n) (ξ (n + 1)) (Mn n) (hdec (n + 1) hn)
      (hξ_step n hn).1 (hξ_step n hn).2.2.2
    have hbwd := gen_block_bwd_intertwine (U (t (n + 1)) (t n))
      (ι n) (ι (n + 1)) (π n) (π (n + 1)) (κ n) (κ (n + 1)) (ρ n) (ρ (n + 1))
      (ξ n) (ξ (n + 1)) (ζ n) (ζ (n + 1)) (W n) (W (n + 1)) (Mb n) (Bn n)
      (hdec n hn.le) (hπι n hn.le) (hρκ n hn.le) (hπκ n hn.le) (hρι n hn.le)
      (hπι (n + 1) hn) (hρκ (n + 1) hn) (hπκ (n + 1) hn) (hρι (n + 1) hn)
      (hW_spec n).1 (hW_spec n).2.1 (hW_spec (n + 1)).1
      (hζ_step n hn).2.1 (hζ_step n hn).2.2 hfwd
    exact ⟨hfwd, hbwd⟩
  have hCenter_step : ∀ n < N,
      (U (t (n + 1)) (t n)).comp (Ic n) = (Ic (n + 1)).comp (Dn n) ∧
      ‖Dn n‖ ≤ Real.exp (a' * L) := by
    intro n hn
    have hc_int := gen_block_center_intertwine (U (t (n + 1)) (t n))
      (ι n) (ι (n + 1)) (π n) (π (n + 1)) (κ n) (κ (n + 1)) (ρ n) (ρ (n + 1))
      (ξ (n + 1)) (ζ n) (ζ (n + 1)) (W n) (W (n + 1)) (Bn n)
      (hdec (n + 1) hn) (hπι n hn.le) (hρκ n hn.le) (hπκ n hn.le) (hρι n hn.le)
      (hW_spec (n + 1)).2.1 (hIntertwine n hn).2
    have hcz : ‖(c n).comp (ζ n)‖ ≤ (1 / 2 : ℝ) * (1 / 2 : ℝ) :=
      ((c n).opNorm_comp_le (ζ n)).trans
        (mul_le_mul (hc_n n hn) (hζ_norm n) (norm_nonneg _) (by positivity))
    have hDn_norm : ‖Dn n‖ ≤ Real.exp (a' * L) := by
      calc ‖Dn n‖ ≤ ‖d n‖ + ‖(c n).comp (ζ n)‖ := norm_add_le _ _
        _ ≤ (1 / 2 : ℝ) * Real.exp (a' * L) + (1 / 2 : ℝ) * (1 / 2 : ℝ) :=
            add_le_add (hd_n n hn) hcz
        _ ≤ Real.exp (a' * L) := strict_margin_center_bound ha' hL
    exact ⟨hc_int, hDn_norm⟩
  refine ⟨Iu, Pu, Piu, Pic, Bn, Mn, ?_, ?_, ?_, ?_, hIntertwine, ?_, ?_⟩
  · change ι 0 + (κ 0).comp (0 : E →L[ℝ] F) = ι 0
    rw [ContinuousLinearMap.comp_zero, add_zero]
  · intro n hn
    exact ⟨genCoordU_comp_genEmbedU (ι n) (π n) (κ n) (ρ n) (ξ n) (ζ n) (W n)
      (hπι n hn) (hρκ n hn) (hπκ n hn) (hρι n hn) (hW_spec n).1, rfl, rfl⟩
  · intro n hn
    have hIu_n := hIu_norm n hn
    have hPu_n := hPu_norm n hn
    have hPiu_n : ‖Piu n‖ ≤ 6 * M_coord ^ 2 := by
      calc ‖(Iu n).comp (Pu n)‖ ≤ ‖Iu n‖ * ‖Pu n‖ := (Iu n).opNorm_comp_le (Pu n)
        _ ≤ (2 * M_coord) * (3 * M_coord) :=
            mul_le_mul hIu_n hPu_n (norm_nonneg _) (by positivity)
        _ = 6 * M_coord ^ 2 := by ring
    have hPic_n : ‖Pic n‖ ≤ 7 * M_coord ^ 2 := by
      calc ‖ContinuousLinearMap.id ℝ X - Piu n‖
          ≤ ‖ContinuousLinearMap.id ℝ X‖ + ‖Piu n‖ := norm_sub_le _ _
        _ ≤ 1 + 6 * M_coord ^ 2 := add_le_add ContinuousLinearMap.norm_id_le hPiu_n
        _ ≤ 7 * M_coord ^ 2 := by nlinarith
    exact ⟨by nlinarith, by nlinarith, by nlinarith, hPic_n⟩
  · intro n hn
    exact ⟨(hξ_step n hn).1, (hξ_step n hn).2.1, (hξ_step n hn).2.2.1⟩
  · intro j k hjk hkN
    let Dprod : ℕ → (F →L[ℝ] F) :=
      Nat.rec (ContinuousLinearMap.id ℝ F) (fun d Pd => (Dn (j + d)).comp Pd)
    have hDprod : ∀ d : ℕ, j + d ≤ N →
        (U (t (j + d)) (t j)).comp (Ic j) = (Ic (j + d)).comp (Dprod d) ∧
        ‖Dprod d‖ ≤ Real.exp (a' * ((d : ℝ) * L)) := by
      intro d
      induction d with
      | zero =>
        intro hjN
        simp only [Nat.add_zero, Nat.cast_zero, zero_mul, mul_zero, Real.exp_zero]
        refine ⟨?_, ContinuousLinearMap.norm_id_le⟩
        change (U (t j) (t j)).comp (Ic j) = (Ic j).comp (ContinuousLinearMap.id ℝ F)
        rw [hU_id j hjN, ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_id]
      | succ d ih =>
        intro hjd1
        have hjd_lt : j + d < N := hjd1
        obtain ⟨hih_eq, hih_norm⟩ := ih hjd_lt.le
        obtain ⟨hc_eq, hc_norm⟩ := hCenter_step (j + d) hjd_lt
        have hcoc := hU_coc j (j + d) (Nat.le_add_right j d) hjd_lt
        refine ⟨?_, ?_⟩
        · change (U (t (j + d + 1)) (t j)).comp (Ic j) =
            (Ic (j + d + 1)).comp ((Dn (j + d)).comp (Dprod d))
          rw [← hcoc, ContinuousLinearMap.comp_assoc, hih_eq,
            ← ContinuousLinearMap.comp_assoc, hc_eq, ContinuousLinearMap.comp_assoc]
        · calc ‖(Dn (j + d)).comp (Dprod d)‖
              ≤ ‖Dn (j + d)‖ * ‖Dprod d‖ := (Dn (j + d)).opNorm_comp_le (Dprod d)
            _ ≤ Real.exp (a' * L) * Real.exp (a' * ((d : ℝ) * L)) :=
                mul_le_mul hc_norm hih_norm (norm_nonneg _) (Real.exp_pos _).le
            _ = Real.exp (a' * L + a' * ((d : ℝ) * L)) := (Real.exp_add _ _).symm
            _ = Real.exp (a' * (((d + 1 : ℕ) : ℝ) * L)) := by congr 1; push_cast; ring
    have hjk_add : j + (k - j) = k := Nat.add_sub_of_le hjk
    have hjdN : j + (k - j) ≤ N := by rw [hjk_add]; exact hkN
    obtain ⟨hD_eq, hD_norm⟩ := hDprod (k - j) hjdN
    rw [hjk_add] at hD_eq
    have hPic_j : Pic j = (Ic j).comp (Pc j) :=
      genProjC_eq_id_sub_genProjU (ι j) (π j) (κ j) (ρ j)
        (ξ j) (ζ j) (W j) (hdec j (hjk.trans hkN)) (hW_spec j).2.1
    have hUPic : (U (t k) (t j)).comp (Pic j) = (Ic k).comp ((Dprod (k - j)).comp (Pc j)) := by
      rw [hPic_j, ← ContinuousLinearMap.comp_assoc, hD_eq, ContinuousLinearMap.comp_assoc]
    have ht_diff : ((k - j : ℕ) : ℝ) * L = t k - t j := by
      dsimp [t]; rw [Nat.cast_sub hjk, sub_mul]
    rw [ht_diff] at hD_norm
    change ‖(U (t k) (t j)).comp (Pic j)‖ ≤ (7 * M_coord ^ 2) * Real.exp (a' * (t k - t j))
    rw [hUPic]
    have hDPc : ‖(Dprod (k - j)).comp (Pc j)‖ ≤ Real.exp (a' * (t k - t j)) * (3 * M_coord) :=
      ((Dprod (k - j)).opNorm_comp_le (Pc j)).trans
        (mul_le_mul hD_norm (hPc_norm j (hjk.trans hkN)) (norm_nonneg _) (Real.exp_pos _).le)
    calc ‖(Ic k).comp ((Dprod (k - j)).comp (Pc j))‖
        ≤ ‖Ic k‖ * ‖(Dprod (k - j)).comp (Pc j)‖ := (Ic k).opNorm_comp_le _
      _ ≤ (2 * M_coord) * (Real.exp (a' * (t k - t j)) * (3 * M_coord)) :=
          mul_le_mul (hIc_norm k hkN) hDPc (norm_nonneg _) (by positivity)
      _ = (6 * M_coord ^ 2) * Real.exp (a' * (t k - t j)) := by ring
      _ ≤ (7 * M_coord ^ 2) * Real.exp (a' * (t k - t j)) :=
          mul_le_mul_of_nonneg_right (by nlinarith) (Real.exp_pos _).le
  · intro j k hjk hkN
    let Mprod : ℕ → (E →L[ℝ] E) :=
      Nat.rec (ContinuousLinearMap.id ℝ E) (fun d Md => Md.comp (Mn (j + d)))
    have hMprod : ∀ d : ℕ, j + d ≤ N →
        (U (t (j + d)) (t j)).comp ((Iu j).comp (Mprod d)) = Iu (j + d) ∧
        (Mprod d).comp ((Pu (j + d)).comp (U (t (j + d)) (t j))) = Pu j ∧
        ‖Mprod d‖ ≤ Real.exp (-b' * ((d : ℝ) * L)) := by
      intro d
      induction d with
      | zero =>
        intro hjN
        simp only [Nat.add_zero, Nat.cast_zero, zero_mul, mul_zero, Real.exp_zero]
        refine ⟨?_, ?_, ContinuousLinearMap.norm_id_le⟩
        · change (U (t j) (t j)).comp ((Iu j).comp (ContinuousLinearMap.id ℝ E)) = Iu j
          rw [hU_id j hjN, ContinuousLinearMap.comp_id, ContinuousLinearMap.id_comp]
        · change (ContinuousLinearMap.id ℝ E).comp ((Pu j).comp (U (t j) (t j))) = Pu j
          rw [hU_id j hjN, ContinuousLinearMap.comp_id, ContinuousLinearMap.id_comp]
      | succ d ih =>
        intro hjd1
        have hjd_lt : j + d < N := hjd1
        obtain ⟨hih1, hih2, hih_norm⟩ := ih hjd_lt.le
        obtain ⟨hfwd_d, hbwd_d⟩ := hIntertwine (j + d) hjd_lt
        obtain ⟨hMB_d, hBM_d, hMn_norm, _⟩ := hξ_step (j + d) hjd_lt
        have hcoc := hU_coc j (j + d) (Nat.le_add_right j d) hjd_lt
        refine ⟨?_, ?_, ?_⟩
        · change (U (t (j + d + 1)) (t j)).comp ((Iu j).comp ((Mprod d).comp (Mn (j + d)))) =
            Iu (j + d + 1)
          have h1 : (U (t (j + d + 1)) (t j)).comp
              ((Iu j).comp ((Mprod d).comp (Mn (j + d)))) =
              (U (t (j + d + 1)) (t (j + d))).comp
                (((U (t (j + d)) (t j)).comp ((Iu j).comp (Mprod d))).comp (Mn (j + d))) := by
            rw [← hcoc]; ext1 x; rfl
          have hBM_comp : (Bn (j + d)).comp (Mn (j + d)) = ContinuousLinearMap.id ℝ E := hBM_d
          rw [h1, hih1, ← ContinuousLinearMap.comp_assoc, hfwd_d,
            ContinuousLinearMap.comp_assoc, hBM_comp, ContinuousLinearMap.comp_id]
        · change ((Mprod d).comp (Mn (j + d))).comp
              ((Pu (j + d + 1)).comp (U (t (j + d + 1)) (t j))) = Pu j
          have h2 : ((Mprod d).comp (Mn (j + d))).comp
              ((Pu (j + d + 1)).comp (U (t (j + d + 1)) (t j))) =
              (Mprod d).comp (((Mn (j + d)).comp
                ((Pu (j + d + 1)).comp (U (t (j + d + 1)) (t (j + d))))).comp
                  (U (t (j + d)) (t j))) := by
            rw [← hcoc]; ext1 x; rfl
          have hMB_comp : (Mn (j + d)).comp (Bn (j + d)) = ContinuousLinearMap.id ℝ E := hMB_d
          rw [h2, hbwd_d, ← ContinuousLinearMap.comp_assoc (Mn (j + d)),
            hMB_comp, ContinuousLinearMap.id_comp, hih2]
        · calc ‖(Mprod d).comp (Mn (j + d))‖
              ≤ ‖Mprod d‖ * ‖Mn (j + d)‖ := (Mprod d).opNorm_comp_le (Mn (j + d))
            _ ≤ Real.exp (-b' * ((d : ℝ) * L)) * Real.exp (-b' * L) :=
                mul_le_mul hih_norm hMn_norm (norm_nonneg _) (Real.exp_pos _).le
            _ = Real.exp (-b' * ((d : ℝ) * L) + -b' * L) := (Real.exp_add _ _).symm
            _ = Real.exp (-b' * (((d + 1 : ℕ) : ℝ) * L)) := by congr 1; push_cast; ring
    have hjk_add : j + (k - j) = k := Nat.add_sub_of_le hjk
    have hjdN : j + (k - j) ≤ N := by rw [hjk_add]; exact hkN
    obtain ⟨hM1, hM2, hM_norm⟩ := hMprod (k - j) hjdN
    rw [hjk_add] at hM1 hM2
    have ht_diff : ((k - j : ℕ) : ℝ) * L = t k - t j := by
      dsimp [t]; rw [Nat.cast_sub hjk, sub_mul]
    rw [ht_diff] at hM_norm
    refine ⟨Mprod (k - j), hM1, hM2, hM_norm, ?_⟩
    have hMPu : ‖(Mprod (k - j)).comp (Pu k)‖ ≤
        Real.exp (-b' * (t k - t j)) * (3 * M_coord) :=
      ((Mprod (k - j)).opNorm_comp_le (Pu k)).trans
        (mul_le_mul hM_norm (hPu_norm k hkN) (norm_nonneg _) (Real.exp_pos _).le)
    calc ‖(Iu j).comp ((Mprod (k - j)).comp (Pu k))‖
        ≤ ‖Iu j‖ * ‖(Mprod (k - j)).comp (Pu k)‖ := (Iu j).opNorm_comp_le _
      _ ≤ (2 * M_coord) * (Real.exp (-b' * (t k - t j)) * (3 * M_coord)) :=
          mul_le_mul (hIu_norm j (hjk.trans hkN)) hMPu (norm_nonneg _) (by positivity)
      _ = (6 * M_coord ^ 2) * Real.exp (-b' * (t k - t j)) := by ring
      _ ≤ (7 * M_coord ^ 2) * Real.exp (-b' * (t k - t j)) :=
          mul_le_mul_of_nonneg_right (by nlinarith) (Real.exp_pos _).le

end AbstractGraph

/-! ## 4. Main theorem: `dichotomyProjections_of` (`PartII-b:F3`) -/

/-- **Main theorem (`PartII-b:F3`)**: `BlockDichotomy` implies `DichotomyProjections`. -/
theorem dichotomyProjections_of (hBD : UnforcedLeray.Short.IIb.BlockDichotomy) :
    UnforcedLeray.Short.IIb.DichotomyProjections := by
  intro m hm Sig lam q hSig hEig a' b' ha' hab' hb' dm dp hdm
  obtain ⟨L₀, M_coord, hL₀, hM_coord, hBD_η⟩ :=
    hBD m hm Sig lam q hSig hEig a' b' ha' hab' hb' dm dp hdm
  obtain ⟨ν₀, hν₀, hBD_p⟩ := hBD_η (1 / 2) (by positivity)
  set C_proj : ℝ := 7 * M_coord ^ 2
  have hC_proj : 1 ≤ C_proj := by dsimp [C_proj]; nlinarith
  refine ⟨L₀, C_proj, ν₀, hL₀, hC_proj, hν₀, ?_⟩
  intro p d hbg hν hAge hMode
  obtain ⟨U, B, hU, hB⟩ := hBD_p p d hbg hν hAge hMode
  have hL_nn : 0 ≤ B.L := by linarith [hB.L_bounds.1]
  have ht_nonneg : ∀ n : ℕ, 0 ≤ B.t n := by
    intro n; unfold BlockFactorizationData.t; positivity
  have ht_mono : ∀ {j k : ℕ}, j ≤ k → B.t j ≤ B.t k := by
    intro j k hjk; unfold BlockFactorizationData.t
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hjk) hL_nn
  have ht_le_H : ∀ {n : ℕ}, n ≤ B.N → B.t n ≤ p.H := by
    intro n hn
    calc B.t n ≤ B.t B.N := ht_mono hn
      _ = p.H := hB.total_age
  haveI : CompleteSpace B.F := B.complete_F
  obtain ⟨Iu, Pu, Piu, Pic, Bn, Mn, hIu0, hproj, hnorms, hinv, hinter, hfwd_c, hbwd_u⟩ :=
    @gen_exists_sequences (Xmc p.c m) E2 B.F _ _ _ _ _ _ _ _
      B.N B.L a' b' M_coord ha' hab' hL_nn hM_coord U B.ι B.π B.κ B.ρ B.ainv
      (fun n hn => hU.id_self (B.t n) ⟨ht_nonneg n, ht_le_H hn⟩)
      (fun j k hjk hk => hU.comp_cocycle (B.t j) (B.t k) (B.t (k + 1))
        (ht_nonneg j) (ht_mono hjk) (ht_mono (Nat.le_succ k)) (ht_le_H hk))
      hB.proj_id_E hB.proj_id_F hB.proj_orth_EF hB.proj_orth_FE hB.decomp_id hB.coord_norm
      hB.block_inv_left hB.block_inv_right hB.block_ainv_norm
      hB.block_d_norm hB.block_b_norm hB.block_c_norm
  let D : DiscreteDichotomyData m p U :=
    { N := B.N
      L := B.L
      Iu := Iu
      Pu := Pu
      Piu := Piu
      Pic := Pic
      Bn := Bn
      Mn := Mn }
  refine ⟨U, D, hU, ?_⟩
  refine
    { N_pos := hB.N_pos
      L_bounds := hB.L_bounds
      total_age := hB.total_age
      entrance_eq := fun α => by
        change (Iu 0 α : B0579.Plane → ℝ) =ᵐ[B0579.cellMeasure p.c m] entranceVorticityComb p α
        rw [hIu0]
        exact hB.entrance_eq α
      zeroCirc_Iu := ?_
      proj_rel := hproj
      norm_bounds := hnorms
      short_prop_norm := fun s r hs hsr hrH hrsL => by
        have hrs2L₀ : r - s ≤ 2 * L₀ := hrsL.trans hB.L_bounds.2
        exact (hB.short_prop_norm s r hs hsr hrH hrs2L₀).trans (by dsimp [C_proj]; nlinarith)
      block_inv := hinv
      block_intertwine := hinter
      forward_center_bound := hfwd_c
      backward_unstable_bound := hbwd_u }
  intro n hn α
  induction n generalizing α with
  | zero =>
    change HasZeroCirculationR p.c (Iu 0 α)
    rw [hIu0]
    exact hB.zeroCirc_ι 0 (Nat.zero_le _) α
  | succ n ih =>
    have hn_lt : n < B.N := hn
    have hBM : (Bn n).comp (Mn n) = ContinuousLinearMap.id ℝ E2 := (hinv n hn_lt).2.1
    have hstep : Iu (n + 1) α = U (B.t (n + 1)) (B.t n) (Iu n (Mn n α)) := by
      have hf := (hinter n hn_lt).1
      have hf_x := DFunLike.congr_fun hf (Mn n α)
      simp only [ContinuousLinearMap.comp_apply] at hf_x
      have hBM_x := DFunLike.congr_fun hBM α
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at hBM_x
      unfold BlockFactorizationData.t
      rw [hf_x, hBM_x]
    change HasZeroCirculationR p.c (Iu (n + 1) α)
    rw [hstep]
    exact hU.zeroCirc (B.t n) (B.t (n + 1)) (ht_nonneg n) (ht_mono (Nat.le_succ n))
      (ht_le_H hn) (Iu n (Mn n α)) (ih hn_lt.le (Mn n α))

end UnforcedLeray.Short.IIb

end
