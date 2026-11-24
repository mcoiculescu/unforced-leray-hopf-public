import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_6

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- Derivatives of a function of the transverse variable only: the `j`-th Fréchet derivative of
`x ↦ G x.2` is bounded by the `j`-th scalar derivative of `G`. -/
theorem norm_iteratedFDeriv_snd_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {G : ℝ → E} (hG : ContDiff ℝ ∞ G) (j : ℕ) (x : ℝ × ℝ) :
    ‖iteratedFDeriv ℝ j (fun y : ℝ × ℝ => G y.2) x‖ ≤ ‖iteratedDeriv j G x.2‖ := by
  have hc : (fun y : ℝ × ℝ => G y.2) = G ∘ (ContinuousLinearMap.snd ℝ ℝ ℝ) := rfl
  rw [hc, ContinuousLinearMap.iteratedFDeriv_comp_right _ hG x (WithTop.coe_le_coe.2 le_top)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have hn := norm_iteratedFDeriv_eq_norm_iteratedDeriv (𝕜 := ℝ) (f := G) (n := j) (x := x.2)
  have hprod : ∏ _i : Fin j, ‖(ContinuousLinearMap.snd ℝ ℝ ℝ : ℝ × ℝ →L[ℝ] ℝ)‖ ≤ 1 :=
    Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun _ _ => ContinuousLinearMap.norm_snd_le ℝ ℝ ℝ)
  calc ‖iteratedFDeriv ℝ j G (ContinuousLinearMap.snd ℝ ℝ ℝ x)‖ *
        ∏ _i : Fin j, ‖(ContinuousLinearMap.snd ℝ ℝ ℝ : ℝ × ℝ →L[ℝ] ℝ)‖
      ≤ ‖iteratedFDeriv ℝ j G (ContinuousLinearMap.snd ℝ ℝ ℝ x)‖ * 1 :=
        mul_le_mul_of_nonneg_left hprod (norm_nonneg _)
    _ = ‖iteratedDeriv j G x.2‖ := by rw [mul_one]; exact hn

theorem meanJetWeighted_of (hV : MeanVecFormula) (hB : MeanStreamJetBound) :
    MeanJetWeighted := by
  intro k j
  obtain ⟨C, N, ν₀, hν₀, hbd⟩ := hB k (j + 1)
  refine ⟨C * ‖UnforcedLeray.Train.toVec (1, 0)‖, N, ν₀, hν₀, ?_⟩
  intro ν hν tr htr s hs
  have hν0 : 0 < ν := hν.1
  have hc : 0 < ν ^ (-2 : ℝ) := Real.rpow_pos_of_pos hν0 _
  obtain ⟨hSsm, hform⟩ := hV ν (ν ^ (-2 : ℝ)) hν0 hc tr htr s hs
  have hgeq : ∀ η : ℝ, UnforcedLeray.Short.PartI.hmean (ν ^ (-2 : ℝ)) (tr.v s) η =
      (-deriv (fun e => UnforcedLeray.Short.PartI.meanStream tr s e) η) •
        UnforcedLeray.Train.toVec (1, 0) := by
    intro η
    rw [hform η, ← UnforcedLeray.Train.toVec_smul]
    congr 1
    ext <;> simp
  have hdS : ContDiff ℝ ∞ (deriv (fun e => UnforcedLeray.Short.PartI.meanStream tr s e)) :=
    (contDiff_infty_iff_deriv.1 hSsm).2
  have hg : ContDiff ℝ ∞ (fun η : ℝ =>
      (-deriv (fun e => UnforcedLeray.Short.PartI.meanStream tr s e) η) •
        UnforcedLeray.Train.toVec (1, 0)) :=
    (hdS.neg).smul contDiff_const
  have hfun : (fun x : ℝ × ℝ => UnforcedLeray.Short.PartI.hmean (ν ^ (-2 : ℝ)) (tr.v s) x.2) =
      fun x : ℝ × ℝ =>
        (-deriv (fun e => UnforcedLeray.Short.PartI.meanStream tr s e) x.2) •
          UnforcedLeray.Train.toVec (1, 0) :=
    funext fun x => hgeq x.2
  rw [hfun]
  refine ⟨hg.comp contDiff_snd, fun x => ?_⟩
  have hA := norm_iteratedFDeriv_snd_le hg j x
  have hdiff : iteratedDeriv j (fun η : ℝ =>
      (-deriv (fun e => UnforcedLeray.Short.PartI.meanStream tr s e) η) •
        UnforcedLeray.Train.toVec (1, 0)) x.2 =
      (-(iteratedDeriv (j + 1) (fun e => UnforcedLeray.Short.PartI.meanStream tr s e) x.2)) •
        UnforcedLeray.Train.toVec (1, 0) := by
    have hsm : ContDiffAt ℝ j (fun η : ℝ =>
        -deriv (fun e => UnforcedLeray.Short.PartI.meanStream tr s e) η) x.2 :=
      (hdS.neg.contDiffAt).of_le (WithTop.coe_le_coe.2 le_top)
    have h1 := iteratedDeriv_smul_const (𝕜 := ℝ) (n := j) (x := x.2) hsm
      (UnforcedLeray.Train.toVec (1, 0))
    rw [h1]
    congr 1
    have h2 : iteratedDeriv j (fun η : ℝ =>
        -deriv (fun e => UnforcedLeray.Short.PartI.meanStream tr s e) η) x.2 =
        -(iteratedDeriv j (deriv (fun e => UnforcedLeray.Short.PartI.meanStream tr s e)) x.2) :=
      iteratedDeriv_neg j (deriv (fun e => UnforcedLeray.Short.PartI.meanStream tr s e)) x.2
    rw [h2, ← iteratedDeriv_succ']
  have hnorm : ‖iteratedDeriv j (fun η : ℝ =>
      (-deriv (fun e => UnforcedLeray.Short.PartI.meanStream tr s e) η) •
        UnforcedLeray.Train.toVec (1, 0)) x.2‖ =
      |iteratedDeriv (j + 1) (fun e => UnforcedLeray.Short.PartI.meanStream tr s e) x.2| *
        ‖UnforcedLeray.Train.toVec (1, 0)‖ := by
    rw [hdiff, norm_smul, Real.norm_eq_abs, abs_neg]
  have hB' := hbd ν hν tr htr s hs x.2
  calc (1 + x.2 ^ 2) ^ k * ‖iteratedFDeriv ℝ j (fun y : ℝ × ℝ =>
          (-deriv (fun e => UnforcedLeray.Short.PartI.meanStream tr s e) y.2) •
            UnforcedLeray.Train.toVec (1, 0)) x‖
      ≤ (1 + x.2 ^ 2) ^ k * (|iteratedDeriv (j + 1)
          (fun e => UnforcedLeray.Short.PartI.meanStream tr s e) x.2| *
            ‖UnforcedLeray.Train.toVec (1, 0)‖) :=
        mul_le_mul_of_nonneg_left (hA.trans hnorm.le) (by positivity)
    _ = ‖UnforcedLeray.Train.toVec (1, 0)‖ * ((1 + x.2 ^ 2) ^ k *
          |iteratedDeriv (j + 1) (fun e => UnforcedLeray.Short.PartI.meanStream tr s e) x.2|) := by
        ring
    _ ≤ ‖UnforcedLeray.Train.toVec (1, 0)‖ * (C * ν⁻¹ ^ N * (1 + s) ^ N) :=
        mul_le_mul_of_nonneg_left hB' (norm_nonneg _)
    _ = C * ‖UnforcedLeray.Train.toVec (1, 0)‖ * ν⁻¹ ^ N * (1 + s) ^ N := by ring

end UnforcedLeray.Short.IIIa
