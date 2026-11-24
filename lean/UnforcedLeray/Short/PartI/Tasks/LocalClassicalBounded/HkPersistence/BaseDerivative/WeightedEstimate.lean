import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.HkPersistence.BaseDerivative.WeightedEstimate.Pointwise

/-!
# Part I, task `PartI:T02/1/2/4/1`: the weighted Volterra estimate for `bilDuhamel`

Target `bilWeightedEstimate : BilWeightedEstimate` (`Short/PartI/Sub/T02_1_2_4.lean`).
Source of record: `the November 2 reference manuscript`, lines 261-288
(the Duhamel smoothing estimate for the mild `H³` solution).

Proof outline:

* `bilWE_bilDuhamel_le` (pointwise form): if the stress `r ↦ a(r) ⊗ b(r)` satisfies
  `‖·‖ ≤ (1536 α β') e^{λ r}` on `(0,t)`, then `‖bilDuhamel a b t‖` is bounded by
  `(2 · 1536 ‖toVecL‖ ν^{-1/2} + 1) / √λ · α β' e^{λ t}`.  It uses the integrand and kernel
  bounds of `Pointwise.lean` and `Kernel.lean`, with `(1/λ)^{1/2} = 1/√λ`.
* `bilWeightedEstimate`: the constant `C₀ = 2 · 1536 ‖toVecL‖ ν^{-1/2} + 1` (depending on `ν`
  only) works for both conjuncts.  The first conjunct uses `‖a r‖ ≤ α e^{λ r}`, `‖b r‖ ≤ β'`,
  and the second exchanges the roles of `a` and `b`, using `‖tensorH3Bilinear u v‖ ≤ 1536 ‖u‖‖v‖`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec toVec)
open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.TrainB
open UnforcedLeray.HeatCylinder

/-- The pointwise weighted bound for `bilDuhamel` from a weighted bound on the tensor stress
`bilStressPath` on `(0,t)`. -/
theorem bilWE_bilDuhamel_le {c ν T : ℝ} (hc : 0 < c) (hc1 : 1 ≤ c) (hν : 0 < ν) (hT : 0 < T)
    (a b : MPath c T) (lam α β' : ℝ) (hlam : 0 < lam) (hα : 0 ≤ α) (hβ : 0 ≤ β')
    (t : Icc (0 : ℝ) T)
    (hstress : ∀ r ∈ Ioo (0 : ℝ) (t : ℝ),
      ‖bilStressPath hc1 (extendCompactPath hT.le a) (extendCompactPath hT.le b) r‖ ≤
        (1536 * α * β') * Real.exp (lam * r)) :
    ‖bilDuhamel hc hc1 hν hT.le a b t‖ ≤
      (2 * (1536 * ‖(UnforcedLeray.Train.toVecL :
          UnforcedLeray.GaussianVortex.Plane →L[ℝ] UnforcedLeray.Train.Vec)‖) *
          ν ^ (-(1 / 2 : ℝ)) + 1) / Real.sqrt lam * α * β' * Real.exp (lam * (t : ℝ)) := by
  have hval : bilDuhamel hc hc1 hν hT.le a b t =
      -(projectedHeatDuhamelIntegral (ν := ν) hc
        (bilStressPath hc1 (extendCompactPath hT.le a) (extendCompactPath hT.le b)) (t : ℝ)) :=
    rfl
  rw [hval, norm_neg]
  have hM : (0 : ℝ) ≤ 1536 * α * β' := mul_nonneg (mul_nonneg (by norm_num) hα) hβ
  have hmain := BilWE.norm_projectedHeatDuhamelIntegral_exp_le hc hν hlam t.2.1 hM
    (bilStressPath hc1 (extendCompactPath hT.le a) (extendCompactPath hT.le b)) hstress
  refine hmain.trans ?_
  have hs : 0 < Real.sqrt lam := Real.sqrt_pos.2 hlam
  have hP : 0 ≤ α * β' * Real.exp (lam * (t : ℝ)) :=
    mul_nonneg (mul_nonneg hα hβ) (Real.exp_pos _).le
  have hKnn : 0 ≤ ‖(UnforcedLeray.Train.toVecL :
      UnforcedLeray.GaussianVortex.Plane →L[ℝ] UnforcedLeray.Train.Vec)‖ := norm_nonneg _
  have hν' : 0 ≤ ν ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hν.le _
  have hX : 0 ≤ 2 * (1536 * ‖(UnforcedLeray.Train.toVecL :
      UnforcedLeray.GaussianVortex.Plane →L[ℝ] UnforcedLeray.Train.Vec)‖) *
      ν ^ (-(1 / 2 : ℝ)) := by
    have h1 : 0 ≤ 2 * (1536 * ‖(UnforcedLeray.Train.toVecL :
        UnforcedLeray.GaussianVortex.Plane →L[ℝ] UnforcedLeray.Train.Vec)‖) :=
      mul_nonneg (by norm_num) (mul_nonneg (by norm_num) hKnn)
    exact mul_nonneg h1 hν'
  calc _ = (2 * (1536 * ‖(UnforcedLeray.Train.toVecL :
          UnforcedLeray.GaussianVortex.Plane →L[ℝ] UnforcedLeray.Train.Vec)‖) *
          ν ^ (-(1 / 2 : ℝ))) * (α * β' * Real.exp (lam * (t : ℝ))) / Real.sqrt lam := by
        ring
    _ ≤ ((2 * (1536 * ‖(UnforcedLeray.Train.toVecL :
          UnforcedLeray.GaussianVortex.Plane →L[ℝ] UnforcedLeray.Train.Vec)‖) *
          ν ^ (-(1 / 2 : ℝ))) + 1) * (α * β' * Real.exp (lam * (t : ℝ))) / Real.sqrt lam := by
        refine div_le_div_of_nonneg_right ?_ hs.le
        exact mul_le_mul_of_nonneg_right (by linarith) hP
    _ = (2 * (1536 * ‖(UnforcedLeray.Train.toVecL :
          UnforcedLeray.GaussianVortex.Plane →L[ℝ] UnforcedLeray.Train.Vec)‖) *
          ν ^ (-(1 / 2 : ℝ)) + 1) / Real.sqrt lam * α * β' * Real.exp (lam * (t : ℝ)) := by
        ring

/-- **Task `PartI:T02/1/2/4/1`: the weighted Volterra estimate for `bilDuhamel`.** The constant
`C₀ = 2 · 1536 ‖toVecL‖ ν^{-1/2} + 1` depends only on `ν` (and the fixed map `toVecL`). -/
theorem bilWeightedEstimate : BilWeightedEstimate := by
  intro ν c hν hc hc1
  have hKnn : 0 ≤ ‖(UnforcedLeray.Train.toVecL :
      UnforcedLeray.GaussianVortex.Plane →L[ℝ] UnforcedLeray.Train.Vec)‖ := norm_nonneg _
  have hX : 0 ≤ 2 * (1536 * ‖(UnforcedLeray.Train.toVecL :
      UnforcedLeray.GaussianVortex.Plane →L[ℝ] UnforcedLeray.Train.Vec)‖) *
      ν ^ (-(1 / 2 : ℝ)) := by
    have hν' : 0 ≤ ν ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hν.le _
    have h1 : 0 ≤ 2 * (1536 * ‖(UnforcedLeray.Train.toVecL :
        UnforcedLeray.GaussianVortex.Plane →L[ℝ] UnforcedLeray.Train.Vec)‖) :=
      mul_nonneg (by norm_num) (mul_nonneg (by norm_num) hKnn)
    exact mul_nonneg h1 hν'
  refine ⟨2 * (1536 * ‖(UnforcedLeray.Train.toVecL :
      UnforcedLeray.GaussianVortex.Plane →L[ℝ] UnforcedLeray.Train.Vec)‖) *
      ν ^ (-(1 / 2 : ℝ)) + 1, by linarith, ?_, ?_⟩
  · intro T hT a b lam α β' hlam hα hβ ha hb t
    apply bilWE_bilDuhamel_le hc hc1 hν hT a b lam α β' hlam hα hβ t
    intro r hr
    have hrI : r ∈ Icc (0 : ℝ) T := ⟨hr.1.le, hr.2.le.trans t.2.2⟩
    have hA : ‖extendCompactPath hT.le a r‖ ≤ α * Real.exp (lam * r) := by
      rw [extendCompactPath_apply_of_mem hT.le a hrI]
      exact ha ⟨r, hrI⟩
    have hB : ‖extendCompactPath hT.le b r‖ ≤ β' := by
      rw [extendCompactPath_apply_of_mem hT.le b hrI]
      exact hb ⟨r, hrI⟩
    calc ‖bilStressPath hc1 (extendCompactPath hT.le a) (extendCompactPath hT.le b) r‖
        = ‖tensorH3Bilinear hc1 (extendCompactPath hT.le a r)
            (extendCompactPath hT.le b r)‖ := rfl
      _ ≤ 1536 * ‖extendCompactPath hT.le a r‖ * ‖extendCompactPath hT.le b r‖ :=
          norm_tensorH3Bilinear_apply_le hc1 _ _
      _ ≤ 1536 * (α * Real.exp (lam * r)) * β' := by gcongr
      _ = (1536 * α * β') * Real.exp (lam * r) := by ring
  · intro T hT a b lam α β' hlam hα hβ ha hb t
    apply bilWE_bilDuhamel_le hc hc1 hν hT a b lam α β' hlam hα hβ t
    intro r hr
    have hrI : r ∈ Icc (0 : ℝ) T := ⟨hr.1.le, hr.2.le.trans t.2.2⟩
    have hA : ‖extendCompactPath hT.le a r‖ ≤ β' := by
      rw [extendCompactPath_apply_of_mem hT.le a hrI]
      exact ha ⟨r, hrI⟩
    have hB : ‖extendCompactPath hT.le b r‖ ≤ α * Real.exp (lam * r) := by
      rw [extendCompactPath_apply_of_mem hT.le b hrI]
      exact hb ⟨r, hrI⟩
    calc ‖bilStressPath hc1 (extendCompactPath hT.le a) (extendCompactPath hT.le b) r‖
        = ‖tensorH3Bilinear hc1 (extendCompactPath hT.le a r)
            (extendCompactPath hT.le b r)‖ := rfl
      _ ≤ 1536 * ‖extendCompactPath hT.le a r‖ * ‖extendCompactPath hT.le b r‖ :=
          norm_tensorH3Bilinear_apply_le hc1 _ _
      _ ≤ 1536 * β' * (α * Real.exp (lam * r)) := by gcongr
      _ = (1536 * α * β') * Real.exp (lam * r) := by ring

end UnforcedLeray.Short.PartI
