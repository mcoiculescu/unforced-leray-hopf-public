import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_3_1_1_org.Glue
import UnforcedLeray.Short.PartIIIa.Clock.FreeMoving.Rate.FmrTrainClose

/-!
# Part III-a, organizer item `PartIII-a:T21/c3/3/1/1/5/thread`: `TrainClose` threaded through the
consumers of the free-rate Duhamel leaf

Source of record: `the November 2 reference manuscript` (SP), lines 2085-2090
(train comparison on `s ≤ Σ/ν`, `ν` small), 2919-2925, 2937-2958, 2982-2988.

The free cylinder flows behind the free-rate Duhamel leaf exist only for trains that are `δ = 1`
close to the periodized Gaussian on the ages `s ≤ Σ/ν`, `Σ = (ν b)⁻¹` (`TrainClose tr (ν b)⁻¹ 1`),
which `FmrTrainClose` provides for `ν ≤ ν₀(b)` (SP 2085-2090).  `ComplFreeRateDuhamelTC κ`
(`Sub/PartIII-a_T21_c3_3_1_1_org/Glue.lean`) is the leaf with that hypothesis.  This file carries it
through the Gronwall step (`WeakFlowProjectedGronwallTC`, the statement of
`WeakFlowDuhamelSub.WeakFlowProjectedGronwall` with the same added hypothesis) and into
`WeakFlowComplPerturbDuhamel κ`, whose `∃ ν₀(b)` is shrunk by the threshold of `FmrTrainClose`
at the same `b`.  The target `WeakFlowComplPerturbDuhamel κ` is unchanged.

The task `PartIII-a:T21/c3/3/1/1` (`WeakFlowDuhamel/FreeRateAssembly.lean`) composes
`weakFlowComplPerturbDuhamel_of_leavesTC` with the five leaf theorems.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Blueprint.Planar
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

open FrameShortBlockSub ComplCouplingSub PerturbDuhamelSub WeakFlowDuhamelSub ComplFreeRateSub

namespace WeakFlowDuhamelTC

/-- **`WeakFlowProjectedGronwall` under the train comparison (SP 2085-2090, 2919-2925, 2937-2958,
2982-2988)**: the statement of `WeakFlowDuhamelSub.WeakFlowProjectedGronwall κ`
(`WeakFlowDuhamel.lean`, body copied unchanged) with the hypothesis
`TrainClose tr (ν b)⁻¹ 1` added after `IsBUCTrain tr`, as in `ComplFreeRateDuhamelTC κ`. -/
def WeakFlowProjectedGronwallTC (κ : PlanarFrameKernels) : Prop :=
  IsSeedKernels κ →
  ∀ (P : PlanarData), IsPlanarReference P →
  ∀ m : ℝ, 8 < m →
  ∀ K C_loc C_H0 b : ℝ, 0 ≤ C_loc → 0 ≤ C_H0 → 1 ≤ b →
  ∀ ν : ℝ, ∀ (hν : 0 < ν), ∀ hF : PerFrameFacts κ ν m b K,
    ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
      UnforcedLeray.Short.PartI.IsBUCTrain tr →
      UnforcedLeray.Short.IIb.TrainClose tr (ν * b)⁻¹ 1 →
      ∀ t₁ t₂ : ℝ, 0 ≤ t₁ → t₁ ≤ t₂ → b ≤ clockTheta ν t₂ →
        ∀ f w u, IsLinearisedFlow ν (ν ^ (-2 : ℝ)) m tr t₁ f w u →
          HasZeroCirculation (ν ^ (-2 : ℝ)) f →
          let F := periodizedFrame κ ν m b K hν hF
          let μ_raw := normGrowthConst m + 1 + (C_loc + C_H0)
          (∀ s₁ s₂ : ℝ, t₁ ≤ s₁ → s₁ ≤ s₂ → s₂ ≤ t₂ →
            ∀ f₀ : B0579.Plane → ℝ, B0579.IsCylTest (ν ^ (-2 : ℝ)) f₀ →
              ∀ ω₀ : ℝ → B0579.Plane → ℝ,
                UnforcedLeray.Short.IIb.IsFreeCylFlow m tr s₁ f₀ ω₀ →
                xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν s₂)) m
                    (JscaleInv (clockA ν s₂) (fun x => ((ω₀ s₂ x : ℝ) : ℂ))) ≤
                  ENNReal.ofReal
                      (Real.exp ((normGrowthConst m + 1) * (movingZ ν s₂ - movingZ ν s₁))) *
                    xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν s₁)) m
                      (JscaleInv (clockA ν s₁) (fun x => ((f₀ x : ℝ) : ℂ)))) →
          (∀ r ∈ Icc t₁ t₂, ∀ Φ : ℝ × ℝ → ℂ,
            let d := cellLen (ν ^ (-2 : ℝ)) (clockA ν r)
            MemLp Φ 2 (B0579.cellMeasure d (-m)) →
            ∃ (χ : ℝ × ℝ → ℂ) (gχ : Fin 2 → ℝ × ℝ → ℂ),
              (∀ j, HasWeakCellDerivC d j χ (gχ j)) ∧
              h1Norm d m χ gχ ≤ ENNReal.ofReal C_loc * xNorm d (-m) Φ ∧
              xNorm d (-m) χ ≤ ENNReal.ofReal C_loc * xNorm d (-m) Φ ∧
              ∀ ψ uψ, B0579.IsCylTest d ψ → IsKernelBiotSavart d ψ uψ →
                ∫ y in B0579.cell d, χ y * (ψ y : ℂ) =
                  ∫ y in B0579.cell d,
                    Φ y * ((uψ y 0 * B0579.pd 0 (movingTrainE tr r) y +
                      uψ y 1 * B0579.pd 1 (movingTrainE tr r) y : ℝ) : ℂ)) →
          (∀ r ∈ Icc t₁ t₂,
            xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m
                (complFiniteRankCoupling F r (movH0 κ tr r · (compl F w r))) ≤
              ENNReal.ofReal C_H0 *
                xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m (compl F w r)) →
          ∃ (H : ℝ≥0∞) (G : ℝ → ℝ≥0∞),
            xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν t₂)) m (compl F w t₂) ≤
              H + ∫⁻ r in Ioc t₁ t₂, G r ∧
            H ≤ ENNReal.ofReal (Real.exp (μ_raw * (movingZ ν t₂ - movingZ ν t₁))) *
              xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν t₁)) m (compl F w t₁) ∧
            ∀ r ∈ Ioc t₁ t₂,
              G r ≤
                ENNReal.ofReal
                    ((clockA ν r) ^ (-2 : ℝ) *
                      Real.exp (μ_raw * (movingZ ν t₂ - movingZ ν r))) *
                  (∑ j : Fin 2,
                    ENNReal.ofReal ‖ampl F w r j‖ *
                      xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m
                        (complModeForce κ P F tr r j))

/-- **Gronwall step under the train comparison** (`ComplFreeRateDuhamelTC κ →
WeakFlowProjectedGronwallTC κ`, SP 2919-2925, 2937-2958): the proof of
`WeakFlowDuhamelSub.weakFlowProjectedGronwall_of_freeRate` with `TrainClose` passed through. -/
theorem weakFlowProjectedGronwallTC_of_freeRate (κ : PlanarFrameKernels)
    (hA : ComplFreeRateDuhamelTC κ) : WeakFlowProjectedGronwallTC κ := by
  intro hSeed P hP m hm K C_loc C_H0 b hC_loc hC_H0 hb1 ν hν hF tr htr hTC t₁ t₂ ht₁ h12 hbt₂
    f w u hFlow hCirc F μ_raw hFree hLoc hH0
  obtain ⟨G, hGm, hGle, hMild⟩ := hA hSeed P hP m hm K C_loc C_H0 b hC_loc hC_H0 hb1 ν hν hF
    tr htr hTC t₁ t₂ ht₁ h12 hbt₂ f w u hFlow hCirc hFree hLoc hH0
  have hm0 : 0 ≤ m := by linarith
  obtain ⟨M, hM, hφM⟩ := exists_bound_xNorm_compl F hν hm0 ht₁ hbt₂ hFlow
  have hμ₀ : 0 ≤ normGrowthConst m + 1 := by
    have := normGrowthConst_nonneg hm0
    linarith
  have hC : 0 ≤ C_loc + C_H0 := add_nonneg hC_loc hC_H0
  set G' : ℝ → ℝ≥0∞ := hGm.mk G with hG'_def
  have hG'm : Measurable G' := hGm.measurable_mk
  have hGG' : G =ᵐ[volume.restrict (Ioc t₁ t₂)] G' := hGm.ae_eq_mk
  have hMild' : ∀ s ∈ Icc t₁ t₂,
      xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)) m (compl F w s) ≤
        ENNReal.ofReal (Real.exp ((normGrowthConst m + 1) * (movingZ ν s - movingZ ν t₁))) *
            xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν t₁)) m (compl F w t₁) +
          ∫⁻ r in Ioc t₁ s,
            ENNReal.ofReal ((clockA ν r) ^ (-2 : ℝ) *
                Real.exp ((normGrowthConst m + 1) * (movingZ ν s - movingZ ν r))) *
              (ENNReal.ofReal (C_loc + C_H0) *
                  xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m (compl F w r) + G' r) := by
    intro s hs
    refine (hMild s hs).trans (le_of_eq ?_)
    congr 1
    refine lintegral_congr_ae ?_
    filter_upwards [ae_restrict_of_ae_restrict_of_subset (Ioc_subset_Ioc_right hs.2) hGG']
      with r hr
    rw [hr]
  have hgr := WeakFlowGronwallSub.gronwall_movingZ hν ht₁ h12 hμ₀ hC hM hφM hG'm hMild'
  refine ⟨ENNReal.ofReal (Real.exp (μ_raw * (movingZ ν t₂ - movingZ ν t₁))) *
      xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν t₁)) m (compl F w t₁),
    fun r => ENNReal.ofReal ((clockA ν r) ^ (-2 : ℝ) *
        Real.exp (μ_raw * (movingZ ν t₂ - movingZ ν r))) *
      (∑ j : Fin 2, ENNReal.ofReal ‖ampl F w r j‖ *
        xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m (complModeForce κ P F tr r j)),
    ?_, le_rfl, fun r _ => le_rfl⟩
  refine hgr.trans (add_le_add le_rfl (lintegral_mono_ae ?_))
  filter_upwards [hGG', hGle] with r h1 h2
  rw [← h1]
  gcongr

/-- **Assembly of `WeakFlowComplPerturbDuhamel κ` under the train comparison** (SP 2085-2090,
2919-2925, 2937-2958, 2982-2988): the proof of `WeakFlowDuhamelSub.weakFlowComplPerturbDuhamel_of`,
with the threshold `ν₀(b)` also below the threshold of `FmrTrainClose` at `b` (`0 < 1 ≤ b`), so
that every BUC train with `ν ≤ ν₀(b)` satisfies `TrainClose tr (ν b)⁻¹ 1`. -/
theorem weakFlowComplPerturbDuhamel_of_TC (κ : PlanarFrameKernels) (hTC : FmrTrainClose)
    (hProj : WeakFlowProjectedGronwallTC κ) :
    WeakFlowComplPerturbDuhamel κ := by
  intro hAdjAll hHeat hEuler hFree hSeed P hP m hm K
  obtain ⟨C_loc, b_loc, hC_loc, hb_loc1, hLocB⟩ :=
    exists_unif_adjointLocalized_bound (hAdjAll m hm)
  obtain ⟨C_H0, b_H0, hC_H0, hb_H01, hH0B⟩ :=
    xNorm_complCoupling_movH0_le_const hHeat hEuler hSeed hm K
  obtain ⟨b_free, hb_free1, hFreeB⟩ :=
    freeMovingEnergy_rate_le_add_one hFree hm
  set C_pert : ℝ := C_loc + C_H0
  set b₀ : ℝ := max b_free (max b_loc b_H0)
  have hC_pert : 0 ≤ C_pert := add_nonneg hC_loc hC_H0
  have hb₀1 : 1 ≤ b₀ := hb_free1.trans (le_max_left _ _)
  refine ⟨C_pert, b₀, hC_pert, hb₀1, fun b hb => ?_⟩
  have hb_free : b_free ≤ b := (le_max_left b_free _).trans hb
  have hb_loc : b_loc ≤ b :=
    (le_trans (le_max_left b_loc b_H0) (le_max_right b_free _)).trans hb
  have hb_H0 : b_H0 ≤ b :=
    (le_trans (le_max_right b_loc b_H0) (le_max_right b_free _)).trans hb
  have hb1 : 1 ≤ b := hb₀1.trans hb
  obtain ⟨ν_free, hν_free, hFree_ν⟩ := hFreeB b hb_free
  obtain ⟨ν_loc, hν_loc, hLoc_ν⟩ := hLocB b hb_loc
  obtain ⟨ν_H0, hν_H0, hH0_ν⟩ := hH0B b hb_H0
  set ν₀ : ℝ := min ν_free (min ν_loc ν_H0)
  have hν₀ : 0 < ν₀ := lt_min hν_free (lt_min hν_loc hν_H0)
  obtain ⟨ν_tc, hν_tc, hTC_ν⟩ := hTC b (lt_of_lt_of_le one_pos hb1)
  set ν₁ : ℝ := min ν₀ ν_tc
  have hν₁ : 0 < ν₁ := lt_min hν₀ hν_tc
  refine ⟨ν₁, hν₁, fun ν hν₁' hF tr htr t₁ t₂ ht₁ h12 hbt₂ f w u hFlow hCirc => ?_⟩
  dsimp only
  have hν : ν ∈ Ioc 0 ν₀ := ⟨hν₁'.1, hν₁'.2.trans (min_le_left _ _)⟩
  have hTCν : UnforcedLeray.Short.IIb.TrainClose tr (ν * b)⁻¹ 1 :=
    hTC_ν ν ⟨hν₁'.1, hν₁'.2.trans (min_le_right _ _)⟩ tr htr
  have hν_in_free : ν ∈ Ioc 0 ν_free :=
    ⟨hν.1, hν.2.trans (min_le_left _ _)⟩
  have hν_in_loc : ν ∈ Ioc 0 ν_loc :=
    ⟨hν.1, hν.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩
  have hν_in_H0 : ν ∈ Ioc 0 ν_H0 :=
    ⟨hν.1, hν.2.trans ((min_le_right _ _).trans (min_le_right _ _))⟩
  have hFree_sub :
      ∀ s₁ s₂ : ℝ, t₁ ≤ s₁ → s₁ ≤ s₂ → s₂ ≤ t₂ →
        ∀ f₀ : B0579.Plane → ℝ, B0579.IsCylTest (ν ^ (-2 : ℝ)) f₀ →
          ∀ ω₀ : ℝ → B0579.Plane → ℝ,
            UnforcedLeray.Short.IIb.IsFreeCylFlow m tr s₁ f₀ ω₀ →
            xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν s₂)) m
                (JscaleInv (clockA ν s₂) (fun x => ((ω₀ s₂ x : ℝ) : ℂ))) ≤
              ENNReal.ofReal
                  (Real.exp ((normGrowthConst m + 1) * (movingZ ν s₂ - movingZ ν s₁))) *
                xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν s₁)) m
                  (JscaleInv (clockA ν s₁) (fun x => ((f₀ x : ℝ) : ℂ))) := by
    intro s₁ s₂ hs₁ hs₁₂ hs₂ f₀ hf₀ ω₀ hω₀
    have hs₁0 : 0 ≤ s₁ := ht₁.trans hs₁
    have hs₂0 : 0 ≤ s₂ := hs₁0.trans hs₁₂
    have hbs₂ : b ≤ clockTheta ν s₂ := hbt₂.trans (theta_anti hν.1 hs₂0 hs₂)
    exact hFree_ν ν hν_in_free tr htr s₁ s₂ hs₁0 hs₁₂ hbs₂ f₀ hf₀ ω₀ hω₀
  have hLoc_sub :
      ∀ r ∈ Icc t₁ t₂, ∀ Φ : ℝ × ℝ → ℂ,
        let d := cellLen (ν ^ (-2 : ℝ)) (clockA ν r)
        MemLp Φ 2 (B0579.cellMeasure d (-m)) →
        ∃ (χ : ℝ × ℝ → ℂ) (gχ : Fin 2 → ℝ × ℝ → ℂ),
          (∀ j, HasWeakCellDerivC d j χ (gχ j)) ∧
          h1Norm d m χ gχ ≤ ENNReal.ofReal C_loc * xNorm d (-m) Φ ∧
          xNorm d (-m) χ ≤ ENNReal.ofReal C_loc * xNorm d (-m) Φ ∧
          ∀ ψ uψ, B0579.IsCylTest d ψ → IsKernelBiotSavart d ψ uψ →
            ∫ y in B0579.cell d, χ y * (ψ y : ℂ) =
              ∫ y in B0579.cell d,
                Φ y * ((uψ y 0 * B0579.pd 0 (movingTrainE tr r) y +
                  uψ y 1 * B0579.pd 1 (movingTrainE tr r) y : ℝ) : ℂ) := by
    intro r hr Φ d hΦ
    have hr0 : 0 ≤ r := ht₁.trans hr.1
    have hbr : b ≤ clockTheta ν r := hbt₂.trans (theta_anti hν.1 hr0 hr.2)
    exact hLoc_ν ν hν_in_loc tr htr r hr0 hbr Φ hΦ
  have hH0_sub :
      ∀ r ∈ Icc t₁ t₂,
        xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m
            (complFiniteRankCoupling (periodizedFrame κ ν m b K hν.1 hF) r
              (movH0 κ tr r · (compl (periodizedFrame κ ν m b K hν.1 hF) w r))) ≤
          ENNReal.ofReal C_H0 *
            xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m
              (compl (periodizedFrame κ ν m b K hν.1 hF) w r) := by
    intro r hr
    have hr0 : 0 ≤ r := ht₁.trans hr.1
    have hbr : b ≤ clockTheta ν r := hbt₂.trans (theta_anti hν.1 hr0 hr.2)
    exact hH0_ν ν hν_in_H0 hF tr htr t₁ r ht₁ hr.1 hbr f w u hFlow
  obtain ⟨H, G, hsplit, hH, hG⟩ :=
    hProj hSeed P hP m hm K C_loc C_H0 b hC_loc hC_H0 hb1 ν hν.1 hF tr htr hTCν
      t₁ t₂ ht₁ h12 hbt₂ f w u hFlow hCirc hFree_sub hLoc_sub hH0_sub
  exact duhamel_ennreal_bound_of_split hsplit hH hG

/-- **Free-rate reduction under the train comparison**: `FmrTrainClose → ComplFreeRateDuhamelTC κ →
WeakFlowComplPerturbDuhamel κ` (SP 2085-2090, 2919-2925, 2937-2958, 2982-2988). -/
theorem weakFlowComplPerturbDuhamel_of_freeRateTC (κ : PlanarFrameKernels)
    (hTC : FmrTrainClose) (hA : ComplFreeRateDuhamelTC κ) : WeakFlowComplPerturbDuhamel κ :=
  weakFlowComplPerturbDuhamel_of_TC κ hTC (weakFlowProjectedGronwallTC_of_freeRate κ hA)

/-- **`WeakFlowComplPerturbDuhamel κ` from the five leaves of `PartIII-a:T21/c3/3/1/1`**
(`complFreeRateDuhamelTC_of_leaves`, `Glue.lean`) and the unconditional `fmrTrainClose`
(`Clock/FreeMoving/Rate/FmrTrainClose.lean`, SP 2085-2090).  Composed by the task
`PartIII-a:T21/c3/3/1/1` (`WeakFlowDuhamel/FreeRateAssembly.lean`) with `freeMovingPropagatorExists`,
`complMildFreeBound κ`, `locInteractionBound`, `complForcingMeasurable κ`, `freeFlowAvailExists`. -/
theorem weakFlowComplPerturbDuhamel_of_leavesTC (κ : PlanarFrameKernels)
    (hA : ∀ ν m (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) t₁ t₂,
      FreeMovingPropagatorExists ν m tr t₁ t₂)
    (hB : ∀ P ν m b K (hν : 0 < ν) (hF : PerFrameFacts κ ν m b K)
      (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) t₁ t₂ C_loc C_H0,
      ComplMildFreeBound κ P ν m b K hν hF tr t₁ t₂ C_loc C_H0)
    (hC : ∀ ν m (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) t₁ t₂ C_loc,
      LocInteractionBound ν m tr t₁ t₂ C_loc)
    (hD : ∀ P ν m b K (hν : 0 < ν) (hF : PerFrameFacts κ ν m b K)
      (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) t₁ t₂,
      ComplForcingMeasurable κ P ν m b K hν hF tr t₁ t₂)
    (hE : ∀ ν m (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) t₁ t₂ b,
      FreeFlowAvailExists ν m tr t₁ t₂ b) :
    WeakFlowComplPerturbDuhamel κ :=
  weakFlowComplPerturbDuhamel_of_freeRateTC κ fmrTrainClose
    (complFreeRateDuhamelTC_of_leaves κ hA hB hC hD hE)

end WeakFlowDuhamelTC

end UnforcedLeray.Short.IIIa
