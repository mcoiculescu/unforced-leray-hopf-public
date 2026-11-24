import UnforcedLeray.Short.PartIIIa.Clock.FrameStableProof.ShortBlock.PerturbDuhamel.WeakFlowDuhamel
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_3_1_1_org

/-! Glue check: `ComplFreeRateDuhamel κ` from the four leaves (to be used by the parent task). -/
set_option autoImplicit false
noncomputable section
open Set MeasureTheory Filter Topology UnforcedLeray.Blueprint.Planar
open scoped ENNReal
namespace UnforcedLeray.Short.IIIa
open ComplFreeRateSub

/-- `ComplFreeRateDuhamel κ` with the train-comparison hypothesis `TrainClose tr (ν b)⁻¹ 1`
(`FmrTrainClose` for `ν ≤ ν₀(b)`) added after `IsBUCTrain tr`: the free cylinder flows of leaf (e)
exist only under it (SP 2085-2090, 2937-2958).  Same statement as `ComplFreeRateDuhamel` otherwise
(`WeakFlowDuhamel.lean`, whose body is copied unchanged). -/
def ComplFreeRateDuhamelTC (κ : PlanarFrameKernels) : Prop :=
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
          let μ₀ := normGrowthConst m + 1
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
          ∃ G : ℝ → ℝ≥0∞,
            AEMeasurable G (volume.restrict (Ioc t₁ t₂)) ∧
            (∀ᵐ r ∂(volume.restrict (Ioc t₁ t₂)),
              G r ≤ ∑ j : Fin 2, ENNReal.ofReal ‖ampl F w r j‖ *
                xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m (complModeForce κ P F tr r j)) ∧
            ∀ s ∈ Icc t₁ t₂,
              xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)) m (compl F w s) ≤
                ENNReal.ofReal (Real.exp (μ₀ * (movingZ ν s - movingZ ν t₁))) *
                    xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν t₁)) m (compl F w t₁) +
                  ∫⁻ r in Ioc t₁ s,
                    ENNReal.ofReal ((clockA ν r) ^ (-2 : ℝ) *
                        Real.exp (μ₀ * (movingZ ν s - movingZ ν r))) *
                      (ENNReal.ofReal (C_loc + C_H0) *
                          xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m (compl F w r) + G r)

theorem complFreeRateDuhamelTC_of_leaves (κ : PlanarFrameKernels)
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
    ComplFreeRateDuhamelTC κ := by
  intro hSeed P hP m hm K C_loc C_H0 b hC_loc hC_H0 hb1 ν hν hF tr htr hTC t₁ t₂ ht₁ h12 hbt₂
    f w u hFlow hCirc F μ₀ hFree hLoc hH0
  exact complFreeRate_inst κ P hSeed hP hm hC_loc hC_H0 hb1 hν hF tr htr ht₁ h12 hbt₂ hFlow hCirc
    hFree hLoc hH0 (hA ν m tr t₁ t₂) (hB P ν m b K hν hF tr t₁ t₂ C_loc C_H0)
    (hC ν m tr t₁ t₂ C_loc) (hD P ν m b K hν hF tr t₁ t₂) (hE ν m tr t₁ t₂ b) hTC
end UnforcedLeray.Short.IIIa
