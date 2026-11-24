import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_8_2_1_2.Statements

/-!
# `newtonCurlSliceBoundNear`: near-field bound of the Newton curl potential

Proves `NewtonCurlSliceBoundNear` (`Statements.lean`), source lines 1393-1400.
`B = projectedTestNewtonVectorPotentialCurl φ` is jointly smooth and `P`-periodic in `τ`
(`contDiff_spatialCurlST_of_contDiff`, `spatialCurlST_periodic_of_periodic`).

Proof. For each `k`, the slice derivative satisfies
`‖D^k_y B(τ, y)‖ ≤ c_k ‖D^k B(τ, y, 0)-shifted‖` (composition with the linear map `inr` and the
translation `z ↦ z + (τ, 0)`), with `c_k` a constant. The map `(τ, y) ↦ ‖D^k B (τ, y)‖` is
continuous, hence bounded on the compact `Icc 0 P × closedBall 0 ρ`. Periodicity reduces an
arbitrary `τ` to `Ico 0 P`, and the bounds for `k = 0, …, 3` are summed.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.SolApprox

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.B0412 UnforcedLeray.RieszLp
open UnforcedLeray.Cons.C03.Concrete
open NavierStokesR3.ComparisonCutoffs

/-- **Near-field bound of the Newton curl potential** (`NewtonCurlSliceBoundNear`). -/
theorem newtonCurlSliceBoundNear : UnforcedLeray.Short.PartIIIb.Concrete.SolApprox.NewtonCurlSliceBoundNear := by
  intro P hP φ hφ ρ
  have hB : ContDiff ℝ ∞ (projectedTestNewtonVectorPotentialCurl φ) :=
    contDiff_spatialCurlST_of_contDiff (contDiff_projectedTestNewtonVectorPotential hφ)
  have hper : ∀ τ y, projectedTestNewtonVectorPotentialCurl φ (τ + P, y) =
      projectedTestNewtonVectorPotentialCurl φ (τ, y) :=
    spatialCurlST_periodic_of_periodic (fun τ y =>
      congrFun (projectedTestNewtonVectorPotential_periodic hφ τ) y)
  -- per-order bound
  have hk : ∀ k : ℕ, ∃ C : ℝ, ∀ τ : ℝ, ∀ y : Space, ‖y‖ ≤ ρ →
      ‖iteratedFDeriv ℝ k (fun x => projectedTestNewtonVectorPotentialCurl φ (τ, x)) y‖ ≤ C := by
    intro k
    have hcont : Continuous (fun p : ℝ × Space =>
        ‖iteratedFDeriv ℝ k (projectedTestNewtonVectorPotentialCurl φ) p‖) :=
      continuous_norm.comp (hB.continuous_iteratedFDeriv (by simp))
    obtain ⟨Cb, hCb⟩ := ((isCompact_Icc (a := (0 : ℝ)) (b := P)).prod
      (isCompact_closedBall (0 : Space) ρ)).exists_bound_of_continuousOn hcont.continuousOn
    -- composition with the affine map x ↦ (τ, x)
    have hcomp : ∀ (τ' : ℝ) (y : Space),
        ‖iteratedFDeriv ℝ k (fun x => projectedTestNewtonVectorPotentialCurl φ (τ', x)) y‖ ≤
          (∏ _i : Fin k, ‖(ContinuousLinearMap.inr ℝ ℝ Space : Space →L[ℝ] ℝ × Space)‖) *
            ‖iteratedFDeriv ℝ k (projectedTestNewtonVectorPotentialCurl φ) (τ', y)‖ := by
      intro τ' y
      have hBs : ContDiff ℝ ∞ (fun z : ℝ × Space =>
          projectedTestNewtonVectorPotentialCurl φ (z + (τ', 0))) :=
        hB.comp (contDiff_id.add contDiff_const)
      have hfun : (fun x : Space => projectedTestNewtonVectorPotentialCurl φ (τ', x)) =
          (fun z : ℝ × Space => projectedTestNewtonVectorPotentialCurl φ (z + (τ', 0))) ∘
            (ContinuousLinearMap.inr ℝ ℝ Space) := by
        funext x
        show projectedTestNewtonVectorPotentialCurl φ (τ', x) =
          projectedTestNewtonVectorPotentialCurl φ ((0, x) + (τ', 0))
        congr 1
        ext <;> simp
      rw [hfun, ContinuousLinearMap.iteratedFDeriv_comp_right _ hBs _ (by simp)]
      have hnorm := ContinuousMultilinearMap.norm_compContinuousLinearMap_le
        (iteratedFDeriv ℝ k (fun z : ℝ × Space =>
          projectedTestNewtonVectorPotentialCurl φ (z + (τ', 0))) ((ContinuousLinearMap.inr ℝ ℝ Space) y))
        (fun _ : Fin k => (ContinuousLinearMap.inr ℝ ℝ Space : Space →L[ℝ] ℝ × Space))
      have hBsI : iteratedFDeriv ℝ k (fun z : ℝ × Space =>
          projectedTestNewtonVectorPotentialCurl φ (z + (τ', 0)))
          ((ContinuousLinearMap.inr ℝ ℝ Space) y) =
          iteratedFDeriv ℝ k (projectedTestNewtonVectorPotentialCurl φ) (τ', y) := by
        rw [iteratedFDeriv_comp_add_right]
        congr 1
        ext <;> simp
      rw [hBsI] at hnorm ⊢
      exact hnorm.trans_eq (mul_comm _ _)
    -- bound at a point of the compact set
    refine ⟨(∏ _i : Fin k, ‖(ContinuousLinearMap.inr ℝ ℝ Space : Space →L[ℝ] ℝ × Space)‖) * |Cb|,
      ?_⟩
    intro τ y hy
    have hperiod : Function.Periodic (fun τ' : ℝ =>
        ‖iteratedFDeriv ℝ k (fun x => projectedTestNewtonVectorPotentialCurl φ (τ', x)) y‖) P := by
      intro τ'
      have hfun : (fun x : Space => projectedTestNewtonVectorPotentialCurl φ (τ' + P, x)) =
          (fun x : Space => projectedTestNewtonVectorPotentialCurl φ (τ', x)) :=
        funext fun x => hper τ' x
      show ‖iteratedFDeriv ℝ k (fun x => projectedTestNewtonVectorPotentialCurl φ (τ' + P, x)) y‖ =
        ‖iteratedFDeriv ℝ k (fun x => projectedTestNewtonVectorPotentialCurl φ (τ', x)) y‖
      rw [hfun]
    obtain ⟨τ', hmem, heq⟩ := hperiod.exists_mem_Ico₀ hP.out τ
    have heq' : ‖iteratedFDeriv ℝ k (fun x => projectedTestNewtonVectorPotentialCurl φ (τ, x)) y‖ =
        ‖iteratedFDeriv ℝ k (fun x => projectedTestNewtonVectorPotentialCurl φ (τ', x)) y‖ := heq
    have hK : ((τ', y) : ℝ × Space) ∈ Icc (0 : ℝ) P ×ˢ Metric.closedBall (0 : Space) ρ := by
      refine ⟨⟨hmem.1, le_of_lt hmem.2⟩, ?_⟩
      rw [Metric.mem_closedBall, dist_zero_right]
      exact hy
    have hbd := hCb (τ', y) hK
    rw [Real.norm_of_nonneg (norm_nonneg _)] at hbd
    have hprod : (0 : ℝ) ≤ ∏ _i : Fin k, ‖(ContinuousLinearMap.inr ℝ ℝ Space : Space →L[ℝ] ℝ × Space)‖ :=
      Finset.prod_nonneg fun _ _ => norm_nonneg _
    rw [heq']
    calc ‖iteratedFDeriv ℝ k (fun x => projectedTestNewtonVectorPotentialCurl φ (τ', x)) y‖
        ≤ (∏ _i : Fin k, ‖(ContinuousLinearMap.inr ℝ ℝ Space : Space →L[ℝ] ℝ × Space)‖) *
            ‖iteratedFDeriv ℝ k (projectedTestNewtonVectorPotentialCurl φ) (τ', y)‖ := hcomp τ' y
      _ ≤ (∏ _i : Fin k, ‖(ContinuousLinearMap.inr ℝ ℝ Space : Space →L[ℝ] ℝ × Space)‖) * |Cb| :=
          mul_le_mul_of_nonneg_left (hbd.trans (le_abs_self _)) hprod
  choose C hC using hk
  refine ⟨∑ k ∈ Finset.range 4, |C k|, ?_, ?_⟩
  · exact Finset.sum_nonneg fun i _ => abs_nonneg _
  · intro τ y hy k hk3
    have h1 := hC k τ y hy
    have h2 : |C k| ≤ ∑ k ∈ Finset.range 4, |C k| :=
      Finset.single_le_sum (f := fun k => |C k|) (fun i _ => abs_nonneg _)
        (Finset.mem_range.2 (by omega))
    linarith [le_abs_self (C k)]

end UnforcedLeray.Short.PartIIIb.Concrete.SolApprox
