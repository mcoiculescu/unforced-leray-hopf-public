import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F2
import UnforcedLeray.Short.PartIIb.Tasks.FreeCylinderBound
import UnforcedLeray.Short.PartIIb.Tasks.BlockFactorization.TrainCloseRegime
import UnforcedLeray.Short.PartIIb.Tasks.BlockFactorization.CoupledPropagator
import UnforcedLeray.Short.PartIIb.Tasks.BlockFactorization.FrozenEulerSplitting
import UnforcedLeray.Short.PartIIb.Tasks.BlockFactorization.CompactDuhamelBlock

/-!
# `PartII-b:F2` (`BlockFactorization.lean`): Block factorization and dichotomy

Source of record: `the November 2 reference manuscript` (SP), lines 2141–2171.

This module imports the decomposition support file `UnforcedLeray.Short.«PartII-b».Sub.«PartII-b_F2»`,
which defines the four leaf propositions:
1. `TrainCloseRegime` (`PartII-b:F2/1`, `Short/PartII-b/Tasks/BlockFactorization/TrainCloseRegime.lean`):
   early-train comparison in the `m`-weighted budget (`short-bg:train-early`, SP 2085–2090);
2. `CoupledPropagatorStep` (`PartII-b:F2/2`, `Short/PartII-b/Tasks/BlockFactorization/CoupledPropagator.lean`):
   free cylinder propagator `Sc` and coupled Duhamel propagator `U` (`short-bg:coupled-prop`,
   SP 2076–2083, 2141–2155);
3. `FrozenEulerSplittingStep` (`PartII-b:F2/3`, `Short/PartII-b/Tasks/BlockFactorization/FrozenEulerSplitting.lean`):
   frozen planar Euler dichotomy and periodized cylinder coordinate projections
   (`short-sp:dichotomy`, SP 931–953, 2145–2171);
4. `CompactDuhamelBlockStep` (`PartII-b:F2/4`, `Short/PartII-b/Tasks/BlockFactorization/CompactDuhamelBlock.lean`):
   compact-Duhamel block approximation on `[t, t + L]` (`short-bg:compact-duhamel`,
   SP 2104–2115, 2145–2166);

together with the Hilbert-space Householder complementary-subspace construction (`PartIIbF2Splittings`),
Neumann 2×2 perturbation (`invertible_two_by_two_of_close`), block grid construction (`exists_block_grid`),
and full conditional assembly theorem `blockDichotomy_of_leaves`.

Once the four leaf theorems `trainCloseRegime_proof`, `coupledPropagatorStep_proof`,
`frozenEulerSplittingStep_proof`, and `compactDuhamelBlockStep_proof` are proved, the target theorem is
assembled immediately by:
```lean
theorem blockDichotomy_of
    (hComp : UnforcedLeray.Short.IIb.InteractionCylinderComparison)
    (hColl : UnforcedLeray.Short.IIb.InteractionCollectiveCompact) :
    UnforcedLeray.Short.IIb.BlockDichotomy :=
  blockDichotomy_of_leaves hComp hColl
    trainCloseRegime_proof
    coupledPropagatorStep_proof
    frozenEulerSplittingStep_proof
    compactDuhamelBlockStep_proof
```
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- Combining `freeCylinderBound_proof` (`PartII-b:T24`), `InteractionCylinderComparison`,
`InteractionCollectiveCompact`, and `TrainCloseRegime` yields simultaneous free-flow bounds,
cylinder-to-planar interaction comparison, and collective compactness in `BgRegime`. -/
theorem interaction_and_free_of_regime
    (hComp : InteractionCylinderComparison)
    (hColl : InteractionCollectiveCompact)
    (hTC : TrainCloseRegime)
    {m Sg dm dp : ℝ} (hm : 8 < m) (hSg : 0 < Sg) (hdm : 0 < dm) :
    ∃ (Cm C b C_Sg : ℝ) (AplOp : ℝ → (Xm m →L[ℝ] Xm m)),
      0 < Cm ∧ 0 < C ∧ 0 < b ∧ 0 < C_Sg ∧
      ContinuousOn AplOp (Icc 0 Sg) ∧
      (∀ σ ∈ Icc 0 Sg, IsPlanarInteractionOp m σ (AplOp σ) ∧ IsCompactOperator (AplOp σ)) ∧
      TotallyBounded (AplOp '' Icc 0 Sg) ∧
      (∀ R : ℝ, TotallyBounded (⋃ σ ∈ Icc 0 Sg, AplOp σ '' Metric.closedBall (0 : Xm m) R)) ∧
      ∀ δ : ℝ, 0 < δ → ∃ ν₀ : ℝ, 0 < ν₀ ∧
        ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ →
          1 ≤ p.c ∧
          TrainCloseM m p.train Sg δ ∧
          TrainClose p.train Sg δ ∧
          (∀ σ ∈ Icc 0 Sg,
            ∃ Ac : Xmc p.c m →L[ℝ] Xmc p.c m,
              IsCylInteractionOp p.train m (σ / p.ν) Ac ∧
              IsCompactOperator Ac ∧
              IsCompactOperator ((Jc p.c m).comp (Ac.comp (Rc p.c m))) ∧
              ‖(Jc p.c m).comp (Ac.comp (Rc p.c m)) - AplOp σ‖ ≤ C_Sg * (p.c ^ (-2 : ℝ) + δ)) ∧
          (∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ Sg / p.ν →
            ∀ f : B0579.Plane → ℝ, MemLp f 2 (B0579.cellMeasure p.c m) →
              ∃ ω : ℝ → B0579.Plane → ℝ,
                IsFreeCylFlow m p.train s f ω ∧
                (∀ ω' : ℝ → B0579.Plane → ℝ, IsFreeCylFlow m p.train s f ω' →
                  ∀ t' : ℝ, s ≤ t' → ω' t' =ᵐ[volume.restrict (B0579.cell p.c)] ω t') ∧
                eLpNorm (ω t) 2 (B0579.cellMeasure p.c m) ≤
                  ENNReal.ofReal
                    (Real.exp ((Cm * p.ν + C * δ + C * Real.exp (-b * p.c ^ 2)) * (t - s))) *
                    eLpNorm f 2 (B0579.cellMeasure p.c m)) := by
  obtain ⟨Cm, C, b, hCm, hC, hb, hFree⟩ := freeCylinderBound_proof m hm Sg hSg
  obtain ⟨C_Sg, hC_Sg, hComp_op⟩ := hComp m hm Sg hSg
  obtain ⟨hColl_cyl, AplOp, hApl_cont, hApl_prop, hApl_tb, hApl_ball⟩ := hColl m hm Sg hSg
  refine ⟨Cm, C, b, C_Sg, AplOp, hCm, hC, hb, hC_Sg, hApl_cont, hApl_prop, hApl_tb, hApl_ball, ?_⟩
  intro δ hδ
  obtain ⟨ν₁, hν₁, hTC_op⟩ := hTC m hm Sg hSg dm dp hdm δ hδ
  refine ⟨min 1 ν₁, lt_min zero_lt_one hν₁, ?_⟩
  intro p d hbg hν
  have hν_le_1 : p.ν ≤ 1 := hν.trans (min_le_left _ _)
  have hν_le_ν₁ : p.ν ≤ ν₁ := hν.trans (min_le_right _ _)
  have hc1 : 1 ≤ p.c := bgRegime_c_ge_one hbg hν_le_1
  have hcloseM : TrainCloseM m p.train Sg δ := hTC_op p d hbg hν_le_ν₁
  have hclose : TrainClose p.train Sg δ := hcloseM.toTrainClose (by linarith)
  refine ⟨hc1, hcloseM, hclose, ?_, ?_⟩
  · intro σ hσ
    obtain ⟨⟨Ac, _, hAc, _⟩, hAc_bd⟩ := hComp_op p d dm dp hbg hc1 δ hδ.le hcloseM σ hσ
    have hs_mem : σ / p.ν ∈ Icc 0 (Sg / p.ν) :=
      ⟨div_nonneg hσ.1 p.ν_pos.le, div_le_div_of_nonneg_right hσ.2 p.ν_pos.le⟩
    have hAc_comp := (hColl_cyl p d dm dp hbg hc1 δ hδ.le hcloseM (σ / p.ν) hs_mem).2 Ac hAc
    exact ⟨Ac, hAc, hAc_comp.1, hAc_comp.2, hAc_bd Ac (AplOp σ) hAc (hApl_prop σ hσ).1⟩
  · intro s t hs hst htT f hf
    exact hFree p d dm dp hbg δ hδ.le hclose s t hs hst htT f hf

theorem blockDichotomy_of
    (hComp : UnforcedLeray.Short.IIb.InteractionCylinderComparison)
    (hColl : UnforcedLeray.Short.IIb.InteractionCollectiveCompact) :
    UnforcedLeray.Short.IIb.BlockDichotomy :=
  blockDichotomy_of_leaves hComp hColl
    trainCloseRegime_proof
    coupledPropagatorStep_proof
    frozenEulerSplittingStep_proof
    compactDuhamelBlockStep_proof

end UnforcedLeray.Short.IIb

end
