import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_1_org_1_a.Op
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_2

/-!
# Part III-a, `PartIII-a:T21/c3/2/1/1/org/1/a`: the bounded damped complement interaction

Source of record: `the November 2 reference manuscript` (SP), lines 2920-2925 and
2974-2978 (`eq:short-causal-damped-complement`).

`relInteractionA`: the bounded perturbation `𝓑 - (G_free - β₀)` of the damped complement generator
(the localized interaction `-(K_d W)·∇E_mov` plus the finite-rank terms
`-E H₀ + [-K₀ + (β₀ - 1)E + E M₀]Λ`, `movDampedComplInt`) defines on every block of moving length
`B` a family `A_rel τ` of bounded operators on `Planar.L2w m` (zero-extended from the moving cell)
with a bound `K_A` independent of `ν`, the train, and the block, and with `τ ↦ A_rel τ x` strongly
measurable.

Helpers (folder `PartIII-a_T21_c3_2_1_1_org_1_a/`):
* `LpMeas`: strong measurability of jointly represented `L²`-valued maps;
* `Interaction`: the localized interaction through the cylinder operator `IIb.cylWeightedOp`;
* `PointBound`, `Package`: the uniform bound `K_A` and the a.e. linearity on `X_{m,d(r)}`
  (`RescaledTrainBounds`, `MovLamDualHeatBound`, `MovLamDualEulerSubBound`,
  `ComplModeForceOscillator`, `PerFrameFacts`);
* `JointMeas`, `JointMeas2`: joint measurability in `(r, y)` (dual generator through its explicit
  moving formula);
* `Op`: the operator on `Planar.L2w m`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Metric UnforcedLeray.Blueprint.Planar
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

open FrameShortBlockSub FrameBlockContractSub CompactDuhamelGapSub

namespace BlockPropagatorInteriorSub

namespace OrgSplit

open RelIntA BlockPropagatorSub ComplFreeRateSub.Leaf4Aux

theorem relInteractionA (κ : PlanarFrameKernels) : IsSeedKernels κ → ∀ (P : PlanarData), IsPlanarReference P → ∀ m : ℝ, 8 < m → ∀ K B : ℝ, 0 < B → ∃ K_A b_prop : ℝ, 0 ≤ K_A ∧ ∀ b : ℝ, b_prop ≤ b → ∃ ν_prop : ℝ, 0 < ν_prop ∧ ∀ ν (_hν : ν ∈ Ioc 0 ν_prop), ∀ _hF : PerFrameFacts κ ν m b K, ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)), UnforcedLeray.Short.PartI.IsBUCTrain tr → ∀ t₁ t₂ : ℝ, 0 ≤ t₁ → t₁ ≤ t₂ → b ≤ clockTheta ν t₂ → movingZ ν t₂ - movingZ ν t₁ = B → ∃ A_rel : ℝ → Planar.L2w m →L[ℂ] Planar.L2w m, IsDampedComplBlockInt κ P ν m tr t₁ B A_rel ∧ (∀ τ : ℝ, ‖A_rel τ‖ ≤ K_A) ∧ ∀ x : Planar.L2w m, AEStronglyMeasurable (fun τ => A_rel τ x) (volume.restrict (Icc 0 B)) := by
  intro hκ P _hP m hm K B hB
  obtain ⟨K_A, b₀, hKA, _hb₀1, hpack⟩ := goodAt_package κ hκ P m hm K
  obtain ⟨D, hD1, hDform⟩ := heatFormula_of κ hκ
  refine ⟨K_A, max b₀ (D ^ 2), hKA, fun b hb => ?_⟩
  have hb₀b : b₀ ≤ b := le_trans (le_max_left _ _) hb
  have hDb : D ^ 2 ≤ b := le_trans (le_max_right _ _) hb
  obtain ⟨ν₀, hν₀, hν₀1, hgood⟩ := hpack b hb₀b
  refine ⟨ν₀, hν₀, fun ν hν hF tr htr t₁ t₂ ht₁ h12 hbt₂ hBdef => ?_⟩
  have hν0 : 0 < ν := hν.1
  have hν1 : ν ≤ 1 := hν.2.trans hν₀1
  have hr0 : ∀ r ∈ Icc t₁ t₂, 0 ≤ r := fun r hr => ht₁.trans hr.1
  have hbr : ∀ r ∈ Icc t₁ t₂, b ≤ clockTheta ν r := fun r hr =>
    hbt₂.trans (theta_anti hν0 (hr0 r hr) hr.2)
  have hgood' : ∀ r ∈ Icc t₁ t₂, GoodAt κ P m K_A tr r := fun r hr =>
    hgood ν hν hF tr htr r (hr0 r hr) (hbr r hr)
  have hd1 : ∀ r ∈ Icc t₁ t₂, 1 ≤ cellLen (ν ^ (-2 : ℝ)) (clockA ν r) := fun r hr =>
    (hgood' r hr).1
  have hdet : ∀ r ∈ Icc t₁ t₂, (perGram κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r))).det ≠ 0 := by
    intro r hr h0
    have h := hF.1 r (hr0 r hr) (hbr r hr) 0 0
    have hinv : (perGram κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)))⁻¹ = 0 :=
      Matrix.nonsing_inv_apply_not_isUnit _ (by rw [isUnit_iff_ne_zero, not_not]; exact h0)
    have hz : ∀ x, perLam κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) 0 x = 0 := fun x => by
      unfold perLam
      rw [hinv]
      simp
    simp only [hz, zero_mul, integral_zero, if_pos rfl] at h
    exact zero_ne_one h
  have hform : ∀ r ∈ Icc t₁ t₂, HeatFormula κ ν r := fun r hr =>
    hDform hν0 (hr0 r hr) (le_cellLen_of hν0 hν1 (hr0 r hr) (by linarith) hDb (hbr r hr))
  -- the clamped age along the block
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : ℝ → ℝ, ρ = fun τ => ageAt ν t₁ (clampB B τ) := ⟨_, rfl⟩
  have hρ : ∀ τ, ρ τ ∈ Icc t₁ t₂ := fun τ => by
    rw [hρdef]
    exact VariationOfConstantsSub.ageAt_mem_Icc hν0 ht₁ h12 hBdef
      ⟨clampB_nonneg _ _, clampB_le B τ hB.le⟩
  have hρm : Measurable ρ := by
    rw [hρdef]
    unfold ageAt FrameStableSub.moveAgeOfZ clampB
    fun_prop
  -- the operators
  have hop : ∀ τ, ∃ T : Planar.L2w m →L[ℂ] Planar.L2w m,
      (∀ x, (T x : ℂ → ℂ) =ᵐ[Planar.wMeasure m] opFun κ P tr (ρ τ) x) ∧ ‖T‖ ≤ K_A :=
    fun τ => exists_op κ P tr (ρ τ) hKA (hgood' _ (hρ τ))
  choose A hArep hAnorm using hop
  refine ⟨A, ?_, hAnorm, fun x => ?_⟩
  · -- the pinning on smooth compactly supported data
    intro τ hτ
    dsimp only
    intro Φ _hΦ _hΦc W hW
    have hclamp : clampB B τ = τ := by
      unfold clampB
      rw [min_eq_left hτ.2, max_eq_right hτ.1]
    have hρτ : ρ τ = ageAt ν t₁ τ := by
      rw [hρdef]
      simp only [hclamp]
    have h1 : (A τ W : ℂ → ℂ) =ᵐ[volume] opFun κ P tr (ρ τ) W :=
      (volume_ac_wMeasure m).ae_le (hArep τ W)
    refine h1.trans (Eventually.of_forall fun z => ?_)
    have hc : cylRep W =ᵐ[volume.restrict
        (B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ρ τ))))] Φ := by
      have h2 : (fun y => (W : ℂ → ℂ) (planeToC y)) =ᵐ[volume]
          fun y => Φ (cToPlane (planeToC y)) :=
        measurePreserving_planeToC_volume.quasiMeasurePreserving.ae_eq_comp hW
      refine ae_restrict_of_ae (h2.mono fun y hy => ?_)
      simp only [cylRep, hy, cToPlane_planeToC]
    unfold opFun
    rw [movDampedComplInt_congr κ P tr (ρ τ) hc, hρτ]
  · -- strong measurability in the block time
    have : SFinite (Planar.wMeasure m) := by
      unfold Planar.wMeasure
      infer_instance
    have hG := measurable_cellZeroExt_joint (dRho ν t₁ t₂) (continuous_dRho hν0 ht₁).measurable
      (fun r => movDampedComplInt κ P tr (rho t₁ t₂ r) (cylRep x))
      (measurable_movDampedComplInt_joint hκ P hν0 ht₁ h12 hd1 hdet hform tr
        (measurable_cylRep x))
    have hmap : Measurable (fun p : ℝ × ℂ => ((ρ p.1, cToPlane p.2) : ℝ × (ℝ × ℝ))) :=
      (hρm.comp measurable_fst).prodMk (measurable_cToPlane.comp measurable_snd)
    have heq : Function.uncurry (fun τ z => opFun κ P tr (ρ τ) x z) =
        (fun q : ℝ × (ℝ × ℝ) => cellZeroExt (dRho ν t₁ t₂ q.1)
          (movDampedComplInt κ P tr (rho t₁ t₂ q.1) (cylRep x)) q.2) ∘
        (fun p : ℝ × ℂ => ((ρ p.1, cToPlane p.2) : ℝ × (ℝ × ℝ))) := by
      funext p
      show opFun κ P tr (ρ p.1) x p.2 = cellZeroExt (dRho ν t₁ t₂ (ρ p.1))
        (movDampedComplInt κ P tr (rho t₁ t₂ (ρ p.1)) (cylRep x)) (cToPlane p.2)
      unfold opFun dRho
      rw [rho_eq (hρ p.1)]
    have hF' : Measurable (Function.uncurry (fun τ z => opFun κ P tr (ρ τ) x z)) := by
      rw [heq]
      exact hG.comp hmap
    exact (stronglyMeasurable_Lp_of_jointly (fun τ z => opFun κ P tr (ρ τ) x z) hF'
      (fun τ => A τ x) (fun τ => hArep τ x)).aestronglyMeasurable

end OrgSplit

end BlockPropagatorInteriorSub

end UnforcedLeray.Short.IIIa
