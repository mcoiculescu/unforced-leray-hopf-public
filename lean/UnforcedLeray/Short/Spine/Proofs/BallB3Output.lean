import UnforcedLeray.Short.Spine.Sub.SP_PII
import UnforcedLeray.Short.PartIIb.Tasks.HeatRemainder
import UnforcedLeray.Short.PartIIb.Tasks.StrongRegularityProof
import UnforcedLeray.Cons.C09PressureProjection
import UnforcedLeray.Cons.L2.BackgroundConcrete
import UnforcedLeray.Lib.BochnerTime
import UnforcedLeray.Loc.L03Evolution
import UnforcedLeray.Loc.L14Realization.WeakForm
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
# `Spine:SP-PII/1`: `BallB3Output`

Source of record: `the November 2 reference manuscript`, lines 2563-2645.

Proves `UnforcedLeray.Short.Spine.SPPII.ballB3Output : BallB3Output`:
1. `IsB3Core` and `UL4` (`D^j U ∈ C_per L⁴` for `j ≤ 2`) at the contraction-ball state `z` come
   from `IIb.ballHeatRemainder_proof` (`PartII-b:B3`, which incorporates `PartII-b:B2` for the
   datum and `PartII-b:S3` / `StrongAllOrders` for the background).
2. Joint smoothness of `U = IIb.bgField p z` (`IIb.strongRegularity_proof`) together with the
   comoving projected equation (`bgComovingFirstEquation_proof` and
   `IIb.smoothLeraySliceRegularity_proof`, where `PartII-b:B1` identifies the projected relations)
   yields the distributional projected similarity equation `Blueprint.SolvesSimilarityBackground`
   via spacetime integration by parts against compact similarity tests and
   `IIb.B3RemH2Sub.Xclass_minusLerayDivX_stressColH2`.
3. The global Riesz pressure `pres` in `C_per L²` is constructed as a jointly measurable
   representative of `Cons.C03.Concrete.stressPressureL2Path`, and the C09 converse
   (`Cons.C09.projectedConvection_eq_of_relation`) recovers `Blueprint.SolvesSimilarityNSWithPressure`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.Short.Spine.SPPII

open UnforcedLeray UnforcedLeray.Blueprint UnforcedLeray.Blueprint.Planar
open UnforcedLeray.Cons.C03.Concrete (Params)

local instance fact_one_le_two_ballB3 : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
local instance fact_one_le_four_ballB3 : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩
local instance isAddHaarMeasure_volume_spaceTime :
    (volume : Measure SpaceTime).IsAddHaarMeasure := by
  rw [Measure.volume_eq_prod]; infer_instance

/-! ## Spacetime integration by parts for smooth fields against compact similarity tests -/

private theorem integrable_inner_compact {f g : SpaceTime → Space}
    (hf : Continuous f) (hg : Continuous g) (hgc : HasCompactSupport g) :
    Integrable (fun z : SpaceTime => inner ℝ (f z) (g z)) volume :=
  (hf.inner hg).integrable_of_hasCompactSupport <|
    HasCompactSupport.intro hgc.isCompact fun z hz => by
      simp [image_eq_zero_of_notMem_tsupport hz]

private theorem ibp_spacetime_inner {f g : SpaceTime → Space}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) (v : SpaceTime) :
    (∫ z : SpaceTime, inner ℝ (f z) (fderiv ℝ g z v)) =
      -∫ z : SpaceTime, inner ℝ (fderiv ℝ f z v) (g z) := by
  have hdf : ContDiff ℝ ∞ (fun z => fderiv ℝ f z v) :=
    (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hdg : ContDiff ℝ ∞ (fun z => fderiv ℝ g z v) :=
    (hg.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hdgc : HasCompactSupport (fun z => fderiv ℝ g z v) :=
    hgc.fderiv_apply (𝕜 := ℝ) v
  exact integral_bilinear_fderiv_right_eq_neg_left_of_integrable (B := innerSL ℝ)
    (integrable_inner_compact hdf.continuous hg.continuous hgc)
    (integrable_inner_compact hf.continuous hdg.continuous hdgc)
    (integrable_inner_compact hf.continuous hg.continuous hgc)
    (fun z _ => hf.differentiable (by simp) z)
    (fun z _ => hg.differentiable (by simp) z)

private theorem fderiv_uncurry_time {U : ℝ → SpatialField}
    (hU : ContDiff ℝ ∞ (fun z : SpaceTime => U z.1 z.2)) (τ : ℝ) (y : Space) :
    fderiv ℝ (fun z : SpaceTime => U z.1 z.2) (τ, y) ((1 : ℝ), (0 : Space)) =
      deriv (fun t => U t y) τ := by
  have hf : HasFDerivAt (fun z : SpaceTime => U z.1 z.2)
      (fderiv ℝ (fun z : SpaceTime => U z.1 z.2) (τ, y)) (τ, y) :=
    (hU.differentiable (by simp) (τ, y)).hasFDerivAt
  have hi : HasDerivAt (fun t : ℝ => ((t, y) : SpaceTime)) ((1 : ℝ), (0 : Space)) τ :=
    (hasDerivAt_id τ).prodMk (hasDerivAt_const τ y)
  exact (hf.comp_hasDerivAt τ hi).deriv.symm

private theorem fderiv_uncurry_space {U : ℝ → SpatialField}
    (hU : ContDiff ℝ ∞ (fun z : SpaceTime => U z.1 z.2)) (τ : ℝ) (y v : Space) :
    fderiv ℝ (fun z : SpaceTime => U z.1 z.2) (τ, y) ((0 : ℝ), v) =
      fderiv ℝ (U τ) y v := by
  have hf : HasFDerivAt (fun z : SpaceTime => U z.1 z.2)
      (fderiv ℝ (fun z : SpaceTime => U z.1 z.2) (τ, y)) (τ, y) :=
    (hU.differentiable (by simp) (τ, y)).hasFDerivAt
  have hc := hf.comp y (hasFDerivAt_prodMk_right (𝕜 := ℝ) τ y)
  rw [show (U τ) = (fun z : SpaceTime => U z.1 z.2) ∘ fun y' : Space => (τ, y') from rfl, hc.fderiv]
  simp

private theorem contDiff_spatialLaplacian_joint {U : ℝ → SpatialField}
    (hU : ContDiff ℝ ∞ (fun z : SpaceTime => U z.1 z.2)) :
    ContDiff ℝ ∞ (fun z : SpaceTime => IIb.spatialLaplacian (U z.1) z.2) := by
  let U₁ : Fin 3 → ℝ → SpatialField := fun i τ y => fderiv ℝ (U τ) y (coordinateVector i)
  have hU₁_eq : ∀ i, (fun z : SpaceTime => U₁ i z.1 z.2) =
      fun z : SpaceTime =>
        fderiv ℝ (fun w : SpaceTime => U w.1 w.2) z ((0 : ℝ), coordinateVector i) :=
    fun i => funext fun ⟨τ, y⟩ => (fderiv_uncurry_space hU τ y (coordinateVector i)).symm
  have hU₁ : ∀ i, ContDiff ℝ ∞ (fun z : SpaceTime => U₁ i z.1 z.2) := fun i => by
    rw [hU₁_eq i]
    exact (hU.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  let U₂ : Fin 3 → ℝ → SpatialField := fun i τ y => fderiv ℝ (U₁ i τ) y (coordinateVector i)
  have hU₂_eq : ∀ i, (fun z : SpaceTime => U₂ i z.1 z.2) =
      fun z : SpaceTime =>
        fderiv ℝ (fun w : SpaceTime => U₁ i w.1 w.2) z ((0 : ℝ), coordinateVector i) :=
    fun i => funext fun ⟨τ, y⟩ => (fderiv_uncurry_space (hU₁ i) τ y (coordinateVector i)).symm
  have hU₂ : ∀ i, ContDiff ℝ ∞ (fun z : SpaceTime => U₂ i z.1 z.2) := fun i => by
    rw [hU₂_eq i]
    exact ((hU₁ i).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have heq : (fun z : SpaceTime => IIb.spatialLaplacian (U z.1) z.2) =
      fun z : SpaceTime => ∑ i : Fin 3, U₂ i z.1 z.2 := by
    funext ⟨τ, y⟩
    simp only [IIb.spatialLaplacian, IIb.dirSpatialJet, U₂, U₁]
    rfl
  rw [heq]
  exact ContDiff.sum fun i _ => hU₂ i

private theorem integral_temporalTerm_smooth {U : ℝ → SpatialField}
    (hU : ContDiff ℝ ∞ (fun z : SpaceTime => U z.1 z.2))
    {ψ : SpaceTime → Space} (hψ : IsSimilarityTest ψ) :
    (∫ z : SpaceTime, temporalTerm U ψ z) =
      -∫ z : SpaceTime, inner ℝ (deriv (fun t => U t z.2) z.1) (ψ z) := by
  have h1 : (fun z : SpaceTime => temporalTerm U ψ z) =
      fun z : SpaceTime => inner ℝ (U z.1 z.2) (fderiv ℝ ψ z ((1 : ℝ), (0 : Space))) := by
    funext z
    simp only [temporalTerm, Blueprint.L14.timeDerivative_eq_Dt hψ.smooth, Blueprint.L14.Dt]
  rw [h1, ibp_spacetime_inner hU hψ.smooth hψ.compact ((1 : ℝ), (0 : Space))]
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall fun ⟨τ, y⟩ => by
    dsimp only
    rw [fderiv_uncurry_time hU τ y]

private theorem integral_diffusionTerm_smooth {U : ℝ → SpatialField}
    (hU : ContDiff ℝ ∞ (fun z : SpaceTime => U z.1 z.2))
    {ψ : SpaceTime → Space} (hψ : IsSimilarityTest ψ) :
    (∫ z : SpaceTime, diffusionTerm U ψ z) =
      ∫ z : SpaceTime, inner ℝ (IIb.spatialLaplacian (U z.1) z.2) (ψ z) := by
  let F : SpaceTime → Space := fun z => U z.1 z.2
  let d : Fin 3 → SpaceTime := fun i => ((0 : ℝ), coordinateVector i)
  let U₁ : Fin 3 → ℝ → SpatialField := fun i τ y => fderiv ℝ (U τ) y (coordinateVector i)
  let F₁ : Fin 3 → SpaceTime → Space := fun i z => U₁ i z.1 z.2
  have hF₁_def : ∀ i, F₁ i = fun z : SpaceTime => fderiv ℝ F z (d i) :=
    fun i => funext fun ⟨τ, y⟩ => (fderiv_uncurry_space hU τ y (coordinateVector i)).symm
  have hF₁ : ∀ i, ContDiff ℝ ∞ (F₁ i) := fun i => by
    rw [hF₁_def i]
    exact (hU.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hF₂ : ∀ i, ContDiff ℝ ∞ (fun z => fderiv ℝ (F₁ i) z (d i)) := fun i =>
    ((hF₁ i).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hF₂_eq : ∀ i τ y, fderiv ℝ (F₁ i) (τ, y) (d i) =
      fderiv ℝ (fun y' => fderiv ℝ (U τ) y' (coordinateVector i)) y (coordinateVector i) :=
    fun i τ y => fderiv_uncurry_space (hF₁ i) τ y (coordinateVector i)
  have h1 : (fun z : SpaceTime => diffusionTerm U ψ z) =
      fun z : SpaceTime => ∑ i : Fin 3,
        inner ℝ (F z) (fderiv ℝ (Blueprint.L14.Ds ψ i) z (d i)) := by
    funext z
    simp only [diffusionTerm, Blueprint.L14.spatialLaplacian_eq_Lap hψ.smooth,
      Blueprint.L14.Lap, inner_sum, F, d]
  have hintL : ∀ i ∈ (Finset.univ : Finset (Fin 3)),
      Integrable (fun z : SpaceTime =>
        inner ℝ (F z) (fderiv ℝ (Blueprint.L14.Ds ψ i) z (d i))) volume := by
    intro i _
    exact integrable_inner_compact hU.continuous
      (Blueprint.L14.contDiff_fderiv_apply' (Blueprint.L14.contDiff_Ds hψ.smooth i) (d i)).continuous
      ((Blueprint.L14.hasCompactSupport_Ds hψ.compact i).fderiv_apply (𝕜 := ℝ) (d i))
  have hintR : ∀ i ∈ (Finset.univ : Finset (Fin 3)),
      Integrable (fun z : SpaceTime => inner ℝ (fderiv ℝ (F₁ i) z (d i)) (ψ z)) volume :=
    fun i _ => integrable_inner_compact (hF₂ i).continuous hψ.smooth.continuous hψ.compact
  rw [h1, integral_finsetSum _ hintL]
  have hstep : ∀ i : Fin 3,
      (∫ z : SpaceTime, inner ℝ (F z) (fderiv ℝ (Blueprint.L14.Ds ψ i) z (d i))) =
        ∫ z : SpaceTime, inner ℝ (fderiv ℝ (F₁ i) z (d i)) (ψ z) := by
    intro i
    rw [ibp_spacetime_inner hU (Blueprint.L14.contDiff_Ds hψ.smooth i)
        (Blueprint.L14.hasCompactSupport_Ds hψ.compact i) (d i)]
    have heqF₁ : (fun z : SpaceTime => inner ℝ (fderiv ℝ F z (d i)) (Blueprint.L14.Ds ψ i z)) =
        fun z : SpaceTime => inner ℝ (F₁ i z) (fderiv ℝ ψ z (d i)) := by
      funext z
      rw [← congrFun (hF₁_def i) z, Blueprint.L14.Ds]
    rw [show (∫ z : SpaceTime, inner ℝ (fderiv ℝ F z (d i)) (Blueprint.L14.Ds ψ i z)) =
        ∫ z : SpaceTime, inner ℝ (F₁ i z) (fderiv ℝ ψ z (d i)) by rw [heqF₁]]
    rw [ibp_spacetime_inner (hF₁ i) hψ.smooth hψ.compact (d i), neg_neg]
  simp_rw [hstep]
  rw [← integral_finsetSum _ hintR]
  apply integral_congr_ae
  exact Eventually.of_forall fun ⟨τ, y⟩ => by
    dsimp only
    rw [← sum_inner]
    congr 1
    simp only [IIb.spatialLaplacian, IIb.dirSpatialJet]
    exact Finset.sum_congr rfl fun i _ => hF₂_eq i τ y

private theorem integral_dilationTerm_smooth {U : ℝ → SpatialField}
    (hU : ContDiff ℝ ∞ (fun z : SpaceTime => U z.1 z.2))
    {ψ : SpaceTime → Space} (hψ : IsSimilarityTest ψ) :
    (∫ z : SpaceTime, dilationTerm U ψ z) =
      -∫ z : SpaceTime, inner ℝ ((3 : ℝ) • U z.1 z.2 + fderiv ℝ (U z.1) z.2 z.2) (ψ z) := by
  let F : SpaceTime → Space := fun z => U z.1 z.2
  let d : Fin 3 → SpaceTime := fun i => ((0 : ℝ), coordinateVector i)
  let G : Fin 3 → SpaceTime → Space := fun i z => z.2 i • F z
  have hcoord : ∀ i : Fin 3, ContDiff ℝ ∞ (fun z : SpaceTime => z.2 i) := fun i =>
    (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp contDiff_snd
  have hG : ∀ i : Fin 3, ContDiff ℝ ∞ (G i) := fun i => (hcoord i).smul hU
  have hdG : ∀ (i : Fin 3) (τ : ℝ) (y : Space),
      fderiv ℝ (G i) (τ, y) (d i) = F (τ, y) + y i • fderiv ℝ (U τ) y (coordinateVector i) := by
    intro i τ y
    have h1 : HasFDerivAt (fun w : SpaceTime => w.2 i)
        ((EuclideanSpace.proj (𝕜 := ℝ) i).comp (ContinuousLinearMap.snd ℝ ℝ Space)) (τ, y) :=
      (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt.comp (τ, y) (hasFDerivAt_snd (𝕜 := ℝ))
    have h2 : HasFDerivAt F (fderiv ℝ F (τ, y)) (τ, y) :=
      (hU.differentiable (by simp) (τ, y)).hasFDerivAt
    have hsm : HasFDerivAt (G i) _ (τ, y) := h1.smul h2
    rw [hsm.fderiv]
    change y i • fderiv ℝ (fun z : SpaceTime => U z.1 z.2) (τ, y) ((0 : ℝ), coordinateVector i) +
        (coordinateVector i : Space) i • F (τ, y) =
      F (τ, y) + y i • fderiv ℝ (U τ) y (coordinateVector i)
    have hci : (coordinateVector i : Space) i = 1 := by
      simp [coordinateVector]
    rw [hci, one_smul, fderiv_uncurry_space hU τ y (coordinateVector i), add_comm]
  have hdecomp : (fun z : SpaceTime => dilationTerm U ψ z) =
      fun z : SpaceTime => ∑ i : Fin 3, inner ℝ (G i z) (fderiv ℝ ψ z (d i)) := by
    funext z
    rw [dilationTerm, Blueprint.L14.spatialDerivative_eq hψ.smooth]
    have hz2 : ((0 : ℝ), z.2) = ∑ i : Fin 3, z.2 i • d i := by
      refine Prod.ext (by simp [d, Prod.fst_sum]) ?_
      rw [Prod.snd_sum]
      exact (Blueprint.L10.space_sum_single z.2).symm
    rw [hz2, map_sum, inner_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, real_inner_smul_right, ← real_inner_smul_left]
  have hintL : ∀ i ∈ (Finset.univ : Finset (Fin 3)),
      Integrable (fun z : SpaceTime => inner ℝ (G i z) (fderiv ℝ ψ z (d i))) volume := by
    intro i _
    exact integrable_inner_compact (hG i).continuous
      (Blueprint.L14.contDiff_Ds hψ.smooth i).continuous
      (Blueprint.L14.hasCompactSupport_Ds hψ.compact i)
  have hintR : ∀ i ∈ (Finset.univ : Finset (Fin 3)),
      Integrable (fun z : SpaceTime => inner ℝ (fderiv ℝ (G i) z (d i)) (ψ z)) volume := by
    intro i _
    have hdf : ContDiff ℝ ∞ (fun z => fderiv ℝ (G i) z (d i)) :=
      ((hG i).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
    exact integrable_inner_compact hdf.continuous hψ.smooth.continuous hψ.compact
  rw [hdecomp, integral_finsetSum _ hintL]
  simp_rw [fun i => ibp_spacetime_inner (hG i) hψ.smooth hψ.compact (d i)]
  rw [Finset.sum_neg_distrib, ← integral_finsetSum _ hintR]
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall fun ⟨τ, y⟩ => by
    dsimp only
    rw [← sum_inner]
    congr 1
    simp_rw [hdG _ τ y]
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    have hfsum : (∑ i : Fin 3, y i • fderiv ℝ (U τ) y (coordinateVector i)) =
        fderiv ℝ (U τ) y y := by
      simp_rw [← map_smul, ← map_sum]
      congr 1
      exact Blueprint.L10.space_sum_single y
    rw [hfsum]
    change (3 : ℕ) • U τ y + fderiv ℝ (U τ) y y = (3 : ℝ) • U τ y + fderiv ℝ (U τ) y y
    rw [← Nat.cast_smul_eq_nsmul ℝ 3 (U τ y)]
    norm_num

/-! ## Pointwise projected equation to `SolvesSimilarityBackground` -/

private theorem projectedConvection_eq_integral_of_smooth_leray
    {f G : SpatialField} {C : ℝ} (hf : ContDiff ℝ 2 f) (hsol : IsSolenoidal f)
    (h0 : eLpNorm f 4 volume ≤ ENNReal.ofReal C)
    (h1 : eLpNorm (fun y => fderiv ℝ f y) 4 volume ≤ ENNReal.ofReal C)
    (h2 : eLpNorm (fun y => iteratedFDeriv ℝ 2 f y) 4 volume ≤ ENNReal.ofReal C)
    (hG : G =ᵐ[volume] ⇑(Leray.projection (toL2 (fun y => fderiv ℝ f y (f y)))))
    {φ : Space → Space} (hφ : IsVectorTest φ) :
    ColumnsL2 (tensorColumns f f) ∧
      lerayDivPairing (tensorColumns f f) φ = ∫ y : Space, inner ℝ (G y) (φ y) := by
  let Pcol := IIb.B3RemH2Sub.stressColH2 f hf h0 h1 h2
  have hPval : ∀ j : Fin 3, ((Pcol j).value : SpatialField) =ᵐ[volume] tensorColumns f f j :=
    fun j => coeFn_toL2 (IIb.B3RemH2Sub.memLp_stressCol hf h0 j).1
  have hMinus := Blueprint.L10.isMinusLerayDiv_minusLerayDivX Pcol (tensorColumns f f) hPval
  refine ⟨hMinus.1, ?_⟩
  have hpair := hMinus.2 φ hφ
  rw [IIb.B3RemH2Sub.Xclass_minusLerayDivX_stressColH2 f hf hsol h0 h1 h2, inner_neg_left] at hpair
  have hpair' : lerayDivPairing (tensorColumns f f) φ =
      inner ℝ (Leray.projection (toL2 (fun y => fderiv ℝ f y (f y)))) (toL2 φ) :=
    neg_inj.mp hpair.symm
  have hGm2 : MemLp G 2 volume :=
    (Lp.memLp (Leray.projection (toL2 (fun y => fderiv ℝ f y (f y))))).ae_eq hG.symm
  have htoL2 : toL2 G = Leray.projection (toL2 (fun y => fderiv ℝ f y (f y))) :=
    Blueprint.L10.toL2_of_ae_eq_coeFn hG.symm
  rw [hpair', ← htoL2, Cons.C09.inner_toL2_toL2 hGm2 (Blueprint.L10.vectorTest_memLp hφ 2)]

private def linRHS (ν : ℝ) (U : ℝ → SpatialField) (z : SpaceTime) : Space :=
  -deriv (fun t => U t z.2) z.1 + ν • IIb.spatialLaplacian (U z.1) z.2 +
    (1 / 2 : ℝ) • U z.1 z.2 + (1 / 2 : ℝ) • fderiv ℝ (U z.1) z.2 z.2

private theorem eq_linRHS_of_sub_eq {a b c d g : Space} (h : a - b = c + d - g) :
    g = -a + c + d + b := by
  have h2 : g = -(a - b) + (c + d) := by rw [h]; abel
  rw [h2]; abel

private theorem lin_inner_identity (ν r1 r2 r3 r4 : ℝ) :
    -r1 + ν * r2 - r3 - (1 / 2 : ℝ) * (-(3 * r3 + r4)) =
      -r1 + ν * r2 + (1 / 2 : ℝ) * r3 + (1 / 2 : ℝ) * r4 := by
  ring

private theorem continuous_deriv_time_of_joint {U : ℝ → SpatialField}
    (hsmooth : ContDiff ℝ ∞ (fun z : SpaceTime => U z.1 z.2)) :
    Continuous (fun z : SpaceTime => deriv (fun t => U t z.2) z.1) := by
  have heq : (fun z : SpaceTime => deriv (fun t => U t z.2) z.1) =
      fun z : SpaceTime => fderiv ℝ (fun w : SpaceTime => U w.1 w.2) z ((1 : ℝ), (0 : Space)) :=
    funext fun ⟨τ, y⟩ => (fderiv_uncurry_time hsmooth τ y).symm
  rw [heq]
  exact ((hsmooth.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).continuous

private theorem continuous_radial_fderiv_of_joint {U : ℝ → SpatialField}
    (hsmooth : ContDiff ℝ ∞ (fun z : SpaceTime => U z.1 z.2)) :
    Continuous (fun z : SpaceTime => fderiv ℝ (U z.1) z.2 z.2) := by
  have heq : (fun z : SpaceTime => fderiv ℝ (U z.1) z.2 z.2) =
      fun z : SpaceTime => fderiv ℝ (fun w : SpaceTime => U w.1 w.2) z ((0 : ℝ), z.2) :=
    funext fun ⟨τ, y⟩ => (fderiv_uncurry_space hsmooth τ y y).symm
  rw [heq]
  exact (hsmooth.continuous_fderiv (by simp)).clm_apply
    (continuous_const.prodMk continuous_snd)

private theorem continuous_linRHS (ν : ℝ) {U : ℝ → SpatialField}
    (hsmooth : ContDiff ℝ ∞ (fun z : SpaceTime => U z.1 z.2)) :
    Continuous (linRHS ν U) := by
  unfold linRHS
  have h1 : Continuous (fun z : SpaceTime => -deriv (fun t => U t z.2) z.1) :=
    (continuous_deriv_time_of_joint hsmooth).neg
  have h2 : Continuous (fun z : SpaceTime => ν • IIb.spatialLaplacian (U z.1) z.2) :=
    (contDiff_spatialLaplacian_joint hsmooth).continuous.const_smul ν
  have h3 : Continuous (fun z : SpaceTime => (1 / 2 : ℝ) • U z.1 z.2) :=
    hsmooth.continuous.const_smul (1 / 2 : ℝ)
  have h4 : Continuous (fun z : SpaceTime => (1 / 2 : ℝ) • fderiv ℝ (U z.1) z.2 z.2) :=
    (continuous_radial_fderiv_of_joint hsmooth).const_smul (1 / 2 : ℝ)
  exact ((h1.add h2).add h3).add h4

private theorem integral_linearBackgroundIntegrand_smooth (ν : ℝ) {U : ℝ → SpatialField}
    (hsmooth : ContDiff ℝ ∞ (fun z : SpaceTime => U z.1 z.2))
    {ψ : SpaceTime → Space} (hψ : IsSimilarityTest ψ)
    (i1 : Integrable (temporalTerm U ψ) volume)
    (i2 : Integrable (diffusionTerm U ψ) volume)
    (i3 : Integrable (pairTerm U ψ) volume)
    (i4 : Integrable (dilationTerm U ψ) volume) :
    (∫ z : SpaceTime, linearBackgroundIntegrand ν U ψ z) =
      ∫ z : SpaceTime, inner ℝ (linRHS ν U z) (ψ z) := by
  have i2' : Integrable (fun z => ν * diffusionTerm U ψ z) volume := i2.const_mul ν
  have i4' : Integrable (fun z => (1 / 2 : ℝ) * dilationTerm U ψ z) volume :=
    i4.const_mul (1 / 2 : ℝ)
  have i12 : Integrable (fun z => temporalTerm U ψ z + ν * diffusionTerm U ψ z) volume :=
    i1.add i2'
  have i123 : Integrable
      (fun z => temporalTerm U ψ z + ν * diffusionTerm U ψ z - pairTerm U ψ z) volume :=
    i12.sub i3
  unfold linearBackgroundIntegrand
  rw [integral_sub i123 i4', integral_sub i12 i3, integral_add i1 i2',
    integral_const_mul, integral_const_mul,
    integral_temporalTerm_smooth hsmooth hψ,
    integral_diffusionTerm_smooth hsmooth hψ,
    integral_dilationTerm_smooth hsmooth hψ]
  have j1 : Integrable (fun z : SpaceTime =>
      inner ℝ (deriv (fun t => U t z.2) z.1) (ψ z)) volume :=
    integrable_inner_compact (continuous_deriv_time_of_joint hsmooth) hψ.smooth.continuous
      hψ.compact
  have j2 : Integrable (fun z : SpaceTime =>
      inner ℝ (IIb.spatialLaplacian (U z.1) z.2) (ψ z)) volume :=
    integrable_inner_compact (contDiff_spatialLaplacian_joint hsmooth).continuous
      hψ.smooth.continuous hψ.compact
  have j4 : Integrable (fun z : SpaceTime =>
      inner ℝ ((3 : ℝ) • U z.1 z.2 + fderiv ℝ (U z.1) z.2 z.2) (ψ z)) volume :=
    integrable_inner_compact
      ((hsmooth.continuous.const_smul (3 : ℝ)).add (continuous_radial_fderiv_of_joint hsmooth))
      hψ.smooth.continuous hψ.compact
  have k1 : Integrable (fun z : SpaceTime =>
      -inner ℝ (deriv (fun t => U t z.2) z.1) (ψ z)) volume := j1.neg
  have k2 : Integrable (fun z : SpaceTime =>
      ν * inner ℝ (IIb.spatialLaplacian (U z.1) z.2) (ψ z)) volume := j2.const_mul ν
  have k12 : Integrable (fun z : SpaceTime =>
      -inner ℝ (deriv (fun t => U t z.2) z.1) (ψ z) +
        ν * inner ℝ (IIb.spatialLaplacian (U z.1) z.2) (ψ z)) volume := k1.add k2
  have k123 : Integrable (fun z : SpaceTime =>
      -inner ℝ (deriv (fun t => U t z.2) z.1) (ψ z) +
        ν * inner ℝ (IIb.spatialLaplacian (U z.1) z.2) (ψ z) - pairTerm U ψ z) volume :=
    k12.sub i3
  have k4 : Integrable (fun z : SpaceTime =>
      (1 / 2 : ℝ) * -inner ℝ ((3 : ℝ) • U z.1 z.2 + fderiv ℝ (U z.1) z.2 z.2) (ψ z)) volume :=
    j4.neg.const_mul (1 / 2 : ℝ)
  rw [← integral_neg, ← integral_const_mul, ← integral_neg, ← integral_const_mul,
    ← integral_add k1 k2, ← integral_sub k12 i3, ← integral_sub k123 k4]
  apply integral_congr_ae
  exact Eventually.of_forall fun ⟨τ, y⟩ => by
    dsimp only [pairTerm, linRHS]
    simp only [inner_add_left, inner_neg_left, real_inner_smul_left]
    exact lin_inner_identity ν _ _ _ _

private theorem solvesSimilarityBackground_of_smooth_evol {ν : ℝ} {U G : ℝ → SpatialField}
    (hsmooth : ContDiff ℝ ∞ (fun z : SpaceTime => U z.1 z.2))
    (hsol : ∀ τ, IsSolenoidal (U τ))
    (hUL4 : ∃ C : ℝ, ∀ τ : ℝ,
      eLpNorm (U τ) 4 volume ≤ ENNReal.ofReal C ∧
      eLpNorm (fun y => fderiv ℝ (U τ) y) 4 volume ≤ ENNReal.ofReal C ∧
      eLpNorm (fun y => iteratedFDeriv ℝ 2 (U τ) y) 4 volume ≤ ENNReal.ofReal C)
    (hpt : ∀ τ y, deriv (fun t => U t y) τ - (1 / 2 : ℝ) • fderiv ℝ (U τ) y y =
      ν • IIb.spatialLaplacian (U τ) y + (1 / 2 : ℝ) • U τ y - G τ y)
    (hGae : ∀ τ, G τ =ᵐ[volume]
      ⇑(Leray.projection (toL2 (fun y => fderiv ℝ (U τ) y (U τ y))))) :
    SolvesSimilarityBackground ν U := by
  obtain ⟨Cu, hCu⟩ := hUL4
  have hUs : ∀ τ, ContDiff ℝ 2 (U τ) := fun τ =>
    (hsmooth.comp (contDiff_const.prodMk contDiff_id)).of_le (by simp)
  have hCols : ∀ τ, ColumnsL2 (tensorColumns (U τ) (U τ)) := fun τ =>
    fun j => (IIb.B3RemH2Sub.memLp_stressCol (hUs τ) (hCu τ).1 j).1
  have htemp : ∀ ψ, IsSimilarityTest ψ → Integrable (temporalTerm U ψ) volume := by
    intro ψ hψ
    refine (integrable_inner_compact hsmooth.continuous
      (Blueprint.L14.contDiff_Dt hψ.smooth).continuous
      (Blueprint.L14.hasCompactSupport_Dt hψ.compact)).congr (Eventually.of_forall fun z => ?_)
    dsimp only
    simp only [temporalTerm, Blueprint.L14.timeDerivative_eq_Dt hψ.smooth]
  have hdiff : ∀ ψ, IsSimilarityTest ψ → Integrable (diffusionTerm U ψ) volume := by
    intro ψ hψ
    refine (integrable_inner_compact hsmooth.continuous
      (Blueprint.L14.contDiff_Lap hψ.smooth).continuous
      (Blueprint.L14.hasCompactSupport_Lap hψ.compact)).congr (Eventually.of_forall fun z => ?_)
    dsimp only
    simp only [diffusionTerm, Blueprint.L14.spatialLaplacian_eq_Lap hψ.smooth]
  have hpair : ∀ ψ, IsSimilarityTest ψ → Integrable (pairTerm U ψ) volume := fun ψ hψ =>
    integrable_inner_compact hsmooth.continuous hψ.smooth.continuous hψ.compact
  have hdil : ∀ ψ, IsSimilarityTest ψ → Integrable (dilationTerm U ψ) volume := by
    intro ψ hψ
    let gD : SpaceTime → Space := fun z => fderiv ℝ ψ z ((0 : ℝ), z.2)
    have hgD : Continuous gD :=
      (hψ.smooth.continuous_fderiv (by simp)).clm_apply (continuous_const.prodMk continuous_snd)
    have hgcD : HasCompactSupport gD :=
      HasCompactSupport.intro (hψ.compact.fderiv (𝕜 := ℝ)).isCompact fun z hz => by
        simp [gD, image_eq_zero_of_notMem_tsupport hz]
    refine (integrable_inner_compact hsmooth.continuous hgD hgcD).congr
      (Eventually.of_forall fun z => ?_)
    dsimp only
    simp only [dilationTerm, gD, Blueprint.L14.spatialDerivative_eq hψ.smooth]
  have hG_eq_L : ∀ z : SpaceTime, G z.1 z.2 = linRHS ν U z := fun ⟨τ, y⟩ =>
    eq_linRHS_of_sub_eq (hpt τ y)
  have hL_cont : Continuous (linRHS ν U) := continuous_linRHS ν hsmooth
  have hproj_eq : ∀ ψ, IsSimilarityTest ψ → ∀ τ : ℝ,
      projectedConvection U ψ τ = ∫ y : Space, inner ℝ (linRHS ν U (τ, y)) (ψ (τ, y)) := by
    intro ψ hψ τ
    have hslice := Blueprint.L14.isVectorTest_slice hψ.smooth hψ.compact τ
    have hc := (projectedConvection_eq_integral_of_smooth_leray (hUs τ) (hsol τ)
      (hCu τ).1 (hCu τ).2.1 (hCu τ).2.2 (hGae τ) hslice).2
    rw [projectedConvection, hc]
    apply integral_congr_ae
    exact Eventually.of_forall fun y => by
      dsimp only
      rw [hG_eq_L (τ, y), slice]
  have hconv_int : ∀ ψ, IsSimilarityTest ψ → Integrable (projectedConvection U ψ) volume := by
    intro ψ hψ
    have hIL : Integrable (fun z : SpaceTime => inner ℝ (linRHS ν U z) (ψ z)) volume :=
      integrable_inner_compact hL_cont hψ.smooth.continuous hψ.compact
    rw [Measure.volume_eq_prod] at hIL
    refine hIL.integral_prod_left.congr (Eventually.of_forall fun τ => ?_)
    dsimp only
    exact (hproj_eq ψ hψ τ).symm
  refine ⟨hCols, htemp, hdiff, hpair, hdil, hconv_int, fun ψ hψ => ?_⟩
  have hIL : Integrable (fun z : SpaceTime => inner ℝ (linRHS ν U z) (ψ z)) volume :=
    integrable_inner_compact hL_cont hψ.smooth.continuous hψ.compact
  have hproj_int : (∫ τ : ℝ, projectedConvection U ψ τ) =
      ∫ z : SpaceTime, inner ℝ (linRHS ν U z) (ψ z) := by
    simp_rw [hproj_eq ψ hψ]
    have hIL' := hIL
    rw [Measure.volume_eq_prod] at hIL'
    rw [Measure.volume_eq_prod, integral_prod _ hIL']
  have hlin_eq := integral_linearBackgroundIntegrand_smooth ν hsmooth hψ
    (htemp ψ hψ) (hdiff ψ hψ) (hpair ψ hψ) (hdil ψ hψ)
  rw [hlin_eq, hproj_int, sub_self]

/-! ## Global Riesz pressure recovery (`IsB3Output` from `IsB3Core` and `SolvesSimilarityBackground`) -/

private theorem norm_toLp_sq_eq_integral {f : Space → ℝ} (hf : MemLp f 2 volume) :
    ‖hf.toLp f‖ ^ 2 = ∫ y : Space, ‖f y‖ ^ 2 := by
  rw [Lp.norm_toLp, hf.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top]
  have h0 : 0 ≤ ∫ y : Space, ‖f y‖ ^ (2 : ℝ≥0∞).toReal :=
    integral_nonneg fun _ => by positivity
  rw [ENNReal.toReal_ofReal (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul h0]
  simp

private theorem isB3Output_of_core_and_projected {ν P : ℝ} (hν : 0 < ν) (hP : 0 < P)
    {a : SpatialField} {U : ℝ → SpatialField} {Q : ℝ → SobolevGraph.H2}
    (hsmooth : ContDiff ℝ ∞ (fun z : SpaceTime => U z.1 z.2))
    (hcore : IsB3Core ν P a U Q) (hbg : SolvesSimilarityBackground ν U) :
    ∃ pres : ℝ → Space → ℝ, IsB3Output ν P a U Q pres := by
  let hT := hbg.tensor_memL2
  obtain ⟨Hpath, hHc, hH⟩ := Cons.C03.Concrete.exists_continuous_heatProfile_L4_of_datum
    hν hcore.datum_smooth hcore.datum_bounds
  let W : ℝ → Lp Space 4 volume := fun τ => Hpath τ + Cons.C03.Concrete.h2ValueL4 (Q τ)
  have hWc : Continuous W :=
    hHc.add (Cons.C03.Concrete.continuous_h2Value_L4 Q hcore.remainder_continuous)
  have hW : ∀ τ, (W τ : SpatialField) =ᵐ[volume] U τ := by
    intro τ
    filter_upwards [Lp.coeFn_add (Hpath τ) (Cons.C03.Concrete.h2ValueL4 (Q τ)), hH τ,
      Cons.C03.Concrete.h2Value_L4_ae (Q τ), hcore.remainder τ] with y hsum hheat hrem hremEq
    rw [hsum, Pi.add_apply, hheat, hrem, hremEq, Pi.sub_apply, add_sub_cancel]
  let Ppath := Cons.C03.Concrete.stressPressureL2Path U hT
  have hPcont : Continuous Ppath :=
    Cons.C03.Concrete.continuous_stressPressureL2Path U hT
      (fun i j => Cons.C03.Concrete.continuous_tensorEntryL2_of_L4 U hT W hWc hW i j)
  have hPper : Function.Periodic Ppath P :=
    Cons.C03.Concrete.periodic_stressPressureL2Path U hT
      (fun i j => Cons.C03.Concrete.periodic_tensorEntryL2 U hT hcore.background_periodic i j)
  obtain ⟨Cp, hCp⟩ := Loc.L03Evolution.exists_norm_le_of_periodic hP.ne' hPper hPcont
  obtain ⟨pres, hjoint, hpres_ae'⟩ := BochnerTime.exists_isJointRep_of_continuousOn
    (μ := volume) (s := Set.univ) MeasurableSet.univ hPcont.continuousOn
  have hpres_ae : ∀ τ, pres τ =ᵐ[volume] Ppath τ := fun τ => hpres_ae' τ (Set.mem_univ τ)
  have hpres_L2 : ∀ τ, MemLp (pres τ) 2 volume := fun τ =>
    (Lp.memLp (Ppath τ)).ae_eq (hpres_ae τ).symm
  have hSq : ∀ τ, ∫ y : Space, ‖pres τ y‖ ^ 2 ≤ Cp ^ 2 := by
    intro τ
    have hclass : (hpres_L2 τ).toLp (pres τ) = Ppath τ := by
      apply Lp.ext
      filter_upwards [(hpres_L2 τ).coeFn_toLp, hpres_ae τ] with y h1 h2
      exact h1.trans h2
    have hnorm : ‖(hpres_L2 τ).toLp (pres τ)‖ ≤ Cp := by rw [hclass]; exact hCp τ
    have hCp0 : 0 ≤ Cp := (norm_nonneg _).trans (hCp τ)
    calc ∫ y : Space, ‖pres τ y‖ ^ 2
        = ‖(hpres_L2 τ).toLp (pres τ)‖ ^ 2 := (norm_toLp_sq_eq_integral (hpres_L2 τ)).symm
      _ ≤ Cp ^ 2 := by nlinarith [norm_nonneg ((hpres_L2 τ).toLp (pres τ))]
  have hslab : ∀ a₀ b₀ : ℝ,
      MemLp (fun z : SpaceTime =>
        (Icc a₀ b₀ ×ˢ (Set.univ : Set Space)).indicator (Function.uncurry pres) z) 2 volume := by
    intro a₀ b₀
    let slabP : SpaceTime → ℝ :=
      (Icc a₀ b₀ ×ˢ (Set.univ : Set Space)).indicator (Function.uncurry pres)
    have hmeas : StronglyMeasurable slabP :=
      hjoint.indicator (measurableSet_Icc.prod MeasurableSet.univ)
    have hnormMeas : AEStronglyMeasurable (fun z : SpaceTime => ‖slabP z‖ ^ 2) volume :=
      hmeas.aestronglyMeasurable.norm.pow 2
    rw [memLp_two_iff_integrable_sq_norm hmeas.aestronglyMeasurable, Measure.volume_eq_prod]
    refine (integrable_prod_iff hnormMeas).mpr ⟨?_, ?_⟩
    · filter_upwards [] with τ
      by_cases hτ : τ ∈ Icc a₀ b₀
      · simpa [slabP, hτ] using (memLp_two_iff_integrable_sq_norm (hpres_L2 τ).1).mp (hpres_L2 τ)
      · simp [slabP, hτ]
    · have hdom : Integrable ((Icc a₀ b₀).indicator (fun _ : ℝ => Cp ^ 2)) volume :=
        (integrableOn_const (C := Cp ^ 2) measure_Icc_lt_top.ne).integrable_indicator
          measurableSet_Icc
      refine Integrable.mono' hdom hnormMeas.norm.integral_prod_right' ?_
      filter_upwards [] with τ
      by_cases hτ : τ ∈ Icc a₀ b₀
      · have hn : 0 ≤ ∫ y : Space, ‖pres τ y‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
        have hIntNorm : (∫ y : Space, ‖‖slabP (τ, y)‖ ^ 2‖) = ∫ y : Space, ‖pres τ y‖ ^ 2 := by
          apply integral_congr_ae
          filter_upwards [] with y
          simp [slabP, hτ]
        rw [hIntNorm, Real.norm_of_nonneg hn]
        simpa [hτ] using hSq τ
      · simp [slabP, hτ]
  have hpresInt : ∀ ψ, IsSimilarityTest ψ → Integrable (pressureSimilarityTerm pres ψ) volume := by
    intro ψ hψ
    let Tset : Set ℝ := Prod.fst '' tsupport (Blueprint.L14.Div ψ)
    have hTc : IsCompact Tset :=
      (Blueprint.L14.hasCompactSupport_Div hψ.compact).isCompact.image continuous_fst
    obtain ⟨a₀, b₀, htime⟩ : ∃ a₀ b₀ : ℝ, ∀ z, Blueprint.L14.Div ψ z ≠ 0 → z.1 ∈ Icc a₀ b₀ := by
      by_cases hne : Tset.Nonempty
      · refine ⟨sInf Tset, sSup Tset, fun z hz => ?_⟩
        have hm : z.1 ∈ Tset := ⟨z, subset_tsupport _ hz, rfl⟩
        exact ⟨csInf_le hTc.bddBelow hm, le_csSup hTc.bddAbove hm⟩
      · refine ⟨0, 0, fun z hz => (hne ⟨z.1, z, subset_tsupport _ hz, rfl⟩).elim⟩
    have hDiv : MemLp (Blueprint.L14.Div ψ) 2 volume :=
      (Blueprint.L14.contDiff_Div hψ.smooth).continuous.memLp_of_hasCompactSupport
        (Blueprint.L14.hasCompactSupport_Div hψ.compact)
    have hprod : Integrable (fun z : SpaceTime =>
        (Icc a₀ b₀ ×ˢ (Set.univ : Set Space)).indicator (Function.uncurry pres) z *
          Blueprint.L14.Div ψ z) volume :=
      (hslab a₀ b₀).integrable_mul hDiv
    refine hprod.congr (Eventually.of_forall fun ⟨τ, y⟩ => ?_)
    dsimp only [pressureSimilarityTerm]
    rw [Blueprint.L14.spatialDivergence_eq_Div hψ.smooth]
    by_cases hdiv : Blueprint.L14.Div ψ (τ, y) = 0
    · simp [hdiv]
    · have ht := htime (τ, y) hdiv
      simp [ht]
  have hconvInt : ∀ ψ, IsSimilarityTest ψ → Integrable (convectionTerm U ψ) volume := by
    intro ψ hψ
    let gC : SpaceTime → Space := fun z => fderiv ℝ ψ z ((0 : ℝ), U z.1 z.2)
    have hgC : Continuous gC :=
      (hψ.smooth.continuous_fderiv (by simp)).clm_apply
        (continuous_const.prodMk hsmooth.continuous)
    have hgcC : HasCompactSupport gC :=
      HasCompactSupport.intro (hψ.compact.fderiv (𝕜 := ℝ)).isCompact fun z hz => by
        simp [gC, image_eq_zero_of_notMem_tsupport hz]
    refine (integrable_inner_compact hsmooth.continuous hgC hgcC).congr
      (Eventually.of_forall fun z => ?_)
    dsimp only
    simp only [convectionTerm, gC, Blueprint.L14.spatialDerivative_eq hψ.smooth]
  have hrel : ∀ τ Φ, IsSpatialTest Φ →
      Cons.C09.colPairing (Cons.C09.stressL2 U pres τ) (Cons.C09.hessL2 Φ) = 0 := by
    intro τ Φ hΦ
    have hstress : Cons.C09.stressL2 U pres τ =
        Cons.C09.stressL2 U (Cons.C03.Concrete.stressPressure U hT) τ := by
      funext j
      simp only [Cons.C09.stressL2]
      congr 1
      apply Infra.JointMeasurableRep.toL2_congr_ae
      filter_upwards [hpres_ae τ] with y hy
      simpa [Cons.C03.Concrete.stressPressure] using congrArg (fun r : ℝ => r • coordinateVector j) hy
    rw [hstress]
    exact Cons.C03.Concrete.stressPressure_c09Relation_path U hT τ hΦ
  refine ⟨pres, { hcore with
    products_L2 := hT
    pressure_L2 := hpres_L2
    equation := {
      temporal_integrable := hbg.temporal_integrable
      diffusion_integrable := hbg.diffusion_integrable
      pair_integrable := hbg.pair_integrable
      dilation_integrable := hbg.dilation_integrable
      convection_integrable := hconvInt
      pressure_integrable := hpresInt
      identity := fun ψ hψ => by
        have hlin : Integrable (linearBackgroundIntegrand ν U ψ) volume :=
          (((hbg.temporal_integrable ψ hψ).add
            ((hbg.diffusion_integrable ψ hψ).const_mul ν)).sub
            (hbg.pair_integrable ψ hψ)).sub
            ((hbg.dilation_integrable ψ hψ).const_mul (1 / 2 : ℝ))
        have hc := hconvInt ψ hψ
        have hp := hpresInt ψ hψ
        have hcp : Integrable
            (fun z => convectionTerm U ψ z + pressureSimilarityTerm pres ψ z) volume := hc.add hp
        have hc' := hc; have hp' := hp; have hcp' := hcp
        rw [Measure.volume_eq_prod] at hc' hp' hcp'
        have hphaseEq : projectedConvection U ψ =ᵐ[volume] fun τ =>
            -∫ y, (convectionTerm U ψ (τ, y) + pressureSimilarityTerm pres ψ (τ, y)) := by
          filter_upwards [hc'.prod_right_ae, hp'.prod_right_ae] with τ hcτ hpτ
          rw [Cons.C09.projectedConvection_eq_of_relation (hT τ) (hpres_L2 τ) (hrel τ) hψ,
            integral_add hcτ hpτ]
          ring
        have hprojInt : (∫ τ, projectedConvection U ψ τ) =
            -∫ z, (convectionTerm U ψ z + pressureSimilarityTerm pres ψ z) := by
          rw [integral_congr_ae hphaseEq, integral_neg, Measure.volume_eq_prod,
            integral_prod _ hcp']
        have hweak := hbg.identity ψ hψ
        have hadd : (∫ z, (linearBackgroundIntegrand ν U ψ z + convectionTerm U ψ z +
            pressureSimilarityTerm pres ψ z)) =
            (∫ z, linearBackgroundIntegrand ν U ψ z) +
              ∫ z, (convectionTerm U ψ z + pressureSimilarityTerm pres ψ z) := by
          rw [← integral_add hlin hcp]
          exact integral_congr_ae (Eventually.of_forall fun z => by dsimp only; ring)
        linarith [hadd, hprojInt, hweak]
    }
  }⟩

/-! ## Main theorem: `ballB3Output` -/

theorem ballB3Output : UnforcedLeray.Short.Spine.SPPII.BallB3Output := by
  let h4 := IIb.affineInletFacts_proof
  let hQ1 := IIb.quadBound_of h4
  let hS1 := _root_.strongFirstDerivative_of h4 hQ1
  let hS2 := IIb.strongAllOrders_of h4 hQ1 hS1
  intro Sig lam q hSig hq m hm dm dp hdm h2m C₁ k₁ hC₁
  obtain ⟨ν₁, hν₁, HB3⟩ :=
    IIb.ballHeatRemainder_proof Sig lam q hSig hq m hm dm dp hdm h2m C₁ k₁ hC₁
  obtain ⟨_, _, ν₂, _, hν₂, HSR⟩ :=
    IIb.strongRegularity_proof Sig lam q hSig hq m hm dm dp hdm h2m C₁ k₁ hC₁
  obtain ⟨ν₃, hν₃, HS2⟩ := hS2 Sig lam q hSig hq m hm dm dp hdm h2m C₁ k₁ hC₁
  obtain ⟨ν₄, hν₄, HC⟩ :=
    _root_.bgComovingFirstEquation_proof Sig lam q hSig hq m hm dm dp hdm h2m C₁ k₁ hC₁
  refine ⟨min (min ν₁ ν₂) (min ν₃ ν₄), lt_min (lt_min hν₁ hν₂) (lt_min hν₃ hν₄),
    fun p d hreg hν hS hq' z hz hzn => ?_⟩
  have hν₁' : p.ν ≤ ν₁ := hν.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hν₂' : p.ν ≤ ν₂ := hν.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hν₃' : p.ν ≤ ν₃ := hν.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hν₄' : p.ν ≤ ν₄ := hν.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨hUL4, ⟨Q, hCore⟩, hEvol⟩ := HB3 p d hreg hν₁' hS hq' z hz hzn
  obtain ⟨hsmooth, -, -, -, -, -, -⟩ := HSR p d hreg hν₂' hS hq' z hz hzn
  obtain ⟨hgrad, hslice, hRaw, hInlet⟩ := HS2 p d hreg hν₃' hS hq' z hz hzn
  have hfam : IIb.IsUniformSmoothL4SliceFamily (IIb.bgField p z) :=
    IIb.isUniformSmoothL4SliceFamily_bgField_of_morreyL4
      (IIb.smoothMorreyL4Bound_of_field IIb.smoothMorreyL4FieldBound_proof) p z hslice
  have hCom := HC p d hreg hν₄' hS hq' z hz hzn hgrad hslice hfam hRaw hInlet
  have hConv : IIb.IsUniformSmoothL4SliceFamily
      (fun τ => IIb.spatialConvect (IIb.bgField p z τ) (IIb.bgField p z τ)) :=
    IIb.HigherPhaseSub.sliceFamily_spatialConvect hfam hfam
  have hpt : ∀ τ y,
      deriv (fun t => IIb.bgField p z t y) τ -
          (1 / 2 : ℝ) • fderiv ℝ (IIb.bgField p z τ) y y =
        p.ν • IIb.spatialLaplacian (IIb.bgField p z τ) y +
          (1 / 2 : ℝ) • IIb.bgField p z τ y -
          IIb.smoothConvectiveLeray (IIb.bgField p z) (IIb.bgField p z) τ y := by
    intro τ y
    have h1 := IIb.B3EvolAux.hasDerivAt_comoving (hsmooth.differentiable (by simp) (τ, y))
    have h2 := hCom [] τ y
    simp only [IIb.dirSpatialJet_nil, List.length_nil, Nat.cast_zero, zero_div, zero_smul,
      add_zero] at h2
    exact h1.unique h2
  have hGae : ∀ τ,
      IIb.smoothConvectiveLeray (IIb.bgField p z) (IIb.bgField p z) τ =ᵐ[volume]
        ⇑(Leray.projection (toL2 (fun y =>
          fderiv ℝ (IIb.bgField p z τ) y (IIb.bgField p z τ y)))) := by
    intro τ
    obtain ⟨hF4, -, hGaeτ⟩ := (IIb.smoothLeraySliceRegularity_proof.1 _ hConv).1 τ
    have hP := RieszLp.lerayLp_toLp_ae_eq_projection (p := 4) (by norm_num) (by norm_num)
      hF4 (hEvol τ).1
    exact hGaeτ.trans hP
  have hbg : SolvesSimilarityBackground p.ν (IIb.bgField p z) :=
    solvesSimilarityBackground_of_smooth_evol hsmooth hCore.background_solenoidal hUL4 hpt hGae
  obtain ⟨pres, hOut⟩ :=
    isB3Output_of_core_and_projected p.ν_pos p.period_pos hsmooth hCore hbg
  exact ⟨Q, pres, hOut⟩

end UnforcedLeray.Short.Spine.SPPII
