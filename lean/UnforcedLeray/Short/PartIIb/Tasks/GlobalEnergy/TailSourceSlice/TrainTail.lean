import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F5_2
import UnforcedLeray.Short.PartI.Sub.PartI_T25_1
import UnforcedLeray.Short.PartI.Tasks.OverlapHighNorm
import UnforcedLeray.Short.PartI.Tasks.OverlapFluctuationDecay
import UnforcedLeray.Short.PartI.Tasks.OverlapMeanPrimitive
import UnforcedLeray.Short.PartI.Tasks.OverlapMeanDecay
import UnforcedLeray.Short.PartI.Tasks.TrainOverlapProof
import UnforcedLeray.Short.PartI.Tasks.TrainVorticityTail
import UnforcedLeray.Short.PartI.Tasks.TrainStreamTails
import UnforcedLeray.Short.PartI.Tasks.TrainFluctuationDecayProof
import UnforcedLeray.Short.PartI.Tasks.TrainMeanExpansionProof
import UnforcedLeray.Short.PartI.Tasks.TrainMeanEquations.TrainMeanV1
import UnforcedLeray.Short.PartI.Tasks.TrainMeanEquations.TrainMeanV2
import UnforcedLeray.Short.PartI.Tasks.TrainClass.BUCMeanStreamSmooth
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# `PartII-b:F7/1` Helper 1: `s ≥ 1` Train `L^{22/3}(C_c)` Decay (`TrainTail.lean`)

Source of record: `the November 2 reference manuscript` (SP), lines 2269–2275,
438–462 (`sct:fluctuation`, `sct:expansion`).

Proves `train_ageJet_lp22_3_tail`: in `BgRegime p d dm dp` for `s ≥ 1`,
`‖ageJet 0 j p.train.v s‖_{L^{22/3}(C_{p.c})} · p.c^{4/11}` is bounded by
`C_tr · (p.ν ^ k_tr)⁻¹ · s^{-41/44}` (`j = 0`) and `C_tr · (p.ν ^ k_tr)⁻¹ · s^{-63/44}` (`j = 1, 2`),
by decomposing `v(s) = hfluct c (v(s)) + (-∂_η S(s), 0)` (`trainMeanV1`, `trainMeanV2`) and
combining `trainFluctuationDecay_uncond` with `trainMeanExpansion_uncond`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Real
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb.TailTrainAux

open UnforcedLeray.Cons.C03.Concrete
open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec jap jet)
open UnforcedLeray.Short.PartI (ageJet polyP trainPeriod IsBUCTrain wSupNorm hmean hfluct meanStream)
open UnforcedLeray.Short.PartI (OverlapFluctuationDecay overlap_fluctuation_decay overlap_highnorm_uniform)
open UnforcedLeray.Short.PartI (TrainOverlap trainOverlap_proof overlap_mean_decay overlap_mean_primitive)
open UnforcedLeray.Short.PartI (TrainStreamVelocityPressureTails train_stream_velocity_pressure_tails)
open UnforcedLeray.Short.PartI (train_vorticity_gaussian_tail)
open UnforcedLeray.Short.PartI (TrainFluctuationDecay trainFluctuationDecay_proof)
open UnforcedLeray.Short.PartI (TrainMeanExpansion trainMeanExpansion_proof)
open UnforcedLeray.Short.PartI (trainMeanV1 trainMeanV2 bucMeanStreamSmooth)

/-! ### 1. Unconditional Part I `TrainFluctuationDecay` and `TrainMeanExpansion` -/

private theorem overlapFD_uncond : OverlapFluctuationDecay :=
  overlap_fluctuation_decay overlap_highnorm_uniform

private theorem trainOverlap_uncond : TrainOverlap :=
  trainOverlap_proof overlapFD_uncond
    (overlap_mean_decay overlap_highnorm_uniform overlapFD_uncond overlap_mean_primitive)

private theorem trainStreamVelocityPressureTails_uncond : TrainStreamVelocityPressureTails :=
  train_stream_velocity_pressure_tails trainOverlap_uncond
    (train_vorticity_gaussian_tail trainOverlap_uncond)

private theorem trainFluctuationDecay_uncond : TrainFluctuationDecay :=
  trainFluctuationDecay_proof trainStreamVelocityPressureTails_uncond overlapFD_uncond
    trainOverlap_uncond

private theorem trainMeanExpansion_uncond : TrainMeanExpansion :=
  trainMeanExpansion_proof trainStreamVelocityPressureTails_uncond trainFluctuationDecay_uncond
    overlap_mean_primitive

/-! ### 2. Decomposition `tr.v s = hfluct c (tr.v s) + (-∂_η S(s), 0)` and jet bound -/

private theorem hmean_vec_apply {ν c : ℝ} (tr : B0140.TrainSol ν c) {s : ℝ} (hs : 0 ≤ s)
    (η : ℝ) (i : Fin 2) :
    (hmean c (tr.v s) η) i = hmean c (fun z : Plane => tr.v s z i) η := by
  let proj : Vec →L[ℝ] ℝ := EuclideanSpace.proj i
  have hv_cont : Continuous (fun q : ℝ => tr.v s (q, η)) := by
    have hcont : ContinuousOn (fun x : ℝ × Plane => tr.v x.1 x.2) (Ici 0 ×ˢ univ) :=
      tr.isTrain.smooth_v.continuousOn
    exact hcont.comp_continuous (continuous_const.prodMk (continuous_id.prodMk continuous_const))
      (fun q => ⟨hs, mem_univ (q, η)⟩)
  change proj (c⁻¹ • ∫ q in Ioc (-c / 2) (c / 2), tr.v s (q, η)) =
    c⁻¹ • ∫ q in Ioc (-c / 2) (c / 2), proj (tr.v s (q, η))
  rw [map_smul, ← proj.integral_comp_comm hv_cont.integrableOn_Ioc]

private theorem contDiff_meanStream_slice {ν c : ℝ} (hν : 0 < ν) (hc : 0 < c)
    (tr : B0140.TrainSol ν c) (hbuc : IsBUCTrain tr) {s : ℝ} (hs : 0 < s) :
    ContDiff ℝ ∞ (meanStream tr s) := by
  have hsm := bucMeanStreamSmooth ν c hν hc tr hbuc
  have hslice : ContDiffOn ℝ ∞ (meanStream tr s) univ :=
    hsm.comp ((contDiffOn_const (c := s)).prodMk contDiffOn_id)
      (fun η _ => (⟨hs, mem_univ η⟩ : ((s, η) : ℝ × ℝ) ∈ Ioi 0 ×ˢ univ))
  exact contDiffOn_univ.1 hslice

private theorem contDiff_train_v_slice {ν c : ℝ} (tr : B0140.TrainSol ν c) {s : ℝ} (hs : 0 ≤ s) :
    ContDiff ℝ ∞ (tr.v s) := by
  have hslice : ContDiffOn ℝ ∞ (fun z : Plane => tr.v s z) univ :=
    tr.isTrain.smooth_v.comp ((contDiffOn_const (c := s)).prodMk contDiffOn_id)
      (fun z _ => (⟨hs, mem_univ z⟩ : ((s, z) : ℝ × Plane) ∈ Ici 0 ×ˢ univ))
  exact contDiffOn_univ.1 hslice

private theorem contDiff_and_ageJet_le_fluct_add_mean {ν c : ℝ} (hν : 0 < ν) (hc : 0 < c)
    (tr : B0140.TrainSol ν c) (hbuc : IsBUCTrain tr) {s : ℝ} (hs : 0 < s) (j : ℕ) :
    ContDiff ℝ ∞ (hfluct c (tr.v s)) ∧
    ContDiff ℝ ∞ (meanStream tr s) ∧
    ∀ z : Plane,
      ‖ageJet 0 j tr.v s z‖ ≤
        ‖ageJet 0 j (fun r => hfluct c (tr.v r)) s z‖ +
          |iteratedDeriv (j + 1) (meanStream tr s) z.2| := by
  have hS_sm : ContDiff ℝ ∞ (meanStream tr s) := contDiff_meanStream_slice hν hc tr hbuc hs
  let b : ℝ → ℝ := fun η => -deriv (meanStream tr s) η
  have hb_sm : ContDiff ℝ ∞ b := (contDiff_infty_iff_deriv.mp hS_sm).2.neg
  let M : Plane → Vec := fun z => hmean c (tr.v s) z.2
  let e₀ : Vec := EuclideanSpace.single (0 : Fin 2) (1 : ℝ)
  let L₁ : ℝ →L[ℝ] Vec := ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) e₀
  let L₂ : Plane →L[ℝ] ℝ := ContinuousLinearMap.snd ℝ ℝ ℝ
  have hM_eq : M = L₁ ∘ (b ∘ L₂) := by
    funext y
    ext i
    fin_cases i
    · have h0 := hmean_vec_apply tr hs.le y.2 0
      rw [trainMeanV1 ν c hν hc tr s hs y.2] at h0
      simpa [M, b, L₁, L₂, e₀] using h0
    · have h1 := hmean_vec_apply tr hs.le y.2 1
      rw [trainMeanV2 ν c hν hc tr s hs y.2] at h1
      simpa [M, L₁, L₂, e₀] using h1
  have hbL₂_sm : ContDiff ℝ ∞ (b ∘ L₂) := hb_sm.comp L₂.contDiff
  have hM_sm : ContDiff ℝ ∞ M := by
    rw [hM_eq]
    exact L₁.contDiff.comp hbL₂_sm
  have hv_sm : ContDiff ℝ ∞ (tr.v s) := contDiff_train_v_slice tr hs.le
  have hF_eq : hfluct c (tr.v s) = tr.v s - M := rfl
  have hF_sm : ContDiff ℝ ∞ (hfluct c (tr.v s)) := by
    rw [hF_eq]
    exact hv_sm.sub hM_sm
  refine ⟨hF_sm, hS_sm, fun z => ?_⟩
  have hv_split : tr.v s = hfluct c (tr.v s) + M := by
    funext w; simp [hfluct, M]
  have hj_top : (j : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by exact_mod_cast le_top
  have hadd : iteratedFDeriv ℝ j (tr.v s) z =
      iteratedFDeriv ℝ j (hfluct c (tr.v s)) z + iteratedFDeriv ℝ j M z := by
    conv_lhs => rw [hv_split]
    exact iteratedFDeriv_add_apply (hF_sm.contDiffAt.of_le hj_top) (hM_sm.contDiffAt.of_le hj_top)
  have he₀ : ‖e₀‖ = 1 := by
    dsimp [e₀]
    rw [PiLp.norm_single, norm_one]
  have hL₁_norm : ‖L₁‖ ≤ 1 := by
    refine L₁.opNorm_le_bound zero_le_one fun r => ?_
    simp [L₁, norm_smul, he₀]
  have hL₂_norm : ‖L₂‖ ≤ 1 := by
    refine L₂.opNorm_le_bound zero_le_one fun w => ?_
    rw [one_mul]
    exact norm_snd_le w
  have hprod_L₂ : ∏ _i : Fin j, ‖L₂‖ ≤ 1 := by
    calc ∏ _i : Fin j, ‖L₂‖
        ≤ ∏ _i : Fin j, (1 : ℝ) :=
          Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun _ _ => hL₂_norm)
      _ = 1 := Finset.prod_const_one
  have hM_bd : ‖iteratedFDeriv ℝ j M z‖ ≤ |iteratedDeriv (j + 1) (meanStream tr s) z.2| := by
    have hcomp1 : ‖iteratedFDeriv ℝ j M z‖ ≤ ‖iteratedFDeriv ℝ j (b ∘ L₂) z‖ := by
      rw [hM_eq]
      have h1 := L₁.norm_iteratedFDeriv_comp_left (f := b ∘ L₂) (x := z)
        (N := (∞ : WithTop ℕ∞)) (n := j) hbL₂_sm.contDiffAt hj_top
      calc ‖iteratedFDeriv ℝ j (L₁ ∘ (b ∘ L₂)) z‖
          ≤ ‖L₁‖ * ‖iteratedFDeriv ℝ j (b ∘ L₂) z‖ := h1
        _ ≤ 1 * ‖iteratedFDeriv ℝ j (b ∘ L₂) z‖ :=
            mul_le_mul_of_nonneg_right hL₁_norm (norm_nonneg _)
        _ = ‖iteratedFDeriv ℝ j (b ∘ L₂) z‖ := one_mul _
    have hcomp2 : ‖iteratedFDeriv ℝ j (b ∘ L₂) z‖ ≤ ‖iteratedDeriv j b z.2‖ := by
      rw [L₂.iteratedFDeriv_comp_right hb_sm z hj_top]
      calc ‖(iteratedFDeriv ℝ j b (L₂ z)).compContinuousLinearMap fun _ => L₂‖
          ≤ ‖iteratedFDeriv ℝ j b (L₂ z)‖ * ∏ _i : Fin j, ‖L₂‖ :=
            ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
        _ ≤ ‖iteratedFDeriv ℝ j b (L₂ z)‖ * 1 :=
            mul_le_mul_of_nonneg_left hprod_L₂ (norm_nonneg _)
        _ = ‖iteratedDeriv j b z.2‖ := by
            rw [mul_one, norm_iteratedFDeriv_eq_norm_iteratedDeriv]
            rfl
    have hb_id : iteratedDeriv j b z.2 = -iteratedDeriv (j + 1) (meanStream tr s) z.2 := by
      have hb_neg : b = -deriv (meanStream tr s) := rfl
      rw [hb_neg, iteratedDeriv_neg, ← iteratedDeriv_succ']
    calc ‖iteratedFDeriv ℝ j M z‖
        ≤ ‖iteratedDeriv j b z.2‖ := hcomp1.trans hcomp2
      _ = |iteratedDeriv (j + 1) (meanStream tr s) z.2| := by
          rw [Real.norm_eq_abs, hb_id, abs_neg]
  have hjet_v : ‖ageJet 0 j tr.v s z‖ = ‖iteratedFDeriv ℝ j (tr.v s) z‖ := by
    simp [ageJet, jet, iteratedDeriv_zero]
  have hjet_F : ‖ageJet 0 j (fun r => hfluct c (tr.v r)) s z‖ =
      ‖iteratedFDeriv ℝ j (hfluct c (tr.v s)) z‖ := by
    simp [ageJet, jet, iteratedDeriv_zero]
  rw [hjet_v, hjet_F, hadd]
  exact (norm_add_le _ _).trans (add_le_add (le_refl _) hM_bd)

/-! ### 3. Cell `L^{22/3}` bounds for fluctuation and vertical profile terms -/

private theorem eLpNorm_22_3_le_of_inv_one_add_sq {c A : ℝ} (hc : 0 < c) (hA : 0 ≤ A)
    (W : Plane → ℝ) (hW0 : ∀ z : Plane, 0 ≤ W z)
    (hW : ∀ z : Plane, W z ≤ A * (1 + z.2 ^ 2)⁻¹) :
    eLpNorm W (ENNReal.ofReal (22 / 3)) (volume.restrict (B0579.cell c)) ≤
      ENNReal.ofReal ((c * Real.pi) ^ (3 / 22 : ℝ) * A) := by
  set μ := volume.restrict (B0579.cell c)
  have hμ_eq : μ = UnforcedLeray.Cyl.cellμ c := by
    dsimp [μ]; rw [cell_eq_cylCell]; rfl
  have hp0 : ENNReal.ofReal (22 / 3) ≠ 0 := by norm_num
  have hpt : ENNReal.ofReal (22 / 3) ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt]
  have hto : (ENNReal.ofReal (22 / 3)).toReal = 22 / 3 := ENNReal.toReal_ofReal (by norm_num)
  have hinv : 1 / (22 / 3 : ℝ) = 3 / 22 := by norm_num
  rw [hto, hinv]
  have h_ae : ∀ᵐ z ∂μ,
      ‖W z‖ₑ ^ (22 / 3 : ℝ) ≤ ENNReal.ofReal (A ^ (22 / 3 : ℝ) * (1 + z.2 ^ 2)⁻¹) := by
    refine Eventually.of_forall fun z => ?_
    have hWz := hW z
    have hinv_le1 : (1 + z.2 ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg z.2])
    have hx1 : ENNReal.ofReal ((1 + z.2 ^ 2)⁻¹) ≤ 1 := ENNReal.ofReal_le_one.2 hinv_le1
    have hx_pow : ENNReal.ofReal ((1 + z.2 ^ 2)⁻¹) ^ (22 / 3 : ℝ) ≤
        ENNReal.ofReal ((1 + z.2 ^ 2)⁻¹) := by
      have hadd : (22 / 3 : ℝ) = 1 + 19 / 3 := by norm_num
      calc ENNReal.ofReal ((1 + z.2 ^ 2)⁻¹) ^ (22 / 3 : ℝ)
          = ENNReal.ofReal ((1 + z.2 ^ 2)⁻¹) ^ (1 : ℝ) *
              ENNReal.ofReal ((1 + z.2 ^ 2)⁻¹) ^ (19 / 3 : ℝ) := by
            rw [hadd, ENNReal.rpow_add_of_nonneg _ _ zero_le_one (by norm_num)]
        _ ≤ ENNReal.ofReal ((1 + z.2 ^ 2)⁻¹) ^ (1 : ℝ) * 1 :=
            mul_le_mul_right (ENNReal.rpow_le_one hx1 (by norm_num)) _
        _ = ENNReal.ofReal ((1 + z.2 ^ 2)⁻¹) := by rw [ENNReal.rpow_one, mul_one]
    calc ‖W z‖ₑ ^ (22 / 3 : ℝ)
        = ENNReal.ofReal (W z) ^ (22 / 3 : ℝ) := by rw [Real.enorm_eq_ofReal (hW0 z)]
      _ ≤ ENNReal.ofReal (A * (1 + z.2 ^ 2)⁻¹) ^ (22 / 3 : ℝ) :=
          ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hWz) (by norm_num)
      _ = ENNReal.ofReal A ^ (22 / 3 : ℝ) *
            ENNReal.ofReal ((1 + z.2 ^ 2)⁻¹) ^ (22 / 3 : ℝ) := by
          rw [ENNReal.ofReal_mul hA, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
      _ ≤ ENNReal.ofReal A ^ (22 / 3 : ℝ) * ENNReal.ofReal ((1 + z.2 ^ 2)⁻¹) :=
          mul_le_mul_right hx_pow _
      _ = ENNReal.ofReal (A ^ (22 / 3 : ℝ) * (1 + z.2 ^ 2)⁻¹) := by
          rw [ENNReal.ofReal_rpow_of_nonneg hA (by norm_num),
            ← ENNReal.ofReal_mul (Real.rpow_nonneg hA _)]
  have hmeas : AEMeasurable
      (fun z : Plane => ENNReal.ofReal (A ^ (22 / 3 : ℝ) * (1 + z.2 ^ 2)⁻¹))
      (UnforcedLeray.Cyl.cellμ c) :=
    (by fun_prop : Measurable
      (fun z : Plane => ENNReal.ofReal (A ^ (22 / 3 : ℝ) * (1 + z.2 ^ 2)⁻¹))).aemeasurable
  have hint_le : ∫⁻ z, ‖W z‖ₑ ^ (22 / 3 : ℝ) ∂μ ≤
      ENNReal.ofReal (c * (A ^ (22 / 3 : ℝ) * Real.pi)) := by
    calc ∫⁻ z, ‖W z‖ₑ ^ (22 / 3 : ℝ) ∂μ
        ≤ ∫⁻ z, ENNReal.ofReal (A ^ (22 / 3 : ℝ) * (1 + z.2 ^ 2)⁻¹) ∂μ := lintegral_mono_ae h_ae
      _ = ∫⁻ z, ENNReal.ofReal (A ^ (22 / 3 : ℝ) * (1 + z.2 ^ 2)⁻¹)
            ∂(UnforcedLeray.Cyl.cellμ c) := by rw [hμ_eq]
      _ = ∫⁻ _q in Ico (-c / 2) (c / 2),
            ∫⁻ η : ℝ, ENNReal.ofReal (A ^ (22 / 3 : ℝ) * (1 + η ^ 2)⁻¹) :=
          UnforcedLeray.Cyl.lintegral_cell_eq hmeas
      _ = ENNReal.ofReal (c * (A ^ (22 / 3 : ℝ) * Real.pi)) := by
          have hint : ∫⁻ η : ℝ, ENNReal.ofReal (A ^ (22 / 3 : ℝ) * (1 + η ^ 2)⁻¹) =
              ENNReal.ofReal (A ^ (22 / 3 : ℝ) * Real.pi) := by
            rw [← ofReal_integral_eq_lintegral_ofReal
              (integrable_inv_one_add_sq.const_mul (A ^ (22 / 3 : ℝ)))
              (ae_of_all _ fun _ => by positivity),
              integral_const_mul, integral_univ_inv_one_add_sq]
          simp_rw [hint]
          rw [setLIntegral_const, Real.volume_Ico]
          have hlen : c / 2 - -c / 2 = c := by ring
          rw [hlen, mul_comm, ← ENNReal.ofReal_mul hc.le]
  refine (ENNReal.rpow_le_rpow hint_le (by norm_num)).trans ?_
  rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)]
  apply ENNReal.ofReal_le_ofReal
  have h1 : c * (A ^ (22 / 3 : ℝ) * Real.pi) = (c * Real.pi) * A ^ (22 / 3 : ℝ) := by ring
  rw [h1, Real.mul_rpow (by positivity) (by positivity),
    ← Real.rpow_mul hA, show (22 / 3 : ℝ) * (3 / 22 : ℝ) = 1 by norm_num, Real.rpow_one]

private theorem eLpNorm_22_3_vert_eq {c : ℝ} (hc : 0 < c) {φ : ℝ → ℝ} (hφ : Measurable φ) :
    eLpNorm (fun z : Plane => |φ z.2|) (ENNReal.ofReal (22 / 3))
        (volume.restrict (B0579.cell c)) =
      ENNReal.ofReal (c ^ (3 / 22 : ℝ)) *
        eLpNorm (fun η : ℝ => (1 : ℝ) ^ 0 * φ η) (ENNReal.ofReal (22 / 3)) volume := by
  have hp0 : ENNReal.ofReal (22 / 3) ≠ 0 := by norm_num
  have hpt : ENNReal.ofReal (22 / 3) ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt]
  have hto : (ENNReal.ofReal (22 / 3)).toReal = 22 / 3 := ENNReal.toReal_ofReal (by norm_num)
  have hinv : 1 / (22 / 3 : ℝ) = 3 / 22 := by norm_num
  rw [hto, hinv]
  have hmeas : AEMeasurable (fun z : Plane => ‖|φ z.2|‖ₑ ^ (22 / 3 : ℝ))
      (UnforcedLeray.Cyl.cellμ c) :=
    (((hφ.comp measurable_snd).abs.enorm).pow_const (22 / 3 : ℝ)).aemeasurable
  rw [cell_eq_cylCell, UnforcedLeray.Cyl.lintegral_cell_eq hmeas]
  have h_inner : ∀ η : ℝ, ‖|φ η|‖ₑ ^ (22 / 3 : ℝ) = ‖(1 : ℝ) ^ 0 * φ η‖ₑ ^ (22 / 3 : ℝ) := by
    intro η
    simp [enorm_abs]
  simp_rw [h_inner]
  rw [setLIntegral_const, Real.volume_Ico]
  have hlen : c / 2 - -c / 2 = c := by ring
  rw [hlen, mul_comm, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
    ENNReal.ofReal_rpow_of_nonneg hc.le (by norm_num)]

/-! ### 4. Polynomial/exponential algebra in `BgRegime` -/

private theorem exp_neg_le_two_div_sq {X : ℝ} (hX : 0 < X) :
    Real.exp (-X) ≤ 2 / X ^ 2 := by
  have hsum := Real.sum_le_exp_of_nonneg hX.le 3
  simp [Finset.sum_range_succ] at hsum
  have hsq : X ^ 2 / 2 ≤ Real.exp X := by linarith
  rw [Real.exp_neg, inv_eq_one_div]
  calc 1 / Real.exp X
      ≤ 1 / (X ^ 2 / 2) := one_div_le_one_div_of_le (by positivity) hsq
    _ = 2 / X ^ 2 := by ring

private theorem polyP_le_bg {C ν c : ℝ} (hC : 0 ≤ C) (hν : 0 < ν) (hν1 : ν ≤ 1)
    (hc_eq : c = (ν ^ 2)⁻¹) (N : ℕ) :
    polyP C N ν c ≤ C * 3 ^ N * (ν ^ (2 * N))⁻¹ := by
  have hν_inv1 : 1 ≤ ν⁻¹ := (one_le_inv₀ hν).2 hν1
  have hc_inv : c = (ν⁻¹) ^ 2 := by rw [hc_eq, inv_pow]
  have h1 : 1 + c + ν⁻¹ ≤ 3 * (ν⁻¹) ^ 2 := by rw [hc_inv]; nlinarith
  have h0 : 0 ≤ 1 + c + ν⁻¹ := by rw [hc_inv]; positivity
  unfold polyP
  calc C * (1 + c + ν⁻¹) ^ N
      ≤ C * (3 * (ν⁻¹) ^ 2) ^ N :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 h1 N) hC
    _ = C * 3 ^ N * (ν ^ (2 * N))⁻¹ := by
        rw [mul_pow, ← pow_mul, inv_pow]
        ring

private theorem cell_factor_le {ν c : ℝ} (hν : 0 < ν) (hν1 : ν ≤ 1) (hc_eq : c = (ν ^ 2)⁻¹) :
    (c * Real.pi) ^ (3 / 22 : ℝ) * c ^ (4 / 11 : ℝ) ≤ 4 * (ν ^ 4)⁻¹ := by
  have hν_inv1 : 1 ≤ ν⁻¹ := (one_le_inv₀ hν).2 hν1
  have hc1 : 1 ≤ c := by rw [hc_eq, ← inv_pow]; exact one_le_pow₀ hν_inv1
  have hpi : c * Real.pi ≤ 4 * c := by nlinarith [Real.pi_le_four]
  have hf1 : (c * Real.pi) ^ (3 / 22 : ℝ) ≤ 4 * c := by
    calc (c * Real.pi) ^ (3 / 22 : ℝ)
        ≤ (4 * c) ^ (3 / 22 : ℝ) := Real.rpow_le_rpow (by positivity) hpi (by norm_num)
      _ ≤ (4 * c) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      _ = 4 * c := Real.rpow_one _
  have hf2 : c ^ (4 / 11 : ℝ) ≤ c := by
    calc c ^ (4 / 11 : ℝ)
        ≤ c ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num)
      _ = c := Real.rpow_one _
  have hc2 : c * c = (ν ^ 4)⁻¹ := by rw [hc_eq, ← mul_inv, ← pow_add]
  calc (c * Real.pi) ^ (3 / 22 : ℝ) * c ^ (4 / 11 : ℝ)
      ≤ (4 * c) * c := mul_le_mul hf1 hf2 (by positivity) (by positivity)
    _ = 4 * (c * c) := by ring
    _ = 4 * (ν ^ 4)⁻¹ := by rw [hc2]

private theorem vert_cell_factor_le {ν c : ℝ} (hν : 0 < ν) (hν1 : ν ≤ 1) (hc_eq : c = (ν ^ 2)⁻¹) :
    c ^ (3 / 22 : ℝ) * c ^ (4 / 11 : ℝ) ≤ (ν ^ 2)⁻¹ := by
  have hν_inv1 : 1 ≤ ν⁻¹ := (one_le_inv₀ hν).2 hν1
  have hc1 : 1 ≤ c := by rw [hc_eq, ← inv_pow]; exact one_le_pow₀ hν_inv1
  calc c ^ (3 / 22 : ℝ) * c ^ (4 / 11 : ℝ)
      = c ^ ((3 / 22 : ℝ) + (4 / 11 : ℝ)) := (Real.rpow_add (by linarith) _ _).symm
    _ ≤ c ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num)
    _ = (ν ^ 2)⁻¹ := by rw [Real.rpow_one, hc_eq]

private theorem fluct_jet_bound (j : ℕ) :
    ∃ (C_f : ℝ) (k_f : ℕ) (ν_f : ℝ), 0 < C_f ∧ 0 < ν_f ∧
      ∀ {ν : ℝ}, 0 < ν → ν ≤ ν_f → ν ≤ 1 →
      ∀ (tr : B0140.TrainSol ν (trainPeriod 2 ν)), IsBUCTrain tr →
      ∀ s : ℝ, 1 ≤ s →
        let c := trainPeriod 2 ν
        eLpNorm (fun z => ‖ageJet 0 j (fun r => hfluct c (tr.v r)) s z‖)
            (ENNReal.ofReal (22 / 3)) (volume.restrict (B0579.cell c)) *
          ENNReal.ofReal (c ^ (4 / 11 : ℝ)) ≤
            ENNReal.ofReal (C_f * (ν ^ k_f)⁻¹ * s ^ (-63 / 44 : ℝ)) := by
  obtain ⟨C, N, κ, ν₀, hC, hκ, hν₀, hFD⟩ :=
    trainFluctuationDecay_uncond 2 (by norm_num) 2 0 j
  refine ⟨8 * C * 3 ^ N / κ ^ 2, 14 + 2 * N, ν₀, by positivity, hν₀, ?_⟩
  intro ν hν hν_le hν1 tr hbuc s hs1
  have hs0 : 0 < s := zero_lt_one.trans_le hs1
  let c := trainPeriod 2 ν
  have hc_eq : c = (ν ^ 2)⁻¹ := vb_trainPeriod_two hν
  have hc_pos : 0 < c := by rw [hc_eq]; positivity
  have hw := (hFD ν hν hν_le tr hbuc s hs0).2.1.2
  let A : ℝ := polyP C N ν c * Real.exp (-(κ * ν * s / c ^ 2))
  have hA_nn : 0 ≤ A := by
    dsimp [A]; unfold polyP; rw [hc_eq]; positivity
  have hpt : ∀ z : Plane,
      ‖ageJet 0 j (fun r => hfluct c (tr.v r)) s z‖ ≤ A * (1 + z.2 ^ 2)⁻¹ := by
    intro z
    have hz : ENNReal.ofReal (Real.sqrt (jap 2 z)) *
        ‖ageJet 0 j (fun r => hfluct c (tr.v r)) s z‖ₑ ≤ ENNReal.ofReal A :=
      (le_iSup (fun w : Plane => ENNReal.ofReal (Real.sqrt (jap 2 w)) *
        ‖ageJet 0 j (fun r => hfluct c (tr.v r)) s w‖ₑ) z).trans hw
    rw [← ofReal_norm, ← ENNReal.ofReal_mul (Real.sqrt_nonneg _)] at hz
    have hz' := (ENNReal.ofReal_le_ofReal_iff hA_nn).1 hz
    have hjap : Real.sqrt (jap 2 z) = 1 + z.2 ^ 2 := by
      unfold jap
      exact Real.sqrt_sq (by positivity)
    rw [hjap] at hz'
    have hpos : 0 < 1 + z.2 ^ 2 := by positivity
    exact (le_mul_inv_iff₀ hpos).2 (by simpa [mul_comm] using hz')
  have hlp := eLpNorm_22_3_le_of_inv_one_add_sq hc_pos hA_nn
    (fun z => ‖ageJet 0 j (fun r => hfluct c (tr.v r)) s z‖)
    (fun _ => norm_nonneg _) hpt
  have hcf := cell_factor_le hν hν1 hc_eq
  have hexp : Real.exp (-(κ * ν * s / c ^ 2)) ≤ (2 / κ ^ 2) * (ν ^ 10)⁻¹ * s ^ (-2 : ℝ) := by
    have hX : 0 < κ * ν * s / c ^ 2 := by positivity
    have h1 := exp_neg_le_two_div_sq hX
    have h2 : 2 / (κ * ν * s / c ^ 2) ^ 2 = (2 / κ ^ 2) * (c ^ 4 * (ν ^ 2)⁻¹) * (s ^ 2)⁻¹ := by
      field_simp
    have hc4 : c ^ 4 * (ν ^ 2)⁻¹ = (ν ^ 10)⁻¹ := by
      rw [hc_eq, inv_pow, ← mul_inv, ← pow_mul, ← pow_add]
    have hs2 : (s ^ 2)⁻¹ = s ^ (-2 : ℝ) := by
      rw [Real.rpow_neg hs0.le, Real.rpow_two]
    rw [h2, hc4, hs2] at h1
    linarith
  have hs_exp : s ^ (-2 : ℝ) ≤ s ^ (-63 / 44 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hs1 (by norm_num)
  have hA_bd : (4 * (ν ^ 4)⁻¹) * A ≤
      (8 * C * 3 ^ N / κ ^ 2) * (ν ^ (14 + 2 * N))⁻¹ * s ^ (-63 / 44 : ℝ) := by
    have hp := polyP_le_bg hC.le hν hν1 hc_eq N
    have hpoly_nn : 0 ≤ polyP C N ν c := by unfold polyP; rw [hc_eq]; positivity
    have hA1 : A ≤ (C * 3 ^ N * (ν ^ (2 * N))⁻¹) * ((2 / κ ^ 2) * (ν ^ 10)⁻¹ * s ^ (-63 / 44 : ℝ)) := by
      dsimp [A]
      exact mul_le_mul hp (hexp.trans (mul_le_mul_of_nonneg_left hs_exp (by positivity)))
        (Real.exp_nonneg _) (by positivity)
    calc (4 * (ν ^ 4)⁻¹) * A
        ≤ (4 * (ν ^ 4)⁻¹) *
            ((C * 3 ^ N * (ν ^ (2 * N))⁻¹) * ((2 / κ ^ 2) * (ν ^ 10)⁻¹ * s ^ (-63 / 44 : ℝ))) :=
          mul_le_mul_of_nonneg_left hA1 (by positivity)
      _ = (8 * C * 3 ^ N / κ ^ 2) * ((ν ^ 4)⁻¹ * (ν ^ (2 * N))⁻¹ * (ν ^ 10)⁻¹) *
            s ^ (-63 / 44 : ℝ) := by ring
      _ = (8 * C * 3 ^ N / κ ^ 2) * (ν ^ (14 + 2 * N))⁻¹ * s ^ (-63 / 44 : ℝ) := by
          have hpow : (ν ^ 4)⁻¹ * (ν ^ (2 * N))⁻¹ * (ν ^ 10)⁻¹ = (ν ^ (14 + 2 * N))⁻¹ := by
            rw [← mul_inv, ← mul_inv, ← pow_add, ← pow_add]
            congr 2; omega
          rw [hpow]
  calc eLpNorm (fun z => ‖ageJet 0 j (fun r => hfluct c (tr.v r)) s z‖)
          (ENNReal.ofReal (22 / 3)) (volume.restrict (B0579.cell c)) *
        ENNReal.ofReal (c ^ (4 / 11 : ℝ))
      ≤ ENNReal.ofReal ((c * Real.pi) ^ (3 / 22 : ℝ) * A) *
          ENNReal.ofReal (c ^ (4 / 11 : ℝ)) := by gcongr
    _ = ENNReal.ofReal (((c * Real.pi) ^ (3 / 22 : ℝ) * c ^ (4 / 11 : ℝ)) * A) := by
        rw [← ENNReal.ofReal_mul (by positivity)]; ring_nf
    _ ≤ ENNReal.ofReal ((4 * (ν ^ 4)⁻¹) * A) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hcf hA_nn)
    _ ≤ ENNReal.ofReal ((8 * C * 3 ^ N / κ ^ 2) * (ν ^ (14 + 2 * N))⁻¹ * s ^ (-63 / 44 : ℝ)) :=
        ENNReal.ofReal_le_ofReal hA_bd

private theorem mean_deriv_bound (b : ℕ) :
    ∃ (C_m : ℝ) (k_m : ℕ) (ν_m : ℝ), 0 < C_m ∧ 0 < ν_m ∧
      ∀ {ν : ℝ}, 0 < ν → ν ≤ ν_m → ν ≤ 1 →
      ∀ (tr : B0140.TrainSol ν (trainPeriod 2 ν)), IsBUCTrain tr →
      ∀ s : ℝ, 1 ≤ s →
        let c := trainPeriod 2 ν
        eLpNorm (fun z : Plane => |iteratedDeriv b (meanStream tr s) z.2|)
            (ENNReal.ofReal (22 / 3)) (volume.restrict (B0579.cell c)) *
          ENNReal.ofReal (c ^ (4 / 11 : ℝ)) ≤
            ENNReal.ofReal (C_m * (ν ^ k_m)⁻¹ * s ^ (-(b : ℝ) / 2 - 19 / 44)) := by
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (22 / 3) := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by norm_num)
  obtain ⟨C, M, ν₀, hC, hν₀, hME⟩ :=
    trainMeanExpansion_uncond 2 (by norm_num) 0 0 b 0 (ENNReal.ofReal (22 / 3)) hp1
  refine ⟨C * 3 ^ M, 2 + 2 * M, ν₀, by positivity, hν₀, ?_⟩
  intro ν hν hν_le hν1 tr hbuc s hs1
  have hs0 : 0 < s := zero_lt_one.trans_le hs1
  let c := trainPeriod 2 ν
  have hc_eq : c = (ν ^ 2)⁻¹ := vb_trainPeriod_two hν
  have hc_pos : 0 < c := by rw [hc_eq]; positivity
  have hS_sm : ContDiff ℝ ∞ (meanStream tr s) := contDiff_meanStream_slice hν hc_pos tr hbuc hs0
  have hcont_b : Continuous (iteratedDeriv b (meanStream tr s)) :=
    (hS_sm.of_le (by simp)).continuous_iteratedDeriv' b
  have hvert := eLpNorm_22_3_vert_eq hc_pos hcont_b.measurable
  have hS_bd := (hME ν hν hν_le tr hbuc).2.2.2 s hs0.le
  have h_id : (fun η : ℝ => η ^ 0 * iteratedDeriv b
      (fun e => iteratedDeriv 0 (fun r => meanStream tr r e) s) η) =
      fun η : ℝ => (1 : ℝ) ^ 0 * iteratedDeriv b (meanStream tr s) η := by
    funext η
    simp [iteratedDeriv_zero]
  rw [h_id] at hS_bd
  have hto : (ENNReal.ofReal (22 / 3)).toReal⁻¹ / 2 = (3 / 44 : ℝ) := by
    rw [ENNReal.toReal_ofReal (by norm_num)]
    norm_num
  have hexp : ((0 : ℕ) - (b : ℝ) - 1) / 2 - (0 : ℕ) +
      (ENNReal.ofReal (22 / 3)).toReal⁻¹ / 2 = -(b : ℝ) / 2 - 19 / 44 := by
    rw [hto]; push_cast; ring
  have hS_bd' : eLpNorm (fun η : ℝ => (1 : ℝ) ^ 0 * iteratedDeriv b (meanStream tr s) η)
      (ENNReal.ofReal (22 / 3)) volume ≤
      ENNReal.ofReal (polyP C M ν c * (1 + s) ^ (-(b : ℝ) / 2 - 19 / 44)) := by
    refine hS_bd.trans_eq ?_
    rw [hexp]
  let α : ℝ := -(b : ℝ) / 2 - 19 / 44
  have hα_neg : α ≤ 0 := by
    dsimp [α]
    have hb0 : (0 : ℝ) ≤ (b : ℝ) := Nat.cast_nonneg b
    linarith
  have hs_1s : (1 + s) ^ α ≤ s ^ α :=
    Real.rpow_le_rpow_of_nonpos hs0 (by linarith) hα_neg
  have hp := polyP_le_bg hC.le hν hν1 hc_eq M
  have hvcf := vert_cell_factor_le hν hν1 hc_eq
  calc eLpNorm (fun z : Plane => |iteratedDeriv b (meanStream tr s) z.2|)
          (ENNReal.ofReal (22 / 3)) (volume.restrict (B0579.cell c)) *
        ENNReal.ofReal (c ^ (4 / 11 : ℝ))
      = ENNReal.ofReal (c ^ (3 / 22 : ℝ)) *
          eLpNorm (fun η : ℝ => (1 : ℝ) ^ 0 * iteratedDeriv b (meanStream tr s) η)
            (ENNReal.ofReal (22 / 3)) volume *
          ENNReal.ofReal (c ^ (4 / 11 : ℝ)) := by rw [hvert]
    _ = (ENNReal.ofReal (c ^ (3 / 22 : ℝ)) * ENNReal.ofReal (c ^ (4 / 11 : ℝ))) *
          eLpNorm (fun η : ℝ => (1 : ℝ) ^ 0 * iteratedDeriv b (meanStream tr s) η)
            (ENNReal.ofReal (22 / 3)) volume := by ring
    _ ≤ ENNReal.ofReal (c ^ (3 / 22 : ℝ) * c ^ (4 / 11 : ℝ)) *
          ENNReal.ofReal (polyP C M ν c * (1 + s) ^ α) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        exact mul_le_mul (le_refl _) hS_bd' zero_le zero_le
    _ = ENNReal.ofReal ((c ^ (3 / 22 : ℝ) * c ^ (4 / 11 : ℝ)) * (polyP C M ν c * (1 + s) ^ α)) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
    _ ≤ ENNReal.ofReal ((ν ^ 2)⁻¹ * ((C * 3 ^ M * (ν ^ (2 * M))⁻¹) * s ^ α)) := by
        apply ENNReal.ofReal_le_ofReal
        have hpoly_nn : 0 ≤ polyP C M ν c := by unfold polyP; rw [hc_eq]; positivity
        have h2 : polyP C M ν c * (1 + s) ^ α ≤ (C * 3 ^ M * (ν ^ (2 * M))⁻¹) * s ^ α :=
          mul_le_mul hp hs_1s (by positivity) (by positivity)
        exact mul_le_mul hvcf h2 (by positivity) (by positivity)
    _ = ENNReal.ofReal ((C * 3 ^ M) * (ν ^ (2 + 2 * M))⁻¹ * s ^ α) := by
        congr 1
        rw [pow_add, mul_inv]
        ring

/-! ### 5. Combined `s ≥ 1` `L^{22/3}` decay for `ageJet 0 0, 1, 2` -/

theorem train_ageJet_lp22_3_tail :
    ∃ (C_tr : ℝ) (k_tr : ℕ) (ν_tr : ℝ), 0 < C_tr ∧ 0 < ν_tr ∧
      ∀ {dm dp : ℝ} (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν_tr →
      ∀ s : ℝ, 1 ≤ s →
        eLpNorm (fun z => ‖ageJet 0 0 p.train.v s z‖) (ENNReal.ofReal (22 / 3))
            (volume.restrict (B0579.cell p.c)) *
          ENNReal.ofReal (p.c ^ (4 / 11 : ℝ)) ≤
            ENNReal.ofReal (C_tr * (p.ν ^ k_tr)⁻¹ * s ^ (-41 / 44 : ℝ)) ∧
        eLpNorm (fun z => ‖ageJet 0 1 p.train.v s z‖) (ENNReal.ofReal (22 / 3))
            (volume.restrict (B0579.cell p.c)) *
          ENNReal.ofReal (p.c ^ (4 / 11 : ℝ)) ≤
            ENNReal.ofReal (C_tr * (p.ν ^ k_tr)⁻¹ * s ^ (-63 / 44 : ℝ)) ∧
        eLpNorm (fun z => ‖ageJet 0 2 p.train.v s z‖) (ENNReal.ofReal (22 / 3))
            (volume.restrict (B0579.cell p.c)) *
          ENNReal.ofReal (p.c ^ (4 / 11 : ℝ)) ≤
            ENNReal.ofReal (C_tr * (p.ν ^ k_tr)⁻¹ * s ^ (-63 / 44 : ℝ)) := by
  obtain ⟨Cf0, kf0, νf0, hCf0, hνf0, hBf0⟩ := fluct_jet_bound 0
  obtain ⟨Cf1, kf1, νf1, hCf1, hνf1, hBf1⟩ := fluct_jet_bound 1
  obtain ⟨Cf2, kf2, νf2, hCf2, hνf2, hBf2⟩ := fluct_jet_bound 2
  obtain ⟨Cm1, km1, νm1, hCm1, hνm1, hBm1⟩ := mean_deriv_bound 1
  obtain ⟨Cm2, km2, νm2, hCm2, hνm2, hBm2⟩ := mean_deriv_bound 2
  obtain ⟨Cm3, km3, νm3, hCm3, hνm3, hBm3⟩ := mean_deriv_bound 3
  set C_tr : ℝ := Cf0 + Cf1 + Cf2 + Cm1 + Cm2 + Cm3
  set k_tr : ℕ := kf0 + kf1 + kf2 + km1 + km2 + km3
  set ν_tr : ℝ := min (min (min νf0 νf1) (min νf2 νm1)) (min (min νm2 νm3) 1)
  have hCtr : 0 < C_tr := by dsimp [C_tr]; positivity
  have hνtr : 0 < ν_tr :=
    lt_min (lt_min (lt_min hνf0 hνf1) (lt_min hνf2 hνm1)) (lt_min (lt_min hνm2 hνm3) one_pos)
  refine ⟨C_tr, k_tr, ν_tr, hCtr, hνtr, ?_⟩
  intro dm dp p d hreg hν_le s hs1
  have hνp : 0 < p.ν := p.ν_pos
  have hν1 : p.ν ≤ 1 := hν_le.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hν_f0 : p.ν ≤ νf0 :=
    hν_le.trans ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _)))
  have hν_f1 : p.ν ≤ νf1 :=
    hν_le.trans ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _)))
  have hν_f2 : p.ν ≤ νf2 :=
    hν_le.trans ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hν_m1 : p.ν ≤ νm1 :=
    hν_le.trans ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hν_m2 : p.ν ≤ νm2 :=
    hν_le.trans ((min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _)))
  have hν_m3 : p.ν ≤ νm3 :=
    hν_le.trans ((min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _)))
  have hs0 : 0 < s := zero_lt_one.trans_le hs1
  have hc_eq : p.c = (p.ν ^ 2)⁻¹ := hreg.c_eq
  have hc2 : trainPeriod 2 p.ν = (p.ν ^ 2)⁻¹ := vb_trainPeriod_two hνp
  have hc_per : p.c = trainPeriod 2 p.ν := hc_eq.trans hc2.symm
  have hc_pos : 0 < trainPeriod 2 p.ν := by rw [hc2]; positivity
  obtain ⟨tr', hbuc, hv_eq⟩ := vb_transport hc_per p.train hreg.train_buc
  rw [← hv_eq, hc_per]
  let c := trainPeriod 2 p.ν
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (22 / 3) := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by norm_num)
  have hcomb : ∀ (j : ℕ) {Cf Cm αf αm α : ℝ} {kf km : ℕ}
      (hCf : 0 < Cf) (hCm : 0 < Cm)
      (hC_sum : Cf + Cm ≤ C_tr) (hkf : kf ≤ k_tr) (hkm : km ≤ k_tr)
      (hαf : αf ≤ α) (hαm : αm ≤ α)
      (hBf : eLpNorm (fun z => ‖ageJet 0 j (fun r => hfluct c (tr'.v r)) s z‖)
          (ENNReal.ofReal (22 / 3)) (volume.restrict (B0579.cell c)) *
        ENNReal.ofReal (c ^ (4 / 11 : ℝ)) ≤
          ENNReal.ofReal (Cf * (p.ν ^ kf)⁻¹ * s ^ αf))
      (hBm : eLpNorm (fun z : Plane => |iteratedDeriv (j + 1) (meanStream tr' s) z.2|)
          (ENNReal.ofReal (22 / 3)) (volume.restrict (B0579.cell c)) *
        ENNReal.ofReal (c ^ (4 / 11 : ℝ)) ≤
          ENNReal.ofReal (Cm * (p.ν ^ km)⁻¹ * s ^ αm)),
      eLpNorm (fun z => ‖ageJet 0 j tr'.v s z‖) (ENNReal.ofReal (22 / 3))
          (volume.restrict (B0579.cell c)) *
        ENNReal.ofReal (c ^ (4 / 11 : ℝ)) ≤
          ENNReal.ofReal (C_tr * (p.ν ^ k_tr)⁻¹ * s ^ α) := by
    intro j Cf Cm αf αm α kf km hCf hCm hC_sum hkf hkm hαf hαm hBf hBm
    obtain ⟨hF_sm, hS_sm, hpt⟩ :=
      contDiff_and_ageJet_le_fluct_add_mean hνp hc_pos tr' hbuc hs0 j
    have hcont_F : Continuous (fun z : Plane => ‖ageJet 0 j (fun r => hfluct c (tr'.v r)) s z‖) := by
      have heq : (fun z : Plane => ‖ageJet 0 j (fun r => hfluct c (tr'.v r)) s z‖) =
          fun z : Plane => ‖iteratedFDeriv ℝ j (hfluct c (tr'.v s)) z‖ := by
        funext z; simp [ageJet, jet, iteratedDeriv_zero]
      rw [heq]
      exact (hF_sm.continuous_iteratedFDeriv (mod_cast le_top)).norm
    have hcont_M : Continuous (fun z : Plane => |iteratedDeriv (j + 1) (meanStream tr' s) z.2|) :=
      (((hS_sm.of_le (by simp)).continuous_iteratedDeriv' (j + 1)).comp continuous_snd).abs
    have hmono : eLpNorm (fun z => ‖ageJet 0 j tr'.v s z‖) (ENNReal.ofReal (22 / 3))
        (volume.restrict (B0579.cell c)) ≤
        eLpNorm (fun z => ‖ageJet 0 j (fun r => hfluct c (tr'.v r)) s z‖ +
          |iteratedDeriv (j + 1) (meanStream tr' s) z.2|)
          (ENNReal.ofReal (22 / 3)) (volume.restrict (B0579.cell c)) :=
      eLpNorm_mono_real fun z => by simpa [Real.norm_of_nonneg (norm_nonneg _)] using hpt z
    have hadd := eLpNorm_add_le (μ := volume.restrict (B0579.cell c))
      hcont_F.aestronglyMeasurable hcont_M.aestronglyMeasurable hp1
    have h1 : Cf * (p.ν ^ kf)⁻¹ * s ^ αf ≤ Cf * (p.ν ^ k_tr)⁻¹ * s ^ α := by
      refine mul_le_mul (mul_le_mul_of_nonneg_left (vb_inv_pow_mono hνp hν1 hkf) hCf.le)
        (Real.rpow_le_rpow_of_exponent_le hs1 hαf) (by positivity) (by positivity)
    have h2 : Cm * (p.ν ^ km)⁻¹ * s ^ αm ≤ Cm * (p.ν ^ k_tr)⁻¹ * s ^ α := by
      refine mul_le_mul (mul_le_mul_of_nonneg_left (vb_inv_pow_mono hνp hν1 hkm) hCm.le)
        (Real.rpow_le_rpow_of_exponent_le hs1 hαm) (by positivity) (by positivity)
    calc eLpNorm (fun z => ‖ageJet 0 j tr'.v s z‖) (ENNReal.ofReal (22 / 3))
            (volume.restrict (B0579.cell c)) *
          ENNReal.ofReal (c ^ (4 / 11 : ℝ))
        ≤ (eLpNorm (fun z => ‖ageJet 0 j (fun r => hfluct c (tr'.v r)) s z‖)
              (ENNReal.ofReal (22 / 3)) (volume.restrict (B0579.cell c)) +
            eLpNorm (fun z => |iteratedDeriv (j + 1) (meanStream tr' s) z.2|)
              (ENNReal.ofReal (22 / 3)) (volume.restrict (B0579.cell c))) *
            ENNReal.ofReal (c ^ (4 / 11 : ℝ)) :=
          mul_le_mul (hmono.trans hadd) (le_refl _) zero_le zero_le
      _ = eLpNorm (fun z => ‖ageJet 0 j (fun r => hfluct c (tr'.v r)) s z‖)
            (ENNReal.ofReal (22 / 3)) (volume.restrict (B0579.cell c)) *
            ENNReal.ofReal (c ^ (4 / 11 : ℝ)) +
          eLpNorm (fun z => |iteratedDeriv (j + 1) (meanStream tr' s) z.2|)
            (ENNReal.ofReal (22 / 3)) (volume.restrict (B0579.cell c)) *
            ENNReal.ofReal (c ^ (4 / 11 : ℝ)) := add_mul _ _ _
      _ ≤ ENNReal.ofReal (Cf * (p.ν ^ kf)⁻¹ * s ^ αf) +
            ENNReal.ofReal (Cm * (p.ν ^ km)⁻¹ * s ^ αm) := add_le_add hBf hBm
      _ ≤ ENNReal.ofReal (Cf * (p.ν ^ k_tr)⁻¹ * s ^ α) +
            ENNReal.ofReal (Cm * (p.ν ^ k_tr)⁻¹ * s ^ α) :=
          add_le_add (ENNReal.ofReal_le_ofReal h1) (ENNReal.ofReal_le_ofReal h2)
      _ = ENNReal.ofReal ((Cf + Cm) * (p.ν ^ k_tr)⁻¹ * s ^ α) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1; ring
      _ ≤ ENNReal.ofReal (C_tr * (p.ν ^ k_tr)⁻¹ * s ^ α) :=
          ENNReal.ofReal_le_ofReal
            (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hC_sum (by positivity)) (by positivity))
  refine ⟨?_, ?_, ?_⟩
  · exact hcomb 0 hCf0 hCm1 (by dsimp [C_tr]; linarith) (by dsimp [k_tr]; omega)
      (by dsimp [k_tr]; omega) (by norm_num) (by push_cast; norm_num)
      (hBf0 hνp hν_f0 hν1 tr' hbuc s hs1) (hBm1 hνp hν_m1 hν1 tr' hbuc s hs1)
  · exact hcomb 1 hCf1 hCm2 (by dsimp [C_tr]; linarith) (by dsimp [k_tr]; omega)
      (by dsimp [k_tr]; omega) (by norm_num) (by push_cast; norm_num)
      (hBf1 hνp hν_f1 hν1 tr' hbuc s hs1) (hBm2 hνp hν_m2 hν1 tr' hbuc s hs1)
  · exact hcomb 2 hCf2 hCm3 (by dsimp [C_tr]; linarith) (by dsimp [k_tr]; omega)
      (by dsimp [k_tr]; omega) (by norm_num) (by push_cast; norm_num)
      (hBf2 hνp hν_f2 hν1 tr' hbuc s hs1) (hBm3 hνp hν_m3 hν1 tr' hbuc s hs1)

end UnforcedLeray.Short.IIb.TailTrainAux

end
