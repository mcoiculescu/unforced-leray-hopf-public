import UnforcedLeray.Short.PartI.Sub.PartI_T25
import UnforcedLeray.Lib.Train.VortexBounds
import UnforcedLeray.Short.PartI.Tasks.TrainErrorEquation
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.RawJet.Leaves.VcJetSup.AgeJetLe
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.RawJet.Leaves.VelBand

/-!
# `PartI:T25/1` Sub-module: Fixed-band `ageJet` bounds for `dv = tr.v - Vc`

Source of record: `the November 2 reference manuscript`, lines 326-336, 468-478,
541-551.

This module proves:
1. Joint smoothness and slice continuity helpers for `ageJet ℓ j` on `s > 0`, and subadditivity of
   `wCellL2 c m` and `wSupNorm m` on differences of continuous fields.
2. Weighted cell-`L²` bound `wCellL2 c (2 * m) (ageJet ℓ j (Vc ν c) s) ≤ ofReal (polyP C 1 ν c)`
   on `0 < s ≤ Sg / ν` from `VcAgeJetLe` (`Train.Vc_heat`) and `Train.Vc_bounds`.
3. Full weight-`2m` polynomial bound `trainFixedBandVelAgeJet_two_mul_m` for `dv = tr.v - Vc`
   for all `m, ℓ, j : ℕ` by combining `hTails.2.2` (converted via
   `PartI_T25.polyPS_le_polyP_of_le_div_nu`) with the `Vc` age-jet bound.
4. Iterated age-derivative identity `iteratedDeriv_succ_dv_eq` and `ageJet_succ_dv_eq` from
   `TrainErrorEquation.train_error_equation`, expressing `ageJet (ℓ + 1) j dv s` as `ageJet ℓ j` of
   `ν • vecLaplacian dv - (advection tr.v - advection Vc) - gradS (tr.p - pc) - matDiv Qc`.
5. Commutation of `iteratedDeriv ℓ` in age with `Train.vecLaplacian` on jointly smooth fields,
   pointwise bound `‖ageJet ℓ j (ν • vecLaplacian F) s z‖ ≤ (2 * ν) * ‖ageJet ℓ (j + 2) F s z‖`,
   and the resulting unweighted (`m = 0`) fixed-band viscous step bound from order `(ℓ, j + 2)`.
6. Joint smoothness on `(0, ∞) × Plane` of `ν • vecLaplacian dv`, `Train.advection tr.v - Train.advection Vc`,
   and `dp = Train.gradS (tr.p - pc)` (from `Train.matDiv Qc` via `train_error_equation`).
7. Inductive step `trainFixedBandVelOrderUnweighted_succ`, strong induction
   `trainFixedBandVelOrderUnweighted_all`, and conditional assembly `trainFixedBandVelAgeJet_of_leaves`
   reducing `TrainFixedBandVelAgeJet` to the three non-viscous forcing leaves:
   * `TrainFixedBandQcDivAgeJet` (`PartI:T25/1/1`),
   * `TrainFixedBandAdvDiffStep` (`PartI:T25/1/2`),
   * `TrainFixedBandPressStep` (`PartI:T25/1/3`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Real
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec jet cellL2 wCellL2 jap Vc pc width)
open UnforcedLeray.Short.IIb (UU isOpen_UU mem_UU Dx eT eQ eE LapU Sm Dx_congr LapU_congr
  LapU_comm_t hasDerivAt_slice slice_Dv slice_lapD lapD vecLaplacian_eq_lapD norm_jet_lapD_le
  vcSmooth_proof)

/-! ### 1. Continuity of `ageJet` and triangle inequalities for `wCellL2` and `wSupNorm` -/

theorem contDiff_slice_iteratedDeriv_of_contDiffOn {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (F : ℝ → Plane → E)
    (hF : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => F x.1 x.2) (Ioi 0 ×ˢ univ))
    (ℓ : ℕ) {s : ℝ} (hs : 0 < s) :
    ContDiff ℝ ∞ (fun w : Plane => iteratedDeriv ℓ (fun r => F r w) s) := by
  refine contDiff_infty.2 fun n => contDiff_iff_contDiffAt.2 fun w => ?_
  exact UnforcedLeray.Short.IIb.vb_slice_contDiffAt (fun x : ℝ × Plane => F x.1 x.2) hF ℓ n hs w

theorem continuous_ageJet_of_contDiffOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : ℝ → Plane → E)
    (hF : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => F x.1 x.2) (Ioi 0 ×ˢ univ))
    (ℓ j : ℕ) {s : ℝ} (hs : 0 < s) :
    Continuous (ageJet ℓ j F s) := by
  unfold ageJet jet
  exact (contDiff_slice_iteratedDeriv_of_contDiffOn F hF ℓ hs).continuous_iteratedFDeriv
    (by exact_mod_cast le_top)

theorem wCellL2_sub_le_of_continuous {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (c : ℝ) (m : ℕ) {f g : Plane → E} (hf : Continuous f) (hg : Continuous g) :
    wCellL2 c m (fun z => f z - g z) ≤ wCellL2 c m f + wCellL2 c m g := by
  unfold wCellL2
  have hsub : (fun z : Plane => Real.sqrt (jap m z) • (f z - g z)) =
      (fun z : Plane => Real.sqrt (jap m z) • f z) -
        (fun z : Plane => Real.sqrt (jap m z) • g z) := by
    funext z
    simp [smul_sub]
  have hjap : Continuous (fun z : Plane => Real.sqrt (jap m z)) := by
    unfold jap
    fun_prop
  rw [hsub]
  exact eLpNorm_sub_le (hjap.smul hf).aestronglyMeasurable
    (hjap.smul hg).aestronglyMeasurable (by norm_num)

theorem wCellL2_sub4_le_of_continuous {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (c : ℝ) (m : ℕ) {f₁ f₂ f₃ f₄ : Plane → E}
    (h₁ : Continuous f₁) (h₂ : Continuous f₂) (h₃ : Continuous f₃) (h₄ : Continuous f₄) :
    wCellL2 c m (fun z => f₁ z - f₂ z - f₃ z - f₄ z) ≤
      wCellL2 c m f₁ + wCellL2 c m f₂ + wCellL2 c m f₃ + wCellL2 c m f₄ := by
  have h₁₂ : Continuous (fun z => f₁ z - f₂ z) := Continuous.sub h₁ h₂
  have h₁₂₃ : Continuous (fun z => f₁ z - f₂ z - f₃ z) := Continuous.sub h₁₂ h₃
  have s1 := wCellL2_sub_le_of_continuous c m h₁₂₃ h₄
  have s2 := wCellL2_sub_le_of_continuous c m h₁₂ h₃
  have s3 := wCellL2_sub_le_of_continuous c m h₁ h₂
  exact s1.trans (add_le_add_left (s2.trans (add_le_add_left s3 _)) _)

theorem wSupNorm_sub_le {E : Type*} [NormedAddCommGroup E] (m : ℕ) (f g : Plane → E) :
    wSupNorm m (fun z => f z - g z) ≤ wSupNorm m f + wSupNorm m g := by
  unfold wSupNorm
  refine iSup_le fun z => ?_
  calc ENNReal.ofReal (Real.sqrt (jap m z)) * ‖f z - g z‖ₑ
      ≤ ENNReal.ofReal (Real.sqrt (jap m z)) * (‖f z‖ₑ + ‖g z‖ₑ) :=
        mul_le_mul_right enorm_sub_le _
    _ = ENNReal.ofReal (Real.sqrt (jap m z)) * ‖f z‖ₑ +
          ENNReal.ofReal (Real.sqrt (jap m z)) * ‖g z‖ₑ := left_distrib _ _ _
    _ ≤ (⨆ w : Plane, ENNReal.ofReal (Real.sqrt (jap m w)) * ‖f w‖ₑ) +
          (⨆ w : Plane, ENNReal.ofReal (Real.sqrt (jap m w)) * ‖g w‖ₑ) :=
        add_le_add
          (le_iSup (fun w : Plane => ENNReal.ofReal (Real.sqrt (jap m w)) * ‖f w‖ₑ) z)
          (le_iSup (fun w : Plane => ENNReal.ofReal (Real.sqrt (jap m w)) * ‖g w‖ₑ) z)

theorem wSupNorm_sub4_le {E : Type*} [NormedAddCommGroup E]
    (m : ℕ) (f₁ f₂ f₃ f₄ : Plane → E) :
    wSupNorm m (fun z => f₁ z - f₂ z - f₃ z - f₄ z) ≤
      wSupNorm m f₁ + wSupNorm m f₂ + wSupNorm m f₃ + wSupNorm m f₄ := by
  have s1 := wSupNorm_sub_le m (fun z => f₁ z - f₂ z - f₃ z) f₄
  have s2 := wSupNorm_sub_le m (fun z => f₁ z - f₂ z) f₃
  have s3 := wSupNorm_sub_le m f₁ f₂
  exact s1.trans (add_le_add_left (s2.trans (add_le_add_left s3 _)) _)

theorem polyP_add_le {C₁ C₂ ν c : ℝ} (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hν : 0 < ν) (hc : 0 ≤ c) (N₁ N₂ : ℕ) :
    polyP C₁ N₁ ν c + polyP C₂ N₂ ν c ≤ polyP (C₁ + C₂) (max N₁ N₂) ν c := by
  unfold polyP
  have hX1 : 1 ≤ 1 + c + ν⁻¹ := by
    have : 0 ≤ ν⁻¹ := inv_nonneg.2 hν.le
    linarith
  have h1 : C₁ * (1 + c + ν⁻¹) ^ N₁ ≤ C₁ * (1 + c + ν⁻¹) ^ max N₁ N₂ :=
    mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hX1 (le_max_left _ _)) hC₁
  have h2 : C₂ * (1 + c + ν⁻¹) ^ N₂ ≤ C₂ * (1 + c + ν⁻¹) ^ max N₁ N₂ :=
    mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hX1 (le_max_right _ _)) hC₂
  linarith

/-! ### 2. Cell `L²` bound from pointwise `(1 + η²)⁻¹` decay -/

theorem wCellL2_le_of_inv_one_add_sq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {c M : ℝ} (hc : 0 ≤ c) (_hM : 0 ≤ M) (m : ℕ) (f : Plane → E)
    (hf : ∀ z : Plane, Real.sqrt (jap m z) * ‖f z‖ ≤ M * (1 + z.2 ^ 2)⁻¹) :
    wCellL2 c m f ≤ ENNReal.ofReal (Real.sqrt (c * (M ^ 2 * Real.pi))) := by
  unfold wCellL2
  refine Train.eLpNorm_two_le_of_lintegral (by positivity) ?_
  have hpt : ∀ z : Plane,
      ‖Real.sqrt (jap m z) • f z‖ₑ ^ 2 ≤ ENNReal.ofReal (M ^ 2 * (1 + z.2 ^ 2)⁻¹) := by
    intro z
    rw [← ofReal_norm, norm_smul, Real.norm_of_nonneg (Real.sqrt_nonneg _),
      ← ENNReal.ofReal_pow (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have h1 := hf z
    have hnn : 0 ≤ Real.sqrt (jap m z) * ‖f z‖ := by positivity
    have hinv_le1 : (1 + z.2 ^ 2)⁻¹ ≤ 1 :=
      inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg z.2])
    calc (Real.sqrt (jap m z) * ‖f z‖) ^ 2
        ≤ (M * (1 + z.2 ^ 2)⁻¹) ^ 2 := pow_le_pow_left₀ hnn h1 2
      _ = M ^ 2 * (1 + z.2 ^ 2)⁻¹ * (1 + z.2 ^ 2)⁻¹ := by ring
      _ ≤ M ^ 2 * (1 + z.2 ^ 2)⁻¹ * 1 :=
          mul_le_mul_of_nonneg_left hinv_le1 (by positivity)
      _ = M ^ 2 * (1 + z.2 ^ 2)⁻¹ := mul_one _
  have hmeas : AEMeasurable (fun z : Plane => ENNReal.ofReal (M ^ 2 * (1 + z.2 ^ 2)⁻¹))
      (Cyl.cellμ c) := by
    have hm : Measurable (fun z : Plane => ENNReal.ofReal (M ^ 2 * (1 + z.2 ^ 2)⁻¹)) := by
      fun_prop
    exact hm.aemeasurable
  calc ∫⁻ z, ‖Real.sqrt (jap m z) • f z‖ₑ ^ 2 ∂(Cyl.cellμ c)
      ≤ ∫⁻ z, ENNReal.ofReal (M ^ 2 * (1 + z.2 ^ 2)⁻¹) ∂(Cyl.cellμ c) :=
        lintegral_mono hpt
    _ = ∫⁻ q in Ico (-c / 2) (c / 2), ∫⁻ η : ℝ, ENNReal.ofReal (M ^ 2 * (1 + η ^ 2)⁻¹) :=
        Cyl.lintegral_cell_eq hmeas
    _ = ENNReal.ofReal (c * (M ^ 2 * Real.pi)) := by
        have hint : ∫⁻ η : ℝ, ENNReal.ofReal (M ^ 2 * (1 + η ^ 2)⁻¹) =
            ENNReal.ofReal (M ^ 2 * Real.pi) := by
          rw [← ofReal_integral_eq_lintegral_ofReal
            (integrable_inv_one_add_sq.const_mul (M ^ 2))
            (ae_of_all _ fun η => by positivity)]
          rw [integral_const_mul, integral_univ_inv_one_add_sq]
        simp_rw [hint]
        rw [setLIntegral_const, Real.volume_Ico]
        have hlen : c / 2 - -c / 2 = c := by ring
        rw [hlen, mul_comm, ← ENNReal.ofReal_mul hc]

/-! ### 3. Weighted `ageJet` bound for `Vc` on `0 < s ≤ Sg / ν` -/

theorem vc_spatial_jet_weighted_bound (k m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ ν c s : ℝ, 0 < ν → 0 < c → 0 ≤ s → 1 ≤ width ν s → width ν s ≤ c ^ 2 →
        ∀ z : Plane,
          (1 + z.2 ^ 2 / width ν s) ^ (m + 1) * ‖jet k (Vc ν c s) z‖ ≤ C := by
  obtain ⟨C, _b, hC, _hb, hB⟩ := Train.Vc_bounds k (m + 1)
  refine ⟨2 * (2 ^ k * C), by positivity, ?_⟩
  intro ν c s hν hc hs hw1 hw z
  have hVc : ContDiff ℝ ∞ (Vc ν c s) :=
    UnforcedLeray.Short.IIb.vc_contDiff_space hν hc hs
  have hcomp : ∀ i : Fin 2,
      (1 + z.2 ^ 2 / width ν s) ^ (m + 1) *
        ‖iteratedFDeriv ℝ k (fun x => Vc ν c s x i) z‖ ≤ 2 ^ k * C := by
    intro i
    have hsm := UnforcedLeray.Short.IIb.contDiff_comp_proj hVc i
    have hsum := cjw_norm_le_sum _ hsm k z
    have hcard : (wordsOfLength k).card ≤ 2 ^ k := by
      unfold wordsOfLength
      exact Finset.card_image_le.trans (by simp)
    have hterm : ∀ w ∈ wordsOfLength k,
        (1 + z.2 ^ 2 / width ν s) ^ (m + 1) *
          |UnforcedLeray.B0151.derivWord w (fun x => Vc ν c s x i) z| ≤ C := by
      intro w hwm
      have hlen : w.length = k := by
        unfold wordsOfLength at hwm
        obtain ⟨r, -, rfl⟩ := Finset.mem_image.1 hwm
        simp
      have h1 := (hB ν c s hc hw1 hw).1 w hlen i z
      have hrpow : width ν s ^ (-(3 + (k : ℝ)) / 2) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hw1 (by
          have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
          linarith)
      nlinarith
    have hw_nn : 0 ≤ (1 + z.2 ^ 2 / width ν s) ^ (m + 1) := by positivity
    calc (1 + z.2 ^ 2 / width ν s) ^ (m + 1) *
          ‖iteratedFDeriv ℝ k (fun x => Vc ν c s x i) z‖
        ≤ (1 + z.2 ^ 2 / width ν s) ^ (m + 1) *
            ∑ w ∈ wordsOfLength k,
              |UnforcedLeray.B0151.derivWord w (fun x => Vc ν c s x i) z| :=
          mul_le_mul_of_nonneg_left hsum hw_nn
      _ = ∑ w ∈ wordsOfLength k,
            (1 + z.2 ^ 2 / width ν s) ^ (m + 1) *
              |UnforcedLeray.B0151.derivWord w (fun x => Vc ν c s x i) z| :=
          Finset.mul_sum _ _ _
      _ ≤ ∑ _w ∈ wordsOfLength k, C := Finset.sum_le_sum hterm
      _ = (wordsOfLength k).card * C := by simp
      _ ≤ 2 ^ k * C := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hC
  have hvec := UnforcedLeray.Short.IIb.norm_jet_vec_le (Vc ν c s) hVc k z
  have hw_nn : 0 ≤ (1 + z.2 ^ 2 / width ν s) ^ (m + 1) := by positivity
  have h0 := hcomp 0
  have h1 := hcomp 1
  unfold jet
  nlinarith [mul_le_mul_of_nonneg_left hvec hw_nn]

theorem vc_wCellL2_two_mul_m_bound (Sg : ℝ) (hSg : 0 < Sg) (m ℓ j : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ ν c s : ℝ, 0 < ν → ν ≤ 1 → 0 < c → 1 + Sg ≤ c ^ 2 → 0 < s → s ≤ Sg / ν →
        wCellL2 c (2 * m) (ageJet ℓ j (Vc ν c) s) ≤ ENNReal.ofReal (polyP C 1 ν c) := by
  obtain ⟨K, hK, hAge⟩ := UnforcedLeray.Short.IIb.vcAgeJetLe_proof ℓ j
  obtain ⟨C_V, hCV, hSpat⟩ := vc_spatial_jet_weighted_bound (j + 2 * ℓ) m
  set M : ℝ := (1 + Sg) ^ (m + 1) * K * C_V + 1
  have hM_pos : 0 < M := by dsimp [M]; positivity
  refine ⟨M * (Real.pi + 1), by positivity, ?_⟩
  intro ν c s hν hν1 hc hSg_c2 hs hs_le
  have hw1 : 1 ≤ width ν s := by
    unfold width
    linarith [mul_pos hν hs]
  have hw_le_Sg : width ν s ≤ 1 + Sg := by
    unfold width
    have hνs : ν * s ≤ Sg := by
      have := mul_le_mul_of_nonneg_left hs_le hν.le
      rwa [mul_div_cancel₀ _ hν.ne'] at this
    linarith
  have hw_le_c2 : width ν s ≤ c ^ 2 := hw_le_Sg.trans hSg_c2
  have hpt : ∀ z : Plane,
      Real.sqrt (jap (2 * m) z) * ‖ageJet ℓ j (Vc ν c) s z‖ ≤ M * (1 + z.2 ^ 2)⁻¹ := by
    intro z
    have h1 : 1 / (1 + Sg) ≤ 1 := div_le_one_of_le₀ (by linarith) (by positivity)
    have h2 : z.2 ^ 2 / (1 + Sg) ≤ z.2 ^ 2 / width ν s :=
      div_le_div_of_nonneg_left (sq_nonneg z.2) (by positivity) hw_le_Sg
    have h3 : (1 + z.2 ^ 2) / (1 + Sg) ≤ 1 + z.2 ^ 2 / width ν s := by
      rw [add_div]
      linarith
    have h4 : 1 + z.2 ^ 2 ≤ (1 + Sg) * (1 + z.2 ^ 2 / width ν s) := by
      rwa [div_le_iff₀ (by positivity), mul_comm] at h3
    have hpow : (1 + z.2 ^ 2) ^ (m + 1) ≤
        (1 + Sg) ^ (m + 1) * (1 + z.2 ^ 2 / width ν s) ^ (m + 1) := by
      calc (1 + z.2 ^ 2) ^ (m + 1)
          ≤ ((1 + Sg) * (1 + z.2 ^ 2 / width ν s)) ^ (m + 1) :=
            pow_le_pow_left₀ (by positivity) h4 (m + 1)
        _ = (1 + Sg) ^ (m + 1) * (1 + z.2 ^ 2 / width ν s) ^ (m + 1) := mul_pow _ _ _
    have hjap_eq : Real.sqrt (jap (2 * m) z) = (1 + z.2 ^ 2) ^ m := by
      have hsq : jap (2 * m) z = ((1 + z.2 ^ 2) ^ m) ^ 2 := by
        unfold jap
        rw [mul_comm 2 m, pow_mul]
      rw [hsq, Real.sqrt_sq (by positivity)]
    have hν_pow : ν ^ ℓ ≤ 1 := pow_le_one₀ hν.le hν1
    have hA : ‖ageJet ℓ j (Vc ν c) s z‖ ≤ K * ‖jet (j + 2 * ℓ) (Vc ν c s) z‖ := by
      calc ‖ageJet ℓ j (Vc ν c) s z‖
          ≤ ν ^ ℓ * K * ‖jet (j + 2 * ℓ) (Vc ν c s) z‖ := hAge ν c hν hc s hs z
        _ ≤ 1 * K * ‖jet (j + 2 * ℓ) (Vc ν c s) z‖ := by gcongr
        _ = K * ‖jet (j + 2 * ℓ) (Vc ν c s) z‖ := by ring
    have hS := hSpat ν c s hν hc hs.le hw1 hw_le_c2 z
    have hprod : (1 + z.2 ^ 2) ^ (m + 1) * ‖ageJet ℓ j (Vc ν c) s z‖ ≤ M := by
      calc (1 + z.2 ^ 2) ^ (m + 1) * ‖ageJet ℓ j (Vc ν c) s z‖
          ≤ (1 + Sg) ^ (m + 1) * (1 + z.2 ^ 2 / width ν s) ^ (m + 1) *
              (K * ‖jet (j + 2 * ℓ) (Vc ν c s) z‖) :=
            mul_le_mul hpow hA (norm_nonneg _) (by positivity)
        _ = (1 + Sg) ^ (m + 1) * K *
              ((1 + z.2 ^ 2 / width ν s) ^ (m + 1) * ‖jet (j + 2 * ℓ) (Vc ν c s) z‖) := by ring
        _ ≤ (1 + Sg) ^ (m + 1) * K * C_V :=
            mul_le_mul_of_nonneg_left hS (by positivity)
        _ ≤ M := by dsimp [M]; linarith
    rw [hjap_eq]
    have h1z_ne : 1 + z.2 ^ 2 ≠ 0 := by positivity
    calc (1 + z.2 ^ 2) ^ m * ‖ageJet ℓ j (Vc ν c) s z‖
        = ((1 + z.2 ^ 2) ^ (m + 1) * ‖ageJet ℓ j (Vc ν c) s z‖) * (1 + z.2 ^ 2)⁻¹ := by
          rw [pow_succ']
          field_simp
          ring
      _ ≤ M * (1 + z.2 ^ 2)⁻¹ := mul_le_mul_of_nonneg_right hprod (by positivity)
  have hL2 := wCellL2_le_of_inv_one_add_sq hc.le hM_pos.le (2 * m) (ageJet ℓ j (Vc ν c) s) hpt
  refine hL2.trans (ENNReal.ofReal_le_ofReal ?_)
  unfold polyP
  rw [pow_one]
  have hsq : c * (M ^ 2 * Real.pi) ≤ (M * (Real.pi + 1) * (1 + c + ν⁻¹)) ^ 2 := by
    have hν_inv : 0 ≤ ν⁻¹ := inv_nonneg.2 hν.le
    have hpi : 0 < Real.pi := Real.pi_pos
    have h1 : c ≤ 1 + c + ν⁻¹ := by linarith
    have h2 : 1 ≤ 1 + c + ν⁻¹ := by linarith
    have h3 : c ≤ (1 + c + ν⁻¹) ^ 2 := by nlinarith
    have h4 : Real.pi ≤ (Real.pi + 1) ^ 2 := by nlinarith
    calc c * (M ^ 2 * Real.pi)
        = M ^ 2 * Real.pi * c := by ring
      _ ≤ M ^ 2 * (Real.pi + 1) ^ 2 * (1 + c + ν⁻¹) ^ 2 := by
          apply mul_le_mul _ h3 hc.le (by positivity)
          exact mul_le_mul_of_nonneg_left h4 (sq_nonneg M)
      _ = (M * (Real.pi + 1) * (1 + c + ν⁻¹)) ^ 2 := by ring
  exact (Real.sqrt_le_iff).2 ⟨by positivity, hsq⟩

/-! ### 4. Weight-`2m` polynomial bound for `dv = tr.v - Vc` for all `m, ℓ, j` -/

theorem trainFixedBandVelAgeJet_two_mul_m
    (hTails : TrainStreamVelocityPressureTails)
    (ρ : ℝ) (hρ : 1 / 2 < ρ) (Sg : ℝ) (hSg : 0 < Sg) (m ℓ j : ℕ) :
    ∃ C : ℝ, ∃ N : ℕ, ∃ ν₀ : ℝ, 0 < C ∧ 0 < ν₀ ∧
      ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
        ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr →
          ∀ s : ℝ, 0 < s → s ≤ Sg / ν →
            let c := trainPeriod ρ ν
            let dv : ℝ → Plane → Vec := fun r z => tr.v r z - Vc ν c r z
            wCellL2 c (2 * m) (ageJet ℓ j dv s) ≤ ENNReal.ofReal (polyP C N ν c) := by
  obtain ⟨C₁, N₁, ν₁, hC₁, hν₁, hT⟩ := hTails.2.2 ρ hρ (2 * m) ℓ j
  obtain ⟨C₂, hC₂, hVc⟩ := vc_wCellL2_two_mul_m_bound Sg hSg m ℓ j
  obtain ⟨νp, hνp, hνp1, hp⟩ := trainPeriodAsymptotics_proof ρ hρ (1 + Sg) (by positivity)
  let C_out := C₁ * (1 + Sg) ^ N₁ + C₂
  let N_out := max (2 * N₁) 1
  refine ⟨C_out, N_out, min ν₁ νp, by positivity, lt_min hν₁ hνp, ?_⟩
  intro ν hν hν_le tr htr s hs hs_le
  have hν₁_le : ν ≤ ν₁ := hν_le.trans (min_le_left _ _)
  have hνp_le : ν ≤ νp := hν_le.trans (min_le_right _ _)
  have hν1 : ν ≤ 1 := hνp_le.trans hνp1
  obtain ⟨hc1, hνc2⟩ := hp ν hν hνp_le
  let c := trainPeriod ρ ν
  have hc_pos : 0 < c := zero_lt_one.trans_le hc1
  have hSg_c2 : 1 + Sg ≤ c ^ 2 := by
    calc 1 + Sg ≤ ν * c ^ 2 := hνc2
      _ ≤ 1 * c ^ 2 := mul_le_mul_of_nonneg_right hν1 (sq_nonneg c)
      _ = c ^ 2 := one_mul _
  have hsm_v : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => tr.v x.1 x.2) (Ioi 0 ×ˢ univ) :=
    tr.isTrain.smooth_v.mono (Set.prod_mono Set.Ioi_subset_Ici_self Subset.rfl)
  have hsm_Vc : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => Vc ν c x.1 x.2) (Ioi 0 ×ˢ univ) :=
    UnforcedLeray.Short.IIb.vcSmooth_proof ν c hν hc_pos
  have hsub : ageJet ℓ j (fun r z => tr.v r z - Vc ν c r z) s =
      fun z => ageJet ℓ j tr.v s z - ageJet ℓ j (Vc ν c) s z :=
    funext (UnforcedLeray.Short.IIb.vb_ageJet_sub tr.v (Vc ν c) hsm_v hsm_Vc hs ℓ j)
  have hcont_v := continuous_ageJet_of_contDiffOn tr.v hsm_v ℓ j hs
  have hcont_Vc := continuous_ageJet_of_contDiffOn (Vc ν c) hsm_Vc ℓ j hs
  have htri := wCellL2_sub_le_of_continuous c (2 * m) hcont_v hcont_Vc
  have hv_bound : wCellL2 c (2 * m) (ageJet ℓ j tr.v s) ≤
      ENNReal.ofReal (polyP (C₁ * (1 + Sg) ^ N₁) (2 * N₁) ν c) := by
    have h1 := ((hT ν hν hν₁_le tr htr s hs).2.2.1).1
    have h2 := PartI_T25.polyPS_le_polyP_of_le_div_nu N₁ hC₁.le hSg.le hν hc_pos.le hs.le hs_le
    exact h1.trans (ENNReal.ofReal_le_ofReal h2)
  have hVc_bound := hVc ν c s hν hν1 hc_pos hSg_c2 hs hs_le
  have hX1 : 1 ≤ 1 + c + ν⁻¹ := by
    have : 0 ≤ ν⁻¹ := inv_nonneg.2 hν.le
    linarith
  have hP₁ : polyP (C₁ * (1 + Sg) ^ N₁) (2 * N₁) ν c ≤
      polyP (C₁ * (1 + Sg) ^ N₁) N_out ν c := by
    unfold polyP
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hX1 (le_max_left _ _)) (by positivity)
  have hP₂ : polyP C₂ 1 ν c ≤ polyP C₂ N_out ν c := by
    unfold polyP
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hX1 (le_max_right _ _)) hC₂.le
  dsimp only
  rw [hsub]
  calc wCellL2 c (2 * m) (fun z => ageJet ℓ j tr.v s z - ageJet ℓ j (Vc ν c) s z)
      ≤ wCellL2 c (2 * m) (ageJet ℓ j tr.v s) + wCellL2 c (2 * m) (ageJet ℓ j (Vc ν c) s) := htri
    _ ≤ ENNReal.ofReal (polyP (C₁ * (1 + Sg) ^ N₁) N_out ν c) +
          ENNReal.ofReal (polyP C₂ N_out ν c) :=
        add_le_add (hv_bound.trans (ENNReal.ofReal_le_ofReal hP₁))
          (hVc_bound.trans (ENNReal.ofReal_le_ofReal hP₂))
    _ = ENNReal.ofReal (polyP C_out N_out ν c) := by
        rw [← ENNReal.ofReal_add (by unfold polyP; positivity) (by unfold polyP; positivity)]
        congr 1
        unfold polyP
        dsimp [C_out]
        ring

/-! ### 5. Iterated age derivative of the error equation and viscous Laplacian commutation -/

namespace PartI_T25_1

/-- Iterated age directional derivative `(Dx eT)^[ℓ] F` on `ℝ × Plane`. -/
def DtU (ℓ : ℕ) (F : ℝ × Plane → Vec) : ℝ × Plane → Vec :=
  (Dx eT)^[ℓ] F

theorem sm_DtU {F : ℝ × Plane → Vec} (hF : Sm F) : ∀ ℓ : ℕ, Sm (DtU ℓ F)
  | 0 => hF
  | ℓ + 1 => by
    unfold DtU
    rw [Function.iterate_succ_apply']
    exact (sm_DtU hF ℓ).dx eT

theorem iteratedDeriv_slice_eq_DtU {F : ℝ × Plane → Vec} (hF : Sm F) :
    ∀ (ℓ : ℕ) {t : ℝ}, 0 < t → ∀ w : Plane,
      iteratedDeriv ℓ (fun r => F (r, w)) t = DtU ℓ F (t, w)
  | 0, _, _, _ => rfl
  | ℓ + 1, t, ht, w => by
    rw [iteratedDeriv_succ]
    have hev : iteratedDeriv ℓ (fun r => F (r, w)) =ᶠ[nhds t] fun r => DtU ℓ F (r, w) := by
      filter_upwards [Ioi_mem_nhds ht] with r hr using iteratedDeriv_slice_eq_DtU hF ℓ hr w
    rw [hev.deriv_eq, (hasDerivAt_slice (sm_DtU hF ℓ) ht w).deriv]
    unfold DtU
    rw [Function.iterate_succ_apply']

theorem DtU_comm_LapU {F : ℝ × Plane → Vec} (hF : Sm F) :
    ∀ ℓ : ℕ, EqOn (DtU ℓ (LapU F)) (LapU (DtU ℓ F)) UU
  | 0 => fun _ _ => rfl
  | ℓ + 1 => by
    intro x hx
    have hDt : ∀ G : ℝ × Plane → Vec, DtU (ℓ + 1) G = Dx eT (DtU ℓ G) :=
      fun G => Function.iterate_succ_apply' (Dx eT) ℓ G
    rw [hDt, hDt, Dx_congr (DtU_comm_LapU hF ℓ) eT hx]
    exact LapU_comm_t (sm_DtU hF ℓ) hx

theorem contDiff_slice_of_sm {F : ℝ → Plane → Vec}
    (hF : Sm (fun x : ℝ × Plane => F x.1 x.2)) {t : ℝ} (ht : 0 < t) :
    ContDiff ℝ ∞ (F t) := by
  rw [← contDiffOn_univ]
  exact hF.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun x _ => mem_UU ht)

theorem vecLaplacian_slice_eq_LapU {F : ℝ → Plane → Vec}
    (hF : Sm (fun x : ℝ × Plane => F x.1 x.2)) {t : ℝ} (ht : 0 < t) (w : Plane) :
    Train.vecLaplacian (F t) w = LapU (fun x : ℝ × Plane => F x.1 x.2) (t, w) := by
  have hu : ContDiff ℝ ∞ (F t) := contDiff_slice_of_sm hF ht
  rw [vecLaplacian_eq_lapD hu]
  exact congrFun (slice_lapD hF ht) w

/-- Joint smoothness of `(r, w) ↦ ν • Train.vecLaplacian (F r) w` on `UU = Ioi 0 ×ˢ univ`. -/
theorem sm_smul_vecLaplacian {F : ℝ → Plane → Vec}
    (hF : Sm (fun x : ℝ × Plane => F x.1 x.2)) (ν : ℝ) :
    Sm (fun x : ℝ × Plane => ν • Train.vecLaplacian (F x.1) x.2) := by
  have hLap : Sm (fun x : ℝ × Plane => ν • LapU (fun y : ℝ × Plane => F y.1 y.2) x) :=
    hF.lap.const_smul ν
  refine hLap.congr fun ⟨t, w⟩ hx => ?_
  dsimp only
  rw [vecLaplacian_slice_eq_LapU hF hx.1 w]

/-- Commutation of `iteratedDeriv ℓ` in age with `ν • Train.vecLaplacian` for jointly smooth `F`. -/
theorem iteratedDeriv_smul_vecLaplacian_eq {F : ℝ → Plane → Vec}
    (hF : Sm (fun x : ℝ × Plane => F x.1 x.2)) (ν : ℝ) (ℓ : ℕ) {s : ℝ} (hs : 0 < s) (w : Plane) :
    iteratedDeriv ℓ (fun r => ν • Train.vecLaplacian (F r) w) s =
      ν • lapD (fun x => iteratedDeriv ℓ (fun r => F r x) s) w := by
  let U : ℝ × Plane → Vec := fun x => F x.1 x.2
  have hev : (fun r => ν • Train.vecLaplacian (F r) w) =ᶠ[nhds s]
      fun r => ν • LapU U (r, w) := by
    filter_upwards [Ioi_mem_nhds hs] with r hr
    rw [vecLaplacian_slice_eq_LapU hF hr w]
  rw [hev.iteratedDeriv_eq ℓ]
  change iteratedDeriv ℓ (ν • fun r => LapU U (r, w)) s = _
  rw [iteratedDeriv_const_smul_field]
  congr 1
  rw [iteratedDeriv_slice_eq_DtU hF.lap ℓ hs w, DtU_comm_LapU hF ℓ (mem_UU hs)]
  rw [← congrFun (slice_lapD (sm_DtU hF ℓ) hs) w]
  congr 1
  funext x
  exact (iteratedDeriv_slice_eq_DtU hF ℓ hs x).symm

/-- Pointwise bound `‖ageJet ℓ j (fun r w => ν • Train.vecLaplacian (F r) w) s z‖ ≤ (2 * ν) * ‖ageJet ℓ (j + 2) F s z‖`
for jointly smooth `F` and `ν ≥ 0`, `s > 0`. -/
theorem norm_ageJet_smul_vecLaplacian_le {F : ℝ → Plane → Vec}
    (hF : Sm (fun x : ℝ × Plane => F x.1 x.2)) {ν : ℝ} (hν : 0 ≤ ν)
    (ℓ j : ℕ) {s : ℝ} (hs : 0 < s) (z : Plane) :
    ‖ageJet ℓ j (fun r w => ν • Train.vecLaplacian (F r) w) s z‖ ≤
      (2 * ν) * ‖ageJet ℓ (j + 2) F s z‖ := by
  have hslice : (fun w => iteratedDeriv ℓ (fun r => ν • Train.vecLaplacian (F r) w) s) =
      fun w => ν • lapD (fun x => iteratedDeriv ℓ (fun r => F r x) s) w :=
    funext fun w => iteratedDeriv_smul_vecLaplacian_eq hF ν ℓ hs w
  have hu : ContDiff ℝ ∞ (fun x : Plane => iteratedDeriv ℓ (fun r => F r x) s) :=
    contDiff_slice_iteratedDeriv_of_contDiffOn F hF ℓ hs
  have hlap : ContDiffAt ℝ j (lapD (fun x => iteratedDeriv ℓ (fun r => F r x) s)) z :=
    ((UnforcedLeray.Short.IIb.contDiff_lapD hu).of_le (by exact_mod_cast le_top)).contDiffAt
  have heq : ageJet ℓ j (fun r w => ν • Train.vecLaplacian (F r) w) s z =
      ν • iteratedFDeriv ℝ j (lapD (fun x => iteratedDeriv ℓ (fun r => F r x) s)) z := by
    unfold ageJet jet
    rw [hslice]
    exact iteratedFDeriv_const_smul_apply' hlap
  rw [heq, norm_smul, Real.norm_of_nonneg hν]
  have h1 := norm_jet_lapD_le hu j z
  unfold ageJet jet
  nlinarith

/-- Expressing `Train.advection (F t) w` on `UU` in terms of `F` and directional derivatives `Dx eQ`, `Dx eE`. -/
theorem advection_slice_eq_Dx {F : ℝ → Plane → Vec}
    (hF : Sm (fun x : ℝ × Plane => F x.1 x.2)) {t : ℝ} (ht : 0 < t) (w : Plane) :
    Train.advection (F t) w =
      let U : ℝ × Plane → Vec := fun x => F x.1 x.2
      Train.toVec
        (U (t, w) 0 * Dx eQ U (t, w) 0 + U (t, w) 1 * Dx eE U (t, w) 0,
         U (t, w) 0 * Dx eQ U (t, w) 1 + U (t, w) 1 * Dx eE U (t, w) 1) := by
  let U : ℝ × Plane → Vec := fun x => F x.1 x.2
  have hu : ContDiff ℝ ∞ (F t) := contDiff_slice_of_sm hF ht
  have hdu : Differentiable ℝ (F t) := hu.differentiable (by simp)
  have hcomp : ∀ k : Fin 2, Differentiable ℝ (fun z : Plane => F t z k) := fun k =>
    ((EuclideanSpace.proj k : Vec →L[ℝ] ℝ).contDiff.comp hu).differentiable (by simp)
  have hQ : ∀ k : Fin 2, Cyl.partialQ (fun z => F t z k) w = Dx eQ U (t, w) k := by
    intro k
    rw [Cyl.partialQ_eq_fderiv (hcomp k) w]
    have hproj := congrFun (UnforcedLeray.Short.IIb.Dv_proj hdu ((1 : ℝ), (0 : ℝ)) k) w
    have hsl := congrFun (slice_Dv hF ht ((1 : ℝ), (0 : ℝ))) w
    exact hproj.trans (congrArg (fun v : Vec => v k) hsl)
  have hE : ∀ k : Fin 2, Cyl.partialEta (fun z => F t z k) w = Dx eE U (t, w) k := by
    intro k
    rw [Cyl.partialEta_eq_fderiv (hcomp k) w]
    have hproj := congrFun (UnforcedLeray.Short.IIb.Dv_proj hdu ((0 : ℝ), (1 : ℝ)) k) w
    have hsl := congrFun (slice_Dv hF ht ((0 : ℝ), (1 : ℝ))) w
    exact hproj.trans (congrArg (fun v : Vec => v k) hsl)
  unfold Train.advection
  rw [hQ 0, hE 0, hQ 1, hE 1]

/-- Joint smoothness of `(r, w) ↦ Train.advection (F r) w` on `UU = Ioi 0 ×ˢ univ`. -/
theorem sm_advection {F : ℝ → Plane → Vec}
    (hF : Sm (fun x : ℝ × Plane => F x.1 x.2)) :
    Sm (fun x : ℝ × Plane => Train.advection (F x.1) x.2) := by
  let U : ℝ × Plane → Vec := fun x => F x.1 x.2
  have hproj : ∀ (G : ℝ × Plane → Vec), Sm G → ∀ k : Fin 2,
      ContDiffOn ℝ ∞ (fun x : ℝ × Plane => G x k) UU := fun G hG k =>
    (EuclideanSpace.proj k : Vec →L[ℝ] ℝ).contDiff.comp_contDiffOn hG
  have hU0 := hproj U hF 0
  have hU1 := hproj U hF 1
  have hQ0 := hproj (Dx eQ U) (hF.dx eQ) 0
  have hQ1 := hproj (Dx eQ U) (hF.dx eQ) 1
  have hE0 := hproj (Dx eE U) (hF.dx eE) 0
  have hE1 := hproj (Dx eE U) (hF.dx eE) 1
  have hpair : ContDiffOn ℝ ∞ (fun x : ℝ × Plane =>
      (U x 0 * Dx eQ U x 0 + U x 1 * Dx eE U x 0,
       U x 0 * Dx eQ U x 1 + U x 1 * Dx eE U x 1)) UU :=
    ((hU0.mul hQ0).add (hU1.mul hE0)).prodMk ((hU0.mul hQ1).add (hU1.mul hE1))
  have hvec : Sm (fun x : ℝ × Plane => Train.toVec
      (U x 0 * Dx eQ U x 0 + U x 1 * Dx eE U x 0,
       U x 0 * Dx eQ U x 1 + U x 1 * Dx eE U x 1)) :=
    (Train.toVecL : (ℝ × ℝ) →L[ℝ] Vec).contDiff.comp_contDiffOn hpair
  refine hvec.congr fun ⟨t, w⟩ hx => ?_
  exact advection_slice_eq_Dx hF hx.1 w

/-- Pointwise time-derivative rearrangement of `TrainErrorEquation.train_error_equation` on `s > 0`. -/
theorem deriv_dv_eq_error_rhs {ν c : ℝ} (tr : B0140.TrainSol ν c)
    (hν : 0 < ν) (hc : c ≠ 0) {s : ℝ} (hs : 0 < s) (z : Plane) :
    deriv (fun t => tr.v t z - Vc ν c t z) s =
      ν • Train.vecLaplacian (fun w => tr.v s w - Vc ν c s w) z
      - (Train.advection (tr.v s) z - Train.advection (Vc ν c s) z)
      - Train.gradS (fun w => tr.p s w - pc ν c s w) z
      - Train.matDiv (Train.Qc ν c s) z := by
  have h := TrainErrorEquation.train_error_equation tr hν hc s hs z
  ext k
  have hk := congrArg (fun v : Vec => v k) h
  simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.neg_apply] at hk ⊢
  linarith

/-- Iterated age derivative of `dv = tr.v - Vc` at order `ℓ + 1` via `train_error_equation`. -/
theorem iteratedDeriv_succ_dv_eq {ν c : ℝ} (tr : B0140.TrainSol ν c)
    (hν : 0 < ν) (hc : c ≠ 0) (ℓ : ℕ) {s : ℝ} (hs : 0 < s) (z : Plane) :
    iteratedDeriv (ℓ + 1) (fun r => tr.v r z - Vc ν c r z) s =
      iteratedDeriv ℓ (fun r =>
        ν • Train.vecLaplacian (fun w => tr.v r w - Vc ν c r w) z
        - (Train.advection (tr.v r) z - Train.advection (Vc ν c r) z)
        - Train.gradS (fun w => tr.p r w - pc ν c r w) z
        - Train.matDiv (Train.Qc ν c r) z) s := by
  rw [iteratedDeriv_succ']
  have hev : deriv (fun r => tr.v r z - Vc ν c r z) =ᶠ[nhds s]
      fun r =>
        ν • Train.vecLaplacian (fun w => tr.v r w - Vc ν c r w) z
        - (Train.advection (tr.v r) z - Train.advection (Vc ν c r) z)
        - Train.gradS (fun w => tr.p r w - pc ν c r w) z
        - Train.matDiv (Train.Qc ν c r) z := by
    filter_upwards [Ioi_mem_nhds hs] with r hr using deriv_dv_eq_error_rhs tr hν hc hr z
  exact hev.iteratedDeriv_eq ℓ

/-- `ageJet (ℓ + 1) j dv s` equals `ageJet ℓ j` of the right-hand side of the velocity error equation. -/
theorem ageJet_succ_dv_eq {ν c : ℝ} (tr : B0140.TrainSol ν c)
    (hν : 0 < ν) (hc : c ≠ 0) (ℓ j : ℕ) {s : ℝ} (hs : 0 < s) :
    ageJet (ℓ + 1) j (fun r z => tr.v r z - Vc ν c r z) s =
      ageJet ℓ j (fun r z =>
        ν • Train.vecLaplacian (fun w => tr.v r w - Vc ν c r w) z
        - (Train.advection (tr.v r) z - Train.advection (Vc ν c r) z)
        - Train.gradS (fun w => tr.p r w - pc ν c r w) z
        - Train.matDiv (Train.Qc ν c r) z) s := by
  unfold ageJet
  congr 1
  funext z
  exact iteratedDeriv_succ_dv_eq tr hν hc ℓ hs z

/-- Joint smoothness of `dp = Train.gradS (tr.p - pc)` on `UU = Ioi 0 ×ˢ univ` derived from
joint smoothness of `Train.matDiv (Train.Qc ν c)` via `train_error_equation`. -/
theorem sm_dp_of_sm_qcDiv {ν c : ℝ} (tr : B0140.TrainSol ν c)
    (hν : 0 < ν) (hc : 0 < c)
    (hQc : Sm (fun x : ℝ × Plane => Train.matDiv (Train.Qc ν c x.1) x.2)) :
    Sm (fun x : ℝ × Plane => Train.gradS (fun w => tr.p x.1 w - pc ν c x.1 w) x.2) := by
  have hsm_v : Sm (fun x : ℝ × Plane => tr.v x.1 x.2) :=
    tr.isTrain.smooth_v.mono (Set.prod_mono Set.Ioi_subset_Ici_self Subset.rfl)
  have hsm_Vc : Sm (fun x : ℝ × Plane => Vc ν c x.1 x.2) := vcSmooth_proof ν c hν hc
  let dv : ℝ → Plane → Vec := fun r z => tr.v r z - Vc ν c r z
  have hsm_dv : Sm (fun x : ℝ × Plane => dv x.1 x.2) := hsm_v.sub hsm_Vc
  have hsm_visc : Sm (fun x : ℝ × Plane => ν • Train.vecLaplacian (dv x.1) x.2) :=
    sm_smul_vecLaplacian hsm_dv ν
  have hsm_dt : Sm (Dx eT (fun x : ℝ × Plane => dv x.1 x.2)) := hsm_dv.dx eT
  have hsm_adv : Sm (fun x : ℝ × Plane =>
      Train.advection (tr.v x.1) x.2 - Train.advection (Vc ν c x.1) x.2) :=
    (sm_advection hsm_v).sub (sm_advection hsm_Vc)
  have hsm_comb : Sm (fun x : ℝ × Plane =>
      ν • Train.vecLaplacian (dv x.1) x.2
      - Dx eT (fun y : ℝ × Plane => dv y.1 y.2) x
      - (Train.advection (tr.v x.1) x.2 - Train.advection (Vc ν c x.1) x.2)
      - Train.matDiv (Train.Qc ν c x.1) x.2) :=
    ((hsm_visc.sub hsm_dt).sub hsm_adv).sub hQc
  refine hsm_comb.congr fun ⟨r, z⟩ hx => ?_
  have hr : 0 < r := hx.1
  have hdt : Dx eT (fun y : ℝ × Plane => dv y.1 y.2) (r, z) = deriv (fun t => dv t z) r :=
    (hasDerivAt_slice hsm_dv hr z).deriv.symm
  have herr := deriv_dv_eq_error_rhs tr hν hc.ne' hr z
  ext k
  have hk := congrArg (fun v : Vec => v k) herr
  have hdt_k := congrArg (fun v : Vec => v k) hdt
  dsimp only [dv] at hk hdt_k ⊢
  simp only [PiLp.sub_apply] at hk hdt_k ⊢
  linarith

end PartI_T25_1

/-! ### 6. Inductive age-derivative hierarchy and leaf propositions for `PartI:T25/1` -/

/-- Unweighted (`m = 0`) fixed-band exponential bound for `ageJet r j dv s` on `0 < s ≤ Sg / ν`
at a fixed age-derivative order `r : ℕ` and all spatial orders `j : ℕ`. -/
def TrainFixedBandVelOrderUnweighted (r : ℕ) : Prop :=
  ∀ ρ : ℝ, 1 / 2 < ρ → ∀ Sg : ℝ, 0 < Sg → ∀ j : ℕ,
    ∃ C : ℝ, ∃ N : ℕ, ∃ CS bS ν₀ : ℝ, 0 < C ∧ 0 < bS ∧ 0 < ν₀ ∧
      ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
        ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr →
          ∀ s : ℝ, 0 < s → s ≤ Sg / ν →
            let c := trainPeriod ρ ν
            let dv : ℝ → Plane → Vec := fun t z => tr.v t z - Vc ν c t z
            wCellL2 c 0 (ageJet r j dv s) ≤
              ENNReal.ofReal (polyP C N ν c * Real.exp (CS / ν - bS * c ^ 2)) ∧
            wSupNorm 0 (ageJet r j dv s) ≤
              ENNReal.ofReal (polyP C N ν c * Real.exp (CS / ν - bS * c ^ 2))

/-- **Base case (`r = 0`) of `TrainFixedBandVelOrderUnweighted`**, proved unconditionally from
`PartI_T25.trainFixedBand_vel_zero_unweighted`. -/
theorem trainFixedBandVelOrderUnweighted_zero : TrainFixedBandVelOrderUnweighted 0 := by
  intro ρ hρ Sg hSg j
  obtain ⟨C, bS, ν₀, hC, hbS, hν₀, h0⟩ :=
    PartI_T25.trainFixedBand_vel_zero_unweighted ρ hρ Sg hSg j
  refine ⟨C, 1, 0, bS, ν₀, hC, hbS, hν₀, ?_⟩
  intro ν hν hν_le tr htr s hs hs_le
  obtain ⟨hL2, hSup⟩ := h0 ν hν hν_le tr htr s hs hs_le
  have hexp : polyP C 1 ν (trainPeriod ρ ν) * Real.exp (-(bS * (trainPeriod ρ ν) ^ 2)) =
      polyP C 1 ν (trainPeriod ρ ν) * Real.exp (0 / ν - bS * (trainPeriod ρ ν) ^ 2) := by
    rw [zero_div, zero_sub]
  dsimp only
  rw [← hexp]
  exact ⟨hL2, hSup⟩

/-- **Viscous diffusion step at age order `ℓ`**: from `TrainFixedBandVelOrderUnweighted ℓ` (applied
at spatial order `j + 2`), `ageJet ℓ j (fun r z => ν • Train.vecLaplacian (dv r) z) s` satisfies the
unweighted (`m = 0`) fixed-band exponential bound. -/
theorem trainFixedBandViscStep_of_order (ℓ : ℕ) (hℓ : TrainFixedBandVelOrderUnweighted ℓ)
    (ρ : ℝ) (hρ : 1 / 2 < ρ) (Sg : ℝ) (hSg : 0 < Sg) (j : ℕ) :
    ∃ C : ℝ, ∃ N : ℕ, ∃ CS bS ν₀ : ℝ, 0 < C ∧ 0 < bS ∧ 0 < ν₀ ∧
      ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
        ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr →
          ∀ s : ℝ, 0 < s → s ≤ Sg / ν →
            let c := trainPeriod ρ ν
            let dv : ℝ → Plane → Vec := fun t z => tr.v t z - Vc ν c t z
            wCellL2 c 0 (ageJet ℓ j (fun r z => ν • Train.vecLaplacian (dv r) z) s) ≤
              ENNReal.ofReal (polyP C N ν c * Real.exp (CS / ν - bS * c ^ 2)) ∧
            wSupNorm 0 (ageJet ℓ j (fun r z => ν • Train.vecLaplacian (dv r) z) s) ≤
              ENNReal.ofReal (polyP C N ν c * Real.exp (CS / ν - bS * c ^ 2)) := by
  obtain ⟨C, N, CS, bS, ν₀, hC, hbS, hν₀, hbd⟩ := hℓ ρ hρ Sg hSg (j + 2)
  refine ⟨2 * C, N, CS, bS, min ν₀ 1, by positivity, hbS, lt_min hν₀ one_pos, ?_⟩
  intro ν hν hν_le tr htr s hs hs_le
  have hν₀_le : ν ≤ ν₀ := hν_le.trans (min_le_left _ _)
  have hν1 : ν ≤ 1 := hν_le.trans (min_le_right _ _)
  let c := trainPeriod ρ ν
  have hc_pos : 0 < c := by
    dsimp [c]
    unfold trainPeriod
    exact Real.rpow_pos_of_pos hν _
  let dv : ℝ → Plane → Vec := fun t z => tr.v t z - Vc ν c t z
  have hsm_v : Sm (fun x : ℝ × Plane => tr.v x.1 x.2) :=
    tr.isTrain.smooth_v.mono (Set.prod_mono Set.Ioi_subset_Ici_self Subset.rfl)
  have hsm_Vc : Sm (fun x : ℝ × Plane => Vc ν c x.1 x.2) := vcSmooth_proof ν c hν hc_pos
  have hsm_dv : Sm (fun x : ℝ × Plane => dv x.1 x.2) := hsm_v.sub hsm_Vc
  have hpt : ∀ z : Plane,
      ‖ageJet ℓ j (fun r w => ν • Train.vecLaplacian (dv r) w) s z‖ ≤
        2 * ‖ageJet ℓ (j + 2) dv s z‖ := by
    intro z
    calc ‖ageJet ℓ j (fun r w => ν • Train.vecLaplacian (dv r) w) s z‖
        ≤ (2 * ν) * ‖ageJet ℓ (j + 2) dv s z‖ :=
          PartI_T25_1.norm_ageJet_smul_vecLaplacian_le hsm_dv hν.le ℓ j hs z
      _ ≤ 2 * ‖ageJet ℓ (j + 2) dv s z‖ :=
          mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
  obtain ⟨hL2, hSup⟩ := hbd ν hν hν₀_le tr htr s hs hs_le
  have h1 := PartI_T25.wCellL2_le_of_pointwise c 0 (K := 2) (by norm_num)
    (ageJet ℓ j (fun r w => ν • Train.vecLaplacian (dv r) w) s) (ageJet ℓ (j + 2) dv s) hpt
  have h2 := PartI_T25.wSupNorm_le_of_pointwise 0 (K := 2) (by norm_num)
    (ageJet ℓ j (fun r w => ν • Train.vecLaplacian (dv r) w) s) (ageJet ℓ (j + 2) dv s) hpt
  have hpoly_eq : 2 * (polyP C N ν c * Real.exp (CS / ν - bS * c ^ 2)) =
      polyP (2 * C) N ν c * Real.exp (CS / ν - bS * c ^ 2) := by
    unfold polyP; ring
  refine ⟨?_, ?_⟩
  · calc wCellL2 c 0 (ageJet ℓ j (fun r z => ν • Train.vecLaplacian (dv r) z) s)
        ≤ ENNReal.ofReal 2 * wCellL2 c 0 (ageJet ℓ (j + 2) dv s) := h1
      _ ≤ ENNReal.ofReal 2 * ENNReal.ofReal (polyP C N ν c * Real.exp (CS / ν - bS * c ^ 2)) :=
          by gcongr
      _ = ENNReal.ofReal (polyP (2 * C) N ν c * Real.exp (CS / ν - bS * c ^ 2)) := by
          rw [← ENNReal.ofReal_mul (by norm_num), hpoly_eq]
  · calc wSupNorm 0 (ageJet ℓ j (fun r z => ν • Train.vecLaplacian (dv r) z) s)
        ≤ ENNReal.ofReal 2 * wSupNorm 0 (ageJet ℓ (j + 2) dv s) := h2
      _ ≤ ENNReal.ofReal 2 * ENNReal.ofReal (polyP C N ν c * Real.exp (CS / ν - bS * c ^ 2)) :=
          by gcongr
      _ = ENNReal.ofReal (polyP (2 * C) N ν c * Real.exp (CS / ν - bS * c ^ 2)) := by
          rw [← ENNReal.ofReal_mul (by norm_num), hpoly_eq]

/-- **Leaf 1 (`PartI:T25/1/1`, `TrainFixedBandQcDivAgeJet`)**:
source lines 326-336, 468-478, 541-551 of `the November 2 reference manuscript`.
Joint smoothness on `(0, ∞) × Plane` of the periodized cross-stress divergence
`(r, z) ↦ Train.matDiv (Train.Qc ν c r) z` (`0 < ν`, `0 < c`), together with the unweighted (`m = 0`)
fixed-band exponential bound for `ageJet ℓ j (fun r z => Train.matDiv (Train.Qc ν c r) z) s` on
`0 < s ≤ Sg / ν` for all `ρ > 1/2`, `Sg > 0`, and `ℓ, j : ℕ`. -/
def TrainFixedBandQcDivAgeJet : Prop :=
  (∀ ν c : ℝ, 0 < ν → 0 < c →
    ContDiffOn ℝ ∞ (fun x : ℝ × Plane => Train.matDiv (Train.Qc ν c x.1) x.2)
      (Ioi 0 ×ˢ univ)) ∧
  (∀ ρ : ℝ, 1 / 2 < ρ → ∀ Sg : ℝ, 0 < Sg → ∀ ℓ j : ℕ,
    ∃ C : ℝ, ∃ N : ℕ, ∃ CS bS ν₀ : ℝ, 0 < C ∧ 0 < bS ∧ 0 < ν₀ ∧
      ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
        ∀ s : ℝ, 0 < s → s ≤ Sg / ν →
          let c := trainPeriod ρ ν
          let qcDiv : ℝ → Plane → Vec := fun r z => Train.matDiv (Train.Qc ν c r) z
          wCellL2 c 0 (ageJet ℓ j qcDiv s) ≤
            ENNReal.ofReal (polyP C N ν c * Real.exp (CS / ν - bS * c ^ 2)) ∧
          wSupNorm 0 (ageJet ℓ j qcDiv s) ≤
            ENNReal.ofReal (polyP C N ν c * Real.exp (CS / ν - bS * c ^ 2)))

/-- **Leaf 2 (`PartI:T25/1/2`, `TrainFixedBandAdvDiffStep`)**:
source lines 326-336, 468-478, 541-551 of `the November 2 reference manuscript`.
Given the unweighted fixed-band velocity bounds `∀ r ≤ ℓ, TrainFixedBandVelOrderUnweighted r` up to
age order `ℓ`, for every `ρ > 1/2`, `Sg > 0`, and `j : ℕ`, the advection difference
`advDiff r z = Train.advection (tr.v r) z - Train.advection (Vc ν c r) z` satisfies the unweighted
(`m = 0`) fixed-band exponential bound at `(ℓ, j)` in `wCellL2 c 0` and `wSupNorm 0`. -/
def TrainFixedBandAdvDiffStep : Prop :=
  ∀ ℓ : ℕ, (∀ r : ℕ, r ≤ ℓ → TrainFixedBandVelOrderUnweighted r) →
    ∀ ρ : ℝ, 1 / 2 < ρ → ∀ Sg : ℝ, 0 < Sg → ∀ j : ℕ,
      ∃ C : ℝ, ∃ N : ℕ, ∃ CS bS ν₀ : ℝ, 0 < C ∧ 0 < bS ∧ 0 < ν₀ ∧
        ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
          ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr →
            ∀ s : ℝ, 0 < s → s ≤ Sg / ν →
              let c := trainPeriod ρ ν
              let advDiff : ℝ → Plane → Vec := fun r z =>
                Train.advection (tr.v r) z - Train.advection (Vc ν c r) z
              wCellL2 c 0 (ageJet ℓ j advDiff s) ≤
                ENNReal.ofReal (polyP C N ν c * Real.exp (CS / ν - bS * c ^ 2)) ∧
              wSupNorm 0 (ageJet ℓ j advDiff s) ≤
                ENNReal.ofReal (polyP C N ν c * Real.exp (CS / ν - bS * c ^ 2))

/-- **Leaf 3 (`PartI:T25/1/3`, `TrainFixedBandPressStep`)**:
source lines 468-478, 543-551 of `the November 2 reference manuscript`.
Given the unweighted fixed-band velocity bounds `∀ r ≤ ℓ, TrainFixedBandVelOrderUnweighted r` up to
age order `ℓ`, for every `ρ > 1/2`, `Sg > 0`, and `j : ℕ`, the pressure gradient difference
`dp r z = Train.gradS (fun w => tr.p r w - pc ν c r w) z` satisfies the unweighted (`m = 0`)
fixed-band exponential bound at `(ℓ, j)` in `wCellL2 c 0` and `wSupNorm 0`. -/
def TrainFixedBandPressStep : Prop :=
  ∀ ℓ : ℕ, (∀ r : ℕ, r ≤ ℓ → TrainFixedBandVelOrderUnweighted r) →
    ∀ ρ : ℝ, 1 / 2 < ρ → ∀ Sg : ℝ, 0 < Sg → ∀ j : ℕ,
      ∃ C : ℝ, ∃ N : ℕ, ∃ CS bS ν₀ : ℝ, 0 < C ∧ 0 < bS ∧ 0 < ν₀ ∧
        ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
          ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr →
            ∀ s : ℝ, 0 < s → s ≤ Sg / ν →
              let c := trainPeriod ρ ν
              let dp : ℝ → Plane → Vec := fun r z =>
                Train.gradS (fun w => tr.p r w - pc ν c r w) z
              wCellL2 c 0 (ageJet ℓ j dp s) ≤
                ENNReal.ofReal (polyP C N ν c * Real.exp (CS / ν - bS * c ^ 2)) ∧
              wSupNorm 0 (ageJet ℓ j dp s) ≤
                ENNReal.ofReal (polyP C N ν c * Real.exp (CS / ν - bS * c ^ 2))

/-- **Higher age-derivative (`ℓ ≥ 1`) unweighted (`m = 0`) fixed-band velocity bound:**
for every `ρ > 1/2`, `Sg > 0`, and `ℓ, j : ℕ`, on `0 < s ≤ Sg / ν`, `ageJet (ℓ + 1) j dv s`
satisfies the unweighted (`m = 0`) exponential fixed-band bound in `wCellL2 c 0` and `wSupNorm 0`. -/
def TrainFixedBandVelHigherAgeUnweighted : Prop :=
  ∀ ρ : ℝ, 1 / 2 < ρ → ∀ Sg : ℝ, 0 < Sg → ∀ ℓ j : ℕ,
    ∃ C : ℝ, ∃ N : ℕ, ∃ CS bS ν₀ : ℝ, 0 < C ∧ 0 < bS ∧ 0 < ν₀ ∧
      ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
        ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr →
          ∀ s : ℝ, 0 < s → s ≤ Sg / ν →
            let c := trainPeriod ρ ν
            let dv : ℝ → Plane → Vec := fun r z => tr.v r z - Vc ν c r z
            wCellL2 c 0 (ageJet (ℓ + 1) j dv s) ≤
              ENNReal.ofReal (polyP C N ν c * Real.exp (CS / ν - bS * c ^ 2)) ∧
            wSupNorm 0 (ageJet (ℓ + 1) j dv s) ≤
              ENNReal.ofReal (polyP C N ν c * Real.exp (CS / ν - bS * c ^ 2))

namespace PartI_T25_1

private theorem polyP_exp_mono {C C' : ℝ} {N N' : ℕ} {CS CS' bS bS' ν c : ℝ}
    (hC : C ≤ C') (hC' : 0 ≤ C') (hN : N ≤ N') (hCS : CS ≤ CS') (hbS : bS' ≤ bS)
    (hν : 0 < ν) (hc : 0 ≤ c) :
    polyP C N ν c * Real.exp (CS / ν - bS * c ^ 2) ≤
      polyP C' N' ν c * Real.exp (CS' / ν - bS' * c ^ 2) := by
  have hX1 : 1 ≤ 1 + c + ν⁻¹ := by
    have : 0 ≤ ν⁻¹ := inv_nonneg.2 hν.le
    linarith
  apply mul_le_mul
  · unfold polyP
    exact mul_le_mul hC (pow_le_pow_right₀ hX1 hN) (by positivity) hC'
  · apply Real.exp_le_exp.2
    have hCS_div : CS / ν ≤ CS' / ν := div_le_div_of_nonneg_right hCS hν.le
    have hb_mul : bS' * c ^ 2 ≤ bS * c ^ 2 := mul_le_mul_of_nonneg_right hbS (sq_nonneg c)
    linarith
  · exact (Real.exp_pos _).le
  · unfold polyP; positivity

private theorem add_four_ofReal_polyP_exp {C₁ C₂ C₃ C₄ : ℝ} {N : ℕ} {CS bS ν c : ℝ}
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hC₃ : 0 ≤ C₃) (hC₄ : 0 ≤ C₄) (hν : 0 < ν) (hc : 0 ≤ c) :
    ENNReal.ofReal (polyP C₁ N ν c * Real.exp (CS / ν - bS * c ^ 2)) +
      ENNReal.ofReal (polyP C₂ N ν c * Real.exp (CS / ν - bS * c ^ 2)) +
      ENNReal.ofReal (polyP C₃ N ν c * Real.exp (CS / ν - bS * c ^ 2)) +
      ENNReal.ofReal (polyP C₄ N ν c * Real.exp (CS / ν - bS * c ^ 2)) =
    ENNReal.ofReal (polyP (C₁ + C₂ + C₃ + C₄) N ν c * Real.exp (CS / ν - bS * c ^ 2)) := by
  have hX : 0 ≤ 1 + c + ν⁻¹ := by
    have : 0 ≤ ν⁻¹ := inv_nonneg.2 hν.le
    linarith
  have h1 : 0 ≤ polyP C₁ N ν c * Real.exp (CS / ν - bS * c ^ 2) := by unfold polyP; positivity
  have h2 : 0 ≤ polyP C₂ N ν c * Real.exp (CS / ν - bS * c ^ 2) := by unfold polyP; positivity
  have h3 : 0 ≤ polyP C₃ N ν c * Real.exp (CS / ν - bS * c ^ 2) := by unfold polyP; positivity
  have h4 : 0 ≤ polyP C₄ N ν c * Real.exp (CS / ν - bS * c ^ 2) := by unfold polyP; positivity
  rw [← ENNReal.ofReal_add h1 h2, ← ENNReal.ofReal_add (add_nonneg h1 h2) h3,
    ← ENNReal.ofReal_add (add_nonneg (add_nonneg h1 h2) h3) h4]
  congr 1
  unfold polyP
  ring

end PartI_T25_1

/-- **Inductive step (`ℓ → ℓ + 1`) for `TrainFixedBandVelOrderUnweighted`**:
combines the proved viscous step (`trainFixedBandViscStep_of_order`), `TrainFixedBandAdvDiffStep`,
`TrainFixedBandPressStep`, and `TrainFixedBandQcDivAgeJet` via `ageJet_succ_dv_eq`. -/
theorem trainFixedBandVelOrderUnweighted_succ
    (hQc : TrainFixedBandQcDivAgeJet)
    (hAdv : TrainFixedBandAdvDiffStep)
    (hPress : TrainFixedBandPressStep)
    (ℓ : ℕ) (hIH : ∀ r : ℕ, r ≤ ℓ → TrainFixedBandVelOrderUnweighted r) :
    TrainFixedBandVelOrderUnweighted (ℓ + 1) := by
  intro ρ hρ Sg hSg j
  obtain ⟨C₁, N₁, CS₁, b₁, ν₁, hC₁, hb₁, hν₁, hVisc⟩ :=
    trainFixedBandViscStep_of_order ℓ (hIH ℓ le_rfl) ρ hρ Sg hSg j
  obtain ⟨C₂, N₂, CS₂, b₂, ν₂, hC₂, hb₂, hν₂, hAdv_bd⟩ := hAdv ℓ hIH ρ hρ Sg hSg j
  obtain ⟨C₃, N₃, CS₃, b₃, ν₃, hC₃, hb₃, hν₃, hPress_bd⟩ := hPress ℓ hIH ρ hρ Sg hSg j
  obtain ⟨C₄, N₄, CS₄, b₄, ν₄, hC₄, hb₄, hν₄, hQc_bd⟩ := hQc.2 ρ hρ Sg hSg ℓ j
  let C_out := C₁ + C₂ + C₃ + C₄
  let N_out := max (max N₁ N₂) (max N₃ N₄)
  let CS_out := max (max CS₁ CS₂) (max CS₃ CS₄)
  let b_out := min (min b₁ b₂) (min b₃ b₄)
  let ν_out := min (min ν₁ ν₂) (min ν₃ ν₄)
  refine ⟨C_out, N_out, CS_out, b_out, ν_out,
    by dsimp [C_out]; positivity,
    lt_min (lt_min hb₁ hb₂) (lt_min hb₃ hb₄),
    lt_min (lt_min hν₁ hν₂) (lt_min hν₃ hν₄), ?_⟩
  intro ν hν hν_le tr htr s hs hs_le
  have hν₁_le : ν ≤ ν₁ := hν_le.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hν₂_le : ν ≤ ν₂ := hν_le.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hν₃_le : ν ≤ ν₃ := hν_le.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hν₄_le : ν ≤ ν₄ := hν_le.trans ((min_le_right _ _).trans (min_le_right _ _))
  let c := trainPeriod ρ ν
  have hc_pos : 0 < c := by
    dsimp [c]
    unfold trainPeriod
    exact Real.rpow_pos_of_pos hν _
  let dv : ℝ → Plane → Vec := fun r z => tr.v r z - Vc ν c r z
  let F₁ : ℝ → Plane → Vec := fun r z => ν • Train.vecLaplacian (dv r) z
  let F₂ : ℝ → Plane → Vec := fun r z => Train.advection (tr.v r) z - Train.advection (Vc ν c r) z
  let F₃ : ℝ → Plane → Vec := fun r z => Train.gradS (fun w => tr.p r w - pc ν c r w) z
  let F₄ : ℝ → Plane → Vec := fun r z => Train.matDiv (Train.Qc ν c r) z
  have hsm_v : Sm (fun x : ℝ × Plane => tr.v x.1 x.2) :=
    tr.isTrain.smooth_v.mono (Set.prod_mono Set.Ioi_subset_Ici_self Subset.rfl)
  have hsm_Vc : Sm (fun x : ℝ × Plane => Vc ν c x.1 x.2) := vcSmooth_proof ν c hν hc_pos
  have hsm_dv : Sm (fun x : ℝ × Plane => dv x.1 x.2) := hsm_v.sub hsm_Vc
  have hsm₁ : Sm (fun x : ℝ × Plane => F₁ x.1 x.2) := PartI_T25_1.sm_smul_vecLaplacian hsm_dv ν
  have hsm₂ : Sm (fun x : ℝ × Plane => F₂ x.1 x.2) :=
    (PartI_T25_1.sm_advection hsm_v).sub (PartI_T25_1.sm_advection hsm_Vc)
  have hsm₄ : Sm (fun x : ℝ × Plane => F₄ x.1 x.2) := hQc.1 ν c hν hc_pos
  have hsm₃ : Sm (fun x : ℝ × Plane => F₃ x.1 x.2) :=
    PartI_T25_1.sm_dp_of_sm_qcDiv tr hν hc_pos hsm₄
  have hsm₁₂ : Sm (fun x : ℝ × Plane => F₁ x.1 x.2 - F₂ x.1 x.2) := hsm₁.sub hsm₂
  have hsm₁₂₃ : Sm (fun x : ℝ × Plane => F₁ x.1 x.2 - F₂ x.1 x.2 - F₃ x.1 x.2) := hsm₁₂.sub hsm₃
  have hjet_eq : ageJet (ℓ + 1) j dv s =
      fun z => ageJet ℓ j F₁ s z - ageJet ℓ j F₂ s z - ageJet ℓ j F₃ s z - ageJet ℓ j F₄ s z := by
    rw [PartI_T25_1.ageJet_succ_dv_eq tr hν hc_pos.ne' ℓ j hs]
    funext z
    have hsub3 := UnforcedLeray.Short.IIb.vb_ageJet_sub
      (fun r w => F₁ r w - F₂ r w - F₃ r w) F₄ hsm₁₂₃ hsm₄ hs ℓ j z
    have hsub2 := UnforcedLeray.Short.IIb.vb_ageJet_sub
      (fun r w => F₁ r w - F₂ r w) F₃ hsm₁₂ hsm₃ hs ℓ j z
    have hsub1 := UnforcedLeray.Short.IIb.vb_ageJet_sub F₁ F₂ hsm₁ hsm₂ hs ℓ j z
    dsimp only [F₁, F₂, F₃, F₄, dv] at hsub3 hsub2 hsub1 ⊢
    rw [hsub3, hsub2, hsub1]
  have hcont₁ := continuous_ageJet_of_contDiffOn F₁ hsm₁ ℓ j hs
  have hcont₂ := continuous_ageJet_of_contDiffOn F₂ hsm₂ ℓ j hs
  have hcont₃ := continuous_ageJet_of_contDiffOn F₃ hsm₃ ℓ j hs
  have hcont₄ := continuous_ageJet_of_contDiffOn F₄ hsm₄ ℓ j hs
  have htri_L2 : wCellL2 c 0 (ageJet (ℓ + 1) j dv s) ≤
      wCellL2 c 0 (ageJet ℓ j F₁ s) + wCellL2 c 0 (ageJet ℓ j F₂ s) +
        wCellL2 c 0 (ageJet ℓ j F₃ s) + wCellL2 c 0 (ageJet ℓ j F₄ s) := by
    rw [hjet_eq]
    exact wCellL2_sub4_le_of_continuous c 0 hcont₁ hcont₂ hcont₃ hcont₄
  have htri_Sup : wSupNorm 0 (ageJet (ℓ + 1) j dv s) ≤
      wSupNorm 0 (ageJet ℓ j F₁ s) + wSupNorm 0 (ageJet ℓ j F₂ s) +
        wSupNorm 0 (ageJet ℓ j F₃ s) + wSupNorm 0 (ageJet ℓ j F₄ s) := by
    rw [hjet_eq]
    exact wSupNorm_sub4_le 0 (ageJet ℓ j F₁ s) (ageJet ℓ j F₂ s) (ageJet ℓ j F₃ s) (ageJet ℓ j F₄ s)
  obtain ⟨hL2_1, hSup_1⟩ := hVisc ν hν hν₁_le tr htr s hs hs_le
  obtain ⟨hL2_2, hSup_2⟩ := hAdv_bd ν hν hν₂_le tr htr s hs hs_le
  obtain ⟨hL2_3, hSup_3⟩ := hPress_bd ν hν hν₃_le tr htr s hs hs_le
  obtain ⟨hL2_4, hSup_4⟩ := hQc_bd ν hν hν₄_le s hs hs_le
  have hm₁ := ENNReal.ofReal_le_ofReal (PartI_T25_1.polyP_exp_mono
    (N' := N_out) (CS' := CS_out) (bS' := b_out) le_rfl hC₁.le
    ((le_max_left N₁ N₂).trans (le_max_left _ _))
    ((le_max_left CS₁ CS₂).trans (le_max_left _ _))
    ((min_le_left _ _).trans (min_le_left _ _)) hν hc_pos.le)
  have hm₂ := ENNReal.ofReal_le_ofReal (PartI_T25_1.polyP_exp_mono
    (N' := N_out) (CS' := CS_out) (bS' := b_out) le_rfl hC₂.le
    ((le_max_right N₁ N₂).trans (le_max_left _ _))
    ((le_max_right CS₁ CS₂).trans (le_max_left _ _))
    ((min_le_left _ _).trans (min_le_right _ _)) hν hc_pos.le)
  have hm₃ := ENNReal.ofReal_le_ofReal (PartI_T25_1.polyP_exp_mono
    (N' := N_out) (CS' := CS_out) (bS' := b_out) le_rfl hC₃.le
    ((le_max_left N₃ N₄).trans (le_max_right _ _))
    ((le_max_left CS₃ CS₄).trans (le_max_right _ _))
    ((min_le_right _ _).trans (min_le_left _ _)) hν hc_pos.le)
  have hm₄ := ENNReal.ofReal_le_ofReal (PartI_T25_1.polyP_exp_mono
    (N' := N_out) (CS' := CS_out) (bS' := b_out) le_rfl hC₄.le
    ((le_max_right N₃ N₄).trans (le_max_right _ _))
    ((le_max_right CS₃ CS₄).trans (le_max_right _ _))
    ((min_le_right _ _).trans (min_le_right _ _)) hν hc_pos.le)
  have hsum_eq := PartI_T25_1.add_four_ofReal_polyP_exp
    (N := N_out) (CS := CS_out) (bS := b_out) hC₁.le hC₂.le hC₃.le hC₄.le hν hc_pos.le
  dsimp only
  refine ⟨?_, ?_⟩
  · calc wCellL2 c 0 (ageJet (ℓ + 1) j dv s)
        ≤ wCellL2 c 0 (ageJet ℓ j F₁ s) + wCellL2 c 0 (ageJet ℓ j F₂ s) +
            wCellL2 c 0 (ageJet ℓ j F₃ s) + wCellL2 c 0 (ageJet ℓ j F₄ s) := htri_L2
      _ ≤ _ := add_le_add (add_le_add (add_le_add (hL2_1.trans hm₁) (hL2_2.trans hm₂))
            (hL2_3.trans hm₃)) (hL2_4.trans hm₄)
      _ = ENNReal.ofReal (polyP C_out N_out ν c * Real.exp (CS_out / ν - b_out * c ^ 2)) := hsum_eq
  · calc wSupNorm 0 (ageJet (ℓ + 1) j dv s)
        ≤ wSupNorm 0 (ageJet ℓ j F₁ s) + wSupNorm 0 (ageJet ℓ j F₂ s) +
            wSupNorm 0 (ageJet ℓ j F₃ s) + wSupNorm 0 (ageJet ℓ j F₄ s) := htri_Sup
      _ ≤ _ := add_le_add (add_le_add (add_le_add (hSup_1.trans hm₁) (hSup_2.trans hm₂))
            (hSup_3.trans hm₃)) (hSup_4.trans hm₄)
      _ = ENNReal.ofReal (polyP C_out N_out ν c * Real.exp (CS_out / ν - b_out * c ^ 2)) := hsum_eq

/-- **All-order unweighted fixed-band velocity bound (`trainFixedBandVelOrderUnweighted_all`)**:
proved by strong induction on `ℓ : ℕ` from `trainFixedBandVelOrderUnweighted_zero` and
`trainFixedBandVelOrderUnweighted_succ`. -/
theorem trainFixedBandVelOrderUnweighted_all
    (hQc : TrainFixedBandQcDivAgeJet)
    (hAdv : TrainFixedBandAdvDiffStep)
    (hPress : TrainFixedBandPressStep) :
    ∀ ℓ : ℕ, TrainFixedBandVelOrderUnweighted ℓ := by
  intro ℓ
  induction ℓ using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => exact trainFixedBandVelOrderUnweighted_zero
    | succ m =>
      exact trainFixedBandVelOrderUnweighted_succ hQc hAdv hPress m
        (fun r hr => ih r (Nat.lt_succ_of_le hr))

/-- **Derivation of `TrainFixedBandVelHigherAgeUnweighted`** from the three forcing leaves. -/
theorem trainFixedBandVelHigherAgeUnweighted_of_leaves
    (hQc : TrainFixedBandQcDivAgeJet)
    (hAdv : TrainFixedBandAdvDiffStep)
    (hPress : TrainFixedBandPressStep) :
    TrainFixedBandVelHigherAgeUnweighted := by
  intro ρ hρ Sg hSg ℓ j
  exact trainFixedBandVelOrderUnweighted_all hQc hAdv hPress (ℓ + 1) ρ hρ Sg hSg j

/-- Conditional assembly of `TrainFixedBandVelAgeJet` from `TrainStreamVelocityPressureTails`
and the higher age-derivative (`ℓ ≥ 1`) unweighted exponential bound. -/
theorem trainFixedBandVelAgeJet_of_higher
    (hTails : TrainStreamVelocityPressureTails)
    (_hFD : TrainFluctuationDecay)
    (hHigher : TrainFixedBandVelHigherAgeUnweighted) :
    TrainFixedBandVelAgeJet := by
  intro ρ hρ Sg hSg m ℓ j
  obtain ⟨C₁, N₁, ν₁, hC₁, hν₁, h2m⟩ := trainFixedBandVelAgeJet_two_mul_m hTails ρ hρ Sg hSg m ℓ j
  cases ℓ with
  | zero =>
    obtain ⟨C₂, bS, ν₂, hC₂, hbS, hν₂, h0⟩ :=
      PartI_T25.trainFixedBand_vel_zero_unweighted ρ hρ Sg hSg j
    refine ⟨max C₁ C₂, max N₁ 1, 0, bS, min ν₁ ν₂,
      lt_max_of_lt_left hC₁, hbS, lt_min hν₁ hν₂, ?_⟩
    intro ν hν hν_le tr htr s hs hs_le
    have hν₁_le : ν ≤ ν₁ := hν_le.trans (min_le_left _ _)
    have hν₂_le : ν ≤ ν₂ := hν_le.trans (min_le_right _ _)
    have hc0 : 0 ≤ trainPeriod ρ ν := by
      unfold trainPeriod
      exact Real.rpow_nonneg hν.le _
    have hX1 : 1 ≤ 1 + trainPeriod ρ ν + ν⁻¹ := by
      have : 0 ≤ ν⁻¹ := inv_nonneg.2 hν.le
      linarith
    have hb_2m := h2m ν hν hν₁_le tr htr s hs hs_le
    obtain ⟨hb_L2, hb_Sup⟩ := h0 ν hν hν₂_le tr htr s hs hs_le
    have hP₁ : polyP C₁ N₁ ν (trainPeriod ρ ν) ≤
        polyP (max C₁ C₂) (max N₁ 1) ν (trainPeriod ρ ν) := by
      unfold polyP
      exact mul_le_mul (le_max_left _ _) (pow_le_pow_right₀ hX1 (le_max_left _ _))
        (by positivity) (by positivity)
    have hP₂ : polyP C₂ 1 ν (trainPeriod ρ ν) * Real.exp (-(bS * (trainPeriod ρ ν) ^ 2)) ≤
        polyP (max C₁ C₂) (max N₁ 1) ν (trainPeriod ρ ν) *
          Real.exp (0 / ν - bS * (trainPeriod ρ ν) ^ 2) := by
      rw [zero_div, zero_sub]
      apply mul_le_mul _ le_rfl (Real.exp_pos _).le (by unfold polyP; positivity)
      unfold polyP
      exact mul_le_mul (le_max_right _ _) (pow_le_pow_right₀ hX1 (le_max_right _ _))
        (by positivity) (by positivity)
    exact ⟨hb_2m.trans (ENNReal.ofReal_le_ofReal hP₁),
      hb_L2.trans (ENNReal.ofReal_le_ofReal hP₂),
      hb_Sup.trans (ENNReal.ofReal_le_ofReal hP₂)⟩
  | succ ℓ =>
    obtain ⟨C₂, N₂, CS, bS, ν₂, hC₂, hbS, hν₂, h0⟩ := hHigher ρ hρ Sg hSg ℓ j
    refine ⟨max C₁ C₂, max N₁ N₂, CS, bS, min ν₁ ν₂,
      lt_max_of_lt_left hC₁, hbS, lt_min hν₁ hν₂, ?_⟩
    intro ν hν hν_le tr htr s hs hs_le
    have hν₁_le : ν ≤ ν₁ := hν_le.trans (min_le_left _ _)
    have hν₂_le : ν ≤ ν₂ := hν_le.trans (min_le_right _ _)
    have hc0 : 0 ≤ trainPeriod ρ ν := by
      unfold trainPeriod
      exact Real.rpow_nonneg hν.le _
    have hX1 : 1 ≤ 1 + trainPeriod ρ ν + ν⁻¹ := by
      have : 0 ≤ ν⁻¹ := inv_nonneg.2 hν.le
      linarith
    have hb_2m := h2m ν hν hν₁_le tr htr s hs hs_le
    obtain ⟨hb_L2, hb_Sup⟩ := h0 ν hν hν₂_le tr htr s hs hs_le
    have hP₁ : polyP C₁ N₁ ν (trainPeriod ρ ν) ≤
        polyP (max C₁ C₂) (max N₁ N₂) ν (trainPeriod ρ ν) := by
      unfold polyP
      exact mul_le_mul (le_max_left _ _) (pow_le_pow_right₀ hX1 (le_max_left _ _))
        (by positivity) (by positivity)
    have hP₂ : polyP C₂ N₂ ν (trainPeriod ρ ν) *
          Real.exp (CS / ν - bS * (trainPeriod ρ ν) ^ 2) ≤
        polyP (max C₁ C₂) (max N₁ N₂) ν (trainPeriod ρ ν) *
          Real.exp (CS / ν - bS * (trainPeriod ρ ν) ^ 2) := by
      apply mul_le_mul _ le_rfl (Real.exp_pos _).le (by unfold polyP; positivity)
      unfold polyP
      exact mul_le_mul (le_max_right _ _) (pow_le_pow_right₀ hX1 (le_max_right _ _))
        (by positivity) (by positivity)
    exact ⟨hb_2m.trans (ENNReal.ofReal_le_ofReal hP₁),
      hb_L2.trans (ENNReal.ofReal_le_ofReal hP₂),
      hb_Sup.trans (ENNReal.ofReal_le_ofReal hP₂)⟩

/-- **Conditional assembly of `TrainFixedBandVelAgeJet` (`PartI:T25/1`)** from
`TrainStreamVelocityPressureTails`, `TrainFluctuationDecay`, and the three non-viscous forcing
leaves `TrainFixedBandQcDivAgeJet` (`PartI:T25/1/1`), `TrainFixedBandAdvDiffStep` (`PartI:T25/1/2`),
and `TrainFixedBandPressStep` (`PartI:T25/1/3`). -/
theorem trainFixedBandVelAgeJet_of_leaves
    (hTails : TrainStreamVelocityPressureTails)
    (hFD : TrainFluctuationDecay)
    (hQc : TrainFixedBandQcDivAgeJet)
    (hAdv : TrainFixedBandAdvDiffStep)
    (hPress : TrainFixedBandPressStep) :
    TrainFixedBandVelAgeJet :=
  trainFixedBandVelAgeJet_of_higher hTails hFD
    (trainFixedBandVelHigherAgeUnweighted_of_leaves hQc hAdv hPress)

end UnforcedLeray.Short.PartI
