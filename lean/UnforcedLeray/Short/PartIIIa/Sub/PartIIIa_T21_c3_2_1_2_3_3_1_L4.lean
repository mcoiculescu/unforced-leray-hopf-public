import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_regime
import UnforcedLeray.Short.PartIIIa.Clock.FrameAmplitudeProof.ComplCoupling.EulerSubBound
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_2_3_3_1_L4.HeatId
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_2_3_3_1_L4.EulerId

/-!
# Part III-a, task `PartIII-a:T21/c3/2/1/2/3/3/1/4`: moving frame leaves in the block regime (`movFrameLeavesRegime`)

Source of record: `the November 2 reference manuscript` (SP), lines 2898-2918
(`eq:short-causal-damped-complement`: `K₀ = G E - ∂_z E ∈ X_{m, d(s)}`, the kernel of `H₀` lies in
`X_{-m, d(s)}`, and `M₀ = H₀ E = Λ K₀`).

Proves the three block-regime moving-frame leaves assembled in `Sub/PartIII-a_T21_c3_2_regime.lean`:
1. `MovDualMemLpRegime κ`: `movingPhi ν (physLamDual κ tr · i) (ageAt ν t₁ σ) ∈ X_{-m, d(s)}`
   from `movLamDualHeatBound`, `movLamDualEulerSubBound`, and `memLp_and_xNorm_perLam0_neg`.
2. `MovH0FrameRegime κ`: `movH0 κ tr (ageAt ν t₁ σ) i (perE κ d k) = movM0 κ P tr (ageAt ν t₁ σ) i k`
   by splitting `movLamDual` into `movLamDualHeat + movEulerAdj` and `movK0` into
   `movOscRes + movL (perE)` and applying `movLamDualHeat_pairing_perE_eq_movOscRes` (`HeatId.lean`)
   and `movEulerAdj_pairing_perE_eq_movL` (`EulerId.lean`).
3. `MovK0MemLpRegime κ`: `movK0 κ P tr (ageAt ν t₁ σ) j ∈ X_{m, d(s)}` from
   `complModeForceOscillator`, `complModeForceEulerError`, and `perE_memLp_cellMeasure`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIIa.MovFrameLeavesSub

open Set MeasureTheory
open UnforcedLeray.Short.IIIa
open FrameShortBlockSub FrameBlockContractSub CompactDuhamelGapSub BlockPropagatorSub

private lemma block_age_and_cellLen {D ν b t₁ t₂ B σ : ℝ} (hD : 0 ≤ D)
    (hν : 0 < ν) (hνD : ν ≤ 1 / (D + 1) ^ 2) (hb1 : 1 ≤ b)
    (ht₁ : 0 ≤ t₁) (ht₁₂ : t₁ ≤ t₂) (hbθ : b ≤ clockTheta ν t₂)
    (hZ : movingZ ν t₂ - movingZ ν t₁ = B) (hσ : σ ∈ Icc (0 : ℝ) B) :
    0 ≤ ageAt ν t₁ σ ∧
    b ≤ clockTheta ν (ageAt ν t₁ σ) ∧
    D ≤ cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ σ)) := by
  have hmem := VariationOfConstantsSub.ageAt_mem_Icc hν ht₁ ht₁₂ hZ hσ
  have hr : 0 ≤ ageAt ν t₁ σ := ht₁.trans hmem.1
  have hθ : b ≤ clockTheta ν (ageAt ν t₁ σ) :=
    hbθ.trans (ComplMildTestedSplit.clockTheta_le_of_le hν hr hmem.2)
  have hd : D ≤ cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ σ)) :=
    cellLen_ge hD hν hνD hb1 hr hθ
  exact ⟨hr, hθ, hd⟩

private lemma memLp_perLam_neg (κ : PlanarFrameKernels) {m d : ℝ} (hm : 8 < m) (hd1 : 1 ≤ d)
    (i : Fin 2) :
    MemLp (perLam κ d i) 2 (B0579.cellMeasure d (-m)) := by
  obtain ⟨_, _, hLam0⟩ := ComplCouplingHeat.memLp_and_xNorm_perLam0_neg κ (m := m) (by linarith)
  have heq : perLam κ d i =
      fun y => (perGram κ d)⁻¹ i 0 * perLam0 κ d 0 y +
        (perGram κ d)⁻¹ i 1 * perLam0 κ d 1 y := by
    funext y; unfold perLam; exact Fin.sum_univ_two _
  rw [heq]
  exact ((hLam0 d hd1 0).1.const_mul _).add ((hLam0 d hd1 1).1.const_mul _)

private theorem movDualMemLpRegime (κ : PlanarFrameKernels) :
    ComplMildTestedSplit.Regime.MovDualMemLpRegime κ := by
  intro hκ _P _hP m hm _K B _hB
  obtain ⟨_, b_h, _, _, hHeatB⟩ := movLamDualHeatBound κ hκ m hm
  obtain ⟨lam, _, b_e, _, _, hEulerB⟩ := _root_.movLamDualEulerSubBound κ hκ m hm
  refine ⟨max b_h b_e, fun b hb hb1 => ?_⟩
  obtain ⟨ν_h, hν_h, hHeat⟩ := hHeatB b ((le_max_left _ _).trans hb)
  obtain ⟨ν_e, hν_e, hEuler⟩ := hEulerB b ((le_max_right _ _).trans hb)
  set ν_D : ℝ := 1 / ((1 : ℝ) + 1) ^ 2
  have hν_D : 0 < ν_D := by positivity
  set ν₀ : ℝ := min (min ν_h ν_e) ν_D
  have hν₀ : 0 < ν₀ := lt_min (lt_min hν_h hν_e) hν_D
  refine ⟨ν₀, hν₀, fun ν hν hν_le _hF tr hBUC t₁ t₂ ht₁ ht₁₂ hbθ hZ σ hσ i => ?_⟩
  have hν_h' : ν ≤ ν_h := hν_le.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hν_e' : ν ≤ ν_e := hν_le.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hν_D' : ν ≤ ν_D := hν_le.trans (min_le_right _ _)
  obtain ⟨hr, hθ, hd1⟩ :=
    block_age_and_cellLen (by norm_num : (0 : ℝ) ≤ 1) hν hν_D' hb1 ht₁ ht₁₂ hbθ hZ hσ
  set r := ageAt ν t₁ σ
  set d := cellLen (ν ^ (-2 : ℝ)) (clockA ν r)
  have hH_mem : MemLp (movLamDualHeat κ ν r i) 2 (B0579.cellMeasure d (-m)) :=
    (hHeat ν ⟨hν, hν_h'⟩ r hr hθ i).1
  have hE_mem : MemLp (movLamDualEulerSub κ lam tr r i) 2 (B0579.cellMeasure d (-m)) :=
    (hEuler ν ⟨hν, hν_e'⟩ tr hBUC r hr hθ i).1
  have hperLam_mem : MemLp (perLam κ d i) 2 (B0579.cellMeasure d (-m)) :=
    memLp_perLam_neg κ hm hd1 i
  have hDual_eq : movLamDual κ tr r i =
      fun y => (movLamDualHeat κ ν r i y + movLamDualEulerSub κ lam tr r i y) +
        seedModeEigen lam i * perLam κ d i y := by
    funext y
    have h1 := ComplCouplingSub.movLamDualSub_eq_add κ lam tr r i y
    unfold movLamDualSub at h1
    exact eq_add_of_sub_eq h1
  have hDual_mem : MemLp (movLamDual κ tr r i) 2 (B0579.cellMeasure d (-m)) := by
    rw [hDual_eq]
    exact (hH_mem.add hE_mem).add (hperLam_mem.const_mul _)
  have ha0 : 0 < clockA ν r := lt_of_lt_of_le zero_lt_one (one_le_clockA hν.le hr)
  have hPhi_eq : movingPhi ν (fun r' => physLamDual κ tr r' i) r =
      fun y => (((clockA ν r) ^ (-2 : ℝ) : ℝ) : ℂ) * movLamDual κ tr r i y := by
    funext y
    unfold movLamDual
    rw [← mul_assoc]
    have ha_inv : (((clockA ν r) ^ (-2 : ℝ) : ℝ) : ℂ) *
        (((clockA ν r) ^ (2 : ℝ) : ℝ) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, ← Real.rpow_add ha0]
      norm_num
    rw [ha_inv, one_mul]
  rw [hPhi_eq]
  exact hDual_mem.const_mul _

private theorem movK0MemLpRegime (κ : PlanarFrameKernels) :
    ComplMildTestedSplit.Regime.MovK0MemLpRegime κ := by
  intro hκ P hP m hm _K B _hB
  obtain ⟨_, b₁, _, _, hOscB⟩ := complModeForceOscillator κ hκ m hm
  obtain ⟨_, b₂, _, _, hEulB⟩ := complModeForceEulerError κ hκ P hP m hm
  obtain ⟨_, _, hperE_all⟩ := DirectHeatDecomp.perE_memLp_cellMeasure κ hm
  refine ⟨max b₁ b₂, fun b hb hb1 => ?_⟩
  obtain ⟨ν₁, hν₁, hOsc⟩ := hOscB b ((le_max_left _ _).trans hb)
  obtain ⟨ν₂, hν₂, hEul⟩ := hEulB b ((le_max_right _ _).trans hb)
  set ν_D : ℝ := 1 / ((1 : ℝ) + 1) ^ 2
  have hν_D : 0 < ν_D := by positivity
  set ν₀ : ℝ := min (min ν₁ ν₂) ν_D
  have hν₀ : 0 < ν₀ := lt_min (lt_min hν₁ hν₂) hν_D
  refine ⟨ν₀, hν₀, fun ν hν hν_le _hF tr hBUC t₁ t₂ ht₁ ht₁₂ hbθ hZ σ hσ j => ?_⟩
  have hν₁' : ν ≤ ν₁ := hν_le.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hν₂' : ν ≤ ν₂ := hν_le.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hν_D' : ν ≤ ν_D := hν_le.trans (min_le_right _ _)
  obtain ⟨hr, hθ, hd1⟩ :=
    block_age_and_cellLen (by norm_num : (0 : ℝ) ≤ 1) hν hν_D' hb1 ht₁ ht₁₂ hbθ hZ hσ
  set r := ageAt ν t₁ σ
  set d := cellLen (ν ^ (-2 : ℝ)) (clockA ν r)
  obtain ⟨hOsc_aesm, hOsc_x⟩ := hOsc ν ⟨hν, hν₁'⟩ r hr hθ j
  obtain ⟨hEul_aesm, hEul_x⟩ := hEul ν ⟨hν, hν₂'⟩ tr hBUC r hr hθ j
  have hOsc_mem : MemLp (movOscRes κ ν r j) 2 (B0579.cellMeasure d m) :=
    ⟨hOsc_aesm, lt_of_le_of_lt hOsc_x ENNReal.ofReal_lt_top⟩
  have hEul_mem : MemLp (movEulerRes κ P tr r j) 2 (B0579.cellMeasure d m) :=
    ⟨hEul_aesm, lt_of_le_of_lt hEul_x ENNReal.ofReal_lt_top⟩
  have hperE_mem : MemLp (perE κ d j) 2 (B0579.cellMeasure d m) := (hperE_all hd1 j).1
  have hK0_eq : movK0 κ P tr r j =
      fun y => (movOscRes κ ν r j y + movEulerRes κ P tr r j y) +
        modeEigen P j * perE κ d j y := rfl
  rw [hK0_eq]
  exact (hOsc_mem.add hEul_mem).add (hperE_mem.const_mul _)

private theorem movH0FrameRegime (κ : PlanarFrameKernels) :
    ComplMildTestedSplit.Regime.MovH0FrameRegime κ := by
  intro hκ P hP m hm _K B _hB
  obtain ⟨_, b_h, _, _, hHeatB⟩ := movLamDualHeatBound κ hκ m hm
  obtain ⟨lam, _, b_e, _, _, hEulerB⟩ := _root_.movLamDualEulerSubBound κ hκ m hm
  obtain ⟨_, b₁, _, _, hOscB⟩ := complModeForceOscillator κ hκ m hm
  obtain ⟨_, b₂, _, _, hEulB⟩ := complModeForceEulerError κ hκ P hP m hm
  obtain ⟨D_H, hDH1, hHeatId⟩ := MovFrameLeavesAux.movLamDualHeat_pairing_perE_eq_movOscRes hκ
  obtain ⟨D_E, hDE1, hEulerId⟩ := MovFrameLeavesAux.movEulerAdj_pairing_perE_eq_movL hκ
  obtain ⟨_, _, hperE_all⟩ := DirectHeatDecomp.perE_memLp_cellMeasure κ hm
  set D : ℝ := max D_H D_E
  have hD1 : 1 ≤ D := hDH1.trans (le_max_left _ _)
  have hD0 : 0 ≤ D := zero_le_one.trans hD1
  set b₀ : ℝ := max (max b_h b_e) (max b₁ b₂)
  refine ⟨b₀, fun b hb hb1 => ?_⟩
  obtain ⟨ν_h, hν_h, hHeat⟩ := hHeatB b (((le_max_left _ _).trans (le_max_left _ _)).trans hb)
  obtain ⟨ν_e, hν_e, hEuler⟩ := hEulerB b (((le_max_right _ _).trans (le_max_left _ _)).trans hb)
  obtain ⟨ν₁, hν₁, hOsc⟩ := hOscB b (((le_max_left _ _).trans (le_max_right _ _)).trans hb)
  obtain ⟨ν₂, hν₂, hEul⟩ := hEulB b (((le_max_right _ _).trans (le_max_right _ _)).trans hb)
  set ν_D : ℝ := 1 / (D + 1) ^ 2
  have hν_D : 0 < ν_D := by positivity
  set ν₀ : ℝ := min (min (min ν_h ν_e) (min ν₁ ν₂)) (min 1 ν_D)
  have hν₀ : 0 < ν₀ := lt_min (lt_min (lt_min hν_h hν_e) (lt_min hν₁ hν₂)) (lt_min zero_lt_one hν_D)
  refine ⟨ν₀, hν₀, fun ν hν hν_le _hF tr hBUC t₁ t₂ ht₁ ht₁₂ hbθ hZ σ hσ i k => ?_⟩
  have hν_left := hν_le.trans (min_le_left _ _)
  have hν_right := hν_le.trans (min_le_right _ _)
  have hν_h' : ν ≤ ν_h := hν_left.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hν_e' : ν ≤ ν_e := hν_left.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hν₁' : ν ≤ ν₁ := hν_left.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hν₂' : ν ≤ ν₂ := hν_left.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hν1 : ν ≤ 1 := hν_right.trans (min_le_left _ _)
  have hν_D' : ν ≤ ν_D := hν_right.trans (min_le_right _ _)
  obtain ⟨hr, hθ, hd_D⟩ := block_age_and_cellLen hD0 hν hν_D' hb1 ht₁ ht₁₂ hbθ hZ hσ
  set r := ageAt ν t₁ σ
  set d := cellLen (ν ^ (-2 : ℝ)) (clockA ν r)
  have hd_DH : D_H ≤ d := (le_max_left _ _).trans hd_D
  have hd_DE : D_E ≤ d := (le_max_right _ _).trans hd_D
  have hd1 : 1 ≤ d := hD1.trans hd_D
  -- `MemLp` memberships in `X_{-m, d}` and `X_{m, d}` for the 4 integrands
  have hHeat_mem : MemLp (movLamDualHeat κ ν r i) 2 (B0579.cellMeasure d (-m)) :=
    (hHeat ν ⟨hν, hν_h'⟩ r hr hθ i).1
  have hEsub_mem : MemLp (movLamDualEulerSub κ lam tr r i) 2 (B0579.cellMeasure d (-m)) :=
    (hEuler ν ⟨hν, hν_e'⟩ tr hBUC r hr hθ i).1
  have hperLam_mem : MemLp (perLam κ d i) 2 (B0579.cellMeasure d (-m)) :=
    memLp_perLam_neg κ hm hd1 i
  have hEulerAdj_eq :
      ComplCouplingEuler.movEulerAdj d (movingTrainV tr r) (movingTrainE tr r) (perLam κ d i) =
        fun y => movLamDualEulerSub κ lam tr r i y + seedModeEigen lam i * perLam κ d i y := by
    funext y
    exact eq_add_of_sub_eq
      (ComplCouplingEuler.movLamDualEulerSub_eq_movEulerAdj_sub κ lam tr hν hr i y).symm
  have hEulerAdj_mem :
      MemLp (ComplCouplingEuler.movEulerAdj d (movingTrainV tr r) (movingTrainE tr r)
        (perLam κ d i)) 2 (B0579.cellMeasure d (-m)) := by
    rw [hEulerAdj_eq]
    exact hEsub_mem.add (hperLam_mem.const_mul _)
  have hperE_mem : MemLp (perE κ d k) 2 (B0579.cellMeasure d m) := (hperE_all hd1 k).1
  obtain ⟨hOsc_aesm, hOsc_x⟩ := hOsc ν ⟨hν, hν₁'⟩ r hr hθ k
  have hOsc_mem : MemLp (movOscRes κ ν r k) 2 (B0579.cellMeasure d m) :=
    ⟨hOsc_aesm, lt_of_le_of_lt hOsc_x ENNReal.ofReal_lt_top⟩
  obtain ⟨hEul_aesm, hEul_x⟩ := hEul ν ⟨hν, hν₂'⟩ tr hBUC r hr hθ k
  have hEul_mem : MemLp (movEulerRes κ P tr r k) 2 (B0579.cellMeasure d m) :=
    ⟨hEul_aesm, lt_of_le_of_lt hEul_x ENNReal.ofReal_lt_top⟩
  have hmovL_eq : movL tr r (perE κ d k) =
      fun y => movEulerRes κ P tr r k y + modeEigen P k * perE κ d k y := by
    funext y
    unfold movEulerRes
    dsimp only [d]
    ring
  have hmovL_mem : MemLp (movL tr r (perE κ d k)) 2 (B0579.cellMeasure d m) := by
    rw [hmovL_eq]
    exact hEul_mem.add (hperE_mem.const_mul _)
  -- `IntegrableOn` on `B0579.cell d` via Cauchy-Schwarz (`CutLimitAux.integrable_complex`)
  have hInt_H : IntegrableOn (fun y => movLamDualHeat κ ν r i y * perE κ d k y) (B0579.cell d) :=
    (CutLimitAux.integrable_complex hperE_mem hHeat_mem).congr (ae_of_all _ fun _ => mul_comm _ _)
  have hInt_E : IntegrableOn
      (fun y => ComplCouplingEuler.movEulerAdj d (movingTrainV tr r) (movingTrainE tr r)
        (perLam κ d i) y * perE κ d k y) (B0579.cell d) :=
    (CutLimitAux.integrable_complex hperE_mem hEulerAdj_mem).congr
      (ae_of_all _ fun _ => mul_comm _ _)
  have hInt_O : IntegrableOn (fun y => perLam κ d i y * movOscRes κ ν r k y) (B0579.cell d) :=
    (CutLimitAux.integrable_complex hOsc_mem hperLam_mem).congr (ae_of_all _ fun _ => mul_comm _ _)
  have hInt_L : IntegrableOn (fun y => perLam κ d i y * movL tr r (perE κ d k) y) (B0579.cell d) :=
    (CutLimitAux.integrable_complex hmovL_mem hperLam_mem).congr
      (ae_of_all _ fun _ => mul_comm _ _)
  -- Split LHS (`movH0`) and RHS (`movM0`) into Heat/Oscillator + Euler parts
  have hcell : movingCell ν (ν ^ (-2 : ℝ)) r = B0579.cell d := rfl
  have hlhs_split :
      movH0 κ tr r i (perE κ d k) =
        (∫ y in B0579.cell d, movLamDualHeat κ ν r i y * perE κ d k y) +
        (∫ y in B0579.cell d,
          ComplCouplingEuler.movEulerAdj d (movingTrainV tr r) (movingTrainE tr r)
            (perLam κ d i) y * perE κ d k y) := by
    rw [ComplCouplingSub.movH0_eq_integral_movLamDual, hcell]
    have hcongr : (fun y => movLamDual κ tr r i y * perE κ d k y) =
        fun y => movLamDualHeat κ ν r i y * perE κ d k y +
          ComplCouplingEuler.movEulerAdj d (movingTrainV tr r) (movingTrainE tr r)
            (perLam κ d i) y * perE κ d k y := by
      funext y
      rw [ComplCouplingSub.movLamDual_eq_heat_add_euler κ tr r i y,
        ComplCouplingEuler.movPullback_physLamDualEuler_eq κ tr hν hr i y, add_mul]
    rw [hcongr,
      integral_add (f := fun y => movLamDualHeat κ ν r i y * perE κ d k y)
        (g := fun y => ComplCouplingEuler.movEulerAdj d (movingTrainV tr r) (movingTrainE tr r)
          (perLam κ d i) y * perE κ d k y) hInt_H hInt_E]
  have hrhs_split :
      movM0 κ P tr r i k =
        (∫ y in B0579.cell d, perLam κ d i y * movOscRes κ ν r k y) +
        (∫ y in B0579.cell d, perLam κ d i y * movL tr r (perE κ d k) y) := by
    unfold movM0 movLamPair
    rw [hcell]
    have hcongr : (fun y => perLam κ d i y * movK0 κ P tr r k y) =
        fun y => perLam κ d i y * movOscRes κ ν r k y +
          perLam κ d i y * movL tr r (perE κ d k) y := by
      funext y
      unfold movK0 movEulerRes
      dsimp only [d]
      ring
    rw [hcongr,
      integral_add (f := fun y => perLam κ d i y * movOscRes κ ν r k y)
        (g := fun y => perLam κ d i y * movL tr r (perE κ d k) y) hInt_O hInt_L]
  rw [hlhs_split, hrhs_split,
    hHeatId hν hr hm hd_DH i k hOsc_mem,
    hEulerId ⟨hν, hν1⟩ tr hBUC hr hd_DE i k]

end UnforcedLeray.Short.IIIa.MovFrameLeavesSub

theorem movFrameLeavesRegime (κ : UnforcedLeray.Short.IIIa.PlanarFrameKernels) :
    UnforcedLeray.Short.IIIa.ComplMildTestedSplit.Regime.MovDualMemLpRegime κ ∧
      UnforcedLeray.Short.IIIa.ComplMildTestedSplit.Regime.MovH0FrameRegime κ ∧
      UnforcedLeray.Short.IIIa.ComplMildTestedSplit.Regime.MovK0MemLpRegime κ :=
  ⟨UnforcedLeray.Short.IIIa.MovFrameLeavesSub.movDualMemLpRegime κ,
    UnforcedLeray.Short.IIIa.MovFrameLeavesSub.movH0FrameRegime κ,
    UnforcedLeray.Short.IIIa.MovFrameLeavesSub.movK0MemLpRegime κ⟩
