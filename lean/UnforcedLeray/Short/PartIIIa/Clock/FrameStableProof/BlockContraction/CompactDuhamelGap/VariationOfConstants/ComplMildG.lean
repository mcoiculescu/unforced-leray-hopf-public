import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_2_3
import UnforcedLeray.Short.PartIIIa.Clock.FrameStableProof.BlockContraction.CompactDuhamelGap.VariationOfConstants.ComplMildG.Bound
import UnforcedLeray.Short.PartIIIa.Clock.FrameStableProof.BlockContraction.CompactDuhamelGap.VariationOfConstants.ComplMildG.Meas
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_3_1_1_org.Leaf4.Force

/-!
# `PartIII-a:T21/c3/2/1/2/3/2`: Leaf C2 `ComplGExists`

Source of record: `the November 2 reference manuscript` (SP), lines 2914-2925
(the mode forcing `G(σ) = N(t₁, s(σ))⁻¹ I_{s(σ)} Σ_j α_j (1 - EΛ) K_{0,j}` of the damped
complement equation `eq:short-causal-damped-complement`).

Construction.  Put `s(σ) = ageAt ν t₁ σ`, clamped to `[t₁, t₂]`, and
`G(σ) = [N(t₁, s)⁻¹ I_{d(s)} Σ_j α_j(s) complModeForce_j(s)] ∈ L²_m`.

* For `r ∈ [t₁, t₂]` the residuals `Ψ_j(r) = movOscRes + movEulerRes` are bounded in
  `X_{m,d(r)}` uniformly (`ComplMildGAux.psi_block_xNorm`: Gaussian profiles, bounded BUC train
  coefficients, exponential decay of the kernel velocity of the zero-mean modes); the frame
  projection is bounded (`xNorm_frameProj_le`), the amplitudes and the normaliser are continuous
  on the compact block.  Hence `‖G(σ)‖` is bounded.
* `(σ, z) ↦ G(σ)(z)` is jointly measurable (`Leaf4Aux.measurable_force_joint`), so `G` is strongly
  measurable (`ComplMildGAux.stronglyMeasurable_toL2w`), hence integrable on `[0, B]`.
* The forcings are measurable on each cell (joint measurability at fixed age).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Metric UnforcedLeray.Blueprint.Planar
open scoped ENNReal ComplexConjugate ContDiff InnerProductSpace

namespace UnforcedLeray.Short.IIIa

open FrameShortBlockSub FrameBlockContractSub CompactDuhamelGapSub BlockPropagatorSub
  VariationOfConstantsSub VariationOfConstantsMildSub ComplMildYAux ComplMildGAux EulerErrorSub

namespace ComplMildGAux

/-- Triangle inequality for a two-term combination in `X_{m,d}`. -/
theorem xNorm_sum_two_le {d m : ℝ} (a : Fin 2 → ℂ) (f : Fin 2 → ℝ × ℝ → ℂ)
    (hf : ∀ j, AEStronglyMeasurable (f j) (B0579.cellMeasure d m)) :
    xNorm d m (fun y => ∑ j : Fin 2, a j * f j y) ≤ ∑ j : Fin 2, ‖a j‖ₑ * xNorm d m (f j) := by
  unfold xNorm
  simp only [Fin.sum_univ_two]
  have h1 : eLpNorm (fun y => a 0 * f 0 y) 2 (B0579.cellMeasure d m) =
      ‖a 0‖ₑ * eLpNorm (f 0) 2 (B0579.cellMeasure d m) := eLpNorm_const_smul (a 0) (f 0) _ _
  have h2 : eLpNorm (fun y => a 1 * f 1 y) 2 (B0579.cellMeasure d m) =
      ‖a 1‖ₑ * eLpNorm (f 1) 2 (B0579.cellMeasure d m) := eLpNorm_const_smul (a 1) (f 1) _ _
  calc eLpNorm (fun y => a 0 * f 0 y + a 1 * f 1 y) 2 (B0579.cellMeasure d m)
      ≤ eLpNorm (fun y => a 0 * f 0 y) 2 (B0579.cellMeasure d m) +
          eLpNorm (fun y => a 1 * f 1 y) 2 (B0579.cellMeasure d m) :=
        eLpNorm_add_le ((hf 0).const_mul _) ((hf 1).const_mul _) (by norm_num)
    _ = _ := by rw [h1, h2]

end ComplMildGAux

/-- **Leaf C2 (`ComplGExists`, SP 2914-2925)**: the mode forcing `G` of the damped moving
complement equation exists in `L²_m`, is integrable on the block, and the forcings are a.e.
strongly measurable on the moving cells. -/
theorem complGExists (κ : UnforcedLeray.Short.IIIa.PlanarFrameKernels) :
    UnforcedLeray.Short.IIIa.ComplMildSplit.ComplGExists κ := by
  intro hκ P _hP m hm K B b hB hb ν hν hF tr htr t₁ t₂ ht₁ h12 hbt hBe f w u hw _hcirc
  have hm0 : (0 : ℝ) ≤ m := by linarith
  have hbr : ∀ r ∈ Icc t₁ t₂, b ≤ clockTheta ν r := fun r hr =>
    hbt.trans (theta_anti hν (ht₁.trans hr.1) hr.2)
  have hθ1 : ∀ r ∈ Icc t₁ t₂, 1 ≤ clockTheta ν r := fun r hr => hb.trans (hbr r hr)
  have hd1 : ∀ r ∈ Icc t₁ t₂, 1 ≤ cellLen (ν ^ (-2 : ℝ)) (clockA ν r) := fun r hr =>
    cellLen_one_le_of_theta hν (ht₁.trans hr.1) hb (hbr r hr)
  have hdet : ∀ r ∈ Icc t₁ t₂,
      (perGram κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r))).det ≠ 0 := by
    intro r hr hdz
    have h1 := hF.1 r (ht₁.trans hr.1) (hbr r hr) 0 0
    have hinv : (perGram κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)))⁻¹ = 0 :=
      Matrix.nonsing_inv_apply_not_isUnit _ (by rw [isUnit_iff_ne_zero]; exact not_not.2 hdz)
    have h0 : ∀ x, perLam κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) 0 x = 0 := by
      intro x
      unfold perLam
      rw [hinv]
      simp
    simp only [h0, zero_mul, integral_zero, ite_true] at h1
    exact zero_ne_one h1
  -- joint measurability of the forcings and of the oscillator residuals
  have hforce := fun j => ComplFreeRateSub.Leaf4Aux.measurable_force_joint hκ hν ht₁ h12 hd1 P
    hF hdet tr j
  have hcmfm : ∀ r ∈ Icc t₁ t₂, ∀ j : Fin 2,
      Measurable (complModeForce κ P (periodizedFrame κ ν m b K hν hF) tr r j) := by
    intro r hr j
    have h := (hforce j).comp
      (measurable_const.prodMk measurable_id : Measurable (fun y : ℝ × ℝ => (r, y)))
    simpa only [Function.comp_def, ComplFreeRateSub.Leaf4Aux.rho_eq hr] using h
  have hoscm : ∀ r ∈ Icc t₁ t₂, ∀ j : Fin 2, Measurable (movOscRes κ ν r j) := by
    intro r hr j
    have h := (ComplFreeRateSub.Leaf4Aux.measurable_movOscRes_joint hκ hν ht₁ h12 hd1 j).comp
      (measurable_const.prodMk measurable_id : Measurable (fun y : ℝ × ℝ => (r, y)))
    simpa only [Function.comp_def, ComplFreeRateSub.Leaf4Aux.rho_eq hr] using h
  -- uniform bound of the forcings on the block
  obtain ⟨C_Ψ, hCΨ0, hCΨ⟩ := psi_block_xNorm hκ P hν tr htr ht₁ h12 hd1 hθ1 hm0
  set C_F : ℝ := (1 + 2 * max K 0 ^ 2) * C_Ψ with hC_F
  have hCF0 : 0 ≤ C_F := by positivity
  have hCF : ∀ r ∈ Icc t₁ t₂, ∀ j : Fin 2,
      xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m
        (complModeForce κ P (periodizedFrame κ ν m b K hν hF) tr r j) ≤ ENNReal.ofReal C_F := by
    intro r hr j
    have hr0 : 0 ≤ r := ht₁.trans hr.1
    have hΨm : AEStronglyMeasurable (fun y => movOscRes κ ν r j y + movEulerRes κ P tr r j y)
        (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m) :=
      (hoscm r hr j).aestronglyMeasurable.add (aesm_movEulerRes hκ P hν tr hr0 m j)
    have hproj := xNorm_frameProj_le (periodizedFrame κ ν m b K hν hF) hr0 (hbr r hr) hΨm
    calc xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m
          (complModeForce κ P (periodizedFrame κ ν m b K hν hF) tr r j)
        ≤ ENNReal.ofReal (1 + 2 * max K 0 ^ 2) *
            xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m
              (fun y => movOscRes κ ν r j y + movEulerRes κ P tr r j y) := hproj
      _ ≤ ENNReal.ofReal (1 + 2 * max K 0 ^ 2) * ENNReal.ofReal C_Ψ := by
          gcongr
          exact hCΨ r hr j
      _ = ENNReal.ofReal C_F := by
          rw [hC_F, ENNReal.ofReal_mul (by positivity)]
  -- amplitudes and normaliser on the block
  have hA : ∀ i : Fin 2, ContinuousOn (fun r => ampl (periodizedFrame κ ν m b K hν hF) w r i)
      (Icc t₁ t₂) := fun i =>
    continuousOn_ampl_age κ hm hν ht₁ h12 hbt hF hd1 hw i
  obtain ⟨C_A0, hCA0⟩ := isCompact_Icc.exists_bound_of_continuousOn (hA 0)
  obtain ⟨C_A1, hCA1⟩ := isCompact_Icc.exists_bound_of_continuousOn (hA 1)
  set C_A : ℝ := max (max C_A0 C_A1) 0 with hC_A
  have hCA0' : 0 ≤ C_A := le_max_right _ _
  have hCA : ∀ r ∈ Icc t₁ t₂, ∀ j : Fin 2,
      ‖ampl (periodizedFrame κ ν m b K hν hF) w r j‖ ≤ C_A := by
    intro r hr j
    fin_cases j
    · exact (hCA0 r hr).trans ((le_max_left _ _).trans (le_max_left _ _))
    · exact (hCA1 r hr).trans ((le_max_right _ _).trans (le_max_left _ _))
  have hN_pos : ∀ r, 0 ≤ r → 0 < clockN P ν t₁ r := fun r hr => by
    unfold clockN
    exact mul_pos (Real.exp_pos _)
      (Real.rpow_pos_of_pos (div_pos (theta_pos hν ht₁) (theta_pos hν hr)) _)
  have hNinv : ContinuousOn (fun r => (((clockN P ν t₁ r : ℝ) : ℂ))⁻¹) (Icc t₁ t₂) := by
    intro r hr
    have hr0 : 0 ≤ r := ht₁.trans hr.1
    have hcont : ContinuousAt (fun r => ((clockN P ν t₁ r : ℝ) : ℂ)) r :=
      Complex.continuous_ofReal.continuousAt.comp
        (hasDerivAt_clockN_movBeta0 P hν ht₁ hr0).continuousAt
    exact (hcont.inv₀ (by exact_mod_cast (hN_pos r hr0).ne')).continuousWithinAt
  obtain ⟨C_N', hCN'⟩ := isCompact_Icc.exists_bound_of_continuousOn hNinv
  set C_N : ℝ := max C_N' 0 with hC_N
  have hCN0 : 0 ≤ C_N := le_max_right _ _
  have hCN : ∀ r ∈ Icc t₁ t₂, ‖(((clockN P ν t₁ r : ℝ) : ℂ))⁻¹‖ ≤ C_N := fun r hr =>
    (hCN' r hr).trans (le_max_left _ _)
  -- the combination on the block
  have hVaesm : ∀ r ∈ Icc t₁ t₂, AEStronglyMeasurable
      (fun y => ∑ j : Fin 2, ampl (periodizedFrame κ ν m b K hν hF) w r j *
        complModeForce κ P (periodizedFrame κ ν m b K hν hF) tr r j y)
      (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m) := by
    intro r hr
    exact (Finset.measurable_sum _ (fun j _ =>
      measurable_const.mul (hcmfm r hr j))).aestronglyMeasurable
  have hVb : ∀ r ∈ Icc t₁ t₂, xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m
      (fun y => ∑ j : Fin 2, ampl (periodizedFrame κ ν m b K hν hF) w r j *
        complModeForce κ P (periodizedFrame κ ν m b K hν hF) tr r j y) ≤
        ENNReal.ofReal (2 * (C_A * C_F)) := by
    intro r hr
    calc xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m
          (fun y => ∑ j : Fin 2, ampl (periodizedFrame κ ν m b K hν hF) w r j *
            complModeForce κ P (periodizedFrame κ ν m b K hν hF) tr r j y)
        ≤ ∑ j : Fin 2, ‖ampl (periodizedFrame κ ν m b K hν hF) w r j‖ₑ *
            xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m
              (complModeForce κ P (periodizedFrame κ ν m b K hν hF) tr r j) :=
          xNorm_sum_two_le _ _ (fun j => (hcmfm r hr j).aestronglyMeasurable)
      _ ≤ ∑ _j : Fin 2, ENNReal.ofReal C_A * ENNReal.ofReal C_F := by
          gcongr with j
          · rw [← ofReal_norm]
            exact ENNReal.ofReal_le_ofReal (hCA r hr j)
          · exact hCF r hr j
      _ = ENNReal.ofReal (2 * (C_A * C_F)) := by
          rw [Fin.sum_univ_two, ← ENNReal.ofReal_mul hCA0',
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1
          ring
  have hVmem : ∀ r ∈ Icc t₁ t₂, MemLp
      (fun y => ∑ j : Fin 2, ampl (periodizedFrame κ ν m b K hν hF) w r j *
        complModeForce κ P (periodizedFrame κ ν m b K hν hF) tr r j y) 2
      (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m) := fun r hr =>
    ⟨hVaesm r hr, (hVb r hr).trans_lt ENNReal.ofReal_lt_top⟩
  -- the clamped age and the representative
  have hage : Measurable (ageAt ν t₁) := by
    unfold ageAt FrameStableSub.moveAgeOfZ
    exact (measurable_const.add measurable_id).div
      (measurable_const.sub (measurable_const.mul (measurable_const.add measurable_id)))
  have hρmem : ∀ σ, ComplFreeRateSub.Leaf4Aux.rho t₁ t₂ (ageAt ν t₁ σ) ∈ Icc t₁ t₂ := fun σ =>
    ComplFreeRateSub.Leaf4Aux.rho_mem h12 _
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : ℝ → ℂ → ℂ, Φ = fun σ z =>
      ((clockN P ν t₁ (ComplFreeRateSub.Leaf4Aux.rho t₁ t₂ (ageAt ν t₁ σ)) : ℝ) : ℂ)⁻¹ *
        cellZeroExt (cellLen (ν ^ (-2 : ℝ))
            (clockA ν (ComplFreeRateSub.Leaf4Aux.rho t₁ t₂ (ageAt ν t₁ σ))))
          (fun y => ∑ j : Fin 2, ampl (periodizedFrame κ ν m b K hν hF) w
              (ComplFreeRateSub.Leaf4Aux.rho t₁ t₂ (ageAt ν t₁ σ)) j *
            complModeForce κ P (periodizedFrame κ ν m b K hν hF) tr
              (ComplFreeRateSub.Leaf4Aux.rho t₁ t₂ (ageAt ν t₁ σ)) j y) (cToPlane z) :=
    ⟨_, rfl⟩
  have hΦmem : ∀ σ, MemLp (Φ σ) 2 (Planar.wMeasure m) := by
    intro σ
    rw [hΦ]
    exact (memLp_cellZeroExt_cToPlane _ m (hVmem _ (hρmem σ))).const_mul _
  have hΦnorm : ∀ σ, eLpNorm (Φ σ) 2 (Planar.wMeasure m) ≤
      ENNReal.ofReal (C_N * (2 * (C_A * C_F))) := by
    intro σ
    set r := ComplFreeRateSub.Leaf4Aux.rho t₁ t₂ (ageAt ν t₁ σ) with hr_def
    have hr : r ∈ Icc t₁ t₂ := hρmem σ
    have heq : Φ σ = (((clockN P ν t₁ r : ℝ) : ℂ))⁻¹ • fun z : ℂ =>
        cellZeroExt (cellLen (ν ^ (-2 : ℝ)) (clockA ν r))
          (fun y => ∑ j : Fin 2, ampl (periodizedFrame κ ν m b K hν hF) w r j *
            complModeForce κ P (periodizedFrame κ ν m b K hν hF) tr r j y) (cToPlane z) := by
      rw [hΦ]
      rfl
    rw [heq, eLpNorm_const_smul, eLpNorm_cellZeroExt_cToPlane _ m (hVaesm r hr),
      ENNReal.ofReal_mul hCN0]
    gcongr
    · rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (hCN r hr)
    · exact hVb r hr
  -- joint measurability of the representative
  have hΦmeas : Measurable (fun p : ℝ × ℂ => Φ p.1 p.2) := by
    have hN : Continuous (fun r => (((clockN P ν t₁ (ComplFreeRateSub.Leaf4Aux.rho t₁ t₂ r) :
        ℝ) : ℂ))⁻¹) :=
      hNinv.comp_continuous (ComplFreeRateSub.Leaf4Aux.continuous_rho t₁ t₂)
        (fun r => ComplFreeRateSub.Leaf4Aux.rho_mem h12 r)
    have hAc : ∀ j : Fin 2, Continuous (fun r => ampl (periodizedFrame κ ν m b K hν hF) w
        (ComplFreeRateSub.Leaf4Aux.rho t₁ t₂ r) j) := fun j =>
      (hA j).comp_continuous (ComplFreeRateSub.Leaf4Aux.continuous_rho t₁ t₂)
        (fun r => ComplFreeRateSub.Leaf4Aux.rho_mem h12 r)
    have hD : Continuous (fun r => cellLen (ν ^ (-2 : ℝ))
        (clockA ν (ComplFreeRateSub.Leaf4Aux.rho t₁ t₂ r))) :=
      ComplFreeRateSub.Leaf4Aux.continuous_dRho hν ht₁
    have hDm : Measurable (fun p : ℝ × ℂ => cellLen (ν ^ (-2 : ℝ))
        (clockA ν (ComplFreeRateSub.Leaf4Aux.rho t₁ t₂ (ageAt ν t₁ p.1)))) :=
      (hD.measurable.comp hage).comp measurable_fst
    have hre : Measurable (fun p : ℝ × ℂ => p.2.re) :=
      Complex.measurable_re.comp measurable_snd
    set S : Set (ℝ × ℂ) := {p : ℝ × ℂ | cToPlane p.2 ∈ B0579.cell (cellLen (ν ^ (-2 : ℝ))
        (clockA ν (ComplFreeRateSub.Leaf4Aux.rho t₁ t₂ (ageAt ν t₁ p.1))))} with hS
    have hset : MeasurableSet S := by
      have : S = {p | -(cellLen (ν ^ (-2 : ℝ))
            (clockA ν (ComplFreeRateSub.Leaf4Aux.rho t₁ t₂ (ageAt ν t₁ p.1))) / 2) ≤ p.2.re} ∩
          {p | p.2.re < cellLen (ν ^ (-2 : ℝ))
            (clockA ν (ComplFreeRateSub.Leaf4Aux.rho t₁ t₂ (ageAt ν t₁ p.1))) / 2} := by
        ext p
        simp [hS, B0579.cell, cToPlane, Set.mem_prod]
      rw [this]
      exact (measurableSet_le (hDm.div_const 2).neg hre).inter
        (measurableSet_lt hre (hDm.div_const 2))
    have hsum : Measurable (fun p : ℝ × ℂ => ∑ j : Fin 2,
        ampl (periodizedFrame κ ν m b K hν hF) w
            (ComplFreeRateSub.Leaf4Aux.rho t₁ t₂ (ageAt ν t₁ p.1)) j *
          complModeForce κ P (periodizedFrame κ ν m b K hν hF) tr
            (ComplFreeRateSub.Leaf4Aux.rho t₁ t₂ (ageAt ν t₁ p.1)) j (cToPlane p.2)) := by
      refine Finset.measurable_sum _ (fun j _ => ?_)
      have h1 : Measurable (fun p : ℝ × ℂ => ampl (periodizedFrame κ ν m b K hν hF) w
          (ComplFreeRateSub.Leaf4Aux.rho t₁ t₂ (ageAt ν t₁ p.1)) j) :=
        ((hAc j).measurable.comp hage).comp measurable_fst
      have hpair : Measurable (fun p : ℝ × ℂ => (ageAt ν t₁ p.1, cToPlane p.2)) :=
        (hage.comp measurable_fst).prodMk (measurable_cToPlane.comp measurable_snd)
      have h2 := (hforce j).comp hpair
      exact h1.mul h2
    have hNm : Measurable (fun p : ℝ × ℂ => (((clockN P ν t₁
        (ComplFreeRateSub.Leaf4Aux.rho t₁ t₂ (ageAt ν t₁ p.1)) : ℝ) : ℂ))⁻¹) :=
      (hN.measurable.comp hage).comp measurable_fst
    have hfun : (fun p : ℝ × ℂ => Φ p.1 p.2) = fun p : ℝ × ℂ =>
        (((clockN P ν t₁ (ComplFreeRateSub.Leaf4Aux.rho t₁ t₂ (ageAt ν t₁ p.1)) : ℝ) : ℂ))⁻¹ *
          S.indicator (fun p : ℝ × ℂ => ∑ j : Fin 2,
            ampl (periodizedFrame κ ν m b K hν hF) w
                (ComplFreeRateSub.Leaf4Aux.rho t₁ t₂ (ageAt ν t₁ p.1)) j *
              complModeForce κ P (periodizedFrame κ ν m b K hν hF) tr
                (ComplFreeRateSub.Leaf4Aux.rho t₁ t₂ (ageAt ν t₁ p.1)) j (cToPlane p.2)) p := by
      funext p
      rw [hΦ]
      dsimp only
      unfold cellZeroExt
      by_cases h : p ∈ S
      · rw [Set.indicator_of_mem h, Set.indicator_of_mem (show cToPlane p.2 ∈ _ from h)]
      · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (show cToPlane p.2 ∉ _ from h)]
    rw [hfun]
    exact hNm.mul (hsum.indicator hset)
  -- the forcing `G`
  refine ⟨fun σ => toL2w m (Φ σ), ?_, ?_, ?_⟩
  · intro σ hσ
    have hρ : ComplFreeRateSub.Leaf4Aux.rho t₁ t₂ (ageAt ν t₁ σ) = ageAt ν t₁ σ :=
      ComplFreeRateSub.Leaf4Aux.rho_eq (ageAt_mem_Icc hν ht₁ h12 hBe hσ)
    have h1 : ⇑(toL2w m (Φ σ)) =ᵐ[Planar.wMeasure m] Φ σ := coeFn_toL2w (hΦmem σ)
    have h2 : ⇑(toL2w m (Φ σ)) =ᵐ[volume] Φ σ := (Planar.volume_ac m).ae_le h1
    refine h2.trans (Eventually.of_forall fun z => ?_)
    rw [hΦ]
    simp only [hρ]
  · have hGsm : StronglyMeasurable (fun σ => toL2w m (Φ σ)) :=
      stronglyMeasurable_toL2w hΦmeas hΦmem
    refine Measure.integrableOn_of_bounded (M := C_N * (2 * (C_A * C_F)))
      measure_Icc_lt_top.ne hGsm.aestronglyMeasurable (Eventually.of_forall fun σ => ?_)
    rw [toL2w, dif_pos (hΦmem σ), Lp.norm_toLp]
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) (hΦnorm σ)
  · intro r hr j
    exact (hcmfm r hr j).aestronglyMeasurable

end UnforcedLeray.Short.IIIa
