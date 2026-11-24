import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_3_1_1_org.Leaf2Regular.SourceMemLp
import UnforcedLeray.Short.PartIIIa.Clock.FrameStableProof.BlockContraction.CompactDuhamelGap.VariationOfConstants.ComplMildG
import UnforcedLeray.Short.PartIIIa.Clock.FrameStableProof.BlockContraction.CompactDuhamelGap.VariationOfConstants.ComplMildY
import UnforcedLeray.Short.PartIIIa.Clock.FrameStableProof.BlockContraction.CompactDuhamelGap.VariationOfConstants.RelLeafB6
import UnforcedLeray.Short.PartIIIa.Clock.FrameStableProof.BlockContraction.CompactDuhamelGap.VariationOfConstants.DuhamelAbstract.Measurability
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_1_org_1_a.Interaction
import UnforcedLeray.Infra.JointMeasurableRep

/-!
# Helper 1 for `ComplSourceRegular` (`PartIII-a:T21/c3/3/1/1/2/2/4`): source path measurability

Source `the November 2 reference manuscript` (SP) lines 2919-2925, 2937-2958,
2974-2978.

Establishes:
1. `forceFinite_of`: unconditional block finiteness `ForceFinite` of `complModeForce` from
   `ComplMildGAux.psi_block_xNorm` and `xNorm_frameProj_le`.
2. `aesm_complSource_toL2w`: strong measurability on `volume.restrict (Icc t₁ t₂)` of the
   zero-extended complement source path `r ↦ toL2w m (cellZeroExt (dd ν r) (complSource ... r) ∘ cToPlane)`
   in `Planar.L2w m`, splitting into the localized Euler interaction `interactionTerm`, the
   finite-rank `movH0` coupling, and the mode-forcing sum.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

open FrameShortBlockSub FrameBlockContractSub CompactDuhamelGapSub BlockPropagatorSub
  ComplCouplingSub PerturbDuhamelSub EulerErrorSub VariationOfConstantsSub
  VariationOfConstantsMildSub ComplMildYAux ComplMildGAux
  BlockPropagatorInteriorSub.OrgSplit.RelIntA

namespace ComplFreeRateSub

namespace Leaf2RegularAux

/-- Standing Gram determinant nonvanishing along `[t₁, t₂]` from `PerFrameFacts`. -/
theorem perGram_det_ne_zero_of_facts (κ : PlanarFrameKernels) {ν m b K t₁ t₂ : ℝ}
    (hν : 0 < ν) (ht₁ : 0 ≤ t₁) (hbt₂ : b ≤ clockTheta ν t₂)
    (hF : PerFrameFacts κ ν m b K) :
    ∀ r ∈ Icc t₁ t₂, (perGram κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r))).det ≠ 0 := by
  intro r hr hdz
  have hr0 : 0 ≤ r := ht₁.trans hr.1
  have hbr : b ≤ clockTheta ν r := hbt₂.trans (theta_anti hν hr0 hr.2)
  have h1 := hF.1 r hr0 hbr 0 0
  have hinv : (perGram κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)))⁻¹ = 0 :=
    Matrix.nonsing_inv_apply_not_isUnit _ (by rw [isUnit_iff_ne_zero]; exact not_not.2 hdz)
  have h0 : ∀ x, perLam κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) 0 x = 0 := by
    intro x
    unfold perLam
    rw [hinv]
    simp
  simp only [h0, zero_mul, integral_zero, ite_true] at h1
  exact zero_ne_one h1

/-- Unconditional finiteness of `complModeForce` norms on `[t₁, t₂]`. -/
theorem forceFinite_of {κ : PlanarFrameKernels} (hκ : IsSeedKernels κ) (P : PlanarData)
    {ν m b K : ℝ} (hν : 0 < ν) (hm : 8 < m) (hb : 1 ≤ b)
    (hF : PerFrameFacts κ ν m b K)
    {tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))}
    (htr : UnforcedLeray.Short.PartI.IsBUCTrain tr)
    {t₁ t₂ : ℝ} (ht₁ : 0 ≤ t₁) (h12 : t₁ ≤ t₂) (hbt₂ : b ≤ clockTheta ν t₂) :
    Leaf2RegularNeeded.ForceFinite κ P ν m b K hν hF tr t₁ t₂ := by
  have hm0 : (0 : ℝ) ≤ m := by linarith
  have hbr : ∀ r ∈ Icc t₁ t₂, b ≤ clockTheta ν r := fun r hr =>
    hbt₂.trans (theta_anti hν (ht₁.trans hr.1) hr.2)
  have hθ1 : ∀ r ∈ Icc t₁ t₂, 1 ≤ clockTheta ν r := fun r hr => hb.trans (hbr r hr)
  have hd1 : ∀ r ∈ Icc t₁ t₂, 1 ≤ cellLen (ν ^ (-2 : ℝ)) (clockA ν r) := fun r hr =>
    cellLen_one_le_of_theta hν (ht₁.trans hr.1) hb (hbr r hr)
  have hoscm : ∀ r ∈ Icc t₁ t₂, ∀ j : Fin 2, Measurable (movOscRes κ ν r j) := by
    intro r hr j
    have h := (Leaf4Aux.measurable_movOscRes_joint hκ hν ht₁ h12 hd1 j).comp
      (measurable_const.prodMk measurable_id : Measurable (fun y : ℝ × ℝ => (r, y)))
    simpa only [Function.comp_def, Leaf4Aux.rho_eq hr] using h
  obtain ⟨C_Ψ, _hCΨ0, hCΨ⟩ := psi_block_xNorm hκ P hν tr htr ht₁ h12 hd1 hθ1 hm0
  intro r hr j
  have hr0 : 0 ≤ r := ht₁.trans hr.1
  have hΨm : AEStronglyMeasurable (fun y => movOscRes κ ν r j y + movEulerRes κ P tr r j y)
      (B0579.cellMeasure (dd ν r) m) :=
    (hoscm r hr j).aestronglyMeasurable.add (aesm_movEulerRes hκ P hν tr hr0 m j)
  have hproj := xNorm_frameProj_le (periodizedFrame κ ν m b K hν hF) hr0 (hbr r hr) hΨm
  have hle : xNorm (dd ν r) m (complModeForce κ P (periodizedFrame κ ν m b K hν hF) tr r j) ≤
      ENNReal.ofReal (1 + 2 * max K 0 ^ 2) * ENNReal.ofReal C_Ψ := by
    refine hproj.trans ?_
    gcongr
    exact hCΨ r hr j
  exact (hle.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)).ne

/-! ### Isometric bridge helpers between `Planar.L2w m` and `B0579.cellMeasure d m` -/

theorem ae_cellMeasure_mem_cell (d m : ℝ) :
    ∀ᵐ y ∂(B0579.cellMeasure d m), y ∈ B0579.cell d :=
  (B0579.cellMeasure_ac d m).ae_le (ae_restrict_mem (B0579.measurableSet_cell d))

theorem ae_eq_cellMeasure_of_wMeasure (d m : ℝ) {F₁ F₂ : ℂ → ℂ}
    (h : F₁ =ᵐ[Planar.wMeasure m] F₂) :
    (fun y : ℝ × ℝ => F₁ (planeToC y)) =ᵐ[B0579.cellMeasure d m]
      fun y : ℝ × ℝ => F₂ (planeToC y) := by
  have hcomp : (fun y : ℝ × ℝ => F₁ (planeToC y))
      =ᵐ[volume.withDensity fun y => (B0579.density m y : ℝ≥0∞)]
      fun y : ℝ × ℝ => F₂ (planeToC y) :=
    (measurePreserving_planeToC_wMeasure m).quasiMeasurePreserving.ae_eq_comp h
  have hrest := hcomp.filter_mono (ae_restrict_le (s := B0579.cell d))
  rwa [restrict_withDensity (B0579.measurableSet_cell d)] at hrest

theorem toL2w_congr_ae {m : ℝ} {g₁ g₂ : ℂ → ℂ} (h₁ : MemLp g₁ 2 (Planar.wMeasure m))
    (hae : g₁ =ᵐ[Planar.wMeasure m] g₂) :
    toL2w m g₁ = toL2w m g₂ := by
  have h₂ : MemLp g₂ 2 (Planar.wMeasure m) := h₁.ae_eq hae
  apply Lp.ext
  exact (coeFn_toL2w h₁).trans (hae.trans (coeFn_toL2w h₂).symm)

theorem toL2w_cellZeroExt_congr_ae (d m : ℝ) {V₁ V₂ : ℝ × ℝ → ℂ}
    (h₁ : MemLp V₁ 2 (B0579.cellMeasure d m))
    (hae : V₁ =ᵐ[B0579.cellMeasure d m] V₂) :
    toL2w m (fun z => cellZeroExt d V₁ (cToPlane z)) =
      toL2w m (fun z => cellZeroExt d V₂ (cToPlane z)) := by
  refine toL2w_congr_ae (memLp_cellZeroExt_cToPlane d m h₁) ?_
  have hind : cellZeroExt d V₁ =ᵐ[volume.withDensity fun y => (B0579.density m y : ℝ≥0∞)]
      cellZeroExt d V₂ := by
    have hcell : ∀ᵐ y ∂((volume.withDensity fun y => (B0579.density m y : ℝ≥0∞)).restrict
        (B0579.cell d)), V₁ y = V₂ y := by
      rw [restrict_withDensity (B0579.measurableSet_cell d)]
      exact hae
    rw [ae_restrict_iff' (B0579.measurableSet_cell d)] at hcell
    filter_upwards [hcell] with y hy
    unfold cellZeroExt
    by_cases hmem : y ∈ B0579.cell d
    · simp [indicator_of_mem hmem, hy hmem]
    · simp [indicator_of_notMem hmem]
  exact (measurePreserving_cToPlane_wMeasure m).quasiMeasurePreserving.ae_eq_comp hind

theorem toL2w_cellZeroExt_add (d m : ℝ) {V₁ V₂ : ℝ × ℝ → ℂ}
    (h₁ : MemLp V₁ 2 (B0579.cellMeasure d m)) (h₂ : MemLp V₂ 2 (B0579.cellMeasure d m)) :
    toL2w m (fun z => cellZeroExt d (fun y => V₁ y + V₂ y) (cToPlane z)) =
      toL2w m (fun z => cellZeroExt d V₁ (cToPlane z)) +
        toL2w m (fun z => cellZeroExt d V₂ (cToPlane z)) := by
  have h12 : MemLp (fun y => V₁ y + V₂ y) 2 (B0579.cellMeasure d m) := h₁.add h₂
  apply Lp.ext
  filter_upwards [coeFn_toL2w (memLp_cellZeroExt_cToPlane d m h12),
    Lp.coeFn_add (toL2w m (fun z => cellZeroExt d V₁ (cToPlane z)))
      (toL2w m (fun z => cellZeroExt d V₂ (cToPlane z))),
    coeFn_toL2w (memLp_cellZeroExt_cToPlane d m h₁),
    coeFn_toL2w (memLp_cellZeroExt_cToPlane d m h₂)] with z e12 eadd e1 e2
  rw [e12, eadd, Pi.add_apply, e1, e2]
  unfold cellZeroExt
  by_cases hz : cToPlane z ∈ B0579.cell d
  · simp [indicator_of_mem hz]
  · simp [indicator_of_notMem hz]

theorem toL2w_cellZeroExt_const_mul (d m : ℝ) (c : ℂ) {V : ℝ × ℝ → ℂ}
    (hV : MemLp V 2 (B0579.cellMeasure d m)) :
    toL2w m (fun z => cellZeroExt d (fun y => c * V y) (cToPlane z)) =
      c • toL2w m (fun z => cellZeroExt d V (cToPlane z)) := by
  have hcV : MemLp (fun y => c * V y) 2 (B0579.cellMeasure d m) := hV.const_mul c
  apply Lp.ext
  filter_upwards [coeFn_toL2w (memLp_cellZeroExt_cToPlane d m hcV),
    Lp.coeFn_smul c (toL2w m (fun z => cellZeroExt d V (cToPlane z))),
    coeFn_toL2w (memLp_cellZeroExt_cToPlane d m hV)] with z ec esm eV
  rw [ec, esm, Pi.smul_apply, eV, smul_eq_mul]
  unfold cellZeroExt
  by_cases hz : cToPlane z ∈ B0579.cell d
  · simp [indicator_of_mem hz]
  · simp [indicator_of_notMem hz]

theorem toL2w_cellZeroExt_neg (d m : ℝ) {V : ℝ × ℝ → ℂ}
    (hV : MemLp V 2 (B0579.cellMeasure d m)) :
    toL2w m (fun z => cellZeroExt d (fun y => -V y) (cToPlane z)) =
      -toL2w m (fun z => cellZeroExt d V (cToPlane z)) := by
  have := toL2w_cellZeroExt_const_mul d m (-1 : ℂ) hV
  simpa using this

/-- Cell restriction of any `X : Planar.L2w m` belongs to `MemLp · 2 (B0579.cellMeasure d m)`. -/
theorem memLp_planeToC (d m : ℝ) (X : Planar.L2w m) :
    MemLp (fun y : ℝ × ℝ => (X : ℂ → ℂ) (planeToC y)) 2 (B0579.cellMeasure d m) := by
  have haesm : AEStronglyMeasurable (fun y : ℝ × ℝ => (X : ℂ → ℂ) (planeToC y))
      (B0579.cellMeasure d m) := by
    have h1 : AEStronglyMeasurable (fun y : ℝ × ℝ => (X : ℂ → ℂ) (planeToC y))
        (volume.withDensity fun y => (B0579.density m y : ℝ≥0∞)) :=
      (Lp.aestronglyMeasurable X).comp_measurePreserving (measurePreserving_planeToC_wMeasure m)
    have h2 := h1.restrict (s := B0579.cell d)
    rwa [restrict_withDensity (B0579.measurableSet_cell d)] at h2
  exact ⟨haesm, (xNorm_planeToC_le_norm d m X).trans_lt ENNReal.ofReal_lt_top⟩

/-- Restricting `toL2w m (cellZeroExt d g ∘ cToPlane)` back to `B0579.cell d` recovers `g` a.e. -/
theorem planeToC_toL2w_cellZeroExt_ae (d m : ℝ) {g : ℝ × ℝ → ℂ}
    (hg : MemLp g 2 (B0579.cellMeasure d m)) :
    (fun y : ℝ × ℝ =>
        (toL2w m (fun z => cellZeroExt d g (cToPlane z)) : ℂ → ℂ) (planeToC y))
      =ᵐ[B0579.cellMeasure d m] g := by
  have hrest := ae_eq_cellMeasure_of_wMeasure d m
    (coeFn_toL2w (memLp_cellZeroExt_cToPlane d m hg))
  filter_upwards [hrest, ae_cellMeasure_mem_cell d m] with y hy hymem
  rw [hy, cToPlane_planeToC]
  unfold cellZeroExt
  exact indicator_of_mem hymem _

/-! ### Continuity of the zero-extended complement path in `Planar.L2w m` -/

/-- Zero-extended moving complement in `Planar.L2w m`. -/
def complExt (κ : PlanarFrameKernels) {ν m b K : ℝ} (hν : 0 < ν) (hF : PerFrameFacts κ ν m b K)
    (w : ℝ → ℝ × ℝ → ℂ) (r : ℝ) : Planar.L2w m :=
  toL2w m (fun z => cellZeroExt (dd ν r)
    (compl (periodizedFrame κ ν m b K hν hF) w r) (cToPlane z))

theorem continuousOn_complExt (κ : PlanarFrameKernels) {ν m b K : ℝ} (hν : 0 < ν)
    (hm : 8 < m) (hb : 1 ≤ b) (hF : PerFrameFacts κ ν m b K)
    {tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))}
    {t₁ t₂ : ℝ} (ht₁ : 0 ≤ t₁) (h12 : t₁ ≤ t₂) (hbt₂ : b ≤ clockTheta ν t₂)
    {f : ℝ × ℝ → ℂ} {w : ℝ → ℝ × ℝ → ℂ} {u : ℝ → ℝ × ℝ → Fin 2 → ℂ}
    (hw : IsLinearisedFlow ν (ν ^ (-2 : ℝ)) m tr t₁ f w u) :
    ContinuousOn (complExt κ hν hF w) (Icc t₁ t₂) := by
  have hm1 : (1 : ℝ) < m := by linarith
  have hm0 : (0 : ℝ) ≤ m := by linarith
  have hbr : ∀ r ∈ Icc t₁ t₂, b ≤ clockTheta ν r := fun r hr =>
    hbt₂.trans (theta_anti hν (ht₁.trans hr.1) hr.2)
  have hd1 : ∀ r ∈ Icc t₁ t₂, 1 ≤ cellLen (ν ^ (-2 : ℝ)) (clockA ν r) := fun r hr =>
    cellLen_one_le_of_theta hν (ht₁.trans hr.1) hb (hbr r hr)
  have hA1 : ∀ r ∈ Icc t₁ t₂, 1 ≤ clockA ν r := fun r hr =>
    one_le_clockA hν.le (ht₁.trans hr.1)
  have hV : ContinuousOn
      (fun r => toL2w m (fun z => cellZeroExt (ν ^ (-2 : ℝ)) (w r) (cToPlane z)))
      (Icc t₁ t₂) := by
    intro r hr
    refine continuousWithinAt_toL2w hr (fun r' hr' => hw.memX r' hr'.1) ?_
    exact (hw.strongCont r hr.1).mono_left
      (nhdsWithin_mono r fun r' (hr' : r' ∈ Icc t₁ t₂) => (hr'.1 : r' ∈ Ici t₁))
  have hE : ∀ i : Fin 2, ContinuousOn
      (fun r => toL2w m (fun z => cellZeroExt (ν ^ (-2 : ℝ)) (eFun κ ν i r) (cToPlane z)))
      (Icc t₁ t₂) := fun i r hr =>
    continuousWithinAt_toL2w hr (fun r' hr' => memLp_eFun κ hm0 hν ht₁ h12 hd1 i r' hr')
      (tendsto_xNorm_eFun κ hm0 hν ht₁ h12 hd1 i r hr)
  have hA : ∀ i : Fin 2, ContinuousOn (fun r => ampl (periodizedFrame κ ν m b K hν hF) w r i)
      (Icc t₁ t₂) := fun i =>
    continuousOn_ampl_age κ hm hν ht₁ h12 hbt₂ hF hd1 hw i
  have hR : ContinuousOn (fun r => fixedRep κ m hν hF w r) (Icc t₁ t₂) :=
    (hV.sub (((hA 0).smul (hE 0)).add ((hA 1).smul (hE 1)))).congr (fun _ _ => rfl)
  have hcA : Continuous (fun r => clockA ν r) := by unfold clockA; fun_prop
  have hD : ContinuousOn (fun r => dilR hm1 (clockA ν r)⁻¹ (fixedRep κ m hν hF w r))
      (Icc t₁ t₂) := by
    intro r hr
    have hpos : 0 < clockA ν r := lt_of_lt_of_le zero_lt_one (hA1 r hr)
    have hbound : ∀ r' ∈ Icc t₁ t₂,
        ‖dilR hm1 (clockA ν r')⁻¹‖ ≤ (clockA ν t₂) ^ (3 / 2 : ℝ) := by
      intro r' hr'
      have h1 := hA1 r' hr'
      rw [dilR_of_pos hm1 (inv_pos.2 (lt_of_lt_of_le zero_lt_one h1))]
      exact (Planar.norm_dilW_inv_le_of_one_le hm1 h1).trans
        (Real.rpow_le_rpow (by linarith) (clockA_mono hν.le hr'.2) (by norm_num))
    have hinv : ContinuousAt (fun r' => (clockA ν r')⁻¹) r :=
      hcA.continuousAt.inv₀ hpos.ne'
    have hstrong : ContinuousWithinAt
        (fun r' => dilR hm1 (clockA ν r')⁻¹ (fixedRep κ m hν hF w r)) (Icc t₁ t₂) r :=
      ((continuousAt_dilR_apply hm1 (fixedRep κ m hν hF w r) (inv_pos.2 hpos)).comp
        (f := fun r' => (clockA ν r')⁻¹) hinv).continuousWithinAt
    exact continuousWithinAt_clm_apply (T := fun r' => dilR hm1 (clockA ν r')⁻¹)
      (g := fun r' => fixedRep κ m hν hF w r') hbound hstrong (hR r hr)
  refine hD.congr (fun s hs => ?_)
  have hs0 : 0 ≤ s := ht₁.trans hs.1
  have hpos : 0 < clockA ν s := lt_of_lt_of_le zero_lt_one (hA1 s hs)
  have hainv : 0 < (clockA ν s)⁻¹ := inv_pos.2 hpos
  have hWmem : MemLp (compl (periodizedFrame κ ν m b K hν hF) w s) 2
      (B0579.cellMeasure (dd ν s) m) :=
    memLp_compl _ hm0 hν ht₁ hs.1 (hbr s hs) hw
  have hRrep : ⇑(fixedRep κ m hν hF w s) =ᵐ[Planar.wMeasure m]
      fun z => cellZeroExt (ν ^ (-2 : ℝ)) (w s) (cToPlane z) -
        (ampl (periodizedFrame κ ν m b K hν hF) w s 0 *
            cellZeroExt (ν ^ (-2 : ℝ)) (eFun κ ν 0 s) (cToPlane z) +
          ampl (periodizedFrame κ ν m b K hν hF) w s 1 *
            cellZeroExt (ν ^ (-2 : ℝ)) (eFun κ ν 1 s) (cToPlane z)) := by
    unfold fixedRep
    filter_upwards [Lp.coeFn_sub (toL2w m (fun z => cellZeroExt (ν ^ (-2 : ℝ)) (w s)
        (cToPlane z))) (ampl (periodizedFrame κ ν m b K hν hF) w s 0 •
          toL2w m (fun z => cellZeroExt (ν ^ (-2 : ℝ)) (eFun κ ν 0 s) (cToPlane z)) +
        ampl (periodizedFrame κ ν m b K hν hF) w s 1 •
          toL2w m (fun z => cellZeroExt (ν ^ (-2 : ℝ)) (eFun κ ν 1 s) (cToPlane z))),
      Lp.coeFn_add (ampl (periodizedFrame κ ν m b K hν hF) w s 0 •
          toL2w m (fun z => cellZeroExt (ν ^ (-2 : ℝ)) (eFun κ ν 0 s) (cToPlane z)))
        (ampl (periodizedFrame κ ν m b K hν hF) w s 1 •
          toL2w m (fun z => cellZeroExt (ν ^ (-2 : ℝ)) (eFun κ ν 1 s) (cToPlane z))),
      Lp.coeFn_smul (ampl (periodizedFrame κ ν m b K hν hF) w s 0)
        (toL2w m (fun z => cellZeroExt (ν ^ (-2 : ℝ)) (eFun κ ν 0 s) (cToPlane z))),
      Lp.coeFn_smul (ampl (periodizedFrame κ ν m b K hν hF) w s 1)
        (toL2w m (fun z => cellZeroExt (ν ^ (-2 : ℝ)) (eFun κ ν 1 s) (cToPlane z))),
      coeFn_toL2w (memLp_cellZeroExt_cToPlane (ν ^ (-2 : ℝ)) m (hw.memX s hs.1)),
      coeFn_toL2w (memLp_cellZeroExt_cToPlane (ν ^ (-2 : ℝ)) m
        (memLp_eFun κ hm0 hν ht₁ h12 hd1 0 s hs)),
      coeFn_toL2w (memLp_cellZeroExt_cToPlane (ν ^ (-2 : ℝ)) m
        (memLp_eFun κ hm0 hν ht₁ h12 hd1 1 s hs))] with z e1 e2 e3 e4 e5 e6 e7
    rw [e1, Pi.sub_apply, e2, Pi.add_apply, e3, e4, Pi.smul_apply, Pi.smul_apply, e5, e6, e7,
      smul_eq_mul, smul_eq_mul]
  have hdil : ⇑(dilR hm1 (clockA ν s)⁻¹ (fixedRep κ m hν hF w s)) =ᵐ[Planar.wMeasure m]
      Planar.dilWFun (clockA ν s)⁻¹ ⇑(fixedRep κ m hν hF w s) := by
    rw [dilR_of_pos hm1 hainv]
    exact Planar.coeFn_dilW hm1 hainv _
  have hcongr := Planar.dilWFun_congr (M := m) hainv hRrep
  unfold complExt
  apply Lp.ext
  filter_upwards [coeFn_toL2w (memLp_cellZeroExt_cToPlane (dd ν s) m hWmem), hdil, hcongr]
    with z h0 h1 h2
  rw [h0, h1, h2]
  exact (dilWFun_rep_eq κ hν hF w hs0 z).symm

/-! ### Measurability of the finite-rank `movH0` coupling path -/

theorem aemeasurable_movH0_compl {κ : PlanarFrameKernels} (hκ : IsSeedKernels κ)
    {ν m b K : ℝ} (hν : 0 < ν) (hm : 8 < m) (hb : 1 ≤ b) (hF : PerFrameFacts κ ν m b K)
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)))
    {t₁ t₂ : ℝ} (ht₁ : 0 ≤ t₁) (h12 : t₁ ≤ t₂) (hbt₂ : b ≤ clockTheta ν t₂)
    {f : ℝ × ℝ → ℂ} {w : ℝ → ℝ × ℝ → ℂ} {u : ℝ → ℝ × ℝ → Fin 2 → ℂ}
    (hw : IsLinearisedFlow ν (ν ^ (-2 : ℝ)) m tr t₁ f w u) (i : Fin 2) :
    AEMeasurable (fun r => movH0 κ tr r i (compl (periodizedFrame κ ν m b K hν hF) w r))
      (volume.restrict (Icc t₁ t₂)) := by
  have hm0 : (0 : ℝ) ≤ m := by linarith
  have hbr : ∀ r ∈ Icc t₁ t₂, b ≤ clockTheta ν r := fun r hr =>
    hbt₂.trans (theta_anti hν (ht₁.trans hr.1) hr.2)
  have hd1 : ∀ r ∈ Icc t₁ t₂, 1 ≤ cellLen (ν ^ (-2 : ℝ)) (clockA ν r) := fun r hr =>
    cellLen_one_le_of_theta hν (ht₁.trans hr.1) hb (hbr r hr)
  have hdet := perGram_det_ne_zero_of_facts κ hν ht₁ hbt₂ hF
  have hform : ∀ r ∈ Icc t₁ t₂, HeatFormula κ ν r := fun r hr =>
    RelRegularityOrg.relB6_heatFormula_of_det κ hκ hν (ht₁.trans hr.1) (hdet r hr)
  have hcont := continuousOn_complExt κ hν hm hb hF ht₁ h12 hbt₂ hw
  obtain ⟨W_joint, hWsm, hWrep⟩ :=
    UnforcedLeray.Infra.JointMeasurableRep.exists_stronglyMeasurable_rep_of_continuousOn_Icc
      (μ := Planar.wMeasure m) (p := 2) hcont
  have hWpl : Measurable (fun q : ℝ × (ℝ × ℝ) => W_joint (q.1, planeToC q.2)) :=
    hWsm.measurable.comp (measurable_fst.prodMk (measurable_planeToC.comp measurable_snd))
  have hLam := measurable_movLamDual_joint hκ hν ht₁ h12 hd1 hdet hform tr i
  have hIntMeas : Measurable (fun r : ℝ =>
      ∫ y in B0579.cell (Leaf4Aux.dRho ν t₁ t₂ r),
        movLamDual κ tr (Leaf4Aux.rho t₁ t₂ r) i y * W_joint (r, planeToC y)) :=
    Leaf4Aux.measurable_setIntegral_cell (Leaf4Aux.dRho ν t₁ t₂)
      (Leaf4Aux.continuous_dRho hν ht₁).measurable
      (fun q : ℝ × (ℝ × ℝ) =>
        movLamDual κ tr (Leaf4Aux.rho t₁ t₂ q.1) i q.2 * W_joint (q.1, planeToC q.2))
      (hLam.mul hWpl)
  refine hIntMeas.aemeasurable.congr ?_
  refine (ae_restrict_mem measurableSet_Icc).mono fun r hr => ?_
  have hWmem : MemLp (compl (periodizedFrame κ ν m b K hν hF) w r) 2
      (B0579.cellMeasure (dd ν r) m) :=
    memLp_compl _ hm0 hν ht₁ hr.1 (hbr r hr) hw
  have h1 : (fun z => W_joint (r, z)) =ᵐ[Planar.wMeasure m]
      fun z => cellZeroExt (dd ν r) (compl (periodizedFrame κ ν m b K hν hF) w r) (cToPlane z) :=
    (hWrep r hr).trans (coeFn_toL2w (memLp_cellZeroExt_cToPlane (dd ν r) m hWmem))
  have h2 : (fun z => W_joint (r, z)) =ᵐ[volume]
      fun z => cellZeroExt (dd ν r) (compl (periodizedFrame κ ν m b K hν hF) w r) (cToPlane z) :=
    (Planar.volume_ac m).ae_le h1
  have h3 : (fun y : ℝ × ℝ => W_joint (r, planeToC y)) =ᵐ[volume]
      fun y => cellZeroExt (dd ν r) (compl (periodizedFrame κ ν m b K hν hF) w r)
        (cToPlane (planeToC y)) :=
    measurePreserving_planeToC_volume.quasiMeasurePreserving.ae_eq_comp h2
  have h4 : ∀ᵐ y ∂(volume.restrict (B0579.cell (dd ν r))),
      movLamDual κ tr r i y * W_joint (r, planeToC y) =
        movLamDual κ tr r i y * compl (periodizedFrame κ ν m b K hν hF) w r y := by
    filter_upwards [ae_restrict_of_ae h3,
      ae_restrict_mem (B0579.measurableSet_cell (dd ν r))] with y hy hymem
    rw [hy, cToPlane_planeToC]
    simp only [cellZeroExt, indicator_of_mem hymem]
  have hd_eq : Leaf4Aux.dRho ν t₁ t₂ r = dd ν r := by
    unfold Leaf4Aux.dRho dd
    rw [Leaf4Aux.rho_eq hr]
  dsimp only
  rw [hd_eq, Leaf4Aux.rho_eq hr, movH0_eq_integral_movLamDual]
  exact integral_congr_ae h4

theorem aesm_coupling_path {κ : PlanarFrameKernels} (hκ : IsSeedKernels κ)
    {ν m b K : ℝ} (hν : 0 < ν) (hm : 8 < m) (hb : 1 ≤ b) (hF : PerFrameFacts κ ν m b K)
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)))
    {t₁ t₂ : ℝ} (ht₁ : 0 ≤ t₁) (h12 : t₁ ≤ t₂) (hbt₂ : b ≤ clockTheta ν t₂)
    {f : ℝ × ℝ → ℂ} {w : ℝ → ℝ × ℝ → ℂ} {u : ℝ → ℝ × ℝ → Fin 2 → ℂ}
    (hw : IsLinearisedFlow ν (ν ^ (-2 : ℝ)) m tr t₁ f w u) :
    AEStronglyMeasurable (fun r => toL2w m (fun z => cellZeroExt (dd ν r)
      (complFiniteRankCoupling (periodizedFrame κ ν m b K hν hF) r
        (movH0 κ tr r · (compl (periodizedFrame κ ν m b K hν hF) w r))) (cToPlane z)))
      (volume.restrict (Icc t₁ t₂)) := by
  set F := periodizedFrame κ ν m b K hν hF
  have hbr : ∀ r ∈ Icc t₁ t₂, b ≤ clockTheta ν r := fun r hr =>
    hbt₂.trans (theta_anti hν (ht₁.trans hr.1) hr.2)
  have hd1 : ∀ r ∈ Icc t₁ t₂, 1 ≤ cellLen (ν ^ (-2 : ℝ)) (clockA ν r) := fun r hr =>
    cellLen_one_le_of_theta hν (ht₁.trans hr.1) hb (hbr r hr)
  have hE_sm : ∀ i : Fin 2, StronglyMeasurable (fun r : ℝ =>
      toL2w m (fun z => cellZeroExt (Leaf4Aux.dRho ν t₁ t₂ r)
        (perE κ (Leaf4Aux.dRho ν t₁ t₂ r) i) (cToPlane z))) := by
    intro i
    have hjoint := measurable_cellZeroExt_joint (Leaf4Aux.dRho ν t₁ t₂)
      (Leaf4Aux.continuous_dRho hν ht₁).measurable
      (fun r => perE κ (Leaf4Aux.dRho ν t₁ t₂ r) i)
      (Leaf4Aux.measurable_perE_joint hκ hν ht₁ h12 hd1 i)
    have hFm : Measurable (fun p : ℝ × ℂ =>
        cellZeroExt (Leaf4Aux.dRho ν t₁ t₂ p.1)
          (perE κ (Leaf4Aux.dRho ν t₁ t₂ p.1) i) (cToPlane p.2)) :=
      Measurable.comp
        (g := fun q : ℝ × (ℝ × ℝ) =>
          cellZeroExt (Leaf4Aux.dRho ν t₁ t₂ q.1) (perE κ (Leaf4Aux.dRho ν t₁ t₂ q.1) i) q.2)
        (f := fun p : ℝ × ℂ => (p.1, cToPlane p.2))
        hjoint (measurable_fst.prodMk (measurable_cToPlane.comp measurable_snd))
    refine stronglyMeasurable_toL2w hFm (fun r => ?_)
    have hrm := Leaf4Aux.rho_mem h12 r
    have hmem : MemLp (perE κ (Leaf4Aux.dRho ν t₁ t₂ r) i) 2
        (B0579.cellMeasure (Leaf4Aux.dRho ν t₁ t₂ r) m) := by
      have := memLp_frame_E F (r := Leaf4Aux.rho t₁ t₂ r) (ht₁.trans hrm.1) (hbr _ hrm) i
      simpa [F, periodizedFrame, Leaf4Aux.dRho, dd] using this
    exact memLp_cellZeroExt_cToPlane _ m hmem
  have hterm : ∀ i : Fin 2, AEStronglyMeasurable (fun r =>
      movH0 κ tr r i (compl F w r) •
        toL2w m (fun z => cellZeroExt (Leaf4Aux.dRho ν t₁ t₂ r)
          (perE κ (Leaf4Aux.dRho ν t₁ t₂ r) i) (cToPlane z)))
      (volume.restrict (Icc t₁ t₂)) := fun i =>
    (aemeasurable_movH0_compl hκ hν hm hb hF tr ht₁ h12 hbt₂ hw i).aestronglyMeasurable.smul
      (hE_sm i).aestronglyMeasurable
  have hsum := ((hterm 0).add (hterm 1)).neg
  refine hsum.congr ?_
  refine (ae_restrict_mem measurableSet_Icc).mono fun r hr => ?_
  have hr0 : 0 ≤ r := ht₁.trans hr.1
  have hmem0 : MemLp (F.E r 0) 2 (B0579.cellMeasure (dd ν r) m) :=
    memLp_frame_E F hr0 (hbr r hr) 0
  have hmem1 : MemLp (F.E r 1) 2 (B0579.cellMeasure (dd ν r) m) :=
    memLp_frame_E F hr0 (hbr r hr) 1
  have hd_eq : Leaf4Aux.dRho ν t₁ t₂ r = dd ν r := by
    unfold Leaf4Aux.dRho dd; rw [Leaf4Aux.rho_eq hr]
  have hE_eq : ∀ i : Fin 2, F.E r i = perE κ (dd ν r) i := fun _ => rfl
  dsimp only [Pi.neg_apply, Pi.add_apply]
  rw [hd_eq]
  have hlin : toL2w m (fun z => cellZeroExt (dd ν r)
        (complFiniteRankCoupling F r (movH0 κ tr r · (compl F w r))) (cToPlane z)) =
      -(movH0 κ tr r 0 (compl F w r) •
          toL2w m (fun z => cellZeroExt (dd ν r) (F.E r 0) (cToPlane z)) +
        movH0 κ tr r 1 (compl F w r) •
          toL2w m (fun z => cellZeroExt (dd ν r) (F.E r 1) (cToPlane z))) := by
    have hfun : complFiniteRankCoupling F r (movH0 κ tr r · (compl F w r)) =
        fun y => -(movH0 κ tr r 0 (compl F w r) * F.E r 0 y +
          movH0 κ tr r 1 (compl F w r) * F.E r 1 y) := by
      funext y
      simp [complFiniteRankCoupling, Fin.sum_univ_two]
    have h01 : MemLp (fun y => movH0 κ tr r 0 (compl F w r) * F.E r 0 y +
        movH0 κ tr r 1 (compl F w r) * F.E r 1 y) 2 (B0579.cellMeasure (dd ν r) m) :=
      (hmem0.const_mul _).add (hmem1.const_mul _)
    rw [hfun, toL2w_cellZeroExt_neg (dd ν r) m h01,
      toL2w_cellZeroExt_add (dd ν r) m (hmem0.const_mul _) (hmem1.const_mul _),
      toL2w_cellZeroExt_const_mul (dd ν r) m _ hmem0,
      toL2w_cellZeroExt_const_mul (dd ν r) m _ hmem1]
  rw [hlin, hE_eq 0, hE_eq 1]

/-! ### Measurability of the mode-forcing sum path -/

theorem aesm_force_sum_path {κ : PlanarFrameKernels} (hκ : IsSeedKernels κ) (P : PlanarData)
    {ν m b K : ℝ} (hν : 0 < ν) (hm : 8 < m) (hb : 1 ≤ b) (hF : PerFrameFacts κ ν m b K)
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)))
    (htr : UnforcedLeray.Short.PartI.IsBUCTrain tr)
    {t₁ t₂ : ℝ} (ht₁ : 0 ≤ t₁) (h12 : t₁ ≤ t₂) (hbt₂ : b ≤ clockTheta ν t₂)
    {f : ℝ × ℝ → ℂ} {w : ℝ → ℝ × ℝ → ℂ} {u : ℝ → ℝ × ℝ → Fin 2 → ℂ}
    (hw : IsLinearisedFlow ν (ν ^ (-2 : ℝ)) m tr t₁ f w u) :
    AEStronglyMeasurable (fun r => toL2w m (fun z => cellZeroExt (dd ν r)
      (fun y => ∑ j : Fin 2, ampl (periodizedFrame κ ν m b K hν hF) w r j *
        complModeForce κ P (periodizedFrame κ ν m b K hν hF) tr r j y) (cToPlane z)))
      (volume.restrict (Icc t₁ t₂)) := by
  set F := periodizedFrame κ ν m b K hν hF
  have hbr : ∀ r ∈ Icc t₁ t₂, b ≤ clockTheta ν r := fun r hr =>
    hbt₂.trans (theta_anti hν (ht₁.trans hr.1) hr.2)
  have hd1 : ∀ r ∈ Icc t₁ t₂, 1 ≤ cellLen (ν ^ (-2 : ℝ)) (clockA ν r) := fun r hr =>
    cellLen_one_le_of_theta hν (ht₁.trans hr.1) hb (hbr r hr)
  have hdet := perGram_det_ne_zero_of_facts κ hν ht₁ hbt₂ hF
  have hFin := forceFinite_of hκ P hν hm hb hF htr ht₁ h12 hbt₂
  have hforce := fun j => Leaf4Aux.measurable_force_joint hκ hν ht₁ h12 hd1 P hF hdet tr j
  have hcmf_mem : ∀ r ∈ Icc t₁ t₂, ∀ j : Fin 2,
      MemLp (complModeForce κ P F tr r j) 2 (B0579.cellMeasure (dd ν r) m) := by
    intro r hr j
    have hm_r : Measurable (complModeForce κ P F tr r j) := by
      have h := (hforce j).comp
        (measurable_const.prodMk measurable_id : Measurable (fun y : ℝ × ℝ => (r, y)))
      simpa only [Function.comp_def, Leaf4Aux.rho_eq hr] using h
    exact ⟨hm_r.aestronglyMeasurable, lt_top_iff_ne_top.2 (hFin r hr j)⟩
  have hF_sm : ∀ j : Fin 2, StronglyMeasurable (fun r : ℝ =>
      toL2w m (fun z => cellZeroExt (Leaf4Aux.dRho ν t₁ t₂ r)
        (complModeForce κ P F tr (Leaf4Aux.rho t₁ t₂ r) j) (cToPlane z))) := by
    intro j
    have hjoint := measurable_cellZeroExt_joint (Leaf4Aux.dRho ν t₁ t₂)
      (Leaf4Aux.continuous_dRho hν ht₁).measurable
      (fun r => complModeForce κ P F tr (Leaf4Aux.rho t₁ t₂ r) j) (hforce j)
    have hFm : Measurable (fun p : ℝ × ℂ =>
        cellZeroExt (Leaf4Aux.dRho ν t₁ t₂ p.1)
          (complModeForce κ P F tr (Leaf4Aux.rho t₁ t₂ p.1) j) (cToPlane p.2)) :=
      Measurable.comp
        (g := fun q : ℝ × (ℝ × ℝ) =>
          cellZeroExt (Leaf4Aux.dRho ν t₁ t₂ q.1)
            (complModeForce κ P F tr (Leaf4Aux.rho t₁ t₂ q.1) j) q.2)
        (f := fun p : ℝ × ℂ => (p.1, cToPlane p.2))
        hjoint (measurable_fst.prodMk (measurable_cToPlane.comp measurable_snd))
    refine stronglyMeasurable_toL2w hFm (fun r => ?_)
    have hrm := Leaf4Aux.rho_mem h12 r
    have hmem : MemLp (complModeForce κ P F tr (Leaf4Aux.rho t₁ t₂ r) j) 2
        (B0579.cellMeasure (Leaf4Aux.dRho ν t₁ t₂ r) m) := by
      simpa [Leaf4Aux.dRho, dd] using hcmf_mem _ hrm j
    exact memLp_cellZeroExt_cToPlane _ m hmem
  have hA : ∀ j : Fin 2, ContinuousOn (fun r => ampl F w r j) (Icc t₁ t₂) := fun j =>
    continuousOn_ampl_age κ hm hν ht₁ h12 hbt₂ hF hd1 hw j
  have hterm : ∀ j : Fin 2, AEStronglyMeasurable (fun r =>
      ampl F w r j • toL2w m (fun z => cellZeroExt (Leaf4Aux.dRho ν t₁ t₂ r)
        (complModeForce κ P F tr (Leaf4Aux.rho t₁ t₂ r) j) (cToPlane z)))
      (volume.restrict (Icc t₁ t₂)) := fun j =>
    ((hA j).aestronglyMeasurable measurableSet_Icc).smul (hF_sm j).aestronglyMeasurable
  refine ((hterm 0).add (hterm 1)).congr ?_
  refine (ae_restrict_mem measurableSet_Icc).mono fun r hr => ?_
  have hd_eq : Leaf4Aux.dRho ν t₁ t₂ r = dd ν r := by
    unfold Leaf4Aux.dRho dd; rw [Leaf4Aux.rho_eq hr]
  dsimp only [Pi.add_apply]
  rw [hd_eq, Leaf4Aux.rho_eq hr]
  have hfun : (fun y => ∑ j : Fin 2, ampl F w r j * complModeForce κ P F tr r j y) =
      fun y => ampl F w r 0 * complModeForce κ P F tr r 0 y +
        ampl F w r 1 * complModeForce κ P F tr r 1 y := by
    funext y; simp [Fin.sum_univ_two]
  rw [hfun,
    toL2w_cellZeroExt_add (dd ν r) m ((hcmf_mem r hr 0).const_mul _)
      ((hcmf_mem r hr 1).const_mul _),
    toL2w_cellZeroExt_const_mul (dd ν r) m _ (hcmf_mem r hr 0),
    toL2w_cellZeroExt_const_mul (dd ν r) m _ (hcmf_mem r hr 1)]

/-! ### Bounded linear realization and measurability of the localized interaction path -/

theorem interactionTerm_congr_ae {ν : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)))
    (r : ℝ) {W₁ W₂ : ℝ × ℝ → ℂ}
    (hae : W₁ =ᵐ[volume.restrict (B0579.cell (dd ν r))] W₂) :
    interactionTerm tr r W₁ = interactionTerm tr r W₂ := by
  funext y
  have hk : ∀ k : Fin 2, kerVelCx (dd ν r) W₁ y k = kerVelCx (dd ν r) W₂ y k := by
    intro k
    unfold kerVelCx
    refine integral_congr_ae ?_
    filter_upwards [hae] with z hz
    rw [hz]
  simp only [interactionTerm, hk 0, hk 1]

theorem interactionTerm_const_mul {ν : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)))
    (r : ℝ) (c : ℂ) (W : ℝ × ℝ → ℂ) :
    interactionTerm tr r (fun z => c * W z) = fun y => c * interactionTerm tr r W y := by
  funext y
  have hk : ∀ k : Fin 2,
      kerVelCx (dd ν r) (fun z => c * W z) y k = c * kerVelCx (dd ν r) W y k := by
    intro k
    unfold kerVelCx
    simp_rw [mul_assoc]
    exact integral_const_mul c _
  simp only [interactionTerm, hk 0, hk 1]
  ring

theorem interactionTerm_add_ae {ν m : ℝ} (hm1 : 1 < m)
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) {r : ℝ} (hd1 : 1 ≤ dd ν r)
    {W₁ W₂ : ℝ × ℝ → ℂ} (h₁ : MemLp W₁ 2 (B0579.cellMeasure (dd ν r) m))
    (h₂ : MemLp W₂ 2 (B0579.cellMeasure (dd ν r) m)) :
    interactionTerm tr r (fun z => W₁ z + W₂ z) =ᵐ[B0579.cellMeasure (dd ν r) m]
      fun y => interactionTerm tr r W₁ y + interactionTerm tr r W₂ y := by
  have hi1 := (B0579.cellMeasure_ac (dd ν r) m).ae_le (ae_integrableOn_kerVelCx hd1 hm1 h₁)
  have hi2 := (B0579.cellMeasure_ac (dd ν r) m).ae_le (ae_integrableOn_kerVelCx hd1 hm1 h₂)
  filter_upwards [hi1, hi2] with y hy1 hy2
  have hk : ∀ k : Fin 2,
      kerVelCx (dd ν r) (fun z => W₁ z + W₂ z) y k =
        kerVelCx (dd ν r) W₁ y k + kerVelCx (dd ν r) W₂ y k := by
    intro k
    unfold kerVelCx
    simp_rw [add_mul]
    exact integral_add (hy1 k) (hy2 k)
  simp only [interactionTerm, hk 0, hk 1]
  ring

/-- Continuous `ℂ`-linear operator on `Planar.L2w m` realizing `interactionTerm` at clamped age. -/
def lIntCLM {ν m t₁ t₂ C_loc : ℝ} (hm1 : 1 < m) (h12 : t₁ ≤ t₂)
    (hd1 : ∀ r ∈ Icc t₁ t₂, 1 ≤ dd ν r)
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)))
    (hInt : LocInteractionConcl ν m tr t₁ t₂ C_loc) (r : ℝ) :
    Planar.L2w m →L[ℂ] Planar.L2w m := by
  set r' := Leaf4Aux.rho t₁ t₂ r
  have hr' : r' ∈ Icc t₁ t₂ := Leaf4Aux.rho_mem h12 r
  have hdr' : 1 ≤ dd ν r' := hd1 r' hr'
  have hmemOut : ∀ X : Planar.L2w m,
      MemLp (interactionTerm tr r' (fun y => (X : ℂ → ℂ) (planeToC y))) 2
        (B0579.cellMeasure (dd ν r') m) := by
    intro X
    have hRX := memLp_planeToC (dd ν r') m X
    obtain ⟨hmX, hbX⟩ := hInt r' hr' _ hRX
    exact ⟨hmX, lt_of_le_of_lt hbX (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hRX.2)⟩
  refine LinearMap.mkContinuous
    { toFun := fun X => toL2w m (fun z => cellZeroExt (dd ν r')
        (interactionTerm tr r' (fun y => (X : ℂ → ℂ) (planeToC y))) (cToPlane z))
      map_add' := fun X Y => by
        have hadd_ae : (fun y : ℝ × ℝ => ((X + Y : Planar.L2w m) : ℂ → ℂ) (planeToC y))
            =ᵐ[volume.restrict (B0579.cell (dd ν r'))]
            fun y => (X : ℂ → ℂ) (planeToC y) + (Y : ℂ → ℂ) (planeToC y) := by
          have h1 := (Planar.volume_ac m).ae_le (Lp.coeFn_add X Y)
          have h2 := measurePreserving_planeToC_volume.quasiMeasurePreserving.ae_eq_comp h1
          filter_upwards [ae_restrict_of_ae h2] with y hy
          exact hy
        rw [interactionTerm_congr_ae tr r' hadd_ae,
          toL2w_cellZeroExt_congr_ae (dd ν r') m (by
            have hRX := memLp_planeToC (dd ν r') m X
            have hRY := memLp_planeToC (dd ν r') m Y
            obtain ⟨hmXY, hbXY⟩ := hInt r' hr' _ (hRX.add hRY)
            exact ⟨hmXY, lt_of_le_of_lt hbXY
              (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hRX.add hRY).2)⟩)
            (interactionTerm_add_ae hm1 tr hdr' (memLp_planeToC (dd ν r') m X)
              (memLp_planeToC (dd ν r') m Y)),
          toL2w_cellZeroExt_add (dd ν r') m (hmemOut X) (hmemOut Y)]
      map_smul' := fun c X => by
        have hsmul_ae : (fun y : ℝ × ℝ => ((c • X : Planar.L2w m) : ℂ → ℂ) (planeToC y))
            =ᵐ[volume.restrict (B0579.cell (dd ν r'))]
            fun y => c * (X : ℂ → ℂ) (planeToC y) := by
          have h1 := (Planar.volume_ac m).ae_le (Lp.coeFn_smul c X)
          have h2 := measurePreserving_planeToC_volume.quasiMeasurePreserving.ae_eq_comp h1
          filter_upwards [ae_restrict_of_ae h2] with y hy
          simpa [smul_eq_mul] using hy
        dsimp only [RingHom.id_apply]
        rw [interactionTerm_congr_ae tr r' hsmul_ae, interactionTerm_const_mul,
          toL2w_cellZeroExt_const_mul (dd ν r') m c (hmemOut X)] }
    (max C_loc 0) (fun X => by
      have hRX := memLp_planeToC (dd ν r') m X
      obtain ⟨hmX, hbX⟩ := hInt r' hr' _ hRX
      have hmemZ := memLp_cellZeroExt_cToPlane (dd ν r') m (hmemOut X)
      have hn : ‖toL2w m (fun z => cellZeroExt (dd ν r')
          (interactionTerm tr r' (fun y => (X : ℂ → ℂ) (planeToC y))) (cToPlane z))‖ =
          (xNorm (dd ν r') m (interactionTerm tr r'
            (fun y => (X : ℂ → ℂ) (planeToC y)))).toReal := by
        rw [Lp.norm_def, eLpNorm_congr_ae (coeFn_toL2w hmemZ),
          eLpNorm_cellZeroExt_cToPlane (dd ν r') m hmX]
      dsimp only [LinearMap.coe_mk, AddHom.coe_mk]
      rw [hn]
      refine ENNReal.toReal_le_of_le_ofReal (mul_nonneg (le_max_right _ _) (norm_nonneg X)) ?_
      calc xNorm (dd ν r') m (interactionTerm tr r' (fun y => (X : ℂ → ℂ) (planeToC y)))
          ≤ ENNReal.ofReal C_loc * xNorm (dd ν r') m (fun y => (X : ℂ → ℂ) (planeToC y)) := hbX
        _ ≤ ENNReal.ofReal (max C_loc 0) * ENNReal.ofReal ‖X‖ :=
            mul_le_mul (ENNReal.ofReal_le_ofReal (le_max_left _ _))
              (xNorm_planeToC_le_norm (dd ν r') m X) bot_le bot_le
        _ = ENNReal.ofReal (max C_loc 0 * ‖X‖) :=
            (ENNReal.ofReal_mul (le_max_right _ _)).symm)

theorem lIntCLM_apply_eq {ν m t₁ t₂ C_loc : ℝ} (hm1 : 1 < m) (h12 : t₁ ≤ t₂)
    (hd1 : ∀ r ∈ Icc t₁ t₂, 1 ≤ dd ν r)
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)))
    (hInt : LocInteractionConcl ν m tr t₁ t₂ C_loc) (r : ℝ) (X : Planar.L2w m) :
    lIntCLM hm1 h12 hd1 tr hInt r X =
      toL2w m (fun z => cellZeroExt (dd ν (Leaf4Aux.rho t₁ t₂ r))
        (interactionTerm tr (Leaf4Aux.rho t₁ t₂ r) (fun y => (X : ℂ → ℂ) (planeToC y)))
        (cToPlane z)) :=
  rfl

theorem aesm_interaction_path (κ : PlanarFrameKernels) {ν m b K C_loc : ℝ} (hν : 0 < ν)
    (hm : 8 < m) (hb : 1 ≤ b) (hF : PerFrameFacts κ ν m b K)
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)))
    {t₁ t₂ : ℝ} (ht₁ : 0 ≤ t₁) (h12 : t₁ ≤ t₂) (hbt₂ : b ≤ clockTheta ν t₂)
    {f : ℝ × ℝ → ℂ} {w : ℝ → ℝ × ℝ → ℂ} {u : ℝ → ℝ × ℝ → Fin 2 → ℂ}
    (hw : IsLinearisedFlow ν (ν ^ (-2 : ℝ)) m tr t₁ f w u)
    (hInt : LocInteractionConcl ν m tr t₁ t₂ C_loc) :
    AEStronglyMeasurable (fun r => toL2w m (fun z => cellZeroExt (dd ν r)
      (interactionTerm tr r (compl (periodizedFrame κ ν m b K hν hF) w r)) (cToPlane z)))
      (volume.restrict (Icc t₁ t₂)) := by
  have hm1 : (1 : ℝ) < m := by linarith
  have hm0 : (0 : ℝ) ≤ m := by linarith
  have hbr : ∀ r ∈ Icc t₁ t₂, b ≤ clockTheta ν r := fun r hr =>
    hbt₂.trans (theta_anti hν (ht₁.trans hr.1) hr.2)
  have hd1 : ∀ r ∈ Icc t₁ t₂, 1 ≤ dd ν r := fun r hr =>
    cellLen_one_le_of_theta hν (ht₁.trans hr.1) hb (hbr r hr)
  have hT_smooth : ∀ W ∈ RelRegularityOrg.relSmoothClass m,
      AEStronglyMeasurable (fun r => lIntCLM hm1 h12 hd1 tr hInt r W)
        (volume.restrict (Icc t₁ t₂)) := by
    rintro W ⟨Φ, hΦs, _hΦc, hWΦ⟩
    have hΦm : Measurable Φ := hΦs.continuous.measurable
    have hjoint := measurable_cellZeroExt_joint (Leaf4Aux.dRho ν t₁ t₂)
      (Leaf4Aux.continuous_dRho hν ht₁).measurable
      (fun r => movLInt tr (Leaf4Aux.rho t₁ t₂ r) Φ)
      (measurable_movLInt_joint (t₂ := t₂) hν ht₁ tr hΦm)
    have hFm : Measurable (fun p : ℝ × ℂ =>
        cellZeroExt (Leaf4Aux.dRho ν t₁ t₂ p.1)
          (movLInt tr (Leaf4Aux.rho t₁ t₂ p.1) Φ) (cToPlane p.2)) :=
      Measurable.comp
        (g := fun q : ℝ × (ℝ × ℝ) =>
          cellZeroExt (Leaf4Aux.dRho ν t₁ t₂ q.1)
            (movLInt tr (Leaf4Aux.rho t₁ t₂ q.1) Φ) q.2)
        (f := fun p : ℝ × ℂ => (p.1, cToPlane p.2))
        hjoint (measurable_fst.prodMk (measurable_cToPlane.comp measurable_snd))
    have hEq_fun : (fun r => lIntCLM hm1 h12 hd1 tr hInt r W) =
        fun r => toL2w m (fun z => cellZeroExt (Leaf4Aux.dRho ν t₁ t₂ r)
          (movLInt tr (Leaf4Aux.rho t₁ t₂ r) Φ) (cToPlane z)) := by
      funext r
      rw [lIntCLM_apply_eq]
      have hRW_ae : (fun y : ℝ × ℝ => (W : ℂ → ℂ) (planeToC y))
          =ᵐ[volume.restrict (B0579.cell (dd ν (Leaf4Aux.rho t₁ t₂ r)))] Φ := by
        have hcomp := measurePreserving_planeToC_volume.quasiMeasurePreserving.ae_eq_comp hWΦ
        exact (ae_restrict_of_ae hcomp).mono fun y hy => by simpa [cToPlane_planeToC] using hy
      have hInt_eq : interactionTerm tr (Leaf4Aux.rho t₁ t₂ r)
          (fun y => (W : ℂ → ℂ) (planeToC y)) =
          movLInt tr (Leaf4Aux.rho t₁ t₂ r) Φ :=
        interactionTerm_congr_ae tr (Leaf4Aux.rho t₁ t₂ r) hRW_ae
      simp only [hInt_eq, Leaf4Aux.dRho, dd]
    rw [hEq_fun]
    refine (stronglyMeasurable_toL2w hFm (fun r => ?_)).aestronglyMeasurable
    have hrm := Leaf4Aux.rho_mem h12 r
    have hRW_ae : (fun y : ℝ × ℝ => (W : ℂ → ℂ) (planeToC y))
        =ᵐ[volume.restrict (B0579.cell (dd ν (Leaf4Aux.rho t₁ t₂ r)))] Φ := by
      have hcomp := measurePreserving_planeToC_volume.quasiMeasurePreserving.ae_eq_comp hWΦ
      exact (ae_restrict_of_ae hcomp).mono fun y hy => by simpa [cToPlane_planeToC] using hy
    have hInt_eq : interactionTerm tr (Leaf4Aux.rho t₁ t₂ r)
        (fun y => (W : ℂ → ℂ) (planeToC y)) =
        movLInt tr (Leaf4Aux.rho t₁ t₂ r) Φ :=
      interactionTerm_congr_ae tr (Leaf4Aux.rho t₁ t₂ r) hRW_ae
    have hRW := memLp_planeToC (dd ν (Leaf4Aux.rho t₁ t₂ r)) m W
    obtain ⟨hmW, hbW⟩ := hInt _ hrm _ hRW
    have hmemOut : MemLp (movLInt tr (Leaf4Aux.rho t₁ t₂ r) Φ) 2
        (B0579.cellMeasure (Leaf4Aux.dRho ν t₁ t₂ r) m) := by
      rw [← hInt_eq]
      exact ⟨hmW, lt_of_le_of_lt hbW (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hRW.2)⟩
    exact memLp_cellZeroExt_cToPlane _ m hmemOut
  have hT : ∀ X : Planar.L2w m,
      AEStronglyMeasurable (fun r => lIntCLM hm1 h12 hd1 tr hInt r X)
        (volume.restrict (Icc t₁ t₂)) :=
    RelRegularityOrg.aestronglyMeasurable_of_dense _ (lIntCLM hm1 h12 hd1 tr hInt)
      (RelRegularityOrg.relSmoothClass m) (RelRegularityOrg.relB6b_leaf m hm) hT_smooth
  have hWcont := continuousOn_complExt κ hν hm hb hF ht₁ h12 hbt₂ hw
  have happ := DuhamelAbstractSub.aestronglyMeasurable_clm_apply hT
    (hWcont.aestronglyMeasurable measurableSet_Icc)
  refine happ.congr ?_
  refine (ae_restrict_mem measurableSet_Icc).mono fun r hr => ?_
  dsimp only
  rw [lIntCLM_apply_eq, Leaf4Aux.rho_eq hr]
  have hWmem : MemLp (compl (periodizedFrame κ ν m b K hν hF) w r) 2
      (B0579.cellMeasure (dd ν r) m) :=
    memLp_compl _ hm0 hν ht₁ hr.1 (hbr r hr) hw
  have hae : (fun y : ℝ × ℝ => (complExt κ hν hF w r : ℂ → ℂ) (planeToC y))
      =ᵐ[volume.restrict (B0579.cell (dd ν r))]
      compl (periodizedFrame κ ν m b K hν hF) w r :=
    (B0579.ac_cellMeasure (dd ν r) m).ae_le (planeToC_toL2w_cellZeroExt_ae (dd ν r) m hWmem)
  rw [interactionTerm_congr_ae tr r hae]

/-! ### Combined zero-extended complement source path measurability -/

theorem aesm_complSource_toL2w {κ : PlanarFrameKernels} (hκ : IsSeedKernels κ) (P : PlanarData)
    {ν m b K C_loc C_H0 : ℝ} (hν : 0 < ν) (hm : 8 < m) (hb : 1 ≤ b)
    (hF : PerFrameFacts κ ν m b K)
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)))
    (htr : UnforcedLeray.Short.PartI.IsBUCTrain tr)
    {t₁ t₂ : ℝ} (ht₁ : 0 ≤ t₁) (h12 : t₁ ≤ t₂) (hbt₂ : b ≤ clockTheta ν t₂)
    {f : ℝ × ℝ → ℂ} {w : ℝ → ℝ × ℝ → ℂ} {u : ℝ → ℝ × ℝ → Fin 2 → ℂ}
    (hw : IsLinearisedFlow ν (ν ^ (-2 : ℝ)) m tr t₁ f w u)
    (hInt : LocInteractionConcl ν m tr t₁ t₂ C_loc)
    (hH0 : H0Hyp κ (periodizedFrame κ ν m b K hν hF) tr w t₁ t₂ C_H0) :
    AEStronglyMeasurable (fun r => toL2w m (fun z => cellZeroExt (dd ν r)
      (complSource κ P (periodizedFrame κ ν m b K hν hF) tr w r) (cToPlane z)))
      (volume.restrict (Icc t₁ t₂)) := by
  set F := periodizedFrame κ ν m b K hν hF
  have hm0 : (0 : ℝ) ≤ m := by linarith
  have hbr : ∀ r ∈ Icc t₁ t₂, b ≤ clockTheta ν r := fun r hr =>
    hbt₂.trans (theta_anti hν (ht₁.trans hr.1) hr.2)
  have hd1 : ∀ r ∈ Icc t₁ t₂, 1 ≤ cellLen (ν ^ (-2 : ℝ)) (clockA ν r) := fun r hr =>
    cellLen_one_le_of_theta hν (ht₁.trans hr.1) hb (hbr r hr)
  have hdet := perGram_det_ne_zero_of_facts κ hν ht₁ hbt₂ hF
  have hFin := forceFinite_of hκ P hν hm hb hF htr ht₁ h12 hbt₂
  have hforce := fun j => Leaf4Aux.measurable_force_joint hκ hν ht₁ h12 hd1 P hF hdet tr j
  have h1 := aesm_interaction_path κ hν hm hb hF tr ht₁ h12 hbt₂ hw hInt
  have h2 := aesm_coupling_path hκ hν hm hb hF tr ht₁ h12 hbt₂ hw
  have h3 := aesm_force_sum_path hκ P hν hm hb hF tr htr ht₁ h12 hbt₂ hw
  refine ((h1.add h2).add h3).congr ?_
  refine (ae_restrict_mem measurableSet_Icc).mono fun r hr => ?_
  have hr0 : 0 ≤ r := ht₁.trans hr.1
  have hW : MemLp (compl F w r) 2 (B0579.cellMeasure (dd ν r) m) :=
    memLp_compl F hm0 hν ht₁ hr.1 (hbr r hr) hw
  obtain ⟨hLm, hLb⟩ := hInt r hr _ hW
  have hL : MemLp (interactionTerm tr r (compl F w r)) 2 (B0579.cellMeasure (dd ν r) m) :=
    ⟨hLm, lt_of_le_of_lt hLb (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hW.2)⟩
  have hH : MemLp (complFiniteRankCoupling F r (movH0 κ tr r · (compl F w r))) 2
      (B0579.cellMeasure (dd ν r) m) :=
    ⟨aesm_complFiniteRankCoupling F hr0 (hbr r hr) _,
      lt_of_le_of_lt (hH0 r hr) (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hW.2)⟩
  have hcmf_aesm : ∀ j : Fin 2,
      AEStronglyMeasurable (complModeForce κ P F tr r j) (B0579.cellMeasure (dd ν r) m) := by
    intro j
    have h := (hforce j).comp
      (measurable_const.prodMk measurable_id : Measurable (fun y : ℝ × ℝ => (r, y)))
    exact (by simpa only [Function.comp_def, Leaf4Aux.rho_eq hr] using h :
      Measurable (complModeForce κ P F tr r j)).aestronglyMeasurable
  have hS : ∀ j : Fin 2, MemLp (fun y => ampl F w r j * complModeForce κ P F tr r j y) 2
      (B0579.cellMeasure (dd ν r) m) := fun j =>
    MemLp.const_mul ⟨hcmf_aesm j, lt_top_iff_ne_top.2 (hFin r hr j)⟩ _
  have hSum : MemLp (fun y => ∑ j : Fin 2, ampl F w r j * complModeForce κ P F tr r j y) 2
      (B0579.cellMeasure (dd ν r) m) := by
    have := memLp_finsetSum' (μ := B0579.cellMeasure (dd ν r) m) (p := 2)
      (f := fun j : Fin 2 => fun y => ampl F w r j * complModeForce κ P F tr r j y)
      Finset.univ (fun j _ => hS j)
    convert this using 1
    ext y; simp [Finset.sum_apply]
  dsimp only [Pi.add_apply]
  have hLH : MemLp (fun y' => interactionTerm tr r (compl F w r) y' +
      complFiniteRankCoupling F r (movH0 κ tr r · (compl F w r)) y') 2
      (B0579.cellMeasure (dd ν r) m) := hL.add hH
  have hsrc : complSource κ P F tr w r = fun y =>
      (fun y' => interactionTerm tr r (compl F w r) y' +
        complFiniteRankCoupling F r (movH0 κ tr r · (compl F w r)) y') y +
      (fun y' => ∑ j : Fin 2, ampl F w r j * complModeForce κ P F tr r j y') y := rfl
  rw [hsrc, toL2w_cellZeroExt_add (dd ν r) m hLH hSum,
    toL2w_cellZeroExt_add (dd ν r) m hL hH]

end Leaf2RegularAux

end ComplFreeRateSub

end UnforcedLeray.Short.IIIa
