import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_3_1_1_org.Leaf2Regular.PropCont

/-!
# Leaf (iii) of `ComplDuhamelRep` (`PartIII-a:T21/c3/3/1/1/2/2/4`): `ComplSourceRegular`

Source `the November 2 reference manuscript` (SP) lines 2919-2925, 2937-2958,
2974-2978.

Proves `complSourceRegular`:
1. `complSource ... r ∈ X_{m,d(r)}` for `r ∈ [t₁, t₂]` via unconditional block finiteness
   `Leaf2RegularAux.forceFinite_of` and `Leaf2RegularNeeded.complSource_memLp_of`.
2. `U s t₁ (compl F w t₁)` is a.e. strongly measurable on `cellMeasure (dd ν s) m` from the
   `PropagatorMeas` clause `hU.2.2.2.2` (`Leaf2RegularNeeded.complInit_aesm_of`).
3. For each `s ∈ [t₁, t₂]`, constructs a jointly measurable representative `G` of
   `a(r)⁻² U s r (complSource ... r)` on `(t₁, s] × cell (dd ν s)` by composing the strongly
   continuous `Lp`-valued propagator family `Leaf2RegularAux.uOpCLM` (`PropCont.lean`) with the
   `Planar.L2w m`-measurable zero-extended source path (`SourcePath.lean`), taking a jointly
   measurable `Lp` representative via `JointMeasurableRep.exists_stronglyMeasurable_rep`, and
   patching on the `(volume.restrict (Ioc t₁ s))`-null set where `uLp` differs from `huLp.mk uLp`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Blueprint.Planar
open scoped ENNReal Classical

namespace UnforcedLeray.Short.IIIa

open FrameShortBlockSub ComplCouplingSub PerturbDuhamelSub VariationOfConstantsSub
  ComplMildYAux

namespace ComplFreeRateSub

theorem complSourceRegular (κ : PlanarFrameKernels) (P : PlanarData) (ν m b K : ℝ) (hν : 0 < ν)
    (hF : PerFrameFacts κ ν m b K)
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (t₁ t₂ C_loc C_H0 : ℝ) :
    UnforcedLeray.Short.IIIa.ComplFreeRateSub.ComplSourceRegular κ P ν m b K hν hF tr t₁ t₂
      C_loc C_H0 := by
  intro hD hκ hP hm hb htr ht₁ h12 hbt₂ f w u U hU _hAvail hFlow _hCirc hInt hH0
  have hm0 : (0 : ℝ) ≤ m := by linarith
  have hforce : ∀ r ∈ Icc t₁ t₂, ∀ j : Fin 2,
      AEStronglyMeasurable (complModeForce κ P (periodizedFrame κ ν m b K hν hF) tr r j)
        (B0579.cellMeasure (dd ν r) m) :=
    (hD hκ hP hm hb htr ht₁ h12 hbt₂ f w u hFlow).1
  have hFin : Leaf2RegularNeeded.ForceFinite κ P ν m b K hν hF tr t₁ t₂ :=
    Leaf2RegularAux.forceFinite_of hκ P hν hm hb hF htr ht₁ h12 hbt₂
  have hSrcMem : ∀ r ∈ Icc t₁ t₂,
      MemLp (complSource κ P (periodizedFrame κ ν m b K hν hF) tr w r) 2
        (B0579.cellMeasure (dd ν r) m) :=
    Leaf2RegularNeeded.complSource_memLp_of κ P hν hF tr hm0 ht₁ hbt₂ hFlow hInt hH0 hforce hFin
  have hInitMeas : ∀ s ∈ Icc t₁ t₂,
      AEStronglyMeasurable (U s t₁ (compl (periodizedFrame κ ν m b K hν hF) w t₁))
        (B0579.cellMeasure (dd ν s) m) :=
    Leaf2RegularNeeded.complInit_aesm_of κ hν hF tr hm0 ht₁ h12 hbt₂ hFlow hU.2.2.2.2
  have hSrcPath : AEStronglyMeasurable
      (fun r => toL2w m (fun z => cellZeroExt (dd ν r)
        (complSource κ P (periodizedFrame κ ν m b K hν hF) tr w r) (cToPlane z)))
      (volume.restrict (Icc t₁ t₂)) :=
    Leaf2RegularAux.aesm_complSource_toL2w hκ P hν hm hb hF tr htr ht₁ h12 hbt₂ hFlow hInt hH0
  refine ⟨hSrcMem, fun s hs => ⟨hInitMeas s hs, ?_⟩⟩
  set F := periodizedFrame κ ν m b K hν hF
  set srcPath : ℝ → Planar.L2w m := fun r =>
    toL2w m (fun z => cellZeroExt (dd ν r) (complSource κ P F tr w r) (cToPlane z))
  have hSubIoc : Ioc t₁ s ⊆ Icc t₁ t₂ :=
    Ioc_subset_Icc_self.trans (Icc_subset_Icc_right hs.2)
  have hSrcPath_s : AEStronglyMeasurable srcPath (volume.restrict (Ioc t₁ s)) :=
    hSrcPath.mono_measure (Measure.restrict_mono hSubIoc le_rfl)
  have hOp_aesm : ∀ X : Planar.L2w m,
      AEStronglyMeasurable (fun r => Leaf2RegularAux.uOpCLM hν ht₁ hU hs r X)
        (volume.restrict (Ioc t₁ s)) := fun X =>
    ((Leaf2RegularAux.continuousOn_uOpCLM_apply hm hν ht₁ htr hU hs X).aestronglyMeasurable
      measurableSet_Icc).mono_measure (Measure.restrict_mono Ioc_subset_Icc_self le_rfl)
  have hApply_aesm : AEStronglyMeasurable
      (fun r => Leaf2RegularAux.uOpCLM hν ht₁ hU hs r (srcPath r))
      (volume.restrict (Ioc t₁ s)) :=
    DuhamelAbstractSub.aestronglyMeasurable_clm_apply hOp_aesm hSrcPath_s
  have hClockCont : ContinuousOn (fun r : ℝ => (((clockA ν r) ^ (-2 : ℝ) : ℝ) : ℂ))
      (Icc t₁ s) := by
    have hcA : Continuous (clockA ν) := by unfold clockA; fun_prop
    refine Complex.continuous_ofReal.comp_continuousOn
      (hcA.continuousOn.rpow_const fun r hr => Or.inl ?_)
    have hr0 : 0 ≤ r := ht₁.trans hr.1
    have hpos : 0 < clockA ν r := by unfold clockA; positivity
    exact hpos.ne'
  have hClock_aesm : AEStronglyMeasurable
      (fun r : ℝ => (((clockA ν r) ^ (-2 : ℝ) : ℝ) : ℂ)) (volume.restrict (Ioc t₁ s)) :=
    (hClockCont.aestronglyMeasurable measurableSet_Icc).mono_measure
      (Measure.restrict_mono Ioc_subset_Icc_self le_rfl)
  let uLp : ℝ → Lp ℂ 2 (B0579.cellMeasure (dd ν s) m) := fun r =>
    (((clockA ν r) ^ (-2 : ℝ) : ℝ) : ℂ) • Leaf2RegularAux.uOpCLM hν ht₁ hU hs r (srcPath r)
  have huLp : AEStronglyMeasurable uLp (volume.restrict (Ioc t₁ s)) :=
    hClock_aesm.smul hApply_aesm
  obtain ⟨F₀, hF₀_sm, hF₀_rep⟩ :=
    UnforcedLeray.Infra.JointMeasurableRep.exists_stronglyMeasurable_rep huLp.stronglyMeasurable_mk
  let G : ℝ → ℝ × ℝ → ℂ := fun r y =>
    if r ∈ Ioc t₁ s ∧ uLp r ≠ huLp.mk uLp r then
      (((clockA ν r) ^ (-2 : ℝ) : ℝ) : ℂ) * U s r (complSource κ P F tr w r) y
    else F₀ (r, y)
  refine ⟨G, ?_, ?_⟩
  · intro r hr
    by_cases heq : uLp r = huLp.mk uLp r
    · have hGF₀ : G r = fun y => F₀ (r, y) := by
        funext y; simp [G, heq]
      rw [hGF₀]
      have hrIcc : r ∈ Icc t₁ s := Ioc_subset_Icc_self hr
      have hrIcc2 : r ∈ Icc t₁ t₂ := hSubIoc hr
      have hUae := Leaf2RegularAux.uOpCLM_toL2w_ae hν ht₁ hU hs hrIcc (hSrcMem r hrIcc2)
      have hsmul := Lp.coeFn_smul (((clockA ν r) ^ (-2 : ℝ) : ℝ) : ℂ)
        (Leaf2RegularAux.uOpCLM hν ht₁ hU hs r (srcPath r))
      filter_upwards [hF₀_rep r, hsmul, hUae] with y hy1 hy2 hy3
      rw [hy1, ← heq, hy2, Pi.smul_apply, smul_eq_mul]
      exact congrArg (_ * ·) hy3
    · exact Eventually.of_forall fun y => ite_cond_eq_true _ _ (eq_true ⟨hr, heq⟩)
  · refine hF₀_sm.aestronglyMeasurable.congr ?_
    filter_upwards [(Measure.quasiMeasurePreserving_fst
        (μ := volume.restrict (Ioc t₁ s))
        (ν := B0579.cellMeasure (dd ν s) m)).ae_eq_comp huLp.ae_eq_mk] with p hp
    have hp' : uLp p.1 = huLp.mk uLp p.1 := hp
    simp [Function.uncurry, G, hp']

end ComplFreeRateSub

end UnforcedLeray.Short.IIIa
