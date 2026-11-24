import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G4.IntInt
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G4.GBPoint
import UnforcedLeray.Short.PartIIIb.Proofs.Flat.BclassAeBound
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_kflat_1_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_kflat_2_1

/-!
# `PartIII-b:IIIb-D3/2/G4/4/1`: measurability in `s` of `upperPiece` and `lowerPiece`

Source of record: `the November 2 reference manuscript`, lines 4584-4592, 4637-4693.
-/

set_option autoImplicit false

noncomputable section

open Filter Topology Set MeasureTheory UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif.G4

open ConcreteYF FlatSettingInst

/-- Continuity of `ξ_B` on `(0,∞)` for `B` of class `𝓑_a` and `0 ≤ μ` (source 4584-4592, 4610). -/
theorem xiD_contOn_of_bclass {κ : IIIa.PlanarFrameKernels} {ν m : ℝ}
    [Fact (1 < m)] [Fact (0 < cOf ν)] {tr : UnforcedLeray.B0140.TrainSol ν (cOf ν)}
    (FI : FlatInstData κ ν (cOf ν) m tr) {μ a : ℝ} (hμ : 0 ≤ μ)
    {B : ℝ → Matrix (Fin 3) (Fin 3) ℝ} (hB : IsBclass a ν B) :
    ContinuousOn (xiD FI (μ : ℂ) B) (Ioi 0) := by
  intro s0 hs0
  apply ContinuousAt.continuousWithinAt
  have hs0' : (0 : ℝ) < s0 := hs0
  have hS : s0 < s0 + 1 := by linarith
  -- source bounds on `[0, s0 + 1]`
  obtain ⟨Ch, hCh⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := s0 + 1)).exists_bound_of_continuousOn
    FI.src.H_cont.continuousOn
  obtain ⟨Cr, hCr⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := s0 + 1)).exists_bound_of_continuousOn
    FI.src.R_cont.continuousOn
  set Csrc : ℝ := |Ch| + |Cr| with hCsrc_def
  have hCsrc0 : 0 ≤ Csrc := by positivity
  -- evolution bound on `[0, s0 + 1]`
  obtain ⟨Cs, hCs⟩ := FI.ev.locBdd (s0 + 1)
  have hCs0 : 0 ≤ Cs := (norm_nonneg (FI.ev.U 0 0)).trans (hCs 0 0 le_rfl le_rfl (by linarith))
  -- a.e. bound on `B` from `bclassAeBound`
  have haeB : ∀ᵐ t ∂(volume.restrict (Ioc (0 : ℝ) (s0 + 1))),
      matNorm (B t) ≤ bNorm a B * (Real.exp (a * t) * t ^ (3 / 2 : ℝ)) :=
    ae_restrict_of_ae_restrict_of_subset Ioc_subset_Ioi_self (bclassAeBound a ν B hB)
  set K : ℝ := Cs * (s0 + 1) ^ μ *
      (3 * Csrc * (bNorm a B * (Real.exp (|a| * (s0 + 1)) * (s0 + 1) ^ (3 / 2 : ℝ)))) with hK_def
  have hbN0 : 0 ≤ bNorm a B := ENNReal.toReal_nonneg
  have hK0 : 0 ≤ K := by positivity
  set G : ℝ → ℝ → Xmc (cOf ν) m := fun s t =>
    (Ioc 0 s).indicator (DuhIntegrand FI μ B s) t with hG_def
  have hG_app : ∀ s t, G s t = (Ioc 0 s).indicator (DuhIntegrand FI μ B s) t := fun _ _ => rfl
  have hint : Integrable (fun _ : ℝ => K) (volume.restrict (Ioc (0 : ℝ) (s0 + 1))) :=
    integrableOn_const measure_Ioc_lt_top.ne
  -- measurability of `B` coefficients
  have hBm : ∀ s : ℝ, AEStronglyMeasurable (DuhIntegrand FI μ B s) (volume.restrict (Ioc 0 s)) := by
    intro s
    have hd : AEStronglyMeasurable (fun t : ℝ => Bd (B t)) (volume.restrict (Ioc 0 s)) :=
      (((hB.1 0 0).sub (hB.1 2 2)).div_const 2).aestronglyMeasurable
    have he : AEStronglyMeasurable (fun t : ℝ => Be (B t)) (volume.restrict (Ioc 0 s)) :=
      (((hB.1 0 2).add (hB.1 2 0)).div_const 2).aestronglyMeasurable
    have hb : AEStronglyMeasurable (fun t : ℝ => Bbeta (B t)) (volume.restrict (Ioc 0 s)) :=
      (((hB.1 0 0).add (hB.1 2 2)).div_const 2).aestronglyMeasurable
    exact duhIntegrand_aesm FI μ B s hd he hb
  have hF_meas : ∀ᶠ s in 𝓝 s0, AEStronglyMeasurable (G s) (volume.restrict (Ioc 0 (s0 + 1))) := by
    filter_upwards [Ioo_mem_nhds hs0' hS] with s hs
    have hsub : Ioc (0 : ℝ) s ⊆ Ioc 0 (s0 + 1) := Ioc_subset_Ioc_right hs.2.le
    change AEStronglyMeasurable ((Ioc 0 s).indicator (DuhIntegrand FI μ B s))
      (volume.restrict (Ioc 0 (s0 + 1)))
    rw [aestronglyMeasurable_indicator_iff measurableSet_Ioc,
      Measure.restrict_restrict measurableSet_Ioc, inter_eq_left.2 hsub]
    exact hBm s
  have hbound : ∀ᶠ s in 𝓝 s0, ∀ᵐ t ∂(volume.restrict (Ioc 0 (s0 + 1))), ‖G s t‖ ≤ K := by
    filter_upwards [Ioo_mem_nhds hs0' hS] with s hs
    filter_upwards [haeB, ae_restrict_mem measurableSet_Ioc] with t htB ht
    by_cases hts : t ≤ s
    · have htI : t ∈ Ioc 0 s := ⟨ht.1, hts⟩
      rw [hG_app s t, indicator_of_mem htI]
      unfold DuhIntegrand
      rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht.1, Complex.ofReal_re]
      have htIcc : t ∈ Icc (0 : ℝ) (s0 + 1) := ⟨ht.1.le, ht.2⟩
      have hHt : ‖FI.src.H t‖ ≤ Csrc :=
        (hCh t htIcc).trans ((le_abs_self _).trans (by linarith [abs_nonneg Cr]))
      have hRt : ‖FI.src.R t‖ ≤ Csrc :=
        (hCr t htIcc).trans ((le_abs_self _).trans (by linarith [abs_nonneg Ch]))
      have hg1 : ‖gBD FI B t‖ ≤ 3 * Csrc * matNorm (B t) := by
        refine gBPointwise (actualFlatSetting FI (fun _ => 0) 0) (s0 + 1) Csrc (fun r hr => ?_) B t htIcc
        have hHr : ‖FI.src.H r‖ ≤ Csrc :=
          (hCh r hr).trans ((le_abs_self _).trans (by linarith [abs_nonneg Cr]))
        have hRr : ‖FI.src.R r‖ ≤ Csrc :=
          (hCr r hr).trans ((le_abs_self _).trans (by linarith [abs_nonneg Ch]))
        change ‖FI.src.H r‖ ≤ Csrc ∧ ‖conjX (FI.src.H r)‖ ≤ Csrc ∧ ‖FI.src.R r‖ ≤ Csrc
        rw [norm_conjX]
        exact ⟨hHr, hHr, hRr⟩
      have hexp : Real.exp (a * t) ≤ Real.exp (|a| * (s0 + 1)) := by
        apply Real.exp_le_exp.2
        calc a * t ≤ |a| * t := mul_le_mul_of_nonneg_right (le_abs_self a) ht.1.le
          _ ≤ |a| * (s0 + 1) := mul_le_mul_of_nonneg_left ht.2 (abs_nonneg a)
      have ht32 : t ^ (3 / 2 : ℝ) ≤ (s0 + 1) ^ (3 / 2 : ℝ) :=
        Real.rpow_le_rpow ht.1.le ht.2 (by norm_num)
      have htμ : t ^ μ ≤ (s0 + 1) ^ μ :=
        Real.rpow_le_rpow ht.1.le ht.2 hμ
      have hB_le : matNorm (B t) ≤ bNorm a B * (Real.exp (|a| * (s0 + 1)) * (s0 + 1) ^ (3 / 2 : ℝ)) :=
        htB.trans (mul_le_mul_of_nonneg_left
          (mul_le_mul hexp ht32 (Real.rpow_nonneg ht.1.le _) (Real.exp_pos _).le) hbN0)
      have hg2 : ‖gBD FI B t‖ ≤
          3 * Csrc * (bNorm a B * (Real.exp (|a| * (s0 + 1)) * (s0 + 1) ^ (3 / 2 : ℝ))) :=
        hg1.trans (mul_le_mul_of_nonneg_left hB_le (by positivity))
      have hU : ‖FI.ev.U s t (gBD FI B t)‖ ≤
          Cs * (3 * Csrc * (bNorm a B * (Real.exp (|a| * (s0 + 1)) * (s0 + 1) ^ (3 / 2 : ℝ)))) :=
        ((FI.ev.U s t).le_opNorm _).trans
          (mul_le_mul (hCs s t ht.1.le hts hs.2.le) hg2 (norm_nonneg _) hCs0)
      calc t ^ μ * ‖FI.ev.U s t (gBD FI B t)‖
          ≤ (s0 + 1) ^ μ *
              (Cs * (3 * Csrc * (bNorm a B * (Real.exp (|a| * (s0 + 1)) * (s0 + 1) ^ (3 / 2 : ℝ))))) :=
            mul_le_mul htμ hU (norm_nonneg _) (by positivity)
        _ = K := by rw [hK_def]; ring
    · have hnot : t ∉ Ioc 0 s := fun h => hts h.2
      rw [hG_app s t, indicator_of_notMem hnot, norm_zero]
      exact hK0
  have hcont_pt : ∀ᵐ t ∂(volume.restrict (Ioc 0 (s0 + 1))), ContinuousAt (fun s => G s t) s0 := by
    have hae : ∀ᵐ t ∂(volume.restrict (Ioc 0 (s0 + 1))), t ≠ s0 :=
      ae_restrict_of_ae (((Set.countable_singleton s0).ae_notMem volume).mono fun t ht => ht)
    filter_upwards [ae_restrict_mem measurableSet_Ioc, hae] with t ht hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hopen : {p : ℝ × ℝ | 0 < p.2 ∧ p.2 < p.1} ∈ 𝓝 (s0, t) := by
        apply IsOpen.mem_nhds
        · exact (isOpen_lt continuous_const continuous_snd).inter
            (isOpen_lt continuous_snd continuous_fst)
        · exact ⟨ht.1, hlt⟩
      have hK_nhds : {p : ℝ × ℝ | 0 ≤ p.2 ∧ p.2 ≤ p.1} ∈ 𝓝 (s0, t) :=
        Filter.mem_of_superset hopen (fun p hp => ⟨hp.1.le, hp.2.le⟩)
      have hjc : ContinuousAt (fun p : ℝ × ℝ => FI.ev.U p.1 p.2 (gBD FI B t)) (s0, t) :=
        (FI.ev.jointCont (gBD FI B t)).continuousAt hK_nhds
      have hcs : ContinuousAt (fun s : ℝ => FI.ev.U s t (gBD FI B t)) s0 :=
        hjc.comp (f := fun s : ℝ => (s, t)) (continuous_id.prodMk continuous_const).continuousAt
      refine (hcs.const_smul ((t : ℂ) ^ (μ : ℂ))).congr ?_
      filter_upwards [eventually_gt_nhds hlt] with s hs
      rw [hG_app s t, indicator_of_mem (show t ∈ Ioc 0 s from ⟨ht.1, hs.le⟩)]
      rfl
    · have hev : ∀ᶠ s in 𝓝 s0, s < t := eventually_lt_nhds hgt
      refine (continuousAt_const (y := (0 : Xmc (cOf ν) m))).congr ?_
      filter_upwards [hev] with s hs
      rw [hG_app s t, indicator_of_notMem (fun h => absurd h.2 (not_le.2 hs))]
  have hcontI : ContinuousAt (fun s => ∫ t, G s t ∂(volume.restrict (Ioc 0 (s0 + 1)))) s0 :=
    continuousAt_of_dominated hF_meas hbound hint hcont_pt
  have hEv : (fun s => xiD FI (μ : ℂ) B s) =ᶠ[𝓝 s0]
      (fun s => ((s : ℂ) ^ (-(μ : ℂ))) • ∫ t, G s t ∂(volume.restrict (Ioc 0 (s0 + 1)))) := by
    filter_upwards [Ioo_mem_nhds hs0' hS] with s hs
    have hint_eq : ∫ t, G s t ∂(volume.restrict (Ioc 0 (s0 + 1)))
        = ∫ t in Ioc 0 s, ((t : ℂ) ^ (μ : ℂ)) • (FI.ev.U s t) (gBD FI B t) := by
      change ∫ t, (Ioc 0 s).indicator (DuhIntegrand FI μ B s) t ∂(volume.restrict (Ioc 0 (s0 + 1))) = _
      rw [setIntegral_indicator measurableSet_Ioc,
        Set.inter_eq_right.2 (Ioc_subset_Ioc_right hs.2.le)]
      rfl
    show xiD FI (μ : ℂ) B s = _
    rw [xiD_apply, hint_eq]
  have hcpow : ContinuousAt (fun s : ℝ => (s : ℂ) ^ (-(μ : ℂ))) s0 :=
    Complex.continuousAt_ofReal_cpow_const s0 (-(μ : ℂ)) (Or.inr hs0'.ne')
  exact (hcpow.smul hcontI).congr hEv.symm

/-- Measurability of the `I_T` density for an actual flat setting and a `𝓑_a` matrix family. -/
theorem measurable_itDens_levelFlat {κ : IIIa.PlanarFrameKernels} {ν m : ℝ}
    [Fact (1 < m)] {tr : UnforcedLeray.B0140.TrainSol ν (cOf ν)} (hν : 0 < ν)
    (FI : FlatInstData κ ν (cOf ν) m tr) {χo : ℝ → ℝ} (hχo : IsOutwardCutoff χo) (ε : ℝ)
    {μ a : ℝ} (hμ : 0 ≤ μ) {B : ℝ → Matrix (Fin 3) (Fin 3) ℝ} (hB : IsBclass a ν B) :
    Measurable (fun s => (levelFlat hν FI χo ε).ITdens
      (fun s => (levelFlat hν FI χo ε).Mcell s ((levelFlat hν FI χo ε).xi (μ : ℂ) B s)) s) := by
  have hc : Fact (0 < cOf ν) := ⟨cOf_pos hν⟩
  have hξc : ContinuousOn (xiD FI (μ : ℂ) B) (Ioi 0) := xiD_contOn_of_bclass FI hμ hB
  have hξ0 : ∀ s : ℝ, s ≤ 0 → xiD FI (μ : ℂ) B s = 0 := fun s hs => xiD_nonpos FI (μ : ℂ) B hs
  have hK := kcJointMeasurable (cOf ν) m (xiD FI (μ : ℂ) B) hξc hξ0
  have hKi : ∀ i : Fin 2, Measurable fun p : Chart => kcMer (xiD FI (μ : ℂ) B p.1) p.2 i :=
    fun i => Complex.measurable_re.comp (hK i)
  have hT : Measurable (NearInst.trainMer tr) := NearInst.trainMerMeasurable ν (cOf ν) tr
  have hP : ∀ i : Fin 2, Measurable fun v : Merid => v i := fun i =>
    (EuclideanSpace.proj i : Merid →L[ℝ] ℝ).continuous.measurable
  have hemb : ∀ k : Fin 3, Measurable fun v : Merid => IIIa.embedMerid v k := by
    intro k; fin_cases k
    · exact hP 0
    · exact measurable_const
    · exact hP 1
  have hTe : ∀ k : Fin 3, Measurable fun p : Chart => IIIa.embedMerid (NearInst.trainMer tr p) k :=
    fun k => (hemb k).comp hT
  have hKe : ∀ k : Fin 3, Measurable fun p : Chart =>
      IIIa.embedMerid (kcMer (xiD FI (μ : ℂ) B p.1) p.2) k := by
    intro k; fin_cases k
    · exact hKi 0
    · exact measurable_const
    · exact hKi 1
  have hSym : ∀ i j : Fin 3, Measurable fun p : Chart =>
      IIIa.symOuter (NearInst.trainMer tr p) (kcMer (xiD FI (μ : ℂ) B p.1) p.2) i j :=
    fun i j => ((hTe i).mul (hKe j)).add ((hKe i).mul (hTe j))
  have hF : Measurable fun p : Chart =>
      2 * IIIa.symOuter (NearInst.trainMer tr p) (kcMer (xiD FI (μ : ℂ) B p.1) p.2) 2 2 -
        IIIa.symOuter (NearInst.trainMer tr p) (kcMer (xiD FI (μ : ℂ) B p.1) p.2) 0 0 :=
    (measurable_const.mul (hSym 2 2)).sub (hSym 0 0)
  have hInt : Measurable fun s : ℝ =>
      ∫ x in (Ioo (-cOf ν / 2) (cOf ν / 2)) ×ˢ (univ : Set ℝ),
        (2 * IIIa.symOuter (NearInst.trainMer tr (s, x)) (kcMer (xiD FI (μ : ℂ) B s) x) 2 2 -
          IIIa.symOuter (NearInst.trainMer tr (s, x)) (kcMer (xiD FI (μ : ℂ) B s) x) 0 0) :=
    (hF.stronglyMeasurable.integral_prod_right').measurable
  have hCell : Measurable fun s : ℝ =>
      cellInt (cOf ν) (fun x =>
        2 * IIIa.symOuter (NearInst.trainMer tr (s, x)) (kcMer (xiD FI (μ : ℂ) B s) x) 2 2 -
          IIIa.symOuter (NearInst.trainMer tr (s, x)) (kcMer (xiD FI (μ : ℂ) B s) x) 0 0) :=
    measurable_const.mul hInt
  have hChi : Measurable fun s : ℝ => χo (ν * s) :=
    (hχo.smooth.continuous.comp (continuous_const.mul continuous_id)).measurable
  have hPow : Measurable fun s : ℝ => s ^ (-(3 / 2 : ℝ)) := measurable_id.pow_const _
  exact (hChi.mul hPow).mul hCell

theorem flatPieceMeas (D : SeqData) : PieceMeas D := by
  intro dm dp hst κ _ m _ _ S hS
  have hmu_ev := mu_eventually_mem D hst.omega_ne hst.sigma_pos hst.sigma_lt
  filter_upwards [hS, hmu_ev] with n ⟨FI, hSn⟩ hmu_z
  intro z hz B hB
  have hμ0 : 0 ≤ D.mu n z := by
    have := (hmu_z z hz).1
    linarith [hst.sigma_pos]
  have hν : 0 < nu D n := retNu_pos D.Pl D.σ₀ n
  set d : ℝ → ℝ := fun s => (S n).ITdens
    (fun s => (S n).Mcell s ((S n).xi (D.mu n z : ℂ) B s)) s with hd_def
  have hd_meas : Measurable d := by
    rw [hd_def, hSn]
    exact measurable_itDens_levelFlat hν FI D.K.hχo (retEps D.Pl D.σ₀ n) hμ0 hB
  let uo : ℝ := nu D n ^ (-(3 / 2 : ℝ))
  have hup_eq : upperPiece D S n z B = (Ici uo).indicator d := by
    funext s
    unfold upperPiece FlatSetting.ITdens
    by_cases hs : nu D n ^ (-(3 / 2 : ℝ)) ≤ s
    · rw [indicator_of_mem (mem_Ici.2 hs)]
      simp [hs, hd_def, FlatSetting.ITdens]
    · rw [indicator_of_notMem (fun h => hs (mem_Ici.1 h))]
      simp [hs, cellInt]
  have hlo_eq : lowerPiece D S n z B = (Iio uo).indicator d := by
    funext s
    unfold lowerPiece FlatSetting.ITdens
    by_cases hs : s < nu D n ^ (-(3 / 2 : ℝ))
    · rw [indicator_of_mem (mem_Iio.2 hs)]
      simp [hs, hd_def, FlatSetting.ITdens]
    · rw [indicator_of_notMem (fun h => hs (mem_Iio.1 h))]
      simp [hs, cellInt]
  rw [hup_eq, hlo_eq]
  exact ⟨(hd_meas.indicator measurableSet_Ici).aestronglyMeasurable,
    (hd_meas.indicator measurableSet_Iio).aestronglyMeasurable⟩

end UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif.G4
