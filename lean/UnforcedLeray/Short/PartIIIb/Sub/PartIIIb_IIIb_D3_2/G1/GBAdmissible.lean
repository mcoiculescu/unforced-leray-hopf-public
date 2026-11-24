import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G1.Org
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G4.GBPoint
import UnforcedLeray.Short.PartIIIb.Proofs.Flat.BclassAeBound
import UnforcedLeray.Short.PartIIIb.Proofs.Flat.FpmInvBound

/-!
# `ORG:D3/2/G1/4`: admissibility of `g_B` (`gBAdmissible`)

Source of record: `the November 2 reference manuscript` (73 pages), lines
4463-4487, 4597-4612.
-/

set_option autoImplicit false

noncomputable section

open Filter Topology Set MeasureTheory

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif.G1

open ConcreteYF

private lemma gB_eq_zero_of_B_eq_zero (S : FlatSetting) {B : ℝ → Matrix (Fin 3) (Fin 3) ℝ} {t : ℝ}
    (hBt : B t = 0) : S.gB B t = 0 := by
  simp [FlatSetting.gB, hBt, Bd, Be, Bbeta]

private lemma measurable_c1 {B : ℝ → Matrix (Fin 3) (Fin 3) ℝ}
    (hB : ∀ i j, Measurable (fun s => B s i j)) :
    Measurable (fun t => -(1 / 2 : ℂ) * (((Bd (B t) : ℝ) : ℂ) - Complex.I * ((Be (B t) : ℝ) : ℂ))) := by
  have hBd : Measurable (fun t => Bd (B t)) := ((hB 0 0).sub (hB 2 2)).div_const 2
  have hBe : Measurable (fun t => Be (B t)) := ((hB 0 2).add (hB 2 0)).div_const 2
  exact ((Complex.measurable_ofReal.comp hBd).sub
    ((Complex.measurable_ofReal.comp hBe).const_mul Complex.I)).const_mul (-(1 / 2 : ℂ))

private lemma measurable_c2 {B : ℝ → Matrix (Fin 3) (Fin 3) ℝ}
    (hB : ∀ i j, Measurable (fun s => B s i j)) :
    Measurable (fun t => -(1 / 2 : ℂ) * (((Bd (B t) : ℝ) : ℂ) + Complex.I * ((Be (B t) : ℝ) : ℂ))) := by
  have hBd : Measurable (fun t => Bd (B t)) := ((hB 0 0).sub (hB 2 2)).div_const 2
  have hBe : Measurable (fun t => Be (B t)) := ((hB 0 2).add (hB 2 0)).div_const 2
  exact ((Complex.measurable_ofReal.comp hBd).add
    ((Complex.measurable_ofReal.comp hBe).const_mul Complex.I)).const_mul (-(1 / 2 : ℂ))

private lemma measurable_c3 {B : ℝ → Matrix (Fin 3) (Fin 3) ℝ}
    (hB : ∀ i j, Measurable (fun s => B s i j)) :
    Measurable (fun t => ((Bbeta (B t) : ℝ) : ℂ)) := by
  have hBb : Measurable (fun t => Bbeta (B t)) := ((hB 0 0).add (hB 2 2)).div_const 2
  exact Complex.measurable_ofReal.comp hBb

private lemma continuousOn_U_apply {ν c m : ℝ} [Fact (1 < m)]
    {tr : UnforcedLeray.B0140.TrainSol ν c}
    (ev : FlatSettingInst.TrainEvolution m tr) (H : ℝ) {f : ℝ → FlatSettingInst.Xmc c m}
    (hf : Continuous f) :
    ContinuousOn (fun t => ev.U H t (f t)) (Icc 0 H) := by
  obtain ⟨Cu, hCu⟩ := ev.locBdd H
  set M : ℝ := max Cu 0
  intro t₀ ht₀
  rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
  have hU_t0 : ContinuousWithinAt (fun t => ev.U H t (f t₀)) (Icc 0 H) t₀ := by
    have hpair : ContinuousWithinAt (fun t : ℝ => (H, t)) (Icc 0 H) t₀ :=
      (continuous_const.prodMk continuous_id).continuousWithinAt
    have hmaps : MapsTo (fun t : ℝ => (H, t)) (Icc 0 H) {p : ℝ × ℝ | 0 ≤ p.2 ∧ p.2 ≤ p.1} :=
      fun t ht => ⟨ht.1, ht.2⟩
    exact ((ev.jointCont (f t₀)).continuousWithinAt ⟨ht₀.1, ht₀.2⟩).comp hpair hmaps
  have hlim1 : Tendsto (fun t => M * ‖f t - f t₀‖ + ‖ev.U H t (f t₀) - ev.U H t₀ (f t₀)‖)
      (𝓝[Icc 0 H] t₀) (𝓝 0) := by
    have hf0 : Tendsto (fun t => ‖f t - f t₀‖) (𝓝[Icc 0 H] t₀) (𝓝 0) :=
      tendsto_iff_norm_sub_tendsto_zero.1 hf.continuousWithinAt
    have hu0 : Tendsto (fun t => ‖ev.U H t (f t₀) - ev.U H t₀ (f t₀)‖) (𝓝[Icc 0 H] t₀) (𝓝 0) :=
      tendsto_iff_norm_sub_tendsto_zero.1 hU_t0
    simpa using (hf0.const_mul M).add hu0
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim1
  filter_upwards [self_mem_nhdsWithin] with t ht
  have hsplit : ev.U H t (f t) - ev.U H t₀ (f t₀) =
      ev.U H t (f t - f t₀) + (ev.U H t (f t₀) - ev.U H t₀ (f t₀)) := by
    rw [map_sub, sub_add_sub_cancel]
  rw [hsplit]
  refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
  refine (ContinuousLinearMap.le_opNorm (ev.U H t) (f t - f t₀)).trans ?_
  exact mul_le_mul_of_nonneg_right ((hCu H t ht.1 ht.2 le_rfl).trans (le_max_left _ _))
    (norm_nonneg _)

private lemma aestronglyMeasurable_U_gB {ν c m : ℝ} [Fact (1 < m)] [Fact (0 < c)]
    {κ : IIIa.PlanarFrameKernels} {tr : UnforcedLeray.B0140.TrainSol ν c}
    (FI : FlatSettingInst.FlatInstData κ ν c m tr) (χo : ℝ → ℝ) (ε H : ℝ) (μ : ℂ)
    {B : ℝ → Matrix (Fin 3) (Fin 3) ℝ} (hB : ∀ i j, Measurable (fun s => B s i j)) :
    AEStronglyMeasurable
      (fun t : ℝ => ((t : ℂ) ^ μ) •
        ((FlatSettingInst.actualFlatSetting FI χo ε).pk.Uev H t
          ((FlatSettingInst.actualFlatSetting FI χo ε).gB B t)))
      (volume.restrict (Ioc 0 H)) := by
  set μr := volume.restrict (Ioc 0 H)
  have hUH : AEStronglyMeasurable (fun t => FI.ev.U H t (FI.src.H t)) μr :=
    ((continuousOn_U_apply FI.ev H FI.src.H_cont).mono Ioc_subset_Icc_self).aestronglyMeasurable
      measurableSet_Ioc
  have hUHb : AEStronglyMeasurable (fun t => FI.ev.U H t (FlatSettingInst.conjX (FI.src.H t))) μr :=
    ((continuousOn_U_apply FI.ev H (FlatSettingInst.continuous_conjX.comp FI.src.H_cont)).mono
      Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  have hUR : AEStronglyMeasurable (fun t => FI.ev.U H t (FI.src.R t)) μr :=
    ((continuousOn_U_apply FI.ev H FI.src.R_cont).mono Ioc_subset_Icc_self).aestronglyMeasurable
      measurableSet_Ioc
  have hc1 := (measurable_c1 hB).aestronglyMeasurable (μ := μr)
  have hc2 := (measurable_c2 hB).aestronglyMeasurable (μ := μr)
  have hc3 := (measurable_c3 hB).aestronglyMeasurable (μ := μr)
  have hw : AEStronglyMeasurable (fun t : ℝ => (t : ℂ) ^ μ) μr :=
    (Complex.measurable_ofReal.pow_const μ).aestronglyMeasurable
  have hU_gB : AEStronglyMeasurable
      (fun t : ℝ => (FlatSettingInst.actualFlatSetting FI χo ε).pk.Uev H t
        ((FlatSettingInst.actualFlatSetting FI χo ε).gB B t)) μr := by
    have heq : (fun t : ℝ => (FlatSettingInst.actualFlatSetting FI χo ε).pk.Uev H t
          ((FlatSettingInst.actualFlatSetting FI χo ε).gB B t)) =
        fun t : ℝ =>
          (-(1 / 2 : ℂ) * (((Bd (B t) : ℝ) : ℂ) - Complex.I * ((Be (B t) : ℝ) : ℂ))) •
              FI.ev.U H t (FI.src.H t)
            + (-(1 / 2 : ℂ) * (((Bd (B t) : ℝ) : ℂ) + Complex.I * ((Be (B t) : ℝ) : ℂ))) •
              FI.ev.U H t (FlatSettingInst.conjX (FI.src.H t))
            - (((Bbeta (B t) : ℝ) : ℂ)) • FI.ev.U H t (FI.src.R t) := by
      funext t
      change FI.ev.U H t (FlatSettingInst.gBD FI B t) = _
      rw [FlatSettingInst.gBD_apply]
      simp only [map_sub, map_add, map_smul]
    rw [heq]
    exact ((hc1.smul hUH).add (hc2.smul hUHb)).sub (hc3.smul hUR)
  exact hw.smul hU_gB

private lemma stronglyMeasurable_gB {ν c m : ℝ} [Fact (1 < m)] [Fact (0 < c)]
    {κ : IIIa.PlanarFrameKernels} {tr : UnforcedLeray.B0140.TrainSol ν c}
    (FI : FlatSettingInst.FlatInstData κ ν c m tr) (χo : ℝ → ℝ) (ε : ℝ)
    {B : ℝ → Matrix (Fin 3) (Fin 3) ℝ} (hB : ∀ i j, Measurable (fun s => B s i j)) :
    StronglyMeasurable ((FlatSettingInst.actualFlatSetting FI χo ε).gB B) := by
  have hH : StronglyMeasurable FI.src.H := FI.src.H_cont.stronglyMeasurable
  have hHb : StronglyMeasurable (fun t => FlatSettingInst.conjX (FI.src.H t)) :=
    (FlatSettingInst.continuous_conjX.comp FI.src.H_cont).stronglyMeasurable
  have hR : StronglyMeasurable FI.src.R := FI.src.R_cont.stronglyMeasurable
  have hc1 := (measurable_c1 hB).stronglyMeasurable
  have hc2 := (measurable_c2 hB).stronglyMeasurable
  have hc3 := (measurable_c3 hB).stronglyMeasurable
  unfold FlatSetting.gB
  exact ((hc1.smul hH).add (hc2.smul hHb)).sub (hc3.smul hR)

private lemma measurable_Fpm_inv_bool (j : Bool) (lam κ : ℂ) (ν : ℝ) :
    Measurable (fun t : ℝ => (Fpm j lam κ ν t 0)⁻¹) :=
  FlatAmp.measurable_Fpm_inv (if j then lam else (starRingEnd ℂ) lam)
    (if j then κ else (starRingEnd ℂ) κ) ν

private lemma measurable_ell_gB {ν c m : ℝ} [Fact (1 < m)] [Fact (0 < c)]
    {κ : IIIa.PlanarFrameKernels} {tr : UnforcedLeray.B0140.TrainSol ν c}
    (FI : FlatSettingInst.FlatInstData κ ν c m tr) (χo : ℝ → ℝ) (ε : ℝ) (j : Bool)
    {B : ℝ → Matrix (Fin 3) (Fin 3) ℝ} (hB : ∀ i j, Measurable (fun s => B s i j)) :
    Measurable (fun t =>
      ((FlatSettingInst.actualFlatSetting FI χo ε).pk.ell j t)
        ((FlatSettingInst.actualFlatSetting FI χo ε).gB B t)) := by
  have hpH : Measurable (fun t => FI.pair.ell j t (FI.src.H t)) :=
    ((FI.pair.ell_cont j).clm_apply FI.src.H_cont).measurable
  have hpHb : Measurable (fun t => FI.pair.ell j t (FlatSettingInst.conjX (FI.src.H t))) :=
    ((FI.pair.ell_cont j).clm_apply (FlatSettingInst.continuous_conjX.comp FI.src.H_cont)).measurable
  have hpR : Measurable (fun t => FI.pair.ell j t (FI.src.R t)) :=
    ((FI.pair.ell_cont j).clm_apply FI.src.R_cont).measurable
  have hc1 := measurable_c1 hB
  have hc2 := measurable_c2 hB
  have hc3 := measurable_c3 hB
  have heq : (fun t => ((FlatSettingInst.actualFlatSetting FI χo ε).pk.ell j t)
        ((FlatSettingInst.actualFlatSetting FI χo ε).gB B t)) =
      fun t =>
        (-(1 / 2 : ℂ) * (((Bd (B t) : ℝ) : ℂ) - Complex.I * ((Be (B t) : ℝ) : ℂ))) *
            FI.pair.ell j t (FI.src.H t)
          + (-(1 / 2 : ℂ) * (((Bd (B t) : ℝ) : ℂ) + Complex.I * ((Be (B t) : ℝ) : ℂ))) *
            FI.pair.ell j t (FlatSettingInst.conjX (FI.src.H t))
          - ((Bbeta (B t) : ℝ) : ℂ) * FI.pair.ell j t (FI.src.R t) := by
    funext t
    change FI.pair.ell j t (FlatSettingInst.gBD FI B t) = _
    rw [FlatSettingInst.gBD_apply]
    simp only [map_sub, map_add, map_smul, smul_eq_mul]
  rw [heq]
  exact ((hc1.mul hpH).add (hc2.mul hpHb)).sub (hc3.mul hpR)

private lemma ell_gB_bound (M : Matrix (Fin 3) (Fin 3) ℝ) (z1 z2 z3 : ℂ) (C : ℝ)
    (hz1 : ‖z1‖ ≤ C) (hz2 : ‖z2‖ ≤ C) (hz3 : ‖z3‖ ≤ C) :
    ‖(-(1 / 2 : ℂ) * (((Bd M : ℝ) : ℂ) - Complex.I * ((Be M : ℝ) : ℂ))) * z1
      + (-(1 / 2 : ℂ) * (((Bd M : ℝ) : ℂ) + Complex.I * ((Be M : ℝ) : ℂ))) * z2
      - ((Bbeta M : ℝ) : ℂ) * z3‖ ≤ 3 * C * matNorm M := by
  have hm0 : 0 ≤ matNorm M := FlatAmp.matNorm_nonneg M
  have hc1 : ‖-(1 / 2 : ℂ) * (((Bd M : ℝ) : ℂ) - Complex.I * ((Be M : ℝ) : ℂ))‖ ≤ matNorm M := by
    rw [norm_mul, show ‖(-(1 / 2 : ℂ))‖ = 1 / 2 by norm_num]
    linarith [FlatAmp.norm_dmie_le M, norm_nonneg (((Bd M : ℝ) : ℂ) - Complex.I * ((Be M : ℝ) : ℂ))]
  have hc2 : ‖-(1 / 2 : ℂ) * (((Bd M : ℝ) : ℂ) + Complex.I * ((Be M : ℝ) : ℂ))‖ ≤ matNorm M := by
    rw [norm_mul, show ‖(-(1 / 2 : ℂ))‖ = 1 / 2 by norm_num]
    linarith [FlatAmp.norm_dpie_le M, norm_nonneg (((Bd M : ℝ) : ℂ) + Complex.I * ((Be M : ℝ) : ℂ))]
  have hc3 : ‖((Bbeta M : ℝ) : ℂ)‖ ≤ matNorm M := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact FlatAmp.abs_beta_le M
  have t1 : ‖(-(1 / 2 : ℂ) * (((Bd M : ℝ) : ℂ) - Complex.I * ((Be M : ℝ) : ℂ))) * z1‖ ≤
      matNorm M * C := by
    rw [norm_mul]; exact mul_le_mul hc1 hz1 (norm_nonneg _) hm0
  have t2 : ‖(-(1 / 2 : ℂ) * (((Bd M : ℝ) : ℂ) + Complex.I * ((Be M : ℝ) : ℂ))) * z2‖ ≤
      matNorm M * C := by
    rw [norm_mul]; exact mul_le_mul hc2 hz2 (norm_nonneg _) hm0
  have t3 : ‖((Bbeta M : ℝ) : ℂ) * z3‖ ≤ matNorm M * C := by
    rw [norm_mul]; exact mul_le_mul hc3 hz3 (norm_nonneg _) hm0
  have hsub := norm_sub_le
    ((-(1 / 2 : ℂ) * (((Bd M : ℝ) : ℂ) - Complex.I * ((Be M : ℝ) : ℂ))) * z1
      + (-(1 / 2 : ℂ) * (((Bd M : ℝ) : ℂ) + Complex.I * ((Be M : ℝ) : ℂ))) * z2)
    (((Bbeta M : ℝ) : ℂ) * z3)
  have hadd := norm_add_le
    ((-(1 / 2 : ℂ) * (((Bd M : ℝ) : ℂ) - Complex.I * ((Be M : ℝ) : ℂ))) * z1)
    ((-(1 / 2 : ℂ) * (((Bd M : ℝ) : ℂ) + Complex.I * ((Be M : ℝ) : ℂ))) * z2)
  linarith

private lemma ae_norm_ell_gB_le {ν c m : ℝ} [Fact (1 < m)] [Fact (0 < c)]
    {κ : IIIa.PlanarFrameKernels} {tr : UnforcedLeray.B0140.TrainSol ν c}
    (FI : FlatSettingInst.FlatInstData κ ν c m tr) (χo : ℝ → ℝ) (ε a T : ℝ) (ha : 0 < a)
    (j : Bool) {B : ℝ → Matrix (Fin 3) (Fin 3) ℝ} (hB : IsBclass a ν B) :
    ∃ Cl : ℝ, 0 ≤ Cl ∧ ∀ᵐ t ∂(volume.restrict (Ioc 0 T)),
      ‖((FlatSettingInst.actualFlatSetting FI χo ε).pk.ell j t)
        ((FlatSettingInst.actualFlatSetting FI χo ε).gB B t)‖ ≤ Cl := by
  obtain ⟨C1, hC1⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc 0 T) ((FI.pair.ell_cont j).clm_apply FI.src.H_cont).continuousOn
  obtain ⟨C2, hC2⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc 0 T) ((FI.pair.ell_cont j).clm_apply
      (FlatSettingInst.continuous_conjX.comp FI.src.H_cont)).continuousOn
  obtain ⟨C3, hC3⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc 0 T) ((FI.pair.ell_cont j).clm_apply FI.src.R_cont).continuousOn
  set Csrc : ℝ := max (max (max C1 C2) C3) 0
  have hCsrc0 : 0 ≤ Csrc := le_max_right _ _
  set Tpos : ℝ := max T 0
  have hTpos : 0 ≤ Tpos := le_max_right _ _
  set Cl : ℝ := 3 * Csrc * (bNorm a B * (Real.exp (a * Tpos) * Tpos ^ (3 / 2 : ℝ)))
  have hbN : 0 ≤ bNorm a B := ENNReal.toReal_nonneg
  have hCl0 : 0 ≤ Cl := by positivity
  refine ⟨Cl, hCl0, ?_⟩
  have hae : ∀ᵐ t ∂(volume.restrict (Ioc (0 : ℝ) T)),
      matNorm (B t) ≤ bNorm a B * (Real.exp (a * t) * t ^ (3 / 2 : ℝ)) :=
    ae_restrict_of_ae_restrict_of_subset Ioc_subset_Ioi_self (bclassAeBound a ν B hB)
  filter_upwards [hae, ae_restrict_mem measurableSet_Ioc] with t hm ht
  have htIcc : t ∈ Icc (0 : ℝ) T := ⟨ht.1.le, ht.2⟩
  have htTpos : t ≤ Tpos := ht.2.trans (le_max_left _ _)
  have hz1 : ‖FI.pair.ell j t (FI.src.H t)‖ ≤ Csrc :=
    (hC1 t htIcc).trans (((le_max_left C1 C2).trans (le_max_left _ C3)).trans (le_max_left _ 0))
  have hz2 : ‖FI.pair.ell j t (FlatSettingInst.conjX (FI.src.H t))‖ ≤ Csrc :=
    (hC2 t htIcc).trans (((le_max_right C1 C2).trans (le_max_left _ C3)).trans (le_max_left _ 0))
  have hz3 : ‖FI.pair.ell j t (FI.src.R t)‖ ≤ Csrc :=
    (hC3 t htIcc).trans ((le_max_right _ C3).trans (le_max_left _ 0))
  have heq : ((FlatSettingInst.actualFlatSetting FI χo ε).pk.ell j t)
      ((FlatSettingInst.actualFlatSetting FI χo ε).gB B t) =
      (-(1 / 2 : ℂ) * (((Bd (B t) : ℝ) : ℂ) - Complex.I * ((Be (B t) : ℝ) : ℂ))) *
          FI.pair.ell j t (FI.src.H t)
        + (-(1 / 2 : ℂ) * (((Bd (B t) : ℝ) : ℂ) + Complex.I * ((Be (B t) : ℝ) : ℂ))) *
          FI.pair.ell j t (FlatSettingInst.conjX (FI.src.H t))
        - ((Bbeta (B t) : ℝ) : ℂ) * FI.pair.ell j t (FI.src.R t) := by
    change FI.pair.ell j t (FlatSettingInst.gBD FI B t) = _
    rw [FlatSettingInst.gBD_apply]
    simp only [map_sub, map_add, map_smul, smul_eq_mul]
  rw [heq]
  have h1 := ell_gB_bound (B t) _ _ _ Csrc hz1 hz2 hz3
  have hexp : Real.exp (a * t) ≤ Real.exp (a * Tpos) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left htTpos ha.le)
  have hpow : t ^ (3 / 2 : ℝ) ≤ Tpos ^ (3 / 2 : ℝ) :=
    Real.rpow_le_rpow ht.1.le htTpos (by norm_num)
  have hm' : matNorm (B t) ≤ bNorm a B * (Real.exp (a * Tpos) * Tpos ^ (3 / 2 : ℝ)) :=
    hm.trans (mul_le_mul_of_nonneg_left
      (mul_le_mul hexp hpow (Real.rpow_nonneg ht.1.le _) (Real.exp_pos _).le) hbN)
  exact h1.trans (mul_le_mul_of_nonneg_left hm' (by positivity))

private lemma ae_norm_gB_le {ν c m : ℝ} [Fact (1 < m)] [Fact (0 < c)]
    {κ : IIIa.PlanarFrameKernels} {tr : UnforcedLeray.B0140.TrainSol ν c}
    (FI : FlatSettingInst.FlatInstData κ ν c m tr) (χo : ℝ → ℝ) (ε a T : ℝ) (ha : 0 < a)
    {B : ℝ → Matrix (Fin 3) (Fin 3) ℝ} (hB : IsBclass a ν B) :
    ∃ Cg : ℝ, 0 ≤ Cg ∧ ∀ᵐ t ∂(volume.restrict (Ioc 0 T)),
      ‖(FlatSettingInst.actualFlatSetting FI χo ε).gB B t‖ ≤ Cg := by
  obtain ⟨CH, hCH⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc 0 T) FI.src.H_cont.continuousOn
  obtain ⟨CR, hCR⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc 0 T) FI.src.R_cont.continuousOn
  set Csrc : ℝ := max (max CH CR) 0
  have hCsrc0 : 0 ≤ Csrc := le_max_right _ _
  have hC_Sn : ∀ t ∈ Icc (0 : ℝ) T,
      ‖(FlatSettingInst.actualFlatSetting FI χo ε).Hper t‖ ≤ Csrc ∧
      ‖(FlatSettingInst.actualFlatSetting FI χo ε).conjX
        ((FlatSettingInst.actualFlatSetting FI χo ε).Hper t)‖ ≤ Csrc ∧
      ‖(FlatSettingInst.actualFlatSetting FI χo ε).Rper t‖ ≤ Csrc := by
    intro t ht
    change ‖FI.src.H t‖ ≤ Csrc ∧ ‖FlatSettingInst.conjX (FI.src.H t)‖ ≤ Csrc ∧ ‖FI.src.R t‖ ≤ Csrc
    rw [FlatSettingInst.norm_conjX]
    have h1 : ‖FI.src.H t‖ ≤ Csrc :=
      (hCH t ht).trans ((le_max_left CH CR).trans (le_max_left _ _))
    have h2 : ‖FI.src.R t‖ ≤ Csrc :=
      (hCR t ht).trans ((le_max_right CH CR).trans (le_max_left _ _))
    exact ⟨h1, h1, h2⟩
  set Tpos : ℝ := max T 0
  have hTpos : 0 ≤ Tpos := le_max_right _ _
  set Cg : ℝ := 3 * Csrc * (bNorm a B * (Real.exp (a * Tpos) * Tpos ^ (3 / 2 : ℝ)))
  have hbN : 0 ≤ bNorm a B := ENNReal.toReal_nonneg
  have hCg0 : 0 ≤ Cg := by positivity
  refine ⟨Cg, hCg0, ?_⟩
  have hae : ∀ᵐ t ∂(volume.restrict (Ioc (0 : ℝ) T)),
      matNorm (B t) ≤ bNorm a B * (Real.exp (a * t) * t ^ (3 / 2 : ℝ)) :=
    ae_restrict_of_ae_restrict_of_subset Ioc_subset_Ioi_self (bclassAeBound a ν B hB)
  filter_upwards [hae, ae_restrict_mem measurableSet_Ioc] with t hm ht
  have htIcc : t ∈ Icc (0 : ℝ) T := ⟨ht.1.le, ht.2⟩
  have htTpos : t ≤ Tpos := ht.2.trans (le_max_left _ _)
  have hgB := G4.gBPointwise (FlatSettingInst.actualFlatSetting FI χo ε) T Csrc hC_Sn B t htIcc
  have hexp : Real.exp (a * t) ≤ Real.exp (a * Tpos) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left htTpos ha.le)
  have hpow : t ^ (3 / 2 : ℝ) ≤ Tpos ^ (3 / 2 : ℝ) :=
    Real.rpow_le_rpow ht.1.le htTpos (by norm_num)
  have hm' : matNorm (B t) ≤ bNorm a B * (Real.exp (a * Tpos) * Tpos ^ (3 / 2 : ℝ)) :=
    hm.trans (mul_le_mul_of_nonneg_left
      (mul_le_mul hexp hpow (Real.rpow_nonneg ht.1.le _) (Real.exp_pos _).le) hbN)
  exact hgB.trans (mul_le_mul_of_nonneg_left hm' (by positivity))

/-- **`g_B` is an admissible Duhamel forcing** for the young source theorem at `α = 1.1`
(source 4463-4487, 4597-4612). -/
theorem gBAdmissible (D : SeqData) : G1.GBAdmissible D := by
  intro dm dp hst κ _ m _ _ S hS
  have hmu_ev := mu_eventually_mem D hst.omega_ne hst.sigma_pos hst.sigma_lt
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hS.and hmu_ev)
  refine ⟨N, fun n hn z hz B hB => ?_⟩
  obtain ⟨⟨FI, hSn⟩, hmu_z⟩ := hN n hn
  have hmu : D.mu n z ∈ Icc (D.σ₀ / 2) ((D.σ₀ + 1 / 4) / 2) := hmu_z z hz
  set ν : ℝ := nu D n
  set μ : ℝ := D.mu n z
  have hν : 0 < ν := retNu_pos D.Pl D.σ₀ n
  have hμ0 : 0 ≤ μ := by
    have := hst.sigma_pos
    linarith [hmu.1]
  have : Fact (0 < cOf ν) := ⟨cOf_pos hν⟩
  have hSn' : S n = FlatSettingInst.actualFlatSetting FI D.K.χo (retEps D.Pl D.σ₀ n) := hSn
  -- 1 & 2: support of g_B
  have hsupp1 : ∀ t, 1.1 / ν < t → (S n).gB B t = 0 := by
    intro t ht
    exact gB_eq_zero_of_B_eq_zero (S n) (hB.2.2.2.1 t (fun h => not_lt.2 h.2.le ht))
  have hsupp2 : ∀ t, t ≤ 0 → (S n).gB B t = 0 := by
    intro t ht
    exact gB_eq_zero_of_B_eq_zero (S n) (hB.2.2.2.1 t (fun h => not_lt.2 ht h.1))
  -- 3: Duhamel integrand on (0, 2/ν]
  have hint1 : Integrable (fun t : ℝ => ((t : ℂ) ^ (μ : ℂ)) •
      ((S n).pk.Uev (2 / ν) t ((S n).gB B t))) (volume.restrict (Ioc 0 (2 / ν))) := by
    rw [hSn']
    set H : ℝ := 2 / ν
    have hH0 : 0 ≤ H := by positivity
    obtain ⟨Cu, hCu⟩ := FI.ev.locBdd H
    obtain ⟨Cg, hCg0, hCg⟩ := ae_norm_gB_le FI D.K.χo (retEps D.Pl D.σ₀ n) D.K.as H hst.as_pos hB
    refine IntegrableOn.of_bound measure_Ioc_lt_top
      (aestronglyMeasurable_U_gB FI D.K.χo (retEps D.Pl D.σ₀ n) H (μ : ℂ) hB.1)
      (H ^ μ * (max Cu 0 * Cg)) ?_
    filter_upwards [hCg, ae_restrict_mem measurableSet_Ioc] with t hg ht
    rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht.1, Complex.ofReal_re]
    have htpow : t ^ μ ≤ H ^ μ := Real.rpow_le_rpow ht.1.le ht.2 hμ0
    have hU : ‖(FlatSettingInst.actualFlatSetting FI D.K.χo (retEps D.Pl D.σ₀ n)).pk.Uev H t
        ((FlatSettingInst.actualFlatSetting FI D.K.χo (retEps D.Pl D.σ₀ n)).gB B t)‖ ≤
        max Cu 0 * Cg := by
      refine (ContinuousLinearMap.le_opNorm (FI.ev.U H t) _).trans ?_
      exact mul_le_mul ((hCu H t ht.1.le ht.2 le_rfl).trans (le_max_left _ _)) hg
        (norm_nonneg _) (le_max_right _ _)
    exact mul_le_mul htpow hU (norm_nonneg _) (Real.rpow_nonneg hH0 _)
  -- 4 & 5: amplitude integrands on (0, 1.1/ν] for j = true, false
  have hint_amp : ∀ j : Bool, Integrable (fun t : ℝ => ((t : ℂ) ^ (μ : ℂ)) *
      (Fpm j D.Pl.eigenvalue D.Pl.kappa ν t 0)⁻¹ * ((S n).pk.ell j t) ((S n).gB B t))
      (volume.restrict (Ioc 0 (1.1 / ν))) := by
    intro j
    rw [hSn']
    set Tf : ℝ := 1.1 / ν
    have hTf0 : 0 ≤ Tf := by positivity
    have hlam_j : 0 < (if j then D.Pl.eigenvalue else (starRingEnd ℂ) D.Pl.eigenvalue).re := by
      cases j <;> simpa using hst.gamma_pos
    obtain ⟨Cf, hCf⟩ := fpmInvBound
      (if j then D.Pl.eigenvalue else (starRingEnd ℂ) D.Pl.eigenvalue)
      (if j then D.Pl.kappa else (starRingEnd ℂ) D.Pl.kappa) hlam_j
    obtain ⟨Cl, hCl0, hCl⟩ := ae_norm_ell_gB_le FI D.K.χo (retEps D.Pl D.σ₀ n) D.K.as Tf
      hst.as_pos j hB
    have hmeas : Measurable (fun t : ℝ => ((t : ℂ) ^ (μ : ℂ)) *
        (Fpm j D.Pl.eigenvalue D.Pl.kappa ν t 0)⁻¹ *
        ((FlatSettingInst.actualFlatSetting FI D.K.χo (retEps D.Pl D.σ₀ n)).pk.ell j t)
          ((FlatSettingInst.actualFlatSetting FI D.K.χo (retEps D.Pl D.σ₀ n)).gB B t)) :=
      ((Complex.measurable_ofReal.pow_const (μ : ℂ)).mul
        (measurable_Fpm_inv_bool j D.Pl.eigenvalue D.Pl.kappa ν)).mul
        (measurable_ell_gB FI D.K.χo (retEps D.Pl D.σ₀ n) j hB.1)
    refine IntegrableOn.of_bound measure_Ioc_lt_top hmeas.aestronglyMeasurable
      (Tf ^ μ * max Cf 0 * Cl) ?_
    filter_upwards [hCl, ae_restrict_mem measurableSet_Ioc] with t hl ht
    rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht.1, Complex.ofReal_re]
    have htpow : t ^ μ ≤ Tf ^ μ := Real.rpow_le_rpow ht.1.le ht.2 hμ0
    have hF : ‖(Fpm j D.Pl.eigenvalue D.Pl.kappa ν t 0)⁻¹‖ ≤ max Cf 0 := by
      have h1 := hCf ν hν t ⟨ht.1.le, ht.2⟩
      have hexp : Real.exp
          (-((if j then D.Pl.eigenvalue else (starRingEnd ℂ) D.Pl.eigenvalue).re / 3) * t) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        exact mul_nonpos_of_nonpos_of_nonneg (by linarith) ht.1.le
      calc ‖(Fpm j D.Pl.eigenvalue D.Pl.kappa ν t 0)⁻¹‖
          ≤ Cf * Real.exp
              (-((if j then D.Pl.eigenvalue else (starRingEnd ℂ) D.Pl.eigenvalue).re / 3) * t) := h1
        _ ≤ max Cf 0 * 1 := mul_le_mul (le_max_left _ _) hexp (Real.exp_pos _).le (le_max_right _ _)
        _ = max Cf 0 := mul_one _
    exact mul_le_mul (mul_le_mul htpow hF (norm_nonneg _) (Real.rpow_nonneg hTf0 _)) hl
      (norm_nonneg _) (mul_nonneg (Real.rpow_nonneg hTf0 _) (le_max_right _ _))
  -- 6: tested norm integrand on (0, 1.1/ν]
  have hint_tested : Integrable (fun t : ℝ => t ^ μ *
      ‖Fpm true D.Pl.eigenvalue D.Pl.kappa ν t 0‖⁻¹ * ‖(S n).gB B t‖)
      (volume.restrict (Ioc 0 (1.1 / ν))) := by
    rw [hSn']
    set Tf : ℝ := 1.1 / ν
    have hTf0 : 0 ≤ Tf := by positivity
    obtain ⟨Cf, hCf⟩ := fpmInvBound D.Pl.eigenvalue D.Pl.kappa hst.gamma_pos
    obtain ⟨Cg, hCg0, hCg⟩ := ae_norm_gB_le FI D.K.χo (retEps D.Pl D.σ₀ n) D.K.as Tf hst.as_pos hB
    have hmeas : Measurable (fun t : ℝ => t ^ μ *
        ‖Fpm true D.Pl.eigenvalue D.Pl.kappa ν t 0‖⁻¹ *
        ‖(FlatSettingInst.actualFlatSetting FI D.K.χo (retEps D.Pl D.σ₀ n)).gB B t‖) := by
      have h1 : Measurable (fun t : ℝ => t ^ μ) := measurable_id.pow_const μ
      have h2 : Measurable (fun t : ℝ => ‖Fpm true D.Pl.eigenvalue D.Pl.kappa ν t 0‖⁻¹) := by
        simpa only [norm_inv] using (FlatAmp.measurable_Fpm_inv D.Pl.eigenvalue D.Pl.kappa ν).norm
      have h3 : Measurable (fun t : ℝ =>
          ‖(FlatSettingInst.actualFlatSetting FI D.K.χo (retEps D.Pl D.σ₀ n)).gB B t‖) :=
        (stronglyMeasurable_gB FI D.K.χo (retEps D.Pl D.σ₀ n) hB.1).norm.measurable
      exact (h1.mul h2).mul h3
    refine IntegrableOn.of_bound measure_Ioc_lt_top hmeas.aestronglyMeasurable
      (Tf ^ μ * max Cf 0 * Cg) ?_
    filter_upwards [hCg, ae_restrict_mem measurableSet_Ioc] with t hg ht
    have hnonneg : 0 ≤ t ^ μ * ‖Fpm true D.Pl.eigenvalue D.Pl.kappa ν t 0‖⁻¹ *
        ‖(FlatSettingInst.actualFlatSetting FI D.K.χo (retEps D.Pl D.σ₀ n)).gB B t‖ :=
      mul_nonneg (mul_nonneg (Real.rpow_nonneg ht.1.le _) (inv_nonneg.2 (norm_nonneg _)))
        (norm_nonneg _)
    rw [Real.norm_of_nonneg hnonneg]
    have htpow : t ^ μ ≤ Tf ^ μ := Real.rpow_le_rpow ht.1.le ht.2 hμ0
    have hF : ‖Fpm true D.Pl.eigenvalue D.Pl.kappa ν t 0‖⁻¹ ≤ max Cf 0 := by
      rw [← norm_inv]
      have h1 := hCf ν hν t ⟨ht.1.le, ht.2⟩
      have hexp : Real.exp (-(D.Pl.eigenvalue.re / 3) * t) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        have hγ := hst.gamma_pos
        exact mul_nonpos_of_nonpos_of_nonneg (by linarith) ht.1.le
      calc ‖(Fpm true D.Pl.eigenvalue D.Pl.kappa ν t 0)⁻¹‖
          ≤ Cf * Real.exp (-(D.Pl.eigenvalue.re / 3) * t) := h1
        _ ≤ max Cf 0 * 1 := mul_le_mul (le_max_left _ _) hexp (Real.exp_pos _).le (le_max_right _ _)
        _ = max Cf 0 := mul_one _
    exact mul_le_mul (mul_le_mul htpow hF (inv_nonneg.2 (norm_nonneg _)) (Real.rpow_nonneg hTf0 _))
      hg (norm_nonneg _) (mul_nonneg (Real.rpow_nonneg hTf0 _) (le_max_right _ _))
  exact ⟨hsupp1, hsupp2, hint1, hint_amp true, hint_amp false, hint_tested⟩

end UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif.G1
