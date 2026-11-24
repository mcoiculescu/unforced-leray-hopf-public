import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T19_2_3_2_3_1
import UnforcedLeray.Short.PartIIIa.T19_PolyCausal.CoreDuhamel.BiotSavartH1
import UnforcedLeray.Short.PartIIIa.T19_PolyCausal.CoreDuhamel.Propagation.BiotSavartSlice
import UnforcedLeray.Short.PartIIIa.Clock.Restart
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.ProductRule
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.VelLip
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.CutProps
import UnforcedLeray.Infra.JointMeasurableRep
import UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.ZeroModeLinearity

/-!
# Forward Duhamel kernel & Biot–Savart reconstruction for smooth nice sources

Constructs the forward Duhamel kernel `k_ker`, vorticity `ω_duh`, velocity `u_duh`, and velocity
gradient `G_duh` for a nice zero-circulation `X_{9,c}` source `f` vanishing on `t ≤ a_zero` and
continuous on `(0, H)`, proving `niceFlowKernelConstruct` unconditionally.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff Interval ComplexInnerProductSpace

namespace UnforcedLeray.Short.IIIa.CoreDuhamelNiceAux

/-! ## Section 1: Weighted `Z^{-1}_{9,c}` bound, zero-circulation subspace `ZC`, & Biot–Savart CLMs -/

/-- Weighted `L²` space `X_{9,c}` (complex-valued). -/
private abbrev XC (c : ℝ) : Type := Lp ℂ 2 (B0579.cellMeasure c 9)

private lemma negNorm_le_xNorm {c : ℝ} {h : ℝ × ℝ → ℂ} (hh : MemLp h 2 (B0579.cellMeasure c 9)) :
    negNorm c 9 h ≤ xNorm c 9 h := by
  unfold negNorm
  refine iSup₂_le fun φ g => iSup₂_le fun hg hh1 => ?_
  have hφm_cell : AEStronglyMeasurable φ (volume.restrict (B0579.cell c)) :=
    CoreDuhamelRepSub.aestronglyMeasurable_val_of_hasWeakCellDerivC (hg 1)
  have hφm : AEStronglyMeasurable φ (B0579.cellMeasure c (-9)) :=
    hφm_cell.mono_ac (B0579.cellMeasure_ac c (-9))
  have hxφ_sq : (xNorm c (-9) φ ^ 2) ^ (1 / 2 : ℝ) ≤ 1 := by
    calc (xNorm c (-9) φ ^ 2) ^ (1 / 2 : ℝ)
        ≤ (xNorm c (-9) φ ^ 2 + ∑ j, xNorm c (-9) (g j) ^ 2) ^ (1 / 2 : ℝ) :=
          ENNReal.rpow_le_rpow le_self_add (by norm_num)
      _ = h1Norm c 9 φ g := rfl
      _ ≤ 1 := hh1
  have hxφ : xNorm c (-9) φ ≤ 1 := by
    have heq : (xNorm c (-9) φ ^ 2) ^ (1 / 2 : ℝ) = xNorm c (-9) φ := by
      rw [← ENNReal.rpow_natCast _ 2, ← ENNReal.rpow_mul]
      norm_num
    rwa [heq] at hxφ_sq
  have hφ_mem : MemLp φ 2 (B0579.cellMeasure c (-9)) :=
    ⟨hφm, hxφ.trans_lt ENNReal.one_lt_top⟩
  have hhold := (PairContAux.holder hh hφ_mem).2
  have hφ_toReal : (eLpNorm φ 2 (B0579.cellMeasure c (-9))).toReal ≤ 1 := by
    have := ENNReal.toReal_mono ENNReal.one_ne_top hxφ
    simpa [xNorm] using this
  have hle : ‖∫ x in B0579.cell c, h x * φ x‖ ≤ (xNorm c 9 h).toReal := by
    calc ‖∫ x in B0579.cell c, h x * φ x‖
        ≤ (eLpNorm h 2 (B0579.cellMeasure c 9)).toReal *
            (eLpNorm φ 2 (B0579.cellMeasure c (-9))).toReal := hhold
      _ ≤ (eLpNorm h 2 (B0579.cellMeasure c 9)).toReal * 1 :=
          mul_le_mul_of_nonneg_left hφ_toReal ENNReal.toReal_nonneg
      _ = (xNorm c 9 h).toReal := by simp [xNorm]
  calc ENNReal.ofReal ‖∫ x in B0579.cell c, h x * φ x‖
      ≤ ENNReal.ofReal (xNorm c 9 h).toReal := ENNReal.ofReal_le_ofReal hle
    _ = xNorm c 9 h := ENNReal.ofReal_toReal hh.2.ne

private def reLp (c : ℝ) : XC c →L[ℝ] B0579.X c 9 :=
  Complex.reCLM.compLpL 2 (B0579.cellMeasure c 9)

private def imLp (c : ℝ) : XC c →L[ℝ] B0579.X c 9 :=
  Complex.imCLM.compLpL 2 (B0579.cellMeasure c 9)

private lemma coeFn_reLp (c : ℝ) (W : XC c) :
    (reLp c W : ℝ × ℝ → ℝ) =ᵐ[B0579.cellMeasure c 9] fun x => (W x).re :=
  Complex.reCLM.coeFn_compLpL (p := 2) (μ := B0579.cellMeasure c 9) W

private lemma coeFn_imLp (c : ℝ) (W : XC c) :
    (imLp c W : ℝ × ℝ → ℝ) =ᵐ[B0579.cellMeasure c 9] fun x => (W x).im :=
  Complex.imCLM.coeFn_compLpL (p := 2) (μ := B0579.cellMeasure c 9) W

private lemma norm_reLp_le (c : ℝ) (W : XC c) : ‖reLp c W‖ ≤ ‖W‖ := by
  have hop : ‖reLp c‖ ≤ 1 := by
    refine (ContinuousLinearMap.norm_compLpL_le _).trans ?_
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun z => ?_
    simpa [Real.norm_eq_abs] using Complex.abs_re_le_norm z
  exact (reLp c).le_opNorm W |>.trans (by nlinarith [norm_nonneg W])

private lemma norm_imLp_le (c : ℝ) (W : XC c) : ‖imLp c W‖ ≤ ‖W‖ := by
  have hop : ‖imLp c‖ ≤ 1 := by
    refine (ContinuousLinearMap.norm_compLpL_le _).trans ?_
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun z => ?_
    simpa [Real.norm_eq_abs] using Complex.abs_im_le_norm z
  exact (imLp c).le_opNorm W |>.trans (by nlinarith [norm_nonneg W])

private def circRe (c : ℝ) : XC c →L[ℝ] ℝ :=
  (UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.circulationCLM
    (c := c) (m := 9) (by norm_num)).comp (reLp c)

private def circIm (c : ℝ) : XC c →L[ℝ] ℝ :=
  (UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.circulationCLM
    (c := c) (m := 9) (by norm_num)).comp (imLp c)

private lemma circRe_apply (c : ℝ) (W : XC c) :
    circRe c W = ∫ x in B0579.cell c, reLp c W x := by
  simp [circRe]

private lemma circIm_apply (c : ℝ) (W : XC c) :
    circIm c W = ∫ x in B0579.cell c, imLp c W x := by
  simp [circIm]

private lemma integrableOn_of_XC (c : ℝ) (W : XC c) :
    IntegrableOn (W : ℝ × ℝ → ℂ) (B0579.cell c) := by
  have hre := UnforcedLeray.B0583.integrable_of_X (c := c) (m := 9) (by norm_num) (reLp c W)
  have him := UnforcedLeray.B0583.integrable_of_X (c := c) (m := 9) (by norm_num) (imLp c W)
  have hre_c : IntegrableOn (fun x => ((reLp c W x : ℝ) : ℂ)) (B0579.cell c) := hre.ofReal
  have him_c : IntegrableOn (fun x => ((imLp c W x : ℝ) : ℂ)) (B0579.cell c) := him.ofReal
  refine (hre_c.add (him_c.const_mul Complex.I)).congr_fun_ae ?_
  filter_upwards [(B0579.ac_cellMeasure c 9).ae_le (coeFn_reLp c W),
    (B0579.ac_cellMeasure c 9).ae_le (coeFn_imLp c W)] with x hx1 hx2
  simp only [Pi.add_apply, hx1, hx2]
  conv_rhs => rw [← Complex.re_add_im (W x)]
  ring

private lemma integral_XC_eq (c : ℝ) (W : XC c) :
    ∫ x in B0579.cell c, (W : ℝ × ℝ → ℂ) x =
      (circRe c W : ℂ) + Complex.I * (circIm c W : ℂ) := by
  have hint := integrableOn_of_XC c W
  have hre_ae := (B0579.ac_cellMeasure c 9).ae_le (coeFn_reLp c W)
  have him_ae := (B0579.ac_cellMeasure c 9).ae_le (coeFn_imLp c W)
  rw [circRe_apply, circIm_apply, integral_congr_ae hre_ae, integral_congr_ae him_ae]
  have hr : (∫ x in B0579.cell c, (W x).re) = (∫ x in B0579.cell c, (W : ℝ × ℝ → ℂ) x).re :=
    integral_re hint
  have hi : (∫ x in B0579.cell c, (W x).im) = (∫ x in B0579.cell c, (W : ℝ × ℝ → ℂ) x).im :=
    integral_im hint
  apply Complex.ext
  · simp [hr]
  · simp [hi]

private def circCCLM (c : ℝ) : XC c →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun W => (circRe c W : ℂ) + Complex.I * (circIm c W : ℂ)
      map_add' := fun W₁ W₂ => by
        simp only [map_add, Complex.ofReal_add]
        ring
      map_smul' := fun z W => by
        simp only [RingHom.id_apply, ← integral_XC_eq]
        have hae : ((z • W : XC c) : ℝ × ℝ → ℂ) =ᵐ[volume.restrict (B0579.cell c)]
            fun x => z * W x :=
          (B0579.ac_cellMeasure c 9).ae_le (Lp.coeFn_smul z W)
        rw [integral_congr_ae hae, integral_const_mul, smul_eq_mul] }
    (‖circRe c‖ + ‖circIm c‖)
    (fun W => by
      calc ‖(circRe c W : ℂ) + Complex.I * (circIm c W : ℂ)‖
          ≤ ‖(circRe c W : ℂ)‖ + ‖Complex.I * (circIm c W : ℂ)‖ := norm_add_le _ _
        _ = ‖circRe c W‖ + ‖circIm c W‖ := by simp
        _ ≤ ‖circRe c‖ * ‖W‖ + ‖circIm c‖ * ‖W‖ :=
            add_le_add ((circRe c).le_opNorm W) ((circIm c).le_opNorm W)
        _ = (‖circRe c‖ + ‖circIm c‖) * ‖W‖ := by ring)

private lemma circCCLM_apply (c : ℝ) (W : XC c) :
    circCCLM c W = ∫ x in B0579.cell c, (W : ℝ × ℝ → ℂ) x :=
  (integral_XC_eq c W).symm

/-- Closed complex subspace `X_{9,c}^0` of zero-circulation fields. -/
private def ZC (c : ℝ) : Submodule ℂ (XC c) := LinearMap.ker (circCCLM c).toLinearMap

private instance isClosed_ZC (c : ℝ) : IsClosed (ZC c : Set (XC c)) := by
  change IsClosed {W : XC c | circCCLM c W = 0}
  exact isClosed_singleton.preimage (circCCLM c).continuous

private instance completeSpace_ZC (c : ℝ) : CompleteSpace (ZC c) :=
  (isClosed_ZC c).completeSpace_coe

private def zcValCLM (c : ℝ) : ZC c →L[ℂ] XC c :=
  LinearMap.mkContinuous (ZC c).subtype 1 (fun W => by simp)

private lemma mem_ZC_iff (c : ℝ) (W : XC c) :
    W ∈ ZC c ↔ ∫ x in B0579.cell c, (W : ℝ × ℝ → ℂ) x = 0 := by
  change circCCLM c W = 0 ↔ _
  rw [circCCLM_apply]

private lemma zc_circRe_zero (c : ℝ) (W : ZC c) : ∫ x in B0579.cell c, reLp c W.1 x = 0 := by
  rw [← circRe_apply]
  have h0 : (circRe c W.1 : ℂ) + Complex.I * (circIm c W.1 : ℂ) = 0 := W.2
  have hre := congrArg Complex.re h0
  simpa using hre

private lemma zc_circIm_zero (c : ℝ) (W : ZC c) : ∫ x in B0579.cell c, imLp c W.1 x = 0 := by
  rw [← circIm_apply]
  have h0 : (circRe c W.1 : ℂ) + Complex.I * (circIm c W.1 : ℂ) = 0 := W.2
  have him := congrArg Complex.im h0
  simpa using him

private def toZC {c : ℝ} {h : ℝ × ℝ → ℂ} (hmem : MemLp h 2 (B0579.cellMeasure c 9))
    (hzc : HasZeroCirculation c h) : ZC c :=
  ⟨hmem.toLp h, by
    rw [mem_ZC_iff]
    have hae : (hmem.toLp h : ℝ × ℝ → ℂ) =ᵐ[volume.restrict (B0579.cell c)] h :=
      (B0579.ac_cellMeasure c 9).ae_le (MemLp.coeFn_toLp hmem)
    rw [integral_congr_ae hae]
    exact hzc.2⟩

private lemma norm_toZC {c : ℝ} {h : ℝ × ℝ → ℂ} (hmem : MemLp h 2 (B0579.cellMeasure c 9))
    (hzc : HasZeroCirculation c h) :
    ‖toZC hmem hzc‖ = (xNorm c 9 h).toReal := by
  change ‖hmem.toLp h‖ = (xNorm c 9 h).toReal
  rw [Lp.norm_toLp, xNorm]

private lemma norm_sub_toZC {c : ℝ} {h₁ h₂ : ℝ × ℝ → ℂ}
    (hm₁ : MemLp h₁ 2 (B0579.cellMeasure c 9)) (hz₁ : HasZeroCirculation c h₁)
    (hm₂ : MemLp h₂ 2 (B0579.cellMeasure c 9)) (hz₂ : HasZeroCirculation c h₂) :
    ‖toZC hm₁ hz₁ - toZC hm₂ hz₂‖ = (xNorm c 9 (h₁ - h₂)).toReal := by
  change ‖hm₁.toLp h₁ - hm₂.toLp h₂‖ = (xNorm c 9 (h₁ - h₂)).toReal
  rw [← MemLp.toLp_sub hm₁ hm₂, Lp.norm_toLp, xNorm]

private lemma memLp_cellVol_of_XC (c : ℝ) (W : XC c) :
    MemLp (W : ℝ × ℝ → ℂ) 2 (B0581.cellVol c) :=
  (Lp.memLp W).mono_measure (B0581.cellVol_le_cellMeasure c (m := 9) (by norm_num))

/-- Inclusion `XC c →L[ℂ] Lp ℂ 2 (cellVol c)`. -/
private def xcToCellL2 (c : ℝ) : XC c →L[ℂ] Lp ℂ 2 (B0581.cellVol c) :=
  LinearMap.mkContinuous
    { toFun := fun W => (memLp_cellVol_of_XC c W).toLp W
      map_add' := fun W₁ W₂ => by
        apply Lp.ext
        have hle := Measure.absolutelyContinuous_of_le
          (B0581.cellVol_le_cellMeasure c (m := 9) (by norm_num))
        filter_upwards [MemLp.coeFn_toLp (memLp_cellVol_of_XC c (W₁ + W₂)),
          MemLp.coeFn_toLp (memLp_cellVol_of_XC c W₁),
          MemLp.coeFn_toLp (memLp_cellVol_of_XC c W₂),
          Lp.coeFn_add ((memLp_cellVol_of_XC c W₁).toLp W₁)
            ((memLp_cellVol_of_XC c W₂).toLp W₂),
          hle.ae_le (Lp.coeFn_add W₁ W₂)] with x h1 h2 h3 h4 h5
        rw [h1, h4, Pi.add_apply, h2, h3, h5, Pi.add_apply]
      map_smul' := fun z W => by
        apply Lp.ext
        have hle := Measure.absolutelyContinuous_of_le
          (B0581.cellVol_le_cellMeasure c (m := 9) (by norm_num))
        filter_upwards [MemLp.coeFn_toLp (memLp_cellVol_of_XC c (z • W)),
          MemLp.coeFn_toLp (memLp_cellVol_of_XC c W),
          Lp.coeFn_smul z ((memLp_cellVol_of_XC c W).toLp W),
          hle.ae_le (Lp.coeFn_smul z W)] with x h1 h2 h3 h4
        simp only [RingHom.id_apply] at h3 ⊢
        rw [h1, h3, Pi.smul_apply, h2, h4, Pi.smul_apply] }
    1
    (fun W => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk, one_mul]
      rw [Lp.norm_toLp, Lp.norm_def]
      exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top W)
        (eLpNorm_mono_measure _ (B0581.cellVol_le_cellMeasure c (by norm_num))))

private lemma coeFn_xcToCellL2 (c : ℝ) (W : XC c) :
    (xcToCellL2 c W : ℝ × ℝ → ℂ) =ᵐ[B0581.cellVol c] W :=
  MemLp.coeFn_toLp (memLp_cellVol_of_XC c W)

/-- Coordinate projection `Lp Vel 2 (cellVol c) →L[ℂ] Lp ℂ 2 (cellVol c)`. -/
private def projVelLp (c : ℝ) (i : Fin 2) :
    Lp B0581.Vel 2 (B0581.cellVol c) →L[ℂ] Lp ℂ 2 (B0581.cellVol c) :=
  (EuclideanSpace.proj (𝕜 := ℂ) i : B0581.Vel →L[ℂ] ℂ).compLpL 2 (B0581.cellVol c)

private lemma coeFn_projVelLp (c : ℝ) (i : Fin 2) (U : Lp B0581.Vel 2 (B0581.cellVol c)) :
    (projVelLp c i U : ℝ × ℝ → ℂ) =ᵐ[B0581.cellVol c] fun x => U x i :=
  (EuclideanSpace.proj (𝕜 := ℂ) i : B0581.Vel →L[ℂ] ℂ).coeFn_compLpL
    (p := 2) (μ := B0581.cellVol c) U

section BiotSavartCLM

variable (c : ℝ) [hc : Fact (0 < c)]

private lemma gradQ_nonzeroPart (w : Lp ℂ 2 (B0581.cellVol c)) :
    B0583.gradQ c (B0581.nonzeroPart c w) = B0583.gradQ c w := by
  rw [B0583.gradQ_apply, B0583.gradQ_apply]
  congr 1
  ext1
  funext k
  change B0583.qModeCLM c k ((B0581.modes c (B0581.nonzeroPart c w) : B0581.ModeSeq ℂ) k) =
    B0583.qModeCLM c k ((B0581.modes c w : B0581.ModeSeq ℂ) k)
  rw [B0581.modes_nonzeroPart]
  split_ifs with hk
  · subst hk
    simp [B0583.qModeCLM_apply, B0581.bsModeCLM_zero]
  · rfl

private lemma gradEta_nonzeroPart (w : Lp ℂ 2 (B0581.cellVol c)) :
    B0583.gradEta c (B0581.nonzeroPart c w) = B0583.gradEta c w := by
  rw [B0583.gradEta_apply, B0583.gradEta_apply]
  congr 1
  ext1
  funext k
  change B0583.etaModeCLM c k ((B0581.modes c (B0581.nonzeroPart c w) : B0581.ModeSeq ℂ) k) =
    B0583.etaModeCLM c k ((B0581.modes c w : B0581.ModeSeq ℂ) k)
  rw [B0581.modes_nonzeroPart]
  split_ifs with hk
  · subst hk
    simp [B0583.etaModeCLM_zero]
  · rfl

private lemma zeroVelEtaLp_add (w z : B0579.X c 9)
    (hw0 : ∫ x in B0579.cell c, w x = 0) (hz0 : ∫ x in B0579.cell c, z x = 0)
    (hwz0 : ∫ x in B0579.cell c, (w + z) x = 0) :
    B0583.zeroVelEtaLp c (by norm_num) (w + z) hwz0 =
      B0583.zeroVelEtaLp c (by norm_num) w hw0 + B0583.zeroVelEtaLp c (by norm_num) z hz0 := by
  have hbar := UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.omegaBar_add_ae
    (c := c) (m := 9) (by norm_num) w z
  have hbar_cell : (fun x : B0579.Plane => B0583.omegaBar c ((w + z : B0579.X c 9) : B0579.Plane → ℝ) x.2)
      =ᵐ[B0581.cellVol c]
        fun x => B0583.omegaBar c w x.2 + B0583.omegaBar c z x.2 := by
    rw [B0581.cellVol_eq]
    exact Measure.quasiMeasurePreserving_snd.ae_eq_comp hbar
  apply Lp.ext
  filter_upwards [B0583.coeFn_zeroVelEtaLp c (by norm_num) (w + z) hwz0,
    B0583.coeFn_zeroVelEtaLp c (by norm_num) w hw0,
    B0583.coeFn_zeroVelEtaLp c (by norm_num) z hz0,
    Lp.coeFn_add (B0583.zeroVelEtaLp c (by norm_num) w hw0)
      (B0583.zeroVelEtaLp c (by norm_num) z hz0),
    hbar_cell] with x hsum hw hz hadd hb
  rw [hsum, hadd, Pi.add_apply, hw, hz]
  change B0583.zeroVelEta c ((w + z : B0579.X c 9) : B0579.Plane → ℝ) x =
    B0583.zeroVelEta c w x + B0583.zeroVelEta c z x
  simp only [B0583.zeroVelEta, B0583.profField]
  rw [hb]
  simp only [neg_add, Complex.ofReal_add, add_smul]

private lemma zeroVelEtaLp_smul (a : ℝ) (w : B0579.X c 9)
    (hw0 : ∫ x in B0579.cell c, w x = 0) (haw0 : ∫ x in B0579.cell c, (a • w) x = 0) :
    B0583.zeroVelEtaLp c (by norm_num) (a • w) haw0 =
      a • B0583.zeroVelEtaLp c (by norm_num) w hw0 := by
  have hbar := UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.omegaBar_smul_ae
    (c := c) (m := 9) (by norm_num) a w
  have hbar_cell : (fun x : B0579.Plane => B0583.omegaBar c ((a • w : B0579.X c 9) : B0579.Plane → ℝ) x.2)
      =ᵐ[B0581.cellVol c]
        fun x => a * B0583.omegaBar c w x.2 := by
    rw [B0581.cellVol_eq]
    exact Measure.quasiMeasurePreserving_snd.ae_eq_comp hbar
  apply Lp.ext
  filter_upwards [B0583.coeFn_zeroVelEtaLp c (by norm_num) (a • w) haw0,
    B0583.coeFn_zeroVelEtaLp c (by norm_num) w hw0,
    Lp.coeFn_smul a (B0583.zeroVelEtaLp c (by norm_num) w hw0),
    hbar_cell] with x hsc hw hsm hb
  rw [hsc, hsm, Pi.smul_apply, hw]
  change B0583.zeroVelEta c ((a • w : B0579.X c 9) : B0579.Plane → ℝ) x =
    a • B0583.zeroVelEta c w x
  simp only [B0583.zeroVelEta, B0583.profField]
  rw [hb]
  ext i
  fin_cases i <;> simp [Complex.ofReal_mul, smul_eq_mul]

private lemma velocity_add_real (w z : B0579.X c 9)
    (hw0 : ∫ x in B0579.cell c, w x = 0) (hz0 : ∫ x in B0579.cell c, z x = 0)
    (hwz0 : ∫ x in B0579.cell c, (w + z) x = 0) :
    B0583.velocity c (by norm_num) (w + z) hwz0 =
      B0583.velocity c (by norm_num) w hw0 + B0583.velocity c (by norm_num) z hz0 := by
  let cx := UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.complexifyXCLM c 9 (by norm_num)
  have heq : ∀ (u : B0579.X c 9) (hu0 : ∫ x in B0579.cell c, u x = 0),
      B0583.velocity c (by norm_num) u hu0 =
        B0581.velNe c (cx u) + B0583.zeroVelLp c (by norm_num) u hu0 := by
    intro u hu0
    unfold B0583.velocity
    rw [B0581.velNe_nonzeroPart]
    rfl
  rw [heq (w + z) hwz0, heq w hw0, heq z hz0, cx.map_add, (B0581.velNe c).map_add,
    UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.zeroVelLp_add (by norm_num) w z hw0 hz0 hwz0]
  abel

private lemma velocity_smul_real (a : ℝ) (w : B0579.X c 9)
    (hw0 : ∫ x in B0579.cell c, w x = 0) (haw0 : ∫ x in B0579.cell c, (a • w) x = 0) :
    B0583.velocity c (by norm_num) (a • w) haw0 =
      a • B0583.velocity c (by norm_num) w hw0 := by
  let cx := UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.complexifyXCLM c 9 (by norm_num)
  have heq : ∀ (u : B0579.X c 9) (hu0 : ∫ x in B0579.cell c, u x = 0),
      B0583.velocity c (by norm_num) u hu0 =
        B0581.velNe c (cx u) + B0583.zeroVelLp c (by norm_num) u hu0 := by
    intro u hu0
    unfold B0583.velocity
    rw [B0581.velNe_nonzeroPart]
    rfl
  have hsm : B0581.velNe c (a • cx w) = a • B0581.velNe c (cx w) :=
    ((B0581.velNe c).restrictScalars ℝ).map_smul a (cx w)
  rw [heq (a • w) haw0, heq w hw0, cx.map_smul, hsm,
    UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.zeroVelLp_smul (by norm_num) a w hw0 haw0,
    smul_add]

private lemma velGradQ_add_real (w z : B0579.X c 9) :
    B0583.velGradQ c (by norm_num) (w + z) =
      B0583.velGradQ c (by norm_num) w + B0583.velGradQ c (by norm_num) z := by
  let cx := UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.complexifyXCLM c 9 (by norm_num)
  have heq : ∀ u : B0579.X c 9, B0583.velGradQ c (by norm_num) u = B0583.gradQ c (cx u) := by
    intro u; unfold B0583.velGradQ; rw [gradQ_nonzeroPart c]; rfl
  rw [heq (w + z), heq w, heq z, cx.map_add, (B0583.gradQ c).map_add]

private lemma velGradQ_smul_real (a : ℝ) (w : B0579.X c 9) :
    B0583.velGradQ c (by norm_num) (a • w) = a • B0583.velGradQ c (by norm_num) w := by
  let cx := UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.complexifyXCLM c 9 (by norm_num)
  have heq : ∀ u : B0579.X c 9, B0583.velGradQ c (by norm_num) u = B0583.gradQ c (cx u) := by
    intro u; unfold B0583.velGradQ; rw [gradQ_nonzeroPart c]; rfl
  have hsm : B0583.gradQ c (a • cx w) = a • B0583.gradQ c (cx w) :=
    ((B0583.gradQ c).restrictScalars ℝ).map_smul a (cx w)
  rw [heq (a • w), heq w, cx.map_smul, hsm]

private lemma velGradEta_add_real (w z : B0579.X c 9)
    (hw0 : ∫ x in B0579.cell c, w x = 0) (hz0 : ∫ x in B0579.cell c, z x = 0)
    (hwz0 : ∫ x in B0579.cell c, (w + z) x = 0) :
    B0583.velGradEta c (by norm_num) (w + z) hwz0 =
      B0583.velGradEta c (by norm_num) w hw0 + B0583.velGradEta c (by norm_num) z hz0 := by
  let cx := UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.complexifyXCLM c 9 (by norm_num)
  have heq : ∀ (u : B0579.X c 9) (hu0 : ∫ x in B0579.cell c, u x = 0),
      B0583.velGradEta c (by norm_num) u hu0 =
        B0583.gradEta c (cx u) + B0583.zeroVelEtaLp c (by norm_num) u hu0 := by
    intro u hu0; unfold B0583.velGradEta; rw [gradEta_nonzeroPart c]; rfl
  rw [heq (w + z) hwz0, heq w hw0, heq z hz0, cx.map_add, (B0583.gradEta c).map_add,
    zeroVelEtaLp_add c w z hw0 hz0 hwz0]
  abel

private lemma velGradEta_smul_real (a : ℝ) (w : B0579.X c 9)
    (hw0 : ∫ x in B0579.cell c, w x = 0) (haw0 : ∫ x in B0579.cell c, (a • w) x = 0) :
    B0583.velGradEta c (by norm_num) (a • w) haw0 =
      a • B0583.velGradEta c (by norm_num) w hw0 := by
  let cx := UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.complexifyXCLM c 9 (by norm_num)
  have heq : ∀ (u : B0579.X c 9) (hu0 : ∫ x in B0579.cell c, u x = 0),
      B0583.velGradEta c (by norm_num) u hu0 =
        B0583.gradEta c (cx u) + B0583.zeroVelEtaLp c (by norm_num) u hu0 := by
    intro u hu0; unfold B0583.velGradEta; rw [gradEta_nonzeroPart c]; rfl
  have hsm : B0583.gradEta c (a • cx w) = a • B0583.gradEta c (cx w) :=
    ((B0583.gradEta c).restrictScalars ℝ).map_smul a (cx w)
  rw [heq (a • w) haw0, heq w hw0, cx.map_smul, hsm,
    zeroVelEtaLp_smul c a w hw0 haw0, smul_add]

omit hc in
private lemma reLp_smul_cx (z : ℂ) (W : XC c) :
    reLp c (z • W) = z.re • reLp c W + (-z.im) • imLp c W := by
  apply Lp.ext
  filter_upwards [coeFn_reLp c (z • W), Lp.coeFn_smul z W,
    Lp.coeFn_add (z.re • reLp c W) ((-z.im) • imLp c W),
    Lp.coeFn_smul z.re (reLp c W), Lp.coeFn_smul (-z.im) (imLp c W),
    coeFn_reLp c W, coeFn_imLp c W] with x h1 h2 h3 h4 h5 h6 h7
  rw [h1, h2, h3, Pi.add_apply, h4, h5]
  simp only [Pi.smul_apply, smul_eq_mul, h6, h7, Complex.mul_re]
  ring

omit hc in
private lemma imLp_smul_cx (z : ℂ) (W : XC c) :
    imLp c (z • W) = z.im • reLp c W + z.re • imLp c W := by
  apply Lp.ext
  filter_upwards [coeFn_imLp c (z • W), Lp.coeFn_smul z W,
    Lp.coeFn_add (z.im • reLp c W) (z.re • imLp c W),
    Lp.coeFn_smul z.im (reLp c W), Lp.coeFn_smul z.re (imLp c W),
    coeFn_reLp c W, coeFn_imLp c W] with x h1 h2 h3 h4 h5 h6 h7
  rw [h1, h2, h3, Pi.add_apply, h4, h5]
  simp only [Pi.smul_apply, smul_eq_mul, h6, h7, Complex.mul_im]
  ring

omit hc in
private lemma real_smul_velLp (r : ℝ) (V : Lp B0581.Vel 2 (B0581.cellVol c)) :
    (r : ℂ) • V = r • V := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_smul (r : ℂ) V, Lp.coeFn_smul r V] with x h1 h2
  rw [h1, h2]
  ext i
  simp [Complex.real_smul]

/-- Complex Biot–Savart velocity as a continuous `ℂ`-linear map on `ZC c`. -/
private def velCCLM : ZC c →L[ℂ] Lp B0581.Vel 2 (B0581.cellVol c) :=
  LinearMap.mkContinuous
    { toFun := fun W =>
        B0583.velocity c (by norm_num) (reLp c W.1) (zc_circRe_zero c W) +
          Complex.I • B0583.velocity c (by norm_num) (imLp c W.1) (zc_circIm_zero c W)
      map_add' := fun W₁ W₂ => by
        have hre : reLp c (W₁ + W₂).1 = reLp c W₁.1 + reLp c W₂.1 := (reLp c).map_add W₁.1 W₂.1
        have him : imLp c (W₁ + W₂).1 = imLp c W₁.1 + imLp c W₂.1 := (imLp c).map_add W₁.1 W₂.1
        have h1 : B0583.velocity c (by norm_num) (reLp c (W₁ + W₂).1) (zc_circRe_zero c (W₁ + W₂)) =
            B0583.velocity c (by norm_num) (reLp c W₁.1) (zc_circRe_zero c W₁) +
              B0583.velocity c (by norm_num) (reLp c W₂.1) (zc_circRe_zero c W₂) := by
          have hc12 : ∫ x in B0579.cell c, (reLp c W₁.1 + reLp c W₂.1) x = 0 := by
            rw [← hre]; exact zc_circRe_zero c (W₁ + W₂)
          simpa [hre] using velocity_add_real c (reLp c W₁.1) (reLp c W₂.1)
            (zc_circRe_zero c W₁) (zc_circRe_zero c W₂) hc12
        have h2 : B0583.velocity c (by norm_num) (imLp c (W₁ + W₂).1) (zc_circIm_zero c (W₁ + W₂)) =
            B0583.velocity c (by norm_num) (imLp c W₁.1) (zc_circIm_zero c W₁) +
              B0583.velocity c (by norm_num) (imLp c W₂.1) (zc_circIm_zero c W₂) := by
          have hc12 : ∫ x in B0579.cell c, (imLp c W₁.1 + imLp c W₂.1) x = 0 := by
            rw [← him]; exact zc_circIm_zero c (W₁ + W₂)
          simpa [him] using velocity_add_real c (imLp c W₁.1) (imLp c W₂.1)
            (zc_circIm_zero c W₁) (zc_circIm_zero c W₂) hc12
        rw [h1, h2, smul_add]
        abel
      map_smul' := fun z W => by
        simp only [RingHom.id_apply]
        have hre := reLp_smul_cx c z W.1
        have him := imLp_smul_cx c z W.1
        have hr0 := zc_circRe_zero c W
        have hi0 := zc_circIm_zero c W
        have h_zre_r : ∫ x in B0579.cell c, (z.re • reLp c W.1) x = 0 := by
          rw [← UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.circulationCLM_apply (by norm_num),
            map_smul, UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.circulationCLM_apply,
            hr0, smul_zero]
        have h_zim_i : ∫ x in B0579.cell c, ((-z.im) • imLp c W.1) x = 0 := by
          rw [← UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.circulationCLM_apply (by norm_num),
            map_smul, UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.circulationCLM_apply,
            hi0, smul_zero]
        have h_zim_r : ∫ x in B0579.cell c, (z.im • reLp c W.1) x = 0 := by
          rw [← UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.circulationCLM_apply (by norm_num),
            map_smul, UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.circulationCLM_apply,
            hr0, smul_zero]
        have h_zre_i : ∫ x in B0579.cell c, (z.re • imLp c W.1) x = 0 := by
          rw [← UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.circulationCLM_apply (by norm_num),
            map_smul, UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.circulationCLM_apply,
            hi0, smul_zero]
        have h1 : B0583.velocity c (by norm_num) (reLp c (z • W).1) (zc_circRe_zero c (z • W)) =
            z.re • B0583.velocity c (by norm_num) (reLp c W.1) hr0 +
              (-z.im) • B0583.velocity c (by norm_num) (imLp c W.1) hi0 := by
          have hc_sum : ∫ x in B0579.cell c, (z.re • reLp c W.1 + (-z.im) • imLp c W.1) x = 0 := by
            rw [← hre]; exact zc_circRe_zero c (z • W)
          calc B0583.velocity c (by norm_num) (reLp c (z • W).1) (zc_circRe_zero c (z • W))
              = B0583.velocity c (by norm_num) (z.re • reLp c W.1 + (-z.im) • imLp c W.1) hc_sum := by
                congr 1
            _ = B0583.velocity c (by norm_num) (z.re • reLp c W.1) h_zre_r +
                  B0583.velocity c (by norm_num) ((-z.im) • imLp c W.1) h_zim_i :=
                velocity_add_real c _ _ h_zre_r h_zim_i hc_sum
            _ = z.re • B0583.velocity c (by norm_num) (reLp c W.1) hr0 +
                  (-z.im) • B0583.velocity c (by norm_num) (imLp c W.1) hi0 := by
                rw [velocity_smul_real c z.re (reLp c W.1) hr0 h_zre_r,
                  velocity_smul_real c (-z.im) (imLp c W.1) hi0 h_zim_i]
        have h2 : B0583.velocity c (by norm_num) (imLp c (z • W).1) (zc_circIm_zero c (z • W)) =
            z.im • B0583.velocity c (by norm_num) (reLp c W.1) hr0 +
              z.re • B0583.velocity c (by norm_num) (imLp c W.1) hi0 := by
          have hc_sum : ∫ x in B0579.cell c, (z.im • reLp c W.1 + z.re • imLp c W.1) x = 0 := by
            rw [← him]; exact zc_circIm_zero c (z • W)
          calc B0583.velocity c (by norm_num) (imLp c (z • W).1) (zc_circIm_zero c (z • W))
              = B0583.velocity c (by norm_num) (z.im • reLp c W.1 + z.re • imLp c W.1) hc_sum := by
                congr 1
            _ = B0583.velocity c (by norm_num) (z.im • reLp c W.1) h_zim_r +
                  B0583.velocity c (by norm_num) (z.re • imLp c W.1) h_zre_i :=
                velocity_add_real c _ _ h_zim_r h_zre_i hc_sum
            _ = z.im • B0583.velocity c (by norm_num) (reLp c W.1) hr0 +
                  z.re • B0583.velocity c (by norm_num) (imLp c W.1) hi0 := by
                rw [velocity_smul_real c z.im (reLp c W.1) hr0 h_zim_r,
                  velocity_smul_real c z.re (imLp c W.1) hi0 h_zre_i]
        rw [h1, h2]
        set V₁ := B0583.velocity c (by norm_num) (reLp c W.1) hr0
        set V₂ := B0583.velocity c (by norm_num) (imLp c W.1) hi0
        rw [← real_smul_velLp c z.re V₁, ← real_smul_velLp c (-z.im) V₂,
          ← real_smul_velLp c z.im V₁, ← real_smul_velLp c z.re V₂]
        calc ((z.re : ℂ) • V₁ + ((-z.im : ℝ) : ℂ) • V₂) +
              Complex.I • ((z.im : ℂ) • V₁ + (z.re : ℂ) • V₂)
            = ((z.re : ℂ) + (z.im : ℂ) * Complex.I) • V₁ +
                ((-(z.im : ℂ)) + (z.re : ℂ) * Complex.I) • V₂ := by
              rw [Complex.ofReal_neg, smul_add, ← mul_smul, ← mul_smul,
                add_smul, add_smul, neg_smul, mul_comm (z.im : ℂ) Complex.I,
                mul_comm (z.re : ℂ) Complex.I]
              abel
          _ = z • V₁ + (z * Complex.I) • V₂ := by
              have hz1 : (z.re : ℂ) + (z.im : ℂ) * Complex.I = z := Complex.re_add_im z
              have hz2 : -(z.im : ℂ) + (z.re : ℂ) * Complex.I = z * Complex.I := by
                calc -(z.im : ℂ) + (z.re : ℂ) * Complex.I
                    = (z.re : ℂ) * Complex.I + (z.im : ℂ) * (Complex.I * Complex.I) := by
                      rw [Complex.I_mul_I]; ring
                  _ = ((z.re : ℂ) + (z.im : ℂ) * Complex.I) * Complex.I := by ring
                  _ = z * Complex.I := by rw [hz1]
              rw [hz1, hz2]
          _ = z • (V₁ + Complex.I • V₂) := by
              rw [smul_add, mul_smul] }
    (2 * (c / (2 * Real.pi) + 2))
    (fun W => by
      have hcpos : 0 < c := hc.out
      have hC : 0 ≤ c / (2 * Real.pi) + 2 := by positivity
      calc ‖B0583.velocity c (by norm_num) (reLp c W.1) (zc_circRe_zero c W) +
              Complex.I • B0583.velocity c (by norm_num) (imLp c W.1) (zc_circIm_zero c W)‖
          ≤ ‖B0583.velocity c (by norm_num) (reLp c W.1) (zc_circRe_zero c W)‖ +
              ‖Complex.I • B0583.velocity c (by norm_num) (imLp c W.1) (zc_circIm_zero c W)‖ :=
            norm_add_le _ _
        _ = ‖B0583.velocity c (by norm_num) (reLp c W.1) (zc_circRe_zero c W)‖ +
              ‖B0583.velocity c (by norm_num) (imLp c W.1) (zc_circIm_zero c W)‖ := by
            rw [norm_smul, Complex.norm_I, one_mul]
        _ ≤ (c / (2 * Real.pi) + 2) * ‖reLp c W.1‖ + (c / (2 * Real.pi) + 2) * ‖imLp c W.1‖ :=
            add_le_add (B0583.norm_velocity_le c (by norm_num) _ _)
              (B0583.norm_velocity_le c (by norm_num) _ _)
        _ ≤ (c / (2 * Real.pi) + 2) * ‖W.1‖ + (c / (2 * Real.pi) + 2) * ‖W.1‖ :=
            add_le_add (mul_le_mul_of_nonneg_left (norm_reLp_le c W.1) hC)
              (mul_le_mul_of_nonneg_left (norm_imLp_le c W.1) hC)
        _ = 2 * (c / (2 * Real.pi) + 2) * ‖W‖ := by change _ = _ * ‖W.1‖; ring)

/-- `∂_q` of the complex Biot–Savart velocity as a continuous `ℝ`-linear map on `ZC c`. -/
private def gqCCLM : ZC c →L[ℝ] Lp B0581.Vel 2 (B0581.cellVol c) :=
  LinearMap.mkContinuous
    { toFun := fun W =>
        B0583.velGradQ c (by norm_num) (reLp c W.1) +
          Complex.I • B0583.velGradQ c (by norm_num) (imLp c W.1)
      map_add' := fun W₁ W₂ => by
        change B0583.velGradQ c (by norm_num) (reLp c (W₁.1 + W₂.1)) +
            Complex.I • B0583.velGradQ c (by norm_num) (imLp c (W₁.1 + W₂.1)) = _
        rw [(reLp c).map_add, (imLp c).map_add, velGradQ_add_real c, velGradQ_add_real c, smul_add]
        abel
      map_smul' := fun a W => by
        simp only [RingHom.id_apply]
        change B0583.velGradQ c (by norm_num) (reLp c ((a : ℝ) • W.1)) +
            Complex.I • B0583.velGradQ c (by norm_num) (imLp c ((a : ℝ) • W.1)) = _
        rw [(reLp c).map_smul, (imLp c).map_smul, velGradQ_smul_real c, velGradQ_smul_real c,
          smul_comm Complex.I a, smul_add] }
    2
    (fun W => by
      calc ‖B0583.velGradQ c (by norm_num) (reLp c W.1) +
              Complex.I • B0583.velGradQ c (by norm_num) (imLp c W.1)‖
          ≤ ‖B0583.velGradQ c (by norm_num) (reLp c W.1)‖ +
              ‖B0583.velGradQ c (by norm_num) (imLp c W.1)‖ := by
            refine (norm_add_le _ _).trans_eq ?_; rw [norm_smul, Complex.norm_I, one_mul]
        _ ≤ ‖reLp c W.1‖ + ‖imLp c W.1‖ :=
            add_le_add (B0583.norm_velGradQ_le c (by norm_num) _)
              (B0583.norm_velGradQ_le c (by norm_num) _)
        _ ≤ ‖W.1‖ + ‖W.1‖ := add_le_add (norm_reLp_le c W.1) (norm_imLp_le c W.1)
        _ = 2 * ‖W‖ := by change _ = 2 * ‖W.1‖; ring)

/-- `∂_η` of the complex Biot–Savart velocity as a continuous `ℝ`-linear map on `ZC c`. -/
private def geCCLM : ZC c →L[ℝ] Lp B0581.Vel 2 (B0581.cellVol c) :=
  LinearMap.mkContinuous
    { toFun := fun W =>
        B0583.velGradEta c (by norm_num) (reLp c W.1) (zc_circRe_zero c W) +
          Complex.I • B0583.velGradEta c (by norm_num) (imLp c W.1) (zc_circIm_zero c W)
      map_add' := fun W₁ W₂ => by
        have hre : reLp c (W₁ + W₂).1 = reLp c W₁.1 + reLp c W₂.1 := (reLp c).map_add W₁.1 W₂.1
        have him : imLp c (W₁ + W₂).1 = imLp c W₁.1 + imLp c W₂.1 := (imLp c).map_add W₁.1 W₂.1
        have h1 : B0583.velGradEta c (by norm_num) (reLp c (W₁ + W₂).1) (zc_circRe_zero c (W₁ + W₂)) =
            B0583.velGradEta c (by norm_num) (reLp c W₁.1) (zc_circRe_zero c W₁) +
              B0583.velGradEta c (by norm_num) (reLp c W₂.1) (zc_circRe_zero c W₂) := by
          have hc12 : ∫ x in B0579.cell c, (reLp c W₁.1 + reLp c W₂.1) x = 0 := by
            rw [← hre]; exact zc_circRe_zero c (W₁ + W₂)
          simpa [hre] using velGradEta_add_real c (reLp c W₁.1) (reLp c W₂.1)
            (zc_circRe_zero c W₁) (zc_circRe_zero c W₂) hc12
        have h2 : B0583.velGradEta c (by norm_num) (imLp c (W₁ + W₂).1) (zc_circIm_zero c (W₁ + W₂)) =
            B0583.velGradEta c (by norm_num) (imLp c W₁.1) (zc_circIm_zero c W₁) +
              B0583.velGradEta c (by norm_num) (imLp c W₂.1) (zc_circIm_zero c W₂) := by
          have hc12 : ∫ x in B0579.cell c, (imLp c W₁.1 + imLp c W₂.1) x = 0 := by
            rw [← him]; exact zc_circIm_zero c (W₁ + W₂)
          simpa [him] using velGradEta_add_real c (imLp c W₁.1) (imLp c W₂.1)
            (zc_circIm_zero c W₁) (zc_circIm_zero c W₂) hc12
        rw [h1, h2, smul_add]
        abel
      map_smul' := fun a W => by
        simp only [RingHom.id_apply]
        have haW : (a • W : ZC c).1 = a • W.1 := rfl
        have hre : reLp c (a • W : ZC c).1 = a • reLp c W.1 := by
          rw [haW, (reLp c).map_smul]
        have him : imLp c (a • W : ZC c).1 = a • imLp c W.1 := by
          rw [haW, (imLp c).map_smul]
        have h1 : B0583.velGradEta c (by norm_num) (reLp c (a • W : ZC c).1) (zc_circRe_zero c (a • W)) =
            a • B0583.velGradEta c (by norm_num) (reLp c W.1) (zc_circRe_zero c W) := by
          have hca : ∫ x in B0579.cell c, (a • reLp c W.1) x = 0 := by
            rw [← hre]; exact zc_circRe_zero c (a • W)
          simpa [hre] using velGradEta_smul_real c a (reLp c W.1) (zc_circRe_zero c W) hca
        have h2 : B0583.velGradEta c (by norm_num) (imLp c (a • W : ZC c).1) (zc_circIm_zero c (a • W)) =
            a • B0583.velGradEta c (by norm_num) (imLp c W.1) (zc_circIm_zero c W) := by
          have hca : ∫ x in B0579.cell c, (a • imLp c W.1) x = 0 := by
            rw [← him]; exact zc_circIm_zero c (a • W)
          simpa [him] using velGradEta_smul_real c a (imLp c W.1) (zc_circIm_zero c W) hca
        rw [h1, h2, smul_comm Complex.I a, smul_add] }
    4
    (fun W => by
      calc ‖B0583.velGradEta c (by norm_num) (reLp c W.1) (zc_circRe_zero c W) +
              Complex.I • B0583.velGradEta c (by norm_num) (imLp c W.1) (zc_circIm_zero c W)‖
          ≤ ‖B0583.velGradEta c (by norm_num) (reLp c W.1) (zc_circRe_zero c W)‖ +
              ‖B0583.velGradEta c (by norm_num) (imLp c W.1) (zc_circIm_zero c W)‖ := by
            refine (norm_add_le _ _).trans_eq ?_; rw [norm_smul, Complex.norm_I, one_mul]
        _ ≤ 2 * ‖reLp c W.1‖ + 2 * ‖imLp c W.1‖ :=
            add_le_add (B0583.norm_velGradEta_le c (by norm_num) _ _)
              (B0583.norm_velGradEta_le c (by norm_num) _ _)
        _ ≤ 2 * ‖W.1‖ + 2 * ‖W.1‖ :=
            add_le_add (mul_le_mul_of_nonneg_left (norm_reLp_le c W.1) (by norm_num))
              (mul_le_mul_of_nonneg_left (norm_imLp_le c W.1) (by norm_num))
        _ = 4 * ‖W‖ := by change _ = 4 * ‖W.1‖; ring)

private lemma isBiotSavart_velCCLM (W : ZC c) :
    IsBiotSavart c (W.1 : ℝ × ℝ → ℂ) (fun x i => (velCCLM c W : B0579.Plane → B0581.Vel) x i) := by
  let U₁ := B0583.velocity c (by norm_num) (reLp c W.1) (zc_circRe_zero c W)
  let U₂ := B0583.velocity c (by norm_num) (imLp c W.1) (zc_circIm_zero c W)
  let u₁ : ℝ × ℝ → Fin 2 → ℂ := fun x i => (U₁ : B0579.Plane → B0581.Vel) x i
  let u₂ : ℝ × ℝ → Fin 2 → ℂ := fun x i => (U₂ : B0579.Plane → B0581.Vel) x i
  let u_sum : ℝ × ℝ → Fin 2 → ℂ := fun x i => u₁ x i + Complex.I * u₂ x i
  obtain ⟨hm₁, hdiv₁, hcurl₁⟩ :=
    CTE.velocityIsBiotSavart c 9 (by norm_num) (reLp c W.1) (zc_circRe_zero c W)
  obtain ⟨hm₂, hdiv₂, hcurl₂⟩ :=
    CTE.velocityIsBiotSavart c 9 (by norm_num) (imLp c W.1) (zc_circIm_zero c W)
  have hae_vel : ∀ᵐ x ∂(volume.restrict (B0579.cell c)),
      (fun i => (velCCLM c W : B0579.Plane → B0581.Vel) x i) = u_sum x := by
    have h1 : velCCLM c W = U₁ + Complex.I • U₂ := rfl
    rw [h1]
    filter_upwards [Lp.coeFn_add U₁ (Complex.I • U₂), Lp.coeFn_smul Complex.I U₂] with x hx1 hx2
    funext i
    rw [hx1, Pi.add_apply, hx2]
    rfl
  have ae₁ := (B0579.ac_cellMeasure c 9).ae_le (coeFn_reLp c W.1)
  have ae₂ := (B0579.ac_cellMeasure c 9).ae_le (coeFn_imLp c W.1)
  refine ⟨fun j => BiotSavartH1Aux.memLp_lp_coord (velCCLM c W) j, ?_, ?_⟩
  · intro ψ hψ
    have hA : IntegrableOn
        (fun x => u₁ x 0 * (B0579.pd 0 ψ x : ℂ) + u₁ x 1 * (B0579.pd 1 ψ x : ℂ))
        (B0579.cell c) :=
      (CTE.T20_7.integrableOn_comp_test u₁ hm₁ 0 (hψ.pd 0)).add
        (CTE.T20_7.integrableOn_comp_test u₁ hm₁ 1 (hψ.pd 1))
    have hB : IntegrableOn
        (fun x => u₂ x 0 * (B0579.pd 0 ψ x : ℂ) + u₂ x 1 * (B0579.pd 1 ψ x : ℂ))
        (B0579.cell c) :=
      (CTE.T20_7.integrableOn_comp_test u₂ hm₂ 0 (hψ.pd 0)).add
        (CTE.T20_7.integrableOn_comp_test u₂ hm₂ 1 (hψ.pd 1))
    have hcongr : ∀ᵐ x ∂(volume.restrict (B0579.cell c)),
        (velCCLM c W x 0 * (B0579.pd 0 ψ x : ℂ) + velCCLM c W x 1 * (B0579.pd 1 ψ x : ℂ)) =
          (u₁ x 0 * (B0579.pd 0 ψ x : ℂ) + u₁ x 1 * (B0579.pd 1 ψ x : ℂ)) +
            Complex.I * (u₂ x 0 * (B0579.pd 0 ψ x : ℂ) + u₂ x 1 * (B0579.pd 1 ψ x : ℂ)) := by
      filter_upwards [hae_vel] with x hx
      have hx0 := congrFun hx 0
      have hx1 := congrFun hx 1
      dsimp [u_sum] at hx0 hx1
      rw [hx0, hx1]
      ring
    rw [integral_congr_ae hcongr, integral_add hA (hB.const_mul Complex.I), integral_const_mul]
    have hd1 : ∫ x in B0579.cell c,
        (u₁ x 0 * (B0579.pd 0 ψ x : ℂ) + u₁ x 1 * (B0579.pd 1 ψ x : ℂ)) = 0 := hdiv₁ ψ hψ
    have hd2 : ∫ x in B0579.cell c,
        (u₂ x 0 * (B0579.pd 0 ψ x : ℂ) + u₂ x 1 * (B0579.pd 1 ψ x : ℂ)) = 0 := hdiv₂ ψ hψ
    rw [hd1, hd2]
    ring
  · intro ψ hψ
    have hI1 : IntegrableOn
        (fun x => u₁ x 0 * (B0579.pd 1 ψ x : ℂ) - u₁ x 1 * (B0579.pd 0 ψ x : ℂ))
        (B0579.cell c) :=
      (CTE.T20_7.integrableOn_comp_test u₁ hm₁ 0 (hψ.pd 1)).sub
        (CTE.T20_7.integrableOn_comp_test u₁ hm₁ 1 (hψ.pd 0))
    have hI2 : IntegrableOn
        (fun x => u₂ x 0 * (B0579.pd 1 ψ x : ℂ) - u₂ x 1 * (B0579.pd 0 ψ x : ℂ))
        (B0579.cell c) :=
      (CTE.T20_7.integrableOn_comp_test u₂ hm₂ 0 (hψ.pd 1)).sub
        (CTE.T20_7.integrableOn_comp_test u₂ hm₂ 1 (hψ.pd 0))
    have hpt : ∀ᵐ x ∂(volume.restrict (B0579.cell c)),
        (W.1 : ℝ × ℝ → ℂ) x * (ψ x : ℂ) = ((reLp c W.1 x : ℝ) : ℂ) * (ψ x : ℂ) +
          Complex.I * (((imLp c W.1 x : ℝ) : ℂ) * (ψ x : ℂ)) := by
      filter_upwards [ae₁, ae₂] with x h₁ h₂
      simp only [h₁, h₂]
      conv_lhs => rw [← Complex.re_add_im (W.1 x)]
      ring
    have hcongr : ∀ᵐ x ∂(volume.restrict (B0579.cell c)),
        (velCCLM c W x 0 * (B0579.pd 1 ψ x : ℂ) - velCCLM c W x 1 * (B0579.pd 0 ψ x : ℂ)) =
          (u₁ x 0 * (B0579.pd 1 ψ x : ℂ) - u₁ x 1 * (B0579.pd 0 ψ x : ℂ)) +
            Complex.I * (u₂ x 0 * (B0579.pd 1 ψ x : ℂ) - u₂ x 1 * (B0579.pd 0 ψ x : ℂ)) := by
      filter_upwards [hae_vel] with x hx
      have hx0 := congrFun hx 0
      have hx1 := congrFun hx 1
      dsimp [u_sum] at hx0 hx1
      rw [hx0, hx1]
      ring
    have hJ1 : IntegrableOn (fun x => ((reLp c W.1 x : ℝ) : ℂ) * (ψ x : ℂ)) (B0579.cell c) :=
      CTE.T20_7.integrableOn_X_test_complex (reLp c W.1) hψ
    have hJ2 : IntegrableOn (fun x => ((imLp c W.1 x : ℝ) : ℂ) * (ψ x : ℂ)) (B0579.cell c) :=
      CTE.T20_7.integrableOn_X_test_complex (imLp c W.1) hψ
    have hc1 : ∫ x in B0579.cell c, ((reLp c W.1 x : ℝ) : ℂ) * (ψ x : ℂ) =
        ∫ x in B0579.cell c,
          (u₁ x 0 * (B0579.pd 1 ψ x : ℂ) - u₁ x 1 * (B0579.pd 0 ψ x : ℂ)) := hcurl₁ ψ hψ
    have hc2 : ∫ x in B0579.cell c, ((imLp c W.1 x : ℝ) : ℂ) * (ψ x : ℂ) =
        ∫ x in B0579.cell c,
          (u₂ x 0 * (B0579.pd 1 ψ x : ℂ) - u₂ x 1 * (B0579.pd 0 ψ x : ℂ)) := hcurl₂ ψ hψ
    rw [integral_congr_ae hpt, integral_add hJ1 (hJ2.const_mul Complex.I),
      integral_const_mul, hc1, hc2,
      integral_congr_ae hcongr, integral_add hI1 (hI2.const_mul Complex.I), integral_const_mul]

private lemma hasWeakCellDerivC_velCCLM_q (W : ZC c) (i : Fin 2) :
    HasWeakCellDerivC c 0 (fun x => (velCCLM c W : B0579.Plane → B0581.Vel) x i)
      (fun x => (gqCCLM c W : B0579.Plane → B0581.Vel) x i) := by
  set U₁ := B0583.velocity c (by norm_num) (reLp c W.1) (zc_circRe_zero c W)
  set U₂ := B0583.velocity c (by norm_num) (imLp c W.1) (zc_circIm_zero c W)
  set GQ₁ := B0583.velGradQ c (by norm_num) (reLp c W.1)
  set GQ₂ := B0583.velGradQ c (by norm_num) (imLp c W.1)
  have h0 := BiotSavartH1Aux.hasWeakCellDerivC_add_I 0
    (BiotSavartH1Aux.hasWeakCellDerivC_of_velDeriv 0 U₁ GQ₁
      (B0583.hasWeakVelDeriv_velocity_q c (by norm_num) _ _) i)
    (BiotSavartH1Aux.hasWeakCellDerivC_of_velDeriv 0 U₂ GQ₂
      (B0583.hasWeakVelDeriv_velocity_q c (by norm_num) _ _) i)
  refine HasWeakCellDerivC.congr_ae ?_ ?_ h0
  · filter_upwards [Lp.coeFn_add U₁ (Complex.I • U₂), Lp.coeFn_smul Complex.I U₂] with x hx1 hx2
    change (U₁ + Complex.I • U₂ : Lp _ _ _) x i = U₁ x i + Complex.I * U₂ x i
    rw [hx1, Pi.add_apply, hx2]; rfl
  · filter_upwards [Lp.coeFn_add GQ₁ (Complex.I • GQ₂), Lp.coeFn_smul Complex.I GQ₂] with x hx1 hx2
    change (GQ₁ + Complex.I • GQ₂ : Lp _ _ _) x i = GQ₁ x i + Complex.I * GQ₂ x i
    rw [hx1, Pi.add_apply, hx2]; rfl

private lemma hasWeakCellDerivC_velCCLM_eta (W : ZC c) (i : Fin 2) :
    HasWeakCellDerivC c 1 (fun x => (velCCLM c W : B0579.Plane → B0581.Vel) x i)
      (fun x => (geCCLM c W : B0579.Plane → B0581.Vel) x i) := by
  set U₁ := B0583.velocity c (by norm_num) (reLp c W.1) (zc_circRe_zero c W)
  set U₂ := B0583.velocity c (by norm_num) (imLp c W.1) (zc_circIm_zero c W)
  set GE₁ := B0583.velGradEta c (by norm_num) (reLp c W.1) (zc_circRe_zero c W)
  set GE₂ := B0583.velGradEta c (by norm_num) (imLp c W.1) (zc_circIm_zero c W)
  have h1 := BiotSavartH1Aux.hasWeakCellDerivC_add_I 1
    (BiotSavartH1Aux.hasWeakCellDerivC_of_velDeriv 1 U₁ GE₁
      (B0583.hasWeakVelDeriv_velocity_eta c (by norm_num) _ _) i)
    (BiotSavartH1Aux.hasWeakCellDerivC_of_velDeriv 1 U₂ GE₂
      (B0583.hasWeakVelDeriv_velocity_eta c (by norm_num) _ _) i)
  refine HasWeakCellDerivC.congr_ae ?_ ?_ h1
  · filter_upwards [Lp.coeFn_add U₁ (Complex.I • U₂), Lp.coeFn_smul Complex.I U₂] with x hx1 hx2
    change (U₁ + Complex.I • U₂ : Lp _ _ _) x i = U₁ x i + Complex.I * U₂ x i
    rw [hx1, Pi.add_apply, hx2]; rfl
  · filter_upwards [Lp.coeFn_add GE₁ (Complex.I • GE₂), Lp.coeFn_smul Complex.I GE₂] with x hx1 hx2
    change (GE₁ + Complex.I • GE₂ : Lp _ _ _) x i = GE₁ x i + Complex.I * GE₂ x i
    rw [hx1, Pi.add_apply, hx2]; rfl

end BiotSavartCLM

/-! ## Section 2: Elementary scalar, `cpow`, `gainG`, & `1 + (s - t)^{-1/2}` helpers -/

private lemma gainG_pos (γ ν s : ℝ) : 0 < gainG γ ν s := Real.exp_pos _

private lemma gainG_le_exp {γ ν H s : ℝ} (hν : 0 < ν) (hs0 : 0 ≤ s) (hsH : s ≤ H) :
    gainG γ ν s ≤ Real.exp (|γ| * H) := by
  unfold gainG
  refine Real.exp_le_exp.2 ?_
  have hden : 1 ≤ 1 + ν * s := by nlinarith
  have h1 : γ * s / (1 + ν * s) ≤ |γ| * s / (1 + ν * s) :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self γ) hs0) (by linarith)
  have h2 : |γ| * s / (1 + ν * s) ≤ |γ| * s :=
    div_le_self (mul_nonneg (abs_nonneg γ) hs0) hden
  exact h1.trans (h2.trans (mul_le_mul_of_nonneg_left hsH (abs_nonneg γ)))

private lemma inv_gainG_le_exp {γ ν H s : ℝ} (hν : 0 < ν) (hs0 : 0 ≤ s) (hsH : s ≤ H) :
    (gainG γ ν s)⁻¹ ≤ Real.exp (|γ| * H) := by
  unfold gainG
  rw [← Real.exp_neg]
  refine Real.exp_le_exp.2 ?_
  have hden : 1 ≤ 1 + ν * s := by nlinarith
  have h1 : -(γ * s / (1 + ν * s)) ≤ |γ| * s / (1 + ν * s) := by
    have heq : -(γ * s / (1 + ν * s)) = (-γ) * s / (1 + ν * s) := by ring
    rw [heq]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (neg_le_abs γ) hs0) (by linarith)
  have h2 : |γ| * s / (1 + ν * s) ≤ |γ| * s :=
    div_le_self (mul_nonneg (abs_nonneg γ) hs0) hden
  exact h1.trans (h2.trans (mul_le_mul_of_nonneg_left hsH (abs_nonneg γ)))

private lemma continuousOn_gainG {γ ν : ℝ} (hν : 0 < ν) : ContinuousOn (gainG γ ν) (Ici 0) := by
  unfold gainG
  refine Real.continuous_exp.comp_continuousOn ?_
  exact (continuousOn_const.mul continuousOn_id).div
    (continuousOn_const.add (continuousOn_const.mul continuousOn_id))
    (fun s hs => by
      have hs0 : (0 : ℝ) ≤ s := hs
      linarith [mul_nonneg hν.le hs0])

private lemma cpow_ofReal_pos_eq_exp {r : ℝ} (hr : 0 < r) (z : ℂ) :
    ((r : ℂ) ^ z) = Complex.exp ((Real.log r : ℂ) * z) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.2 hr.ne'), ← Complex.ofReal_log hr.le]

private lemma cpow_div_ofReal_pos {t s : ℝ} (ht : 0 < t) (hs : 0 < s) (μ : ℂ) :
    ((t / s : ℝ) : ℂ) ^ μ = ((t : ℂ) ^ μ) * ((s : ℂ) ^ (-μ)) := by
  rw [cpow_ofReal_pos_eq_exp (div_pos ht hs) μ, cpow_ofReal_pos_eq_exp ht μ,
    cpow_ofReal_pos_eq_exp hs (-μ), ← Complex.exp_add, Real.log_div ht.ne' hs.ne']
  congr 1
  push_cast
  ring

private lemma cpow_mul_neg_ofReal_pos {r : ℝ} (hr : 0 < r) (μ : ℂ) :
    ((r : ℂ) ^ μ) * ((r : ℂ) ^ (-μ)) = 1 := by
  rw [cpow_ofReal_pos_eq_exp hr μ, cpow_ofReal_pos_eq_exp hr (-μ), ← Complex.exp_add]
  have : (Real.log r : ℂ) * μ + (Real.log r : ℂ) * (-μ) = 0 := by ring
  rw [this, Complex.exp_zero]

private def rawScalar (μ : ℂ) (γ ν t : ℝ) : ℂ := ((t : ℂ) ^ μ) * (gainG γ ν t : ℂ)

private def invScalar (μ : ℂ) (γ ν s : ℝ) : ℂ := ((s : ℂ) ^ (-μ)) * ((gainG γ ν s)⁻¹ : ℂ)

private def duhamelFactor (μ : ℂ) (γ ν s t : ℝ) : ℂ :=
  ((t / s : ℝ) : ℂ) ^ μ * ((gainG γ ν t / gainG γ ν s : ℝ) : ℂ)

private lemma duhamelFactor_eq_mul {t s : ℝ} (ht : 0 < t) (hs : 0 < s) (μ : ℂ) (γ ν : ℝ) :
    duhamelFactor μ γ ν s t = invScalar μ γ ν s * rawScalar μ γ ν t := by
  unfold duhamelFactor invScalar rawScalar
  rw [cpow_div_ofReal_pos ht hs μ, div_eq_mul_inv, Complex.ofReal_mul, Complex.ofReal_inv]
  ring

private lemma norm_rawScalar_le {μ : ℂ} (hμ0 : 0 < μ.re) {γ ν H t : ℝ} (hν : 0 < ν)
    (ht0 : 0 < t) (htH : t ≤ H) :
    ‖rawScalar μ γ ν t‖ ≤ H ^ μ.re * Real.exp (|γ| * H) := by
  unfold rawScalar
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0, Complex.norm_real,
    Real.norm_of_nonneg (gainG_pos γ ν t).le]
  exact mul_le_mul (Real.rpow_le_rpow ht0.le htH hμ0.le)
    (gainG_le_exp hν ht0.le htH) (gainG_pos γ ν t).le (Real.rpow_nonneg (ht0.le.trans htH) _)

private lemma norm_duhamelFactor_le {μ : ℂ} (hμ0 : 0 < μ.re) {γ ν H s t : ℝ} (hν : 0 < ν)
    (ht0 : 0 < t) (hts : t < s) (hsH : s ≤ H) :
    ‖duhamelFactor μ γ ν s t‖ ≤ Real.exp (|γ| * H) ^ 2 := by
  unfold duhamelFactor
  have hs0 : 0 < s := ht0.trans hts
  have hdiv_pos : 0 < t / s := div_pos ht0 hs0
  have hdiv_le : t / s ≤ 1 := (div_le_one hs0).2 hts.le
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hdiv_pos, Complex.norm_real,
    Real.norm_of_nonneg (div_pos (gainG_pos γ ν t) (gainG_pos γ ν s)).le]
  have h1 : (t / s) ^ μ.re ≤ 1 := Real.rpow_le_one hdiv_pos.le hdiv_le hμ0.le
  have h2 : gainG γ ν t / gainG γ ν s ≤ Real.exp (|γ| * H) ^ 2 := by
    rw [div_eq_mul_inv, sq]
    exact mul_le_mul (gainG_le_exp hν ht0.le (hts.le.trans hsH))
      (inv_gainG_le_exp hν hs0.le hsH) (inv_nonneg.2 (gainG_pos γ ν s).le) (Real.exp_pos _).le
  calc (t / s) ^ μ.re * (gainG γ ν t / gainG γ ν s)
      ≤ 1 * Real.exp (|γ| * H) ^ 2 :=
        mul_le_mul h1 h2 (div_pos (gainG_pos γ ν t) (gainG_pos γ ν s)).le zero_le_one
    _ = Real.exp (|γ| * H) ^ 2 := one_mul _

private lemma continuousOn_rawScalar (μ : ℂ) {γ ν : ℝ} (hν : 0 < ν) :
    ContinuousOn (rawScalar μ γ ν) (Ioi 0) := by
  have hlog : ContinuousOn Real.log (Ioi 0) :=
    Real.continuousOn_log.mono (fun x (hx : 0 < x) => hx.ne')
  have hcpow : ContinuousOn (fun t : ℝ => (t : ℂ) ^ μ) (Ioi 0) := by
    refine (Complex.continuous_exp.comp_continuousOn
      ((Complex.continuous_ofReal.comp_continuousOn hlog).mul
        (continuousOn_const (c := μ)))).congr ?_
    intro t ht
    have ht' : 0 < t := ht
    exact cpow_ofReal_pos_eq_exp ht' μ
  exact hcpow.mul (Complex.continuous_ofReal.comp_continuousOn
    ((continuousOn_gainG hν).mono Ioi_subset_Ici_self))

private lemma continuousOn_invScalar (μ : ℂ) {γ ν : ℝ} (hν : 0 < ν) :
    ContinuousOn (invScalar μ γ ν) (Ioi 0) := by
  have hlog : ContinuousOn Real.log (Ioi 0) :=
    Real.continuousOn_log.mono (fun x (hx : 0 < x) => hx.ne')
  have hcpow : ContinuousOn (fun s : ℝ => (s : ℂ) ^ (-μ)) (Ioi 0) := by
    refine (Complex.continuous_exp.comp_continuousOn
      ((Complex.continuous_ofReal.comp_continuousOn hlog).mul
        (continuousOn_const (c := -μ)))).congr ?_
    intro s hs
    have hs' : 0 < s := hs
    exact cpow_ofReal_pos_eq_exp hs' (-μ)
  have hginv : ContinuousOn (fun s : ℝ => ((gainG γ ν s : ℂ))⁻¹) (Ioi 0) :=
    (Complex.continuous_ofReal.comp_continuousOn
      ((continuousOn_gainG hν).mono Ioi_subset_Ici_self)).inv₀
      (fun s _ => Complex.ofReal_ne_zero.2 (gainG_pos γ ν s).ne')
  exact hcpow.mul hginv

private lemma integrableOn_one_add_inv_sqrt {a s : ℝ} (has : a ≤ s) :
    IntegrableOn (fun t : ℝ => 1 + (s - t) ^ (-1 / 2 : ℝ)) (Ioo a s) ∧
    ∫ t in Ioo a s, (1 + (s - t) ^ (-1 / 2 : ℝ)) = (s - a) + 2 * (s - a) ^ (1 / 2 : ℝ) := by
  have hi_u : IntervalIntegrable (fun u : ℝ => 1 + u ^ (-1 / 2 : ℝ)) volume 0 (s - a) :=
    intervalIntegrable_const.add (intervalIntegral.intervalIntegrable_rpow' (by norm_num))
  have hi_t : IntervalIntegrable (fun t : ℝ => 1 + (s - t) ^ (-1 / 2 : ℝ)) volume a s := by
    have := (hi_u.comp_sub_left s).symm
    simpa [sub_sub_cancel, sub_zero] using this
  have hint_Ioc : IntegrableOn (fun t : ℝ => 1 + (s - t) ^ (-1 / 2 : ℝ)) (Ioc a s) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le has).1 hi_t
  refine ⟨hint_Ioc.mono_set Ioo_subset_Ioc_self, ?_⟩
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le has]
  have hsub := intervalIntegral.integral_comp_sub_left (fun u : ℝ => 1 + u ^ (-1 / 2 : ℝ)) s
    (a := a) (b := s)
  rw [sub_self] at hsub
  rw [hsub, intervalIntegral.integral_add intervalIntegrable_const
    (intervalIntegral.intervalIntegrable_rpow' (by norm_num)),
    intervalIntegral.integral_const, integral_rpow (Or.inl (by norm_num))]
  have h0 : (0 : ℝ) ^ ((-1 / 2 : ℝ) + 1) = 0 := Real.zero_rpow (by norm_num)
  have he : (-1 / 2 : ℝ) + 1 = 1 / 2 := by norm_num
  rw [h0, he, smul_eq_mul]
  ring

/-! ## Section 3: Bochner-to-pointwise integral identification in `XC c` -/

private lemma bochner_integral_ae_eq_pointwise {c s : ℝ} {u : ℝ → XC c}
    (hu : IntegrableOn u (Ioo 0 s) volume)
    {k : ℝ → ℝ × ℝ → ℂ} (hkm : Measurable (Function.uncurry k))
    (hk_rep : ∀ t ∈ Ioo 0 s, k t =ᵐ[B0579.cellMeasure c 9] (u t : ℝ × ℝ → ℂ)) :
    ((∫ t in Ioo 0 s, u t : XC c) : ℝ × ℝ → ℂ)
      =ᵐ[volume.restrict (B0579.cell c)] fun x => ∫ t in Ioo 0 s, k t x := by
  let μ9 := B0579.cellMeasure c 9
  have : SigmaFinite μ9 := V3.sigmaFinite_cellMeasure' c 9
  set g : ℝ × ℝ → ℂ := fun x => ∫ t in Ioo 0 s, k t x
  have hkm_swap : AEStronglyMeasurable (Function.uncurry fun (x : ℝ × ℝ) (t : ℝ) => k t x)
      (μ9.prod (volume.restrict (Ioo 0 s))) :=
    (hkm.comp measurable_swap).aestronglyMeasurable
  have hmink := UnforcedLeray.PlanarBS.Conv.eLpNorm_integral_le (μ := μ9)
    (ν := volume.restrict (Ioo 0 s)) hkm_swap (p := 2) (by norm_num) (by norm_num)
  have hlint_u : ∫⁻ t in Ioo 0 s, eLpNorm (k t) 2 μ9 < ⊤ := by
    have hcongr : ∫⁻ t in Ioo 0 s, eLpNorm (k t) 2 μ9 = ∫⁻ t in Ioo 0 s, ‖u t‖ₑ := by
      refine setLIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
      rw [eLpNorm_congr_ae (hk_rep t ht), ← ofReal_norm, Lp.norm_def,
        ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top (u t))]
    rw [hcongr]
    exact hu.2
  have hg_meas : StronglyMeasurable g := by
    have hm : StronglyMeasurable (Function.uncurry fun (x : ℝ × ℝ) (t : ℝ) => k t x) :=
      (hkm.comp measurable_swap).stronglyMeasurable
    exact hm.integral_prod_right'
  have hg_mem : MemLp g 2 μ9 := ⟨hg_meas.aestronglyMeasurable, lt_of_le_of_lt hmink hlint_u⟩
  set G : XC c := hg_mem.toLp g
  set W : XC c := ∫ t in Ioo 0 s, u t
  have hWG : W = G := by
    refine ext_inner_left ℂ fun ψ => ?_
    have hL : ⟪ψ, W⟫ = ∫ t in Ioo 0 s, ⟪ψ, u t⟫ :=
      (((innerSL ℂ ψ).restrictScalars ℝ).integral_comp_comm hu).symm
    have hprod_int : Integrable (fun q : ℝ × (ℝ × ℝ) => starRingEnd ℂ (ψ q.2) * k q.1 q.2)
        ((volume.restrict (Ioo 0 s)).prod μ9) := by
      have hsm : AEStronglyMeasurable (fun q : ℝ × (ℝ × ℝ) => starRingEnd ℂ (ψ q.2) * k q.1 q.2)
          ((volume.restrict (Ioo 0 s)).prod μ9) :=
        ((Complex.continuous_conj.comp_stronglyMeasurable
          ((Lp.stronglyMeasurable ψ).comp_measurable measurable_snd)).aestronglyMeasurable).mul
          hkm.aestronglyMeasurable
      refine ⟨hsm, ?_⟩
      rw [HasFiniteIntegral, lintegral_prod _ hsm.enorm]
      have hsec : ∀ t ∈ Ioo (0 : ℝ) s,
          ∫⁻ x, ‖starRingEnd ℂ (ψ x) * k t x‖ₑ ∂μ9 ≤ eLpNorm ψ 2 μ9 * ‖u t‖ₑ := by
        intro t ht
        have hkt_m : Measurable (k t) :=
          hkm.comp ((measurable_const : Measurable fun _ : ℝ × ℝ => t).prodMk measurable_id)
        have h1 := ENNReal.lintegral_mul_le_Lp_mul_Lq μ9 Real.HolderConjugate.two_two
          (Lp.aestronglyMeasurable ψ).enorm hkt_m.aemeasurable.enorm
        calc ∫⁻ x, ‖starRingEnd ℂ (ψ x) * k t x‖ₑ ∂μ9
            = ∫⁻ x, ‖ψ x‖ₑ * ‖k t x‖ₑ ∂μ9 := by
              refine lintegral_congr fun x => ?_
              rw [enorm_mul, RCLike.enorm_conj]
          _ ≤ (∫⁻ x, ‖ψ x‖ₑ ^ (2 : ℝ) ∂μ9) ^ (1 / 2 : ℝ) *
                (∫⁻ x, ‖k t x‖ₑ ^ (2 : ℝ) ∂μ9) ^ (1 / 2 : ℝ) := h1
          _ = eLpNorm ψ 2 μ9 * eLpNorm (k t) 2 μ9 := by
              rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top,
                eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top]
              norm_num
          _ = eLpNorm ψ 2 μ9 * ‖u t‖ₑ := by
              rw [eLpNorm_congr_ae (hk_rep t ht), ← ofReal_norm, Lp.norm_def,
                ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top (u t))]
      calc ∫⁻ t in Ioo 0 s, ∫⁻ x, ‖starRingEnd ℂ (ψ x) * k t x‖ₑ ∂μ9
          ≤ ∫⁻ t in Ioo 0 s, eLpNorm ψ 2 μ9 * ‖u t‖ₑ :=
            setLIntegral_mono' measurableSet_Ioo hsec
        _ = eLpNorm ψ 2 μ9 * ∫⁻ t in Ioo 0 s, ‖u t‖ₑ :=
            lintegral_const_mul' _ _ (Lp.eLpNorm_ne_top ψ)
        _ < ⊤ := ENNReal.mul_lt_top (Lp.eLpNorm_lt_top ψ) hu.2
    have hR : ⟪ψ, G⟫ = ∫ t in Ioo 0 s, ⟪ψ, u t⟫ := by
      rw [L2.inner_def]
      have hG_ae : ∀ᵐ x ∂μ9, ⟪(ψ : ℝ × ℝ → ℂ) x, (G : ℝ × ℝ → ℂ) x⟫ =
          ∫ t in Ioo 0 s, starRingEnd ℂ (ψ x) * k t x := by
        filter_upwards [MemLp.coeFn_toLp hg_mem] with x hx
        rw [hx, RCLike.inner_apply, mul_comm, ← integral_const_mul]
      rw [integral_congr_ae hG_ae,
        ← integral_integral_swap (f := fun t x => starRingEnd ℂ (ψ x) * k t x) hprod_int]
      refine setIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
      rw [L2.inner_def]
      refine integral_congr_ae ?_
      filter_upwards [hk_rep t ht] with x hx
      rw [RCLike.inner_apply, hx, mul_comm]
    rw [hL, hR]
  have hWG_ae : (W : ℝ × ℝ → ℂ) =ᵐ[μ9] g := by
    rw [hWG]
    exact MemLp.coeFn_toLp hg_mem
  exact (B0579.ac_cellMeasure c 9).ae_le hWG_ae

/-! ## Section 4: Zero-datum flow, weak curl uniqueness, & `ladFlowCx` complex-scalar helpers -/

private lemma isLinearisedFlow_zero_of_eq_zero {ν c m t : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c)
    {f₀ : ℝ × ℝ → ℂ} (hf₀ : ∀ x, f₀ x = 0) :
    IsLinearisedFlow ν c m tr t f₀ (fun _ _ => 0) (fun _ _ _ => 0) where
  initial := Eventually.of_forall fun x => (hf₀ x).symm
  memX := fun _ _ => MemLp.zero
  strongCont := fun s _ => by
    have h0 : (fun s' : ℝ => xNorm c m ((fun _ : ℝ × ℝ => (0 : ℂ)) - (fun _ => 0))) =
        fun _ => 0 := by
      funext s'
      simp [xNorm]
    rw [h0]
    exact tendsto_const_nhds
  biotSavart := fun _ _ => ⟨fun _ => MemLp.zero, fun _ _ => by simp, fun _ _ => by simp⟩
  integrable := fun φ _ r _ => by
    have h0 : flowIntegrand tr (fun _ => 0) (fun _ _ => 0) r φ = fun _ => 0 := by
      funext x; simp [flowIntegrand]
    rw [h0]; exact integrableOn_zero
  timeIntegrable := fun φ _ s _ => by
    have h0 : (fun r => ∫ x in B0579.cell c, flowIntegrand tr (fun _ => 0) (fun _ _ => 0) r φ x) =
        fun _ => 0 := by
      funext r; simp [flowIntegrand]
    rw [h0]; exact intervalIntegrable_const
  weak := fun φ _ s _ => by
    simp [flowIntegrand, hf₀]

private lemma ae_eq_of_isBiotSavart_same_vel {c : ℝ} {g₁ g₂ : ℝ × ℝ → ℂ}
    {u : ℝ × ℝ → Fin 2 → ℂ}
    (hg₁ : MemLp g₁ 2 (volume.restrict (B0579.cell c)))
    (hg₂ : MemLp g₂ 2 (volume.restrict (B0579.cell c)))
    (hbs₁ : IsBiotSavart c g₁ u) (hbs₂ : IsBiotSavart c g₂ u) :
    g₁ =ᵐ[volume.restrict (B0579.cell c)] g₂ := by
  have hw₁ : HasWeakCellDerivC c 0 (fun _ => 0) (fun x => g₁ x - g₂ x) := by
    refine ⟨fun ψ hψ => ⟨by simp, ?_⟩, fun ψ hψ => ?_⟩
    · have i₁ := CoreDuhamelRepSub.integrableOn_cylTest_mul hψ hg₁
      have i₂ := CoreDuhamelRepSub.integrableOn_cylTest_mul hψ hg₂
      exact (i₁.sub i₂).congr_fun_ae (Eventually.of_forall fun x => by dsimp; ring)
    · have i₁ := CoreDuhamelRepSub.integrableOn_cylTest_mul hψ hg₁
      have i₂ := CoreDuhamelRepSub.integrableOn_cylTest_mul hψ hg₂
      have heq : (fun x => (g₁ x - g₂ x) * (ψ x : ℂ)) =
          fun x => g₁ x * (ψ x : ℂ) - g₂ x * (ψ x : ℂ) := funext fun _ => sub_mul _ _ _
      rw [heq, integral_sub i₁ i₂, hbs₁.2.2 ψ hψ, hbs₂.2.2 ψ hψ, sub_self]
      simp
  have hw₂ : HasWeakCellDerivC c 0 (fun _ => 0) (fun _ => 0) :=
    ⟨fun _ _ => ⟨by simp, by simp⟩, fun _ _ => by simp⟩
  have h0 := weakCellAeUnique c 0 (fun _ => 0) (fun x => g₁ x - g₂ x) (fun _ => 0) hw₁ hw₂
  filter_upwards [h0] with x hx
  exact sub_eq_zero.1 hx

private lemma ladFlowCx_const_mul_ofReal {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c)
    (om : ℝ × ℝ → ℂ) (u : ℝ × ℝ → Fin 2 → ℂ) (ρ : ℝ) (z : ℂ)
    {a : ℝ × ℝ → ℝ} (ha : B0579.IsCylTest c a) (x : ℝ × ℝ) :
    ladFlowCx tr om u ρ (fun y => z * (a y : ℂ)) x = z * flowIntegrand tr om u ρ a x := by
  have hA : ContDiff ℝ ∞ (fun _ : ℝ × ℝ => (0 : ℂ)) := contDiff_const
  have hB : ContDiff ℝ ∞ (fun y : ℝ × ℝ => (a y : ℂ)) := RateSplitAux.contDiff_ofReal ha.smooth
  have hfun : (fun y : ℝ × ℝ => z * (a y : ℂ)) = fun y => (0 : ℂ) + (a y : ℂ) * z := by
    funext y; ring
  have hp0 : ∀ j, pdCx j (fun _ : ℝ × ℝ => (0 : ℂ)) = fun _ => 0 := fun j => by
    funext y; simp [pdCx]
  have hlap0 : ladLapCx (fun _ : ℝ × ℝ => (0 : ℂ)) x = 0 := by simp [ladLapCx, hp0]
  have htr0 : ladTransport tr ρ (fun _ : ℝ × ℝ => (0 : ℂ)) x = 0 := by simp [ladTransport, hp0]
  rw [hfun]
  unfold ladFlowCx
  rw [LadPRWeakAux.ladLapCx_lin hA hB z x, LadPRWeakAux.ladTransport_lin tr ρ hA hB z x,
    hlap0, htr0, zero_add, zero_add, LadPRWeakAux.ladLapCx_ofReal ha x,
    LadPRWeakAux.ladTransport_ofReal tr ρ ha x]
  unfold flowIntegrand ladForce
  push_cast
  ring

private lemma flowIntegrand_const_smul {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c)
    (om : ℝ × ℝ → ℂ) (u : ℝ × ℝ → Fin 2 → ℂ) (ρ : ℝ) (α : ℂ) (a : ℝ × ℝ → ℝ) (x : ℝ × ℝ) :
    flowIntegrand tr (fun y => α * om y) (fun y => α • u y) ρ a x =
      α * flowIntegrand tr om u ρ a x := by
  unfold flowIntegrand
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

private def smulZCLM (c : ℝ) (z : ℂ) : ZC c →L[ℝ] ZC c :=
  LinearMap.mkContinuous
    { toFun := fun W => z • W
      map_add' := fun W₁ W₂ => smul_add z W₁ W₂
      map_smul' := fun (a : ℝ) W => by
        simp only [RingHom.id_apply]
        apply Subtype.ext
        change z • ((a : ℝ) • W.1) = (a : ℝ) • (z • W.1)
        apply Lp.ext
        filter_upwards [Lp.coeFn_smul z ((a : ℝ) • W.1), Lp.coeFn_smul a W.1,
          Lp.coeFn_smul a (z • W.1), Lp.coeFn_smul z W.1] with x h1 h2 h3 h4
        rw [h1, Pi.smul_apply, h2, Pi.smul_apply, h3, Pi.smul_apply, h4, Pi.smul_apply,
          Complex.real_smul, Complex.real_smul, smul_eq_mul, smul_eq_mul]
        ring }
    ‖z‖
    (fun W => by
      change ‖z • W‖ ≤ ‖z‖ * ‖W‖
      rw [norm_smul])

private lemma isBiotSavart_congr_ae {c : ℝ} {ω₁ ω₂ : ℝ × ℝ → ℂ}
    {u₁ u₂ : ℝ × ℝ → Fin 2 → ℂ}
    (hω : ω₁ =ᵐ[volume.restrict (B0579.cell c)] ω₂)
    (hu : ∀ j, (fun x => u₁ x j) =ᵐ[volume.restrict (B0579.cell c)] (fun x => u₂ x j))
    (hbs : IsBiotSavart c ω₁ u₁) :
    IsBiotSavart c ω₂ u₂ := by
  refine ⟨fun j => (hbs.1 j).ae_eq (hu j), fun ψ hψ => ?_, fun ψ hψ => ?_⟩
  · rw [← hbs.2.1 ψ hψ]
    refine integral_congr_ae ?_
    filter_upwards [hu 0, hu 1] with x hx0 hx1
    rw [hx0, hx1]
  · have hL : ∫ x in B0579.cell c, ω₂ x * (ψ x : ℂ) = ∫ x in B0579.cell c, ω₁ x * (ψ x : ℂ) := by
      refine integral_congr_ae ?_
      filter_upwards [hω] with x hx
      rw [hx]
    have hR : ∫ x in B0579.cell c, (u₂ x 0 * (B0579.pd 1 ψ x : ℂ) - u₂ x 1 * (B0579.pd 0 ψ x : ℂ)) =
        ∫ x in B0579.cell c, (u₁ x 0 * (B0579.pd 1 ψ x : ℂ) - u₁ x 1 * (B0579.pd 0 ψ x : ℂ)) := by
      refine integral_congr_ae ?_
      filter_upwards [hu 0, hu 1] with x hx0 hx1
      rw [hx0, hx1]
    rw [hL, hR, hbs.2.2 ψ hψ]

private lemma memLp_conj_cellVol {c : ℝ} {B : ℝ × ℝ → ℂ} (hB : MemLp B 2 (B0581.cellVol c)) :
    MemLp (fun x => starRingEnd ℂ (B x)) 2 (B0581.cellVol c) :=
  Complex.conjCLE.toContinuousLinearMap.comp_memLp' hB

private def pairCellCLM (c : ℝ) (B : ℝ × ℝ → ℂ) (hB : MemLp B 2 (B0581.cellVol c)) :
    Lp ℂ 2 (B0581.cellVol c) →L[ℂ] ℂ :=
  innerSL ℂ ((memLp_conj_cellVol hB).toLp (fun x => starRingEnd ℂ (B x)))

private lemma pairCellCLM_integrable {c : ℝ} {B : ℝ × ℝ → ℂ}
    (hB : MemLp B 2 (B0581.cellVol c)) (F : Lp ℂ 2 (B0581.cellVol c)) :
    IntegrableOn (fun x => (F : ℝ × ℝ → ℂ) x * B x) (B0579.cell c) := by
  let Bc := (memLp_conj_cellVol hB).toLp (fun x => starRingEnd ℂ (B x))
  refine (L2.integrable_inner Bc F).congr ?_
  filter_upwards [MemLp.coeFn_toLp (memLp_conj_cellVol hB)] with x hx
  change ⟪(Bc : ℝ × ℝ → ℂ) x, (F : ℝ × ℝ → ℂ) x⟫ = (F : ℝ × ℝ → ℂ) x * B x
  dsimp only [Bc]
  rw [hx, RCLike.inner_apply, starRingEnd_self_apply]

private lemma pairCellCLM_apply {c : ℝ} {B : ℝ × ℝ → ℂ}
    (hB : MemLp B 2 (B0581.cellVol c)) (F : Lp ℂ 2 (B0581.cellVol c)) :
    pairCellCLM c B hB F = ∫ x in B0579.cell c, (F : ℝ × ℝ → ℂ) x * B x := by
  unfold pairCellCLM
  let Bc := (memLp_conj_cellVol hB).toLp (fun x => starRingEnd ℂ (B x))
  change ⟪Bc, F⟫ = _
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [MemLp.coeFn_toLp (memLp_conj_cellVol hB)] with x hx
  dsimp only [Bc]
  rw [hx, RCLike.inner_apply, starRingEnd_self_apply]

private lemma norm_pairCellCLM_apply_le {c : ℝ} {B : ℝ × ℝ → ℂ}
    (hB : MemLp B 2 (B0581.cellVol c)) (F : Lp ℂ 2 (B0581.cellVol c)) :
    ‖pairCellCLM c B hB F‖ ≤ (eLpNorm B 2 (B0581.cellVol c)).toReal * ‖F‖ := by
  unfold pairCellCLM
  let Bc := (memLp_conj_cellVol hB).toLp (fun x => starRingEnd ℂ (B x))
  change ‖⟪Bc, F⟫‖ ≤ _
  have h1 : ‖⟪Bc, F⟫‖ ≤ ‖Bc‖ * ‖F‖ := norm_inner_le_norm Bc F
  have h2 : ‖Bc‖ = (eLpNorm B 2 (B0581.cellVol c)).toReal := by
    dsimp only [Bc]
    rw [Lp.norm_toLp]
    congr 1
    exact eLpNorm_congr_norm_ae (Eventually.of_forall fun x => RCLike.norm_conj (B x))
  rwa [h2] at h1

private lemma ofReal_cpow_contDiffAt (z : ℂ) {s0 : ℝ} (hs0 : 0 < s0) :
    ContDiffAt ℝ ∞ (fun s : ℝ => (s : ℂ) ^ z) s0 := by
  have hev : ∀ᶠ s : ℝ in 𝓝 s0, (s : ℂ) ^ z = Complex.exp (((Real.log s : ℝ) : ℂ) * z) := by
    filter_upwards [Ioi_mem_nhds hs0] with s hs
    exact cpow_ofReal_pos_eq_exp hs z
  have h1 : ContDiffAt ℝ ∞ (fun s : ℝ => ((Real.log s : ℝ) : ℂ)) s0 :=
    (Complex.ofRealCLM.contDiff.contDiffAt).comp s0 (Real.contDiffAt_log.2 hs0.ne')
  exact ((h1.mul contDiffAt_const).cexp).congr_of_eventuallyEq hev

private lemma ofReal_cpow_hasDerivAt (z : ℂ) {s0 : ℝ} (hs0 : 0 < s0) :
    HasDerivAt (fun s : ℝ => (s : ℂ) ^ z) (z * (s0 : ℂ) ^ (z - 1)) s0 := by
  by_cases hz : z = 0
  · subst hz
    simp only [Complex.cpow_zero, zero_mul]
    exact hasDerivAt_const s0 (1 : ℂ)
  · exact hasDerivAt_ofReal_cpow_const hs0.ne' hz

/-! ## Section 5: Main theorem `niceFlowKernelConstruct` -/

theorem niceFlowKernelConstruct
    (P : PlanarData) (hP : IsPlanarReference P)
    (K : Set ℂ) (hK : IsAdmissibleK K)
    (b : ℝ) (hb : 1 ≤ b)
    (ν : ℝ) (hν0 : 0 < ν) (hν1 : ν ≤ 1 / 2) (hνb : ν ≤ (2 * b)⁻¹)
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)))
    (hflow : FullFlowExists ν (ν ^ (-2 : ℝ)) 9 tr)
    (μ : ℂ) (hμ : μ ∈ K)
    (C_clock : ℝ) (hclock : ClockBoundAt P 9 b C_clock ν tr)
    (f : ℝ → ℝ × ℝ → ℂ) (a_zero M_f : ℝ)
    (ha0 : 0 < a_zero) (hMf : 0 ≤ M_f)
    (hf_zero : ∀ t ≤ a_zero, ∀ x, f t x = 0)
    (hf_slice : ∀ t ∈ Ioc (0 : ℝ) (coreEnd ν b),
      MemLp (f t) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) 9) ∧
      HasZeroCirculation (ν ^ (-2 : ℝ)) (f t) ∧
      xNorm (ν ^ (-2 : ℝ)) 9 (f t) ≤ ENNReal.ofReal M_f)
    (hf_cont : ∀ t ∈ Ioo (0 : ℝ) (coreEnd ν b),
      Tendsto (fun t' => xNorm (ν ^ (-2 : ℝ)) 9 (f t' - f t)) (𝓝 t) (𝓝 0)) :
    ∃ (k_ker : ℝ → ℝ → ℝ × ℝ → ℂ)
      (ω_duh : ℝ → ℝ × ℝ → ℂ)
      (u_duh : ℝ × (ℝ × ℝ) → Fin 2 → ℂ)
      (G_duh : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ),
      (∀ i, Measurable fun p => u_duh p i) ∧
      (∀ i j, Measurable fun p => G_duh p i j) ∧
      (∀ s ≤ a_zero, ∀ x i, u_duh (s, x) i = 0) ∧
      (∀ s ≤ a_zero, ∀ x i j, G_duh (s, x) i j = 0) ∧
      (∃ M_duh : ℝ, 0 ≤ M_duh ∧ ∀ s ∈ Ioo (0 : ℝ) (coreEnd ν b),
        ∫⁻ x in B0579.cell (ν ^ (-2 : ℝ)),
          ENNReal.ofReal (vnorm2 (u_duh (s, x)) ^ 2 + tnorm2 (G_duh (s, x)) ^ 2) ≤
            ENNReal.ofReal M_duh) ∧
      (∀ s ∈ Ioo (0 : ℝ) (coreEnd ν b),
        (∀ i, MemLp (fun x => u_duh (s, x) i) 2
          (volume.restrict (B0579.cell (ν ^ (-2 : ℝ))))) ∧
        (∀ i j, MemLp (fun x => G_duh (s, x) i j) 2
          (volume.restrict (B0579.cell (ν ^ (-2 : ℝ))))) ∧
        MemLp (ω_duh s) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) 9) ∧
        (∀ ψ, B0579.IsCylTest (ν ^ (-2 : ℝ)) ψ →
          ∫ x in B0579.cell (ν ^ (-2 : ℝ)),
            (u_duh (s, x) 0 * (B0579.pd 0 ψ x : ℂ) +
              u_duh (s, x) 1 * (B0579.pd 1 ψ x : ℂ)) = 0) ∧
        (∀ i j, HasWeakCellDerivC (ν ^ (-2 : ℝ)) j
          (fun x => u_duh (s, x) i) (fun x => G_duh (s, x) i j)) ∧
        ((fun x => G_duh (s, x) 1 0 - G_duh (s, x) 0 1)
          =ᵐ[volume.restrict (B0579.cell (ν ^ (-2 : ℝ)))] ω_duh s) ∧
        Measurable (Function.uncurry (k_ker s)) ∧
        (∀ᵐ t ∂volume, t ∈ Ioo 0 s →
          ∃ (w : ℝ → ℝ × ℝ → ℂ) (u : ℝ → ℝ × ℝ → Fin 2 → ℂ),
            IsLinearisedFlow ν (ν ^ (-2 : ℝ)) 9 tr t (f t) w u ∧
            k_ker s t =ᵐ[volume.restrict (B0579.cell (ν ^ (-2 : ℝ)))]
              fun x => ((t / s : ℝ) : ℂ) ^ μ *
                ((gainG P.eigenvalue.re ν t / gainG P.eigenvalue.re ν s : ℝ) : ℂ) *
                w s x) ∧
        ω_duh s =ᵐ[volume.restrict (B0579.cell (ν ^ (-2 : ℝ)))]
          fun x => ∫ t in Ioo 0 s, k_ker s t x) ∧
      ∀ (ψ : ℝ → ℝ × ℝ → ℝ) (s₁ s₂ R₁ : ℝ),
        0 < s₁ → s₁ < s₂ → s₂ < coreEnd ν b → 0 < R₁ →
        ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => ψ p.1 p.2) →
        (∀ s x, ψ s (x.1 + ν ^ (-2 : ℝ), x.2) = ψ s x) →
        (∀ s x, (s < s₁ ∨ s₂ < s ∨ R₁ < |x.2|) → ψ s x = 0) →
        ∫ ρ in Ioo (0 : ℝ) (coreEnd ν b),
          ((∫ x in B0579.cell (ν ^ (-2 : ℝ)),
              flowIntegrand tr
                (fun y => (gainG P.eigenvalue.re ν ρ : ℂ) * ω_duh ρ y)
                (fun y => (gainG P.eigenvalue.re ν ρ : ℂ) • u_duh (ρ, y))
                ρ (ψ ρ) x) +
            (∫ x in B0579.cell (ν ^ (-2 : ℝ)),
              ((gainG P.eigenvalue.re ν ρ : ℂ) * ω_duh ρ x) *
                (-(μ / (ρ : ℂ)) * (ψ ρ x : ℂ) + (deriv (fun ρ' => ψ ρ' x) ρ : ℂ))) +
            (gainG P.eigenvalue.re ν ρ : ℂ) *
              ∫ x in B0579.cell (ν ^ (-2 : ℝ)), f ρ x * (ψ ρ x : ℂ)) = 0 := by
  let _ := hP
  let c : ℝ := ν ^ (-2 : ℝ)
  let H : ℝ := coreEnd ν b
  let γ : ℝ := P.eigenvalue.re
  have hH_gt_one : 1 < H := (coreEnd_bounds hb hν0 hν1 hνb).1
  have hH_pos : 0 < H := zero_lt_one.trans hH_gt_one
  have hc_ge_one : 1 ≤ c := by
    dsimp only [c]
    rw [Real.rpow_neg hν0.le]
    have hν_sq : ν ^ (2 : ℝ) ≤ 1 := by
      rw [Real.rpow_two]
      nlinarith
    exact one_le_inv₀ (Real.rpow_pos_of_pos hν0 2) |>.2 hν_sq
  have hc_pos : 0 < c := zero_lt_one.trans_le hc_ge_one
  have : Fact (0 < c) := ⟨hc_pos⟩
  obtain ⟨hμ_pos, _hμ_quarter⟩ := hK.2 μ hμ

  -- 1. Chosen linearised flow family `(w_fam t, u_fam t)`
  have hflow_ex : ∀ t : ℝ, t ∈ Ioc a_zero H →
      ∃ w u, IsLinearisedFlow ν c 9 tr t (f t) w u := by
    intro t ht
    have htI : t ∈ Ioc (0 : ℝ) H := ⟨ha0.trans ht.1, ht.2⟩
    exact hflow t htI.1.le (f t) (hf_slice t htI).1 (hf_slice t htI).2.1
  let w_fam : ℝ → ℝ → ℝ × ℝ → ℂ := fun t =>
    if ht : t ∈ Ioc a_zero H then Classical.choose (hflow_ex t ht) else fun _ _ => 0
  let u_fam : ℝ → ℝ → ℝ × ℝ → Fin 2 → ℂ := fun t =>
    if ht : t ∈ Ioc a_zero H then Classical.choose (Classical.choose_spec (hflow_ex t ht))
    else fun _ _ _ => 0
  have hw_fam : ∀ {t : ℝ}, t ∈ Ioc (0 : ℝ) H →
      IsLinearisedFlow ν c 9 tr t (f t) (w_fam t) (u_fam t) := by
    intro t ht
    by_cases hta : a_zero < t
    · have ht' : t ∈ Ioc a_zero H := ⟨hta, ht.2⟩
      simp only [w_fam, u_fam, ht', ↓reduceDIte]
      exact Classical.choose_spec (Classical.choose_spec (hflow_ex t ht'))
    · have hle : t ≤ a_zero := not_lt.1 hta
      have ht' : t ∉ Ioc a_zero H := fun h => hta h.1
      simp only [w_fam, u_fam, ht', ↓reduceDIte]
      exact isLinearisedFlow_zero_of_eq_zero tr (hf_zero t hle)
  have hw_fam_zero : ∀ {t : ℝ}, t ≤ a_zero → w_fam t = fun _ _ => 0 := by
    intro t hta
    have ht' : t ∉ Ioc a_zero H := fun h => not_lt_of_ge hta h.1
    simp only [w_fam, ht', ↓reduceDIte]

  -- Lift `w_fam t s` to `ZC c`
  let wZ : ℝ → ℝ → ZC c := fun t s =>
    if ht : t ∈ Ioc (0 : ℝ) H then
      if hts : t ≤ s then
        toZC ((hw_fam ht).memX s hts)
          (CoreDuhamelRepSub.hasZeroCirculation_of_isLinearisedFlow hc_pos hts (hw_fam ht))
      else 0
    else 0
  have hwZ_zero : ∀ {t s : ℝ}, t ≤ a_zero → wZ t s = 0 := by
    intro t s hta
    dsimp only [wZ]
    split_ifs with ht hts
    · apply Subtype.ext
      apply Lp.ext
      filter_upwards [MemLp.coeFn_toLp ((hw_fam ht).memX s hts),
        Lp.coeFn_zero ℂ 2 (B0579.cellMeasure c 9)] with x hx1 hx2
      change (((hw_fam ht).memX s hts).toLp (w_fam t s) : ℝ × ℝ → ℂ) x =
        ((0 : XC c) : ℝ × ℝ → ℂ) x
      rw [hx1, hx2, hw_fam_zero hta]
      rfl
    · rfl
    · rfl
  have hwZ_rep : ∀ {t s : ℝ} (ht : t ∈ Ioc (0 : ℝ) H) (hts : t ≤ s),
      ((wZ t s).1 : ℝ × ℝ → ℂ) =ᵐ[B0579.cellMeasure c 9] w_fam t s := by
    intro t s ht hts
    simp only [wZ, ht, hts, ↓reduceDIte]
    exact MemLp.coeFn_toLp ((hw_fam ht).memX s hts)
  have hwZ_norm : ∀ {t s : ℝ} (ht : t ∈ Ioc (0 : ℝ) H) (hts : t ≤ s),
      ‖wZ t s‖ = (xNorm c 9 (w_fam t s)).toReal := by
    intro t s ht hts
    simp only [wZ, ht, hts, ↓reduceDIte, norm_toZC]

  -- 2. Clock bounds on `wZ` (single & restart comparison)
  let M_exp : ℝ := Real.exp (|γ| * H)
  have hM_exp_pos : 0 < M_exp := Real.exp_pos _
  let C_clk : ℝ := (|C_clock| * ν ^ (-(weakDegree 9 P.kappa : ℝ))) * M_exp ^ 2
  have hC_clk_nn : 0 ≤ C_clk := by positivity

  have hclock_real : ∀ {t s : ℝ} (ht0 : 0 < t) (hts : t < s) (hsH : s ≤ H)
      {h : ℝ × ℝ → ℂ} {w : ℝ → ℝ × ℝ → ℂ} {u : ℝ → ℝ × ℝ → Fin 2 → ℂ}
      (hh_mem : MemLp h 2 (B0579.cellMeasure c 9)) (hh_zc : HasZeroCirculation c h)
      (hw : IsLinearisedFlow ν c 9 tr t h w u),
      (xNorm c 9 (w s)).toReal ≤
        C_clk * (1 + (s - t) ^ (-1 / 2 : ℝ)) * (xNorm c 9 h).toReal := by
    intro t s ht0 hts hsH h w u hh_mem hh_zc hw
    have hs0 : 0 < s := ht0.trans hts
    have hcb := hclock t s ht0 hts hsH h hh_mem hh_zc w u hw
    have hgt_pos : 0 < gainG γ ν t := gainG_pos γ ν t
    have hgs_pos : 0 < gainG γ ν s := gainG_pos γ ν s
    have hratio_pos : 0 < gainG γ ν s / gainG γ ν t := div_pos hgs_pos hgt_pos
    have hratio_le : gainG γ ν s / gainG γ ν t ≤ M_exp ^ 2 := by
      rw [div_eq_mul_inv, sq]
      exact mul_le_mul (gainG_le_exp hν0 hs0.le hsH)
        (inv_gainG_le_exp hν0 ht0.le (hts.le.trans hsH))
        (inv_nonneg.2 hgt_pos.le) hM_exp_pos.le
    have hcancel : ENNReal.ofReal (gainG γ ν s / gainG γ ν t) *
        ENNReal.ofReal (gainG γ ν t / gainG γ ν s) = 1 := by
      rw [← ENNReal.ofReal_mul hratio_pos.le, div_mul_div_cancel₀ hgt_pos.ne',
        div_self hgs_pos.ne', ENNReal.ofReal_one]
    have hker_pos : 0 ≤ 1 + (s - t) ^ (-1 / 2 : ℝ) := by
      have : 0 ≤ (s - t) ^ (-1 / 2 : ℝ) := Real.rpow_nonneg (sub_pos.2 hts).le _
      linarith
    have hC_le : C_clock * ν ^ (-(weakDegree 9 P.kappa : ℝ)) * (1 + (s - t) ^ (-1 / 2 : ℝ)) ≤
        |C_clock| * ν ^ (-(weakDegree 9 P.kappa : ℝ)) * (1 + (s - t) ^ (-1 / 2 : ℝ)) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_abs_self C_clock) (Real.rpow_nonneg hν0.le _)) hker_pos
    have hstep : xNorm c 9 (w s) ≤
        ENNReal.ofReal (C_clk * (1 + (s - t) ^ (-1 / 2 : ℝ)) * (xNorm c 9 h).toReal) := by
      calc xNorm c 9 (w s)
          = 1 * xNorm c 9 (w s) := (one_mul _).symm
        _ = ENNReal.ofReal (gainG γ ν s / gainG γ ν t) *
              (ENNReal.ofReal (gainG γ ν t / gainG γ ν s) * xNorm c 9 (w s)) := by
            rw [← mul_assoc, hcancel]
        _ ≤ ENNReal.ofReal (gainG γ ν s / gainG γ ν t) *
              (ENNReal.ofReal (C_clock * ν ^ (-(weakDegree 9 P.kappa : ℝ)) *
                (1 + (s - t) ^ (-1 / 2 : ℝ))) * negNorm c 9 h) :=
            mul_le_mul_of_nonneg_left hcb bot_le
        _ ≤ ENNReal.ofReal (M_exp ^ 2) *
              (ENNReal.ofReal (|C_clock| * ν ^ (-(weakDegree 9 P.kappa : ℝ)) *
                (1 + (s - t) ^ (-1 / 2 : ℝ))) * xNorm c 9 h) :=
            mul_le_mul (ENNReal.ofReal_le_ofReal hratio_le)
              (mul_le_mul (ENNReal.ofReal_le_ofReal hC_le) (negNorm_le_xNorm hh_mem)
                bot_le bot_le) bot_le bot_le
        _ = ENNReal.ofReal (C_clk * (1 + (s - t) ^ (-1 / 2 : ℝ)) * (xNorm c 9 h).toReal) := by
            have hx_eq : xNorm c 9 h = ENNReal.ofReal (xNorm c 9 h).toReal :=
              (ENNReal.ofReal_toReal hh_mem.2.ne).symm
            conv_lhs => rw [hx_eq]
            rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
              ← ENNReal.ofReal_mul (by positivity)]
            congr 1
            dsimp [C_clk]
            ring
    have hres := ENNReal.toReal_mono ENNReal.ofReal_ne_top hstep
    rwa [ENNReal.toReal_ofReal (by positivity)] at hres

  have hwZ_bound : ∀ {t s : ℝ} (ht0 : 0 < t) (hts : t < s) (hsH : s ≤ H),
      ‖wZ t s‖ ≤ C_clk * (1 + (s - t) ^ (-1 / 2 : ℝ)) * M_f := by
    intro t s ht0 hts hsH
    have ht : t ∈ Ioc (0 : ℝ) H := ⟨ht0, hts.le.trans hsH⟩
    rw [hwZ_norm ht hts.le]
    have h1 := hclock_real ht0 hts hsH (hf_slice t ht).1 (hf_slice t ht).2.1 (hw_fam ht)
    have hf_le : (xNorm c 9 (f t)).toReal ≤ M_f := by
      have := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hf_slice t ht).2.2
      rwa [ENNReal.toReal_ofReal hMf] at this
    have hker_nn : 0 ≤ C_clk * (1 + (s - t) ^ (-1 / 2 : ℝ)) := by
      have : 0 ≤ (s - t) ^ (-1 / 2 : ℝ) := Real.rpow_nonneg (sub_pos.2 hts).le _
      positivity
    exact h1.trans (mul_le_mul_of_nonneg_left hf_le hker_nn)

  have hwZ_restart_diff : ∀ {t τ s : ℝ} (ht0 : 0 < t) (htτ : t ≤ τ) (hτs : τ < s) (hsH : s ≤ H),
      ‖wZ t s - wZ τ s‖ ≤ C_clk * (1 + (s - τ) ^ (-1 / 2 : ℝ)) *
        ((xNorm c 9 (w_fam t τ - w_fam t t)).toReal + (xNorm c 9 (f τ - f t)).toReal) := by
    intro t τ s ht0 htτ hτs hsH
    have ht : t ∈ Ioc (0 : ℝ) H := ⟨ht0, (htτ.trans hτs.le).trans hsH⟩
    have hτ : τ ∈ Ioc (0 : ℝ) H := ⟨ht0.trans_le htτ, hτs.le.trans hsH⟩
    have hts : t ≤ s := htτ.trans hτs.le
    have hw_t_res := (hw_fam ht).restart htτ
    have hw_τ := hw_fam hτ
    have hm_wtτ := (hw_fam ht).memX τ htτ
    have hm_fτ := (hf_slice τ hτ).1
    have hzc_wtτ := CoreDuhamelRepSub.hasZeroCirculation_of_isLinearisedFlow hc_pos htτ (hw_fam ht)
    have hzc_fτ := (hf_slice τ hτ).2.1
    have hm_sub : MemLp (fun x => w_fam t τ x - f τ x) 2 (B0579.cellMeasure c 9) :=
      hm_wtτ.sub hm_fτ
    have hzc_sub : HasZeroCirculation c (fun x => w_fam t τ x - f τ x) :=
      ⟨hzc_wtτ.1.sub hzc_fτ.1, by rw [integral_sub hzc_wtτ.1 hzc_fτ.1, hzc_wtτ.2, hzc_fτ.2, sub_self]⟩
    have hw_sub := CoreDuhamelRepSub.isLinearisedFlow_sub hm_wtτ hm_fτ hw_t_res hw_τ
    have hnorm_sub : ‖wZ t s - wZ τ s‖ = (xNorm c 9 (fun x => w_fam t s x - w_fam τ s x)).toReal := by
      simp only [wZ, ht, hts, hτ, hτs.le, ↓reduceDIte]
      exact norm_sub_toZC _ _ _ _
    rw [hnorm_sub]
    have hcb := hclock_real hτ.1 hτs hsH hm_sub hzc_sub hw_sub
    have hinit_9 : w_fam t t =ᵐ[B0579.cellMeasure c 9] f t :=
      (B0579.cellMeasure_ac c 9).ae_le (hw_fam ht).initial
    have htri_enn : xNorm c 9 (fun x => w_fam t τ x - f τ x) ≤
        xNorm c 9 (w_fam t τ - w_fam t t) + xNorm c 9 (f τ - f t) := by
      have hae : (fun x => w_fam t τ x - f τ x) =ᵐ[B0579.cellMeasure c 9]
          (w_fam t τ - w_fam t t) + (f t - f τ) := by
        filter_upwards [hinit_9] with x hx
        simp only [Pi.add_apply, Pi.sub_apply, hx]
        ring
      have hsymm : xNorm c 9 (f t - f τ) = xNorm c 9 (f τ - f t) := by
        unfold xNorm
        have hneg : f t - f τ = -(f τ - f t) := by funext x; simp [ neg_sub ]
        rw [hneg, eLpNorm_neg]
      rw [xNorm, eLpNorm_congr_ae hae, ← hsymm]
      exact eLpNorm_add_le
        ((hm_wtτ.sub ((hw_fam ht).memX t le_rfl)).1)
        (((hf_slice t ht).1.sub hm_fτ).1) one_le_two
    have hfin1 : xNorm c 9 (w_fam t τ - w_fam t t) ≠ ⊤ :=
      (hm_wtτ.sub ((hw_fam ht).memX t le_rfl)).2.ne
    have hfin2 : xNorm c 9 (f τ - f t) ≠ ⊤ :=
      (hm_fτ.sub (hf_slice t ht).1).2.ne
    have htri_real : (xNorm c 9 (fun x => w_fam t τ x - f τ x)).toReal ≤
        (xNorm c 9 (w_fam t τ - w_fam t t)).toReal + (xNorm c 9 (f τ - f t)).toReal := by
      have := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hfin1, hfin2⟩) htri_enn
      rwa [ENNReal.toReal_add hfin1 hfin2] at this
    have hker_nn : 0 ≤ C_clk * (1 + (s - τ) ^ (-1 / 2 : ℝ)) := by
      have : 0 ≤ (s - τ) ^ (-1 / 2 : ℝ) := Real.rpow_nonneg (sub_pos.2 hτs).le _
      positivity
    exact hcb.trans (mul_le_mul_of_nonneg_left htri_real hker_nn)

  -- 3. Dyadic-from-above `StronglyMeasurable` of `t ↦ wZ t s` on `Ioo 0 s`
  have hwZ_sm : ∀ {s : ℝ}, s ∈ Ioo (0 : ℝ) H →
      StronglyMeasurable ((Ioo (0 : ℝ) s).indicator fun t => wZ t s) := by
    intro s hs
    have hs0 : 0 < s := hs.1
    let apt : ℕ → ℕ → ℝ := fun n k => (k : ℝ) * s / (2 : ℝ) ^ n
    let approx : ℕ → ℝ → ZC c := fun n t =>
      ∑ k ∈ Finset.range (2 ^ n - 1),
        (Ioc (apt n k) (apt n (k + 1))).indicator (fun _ => wZ (apt n (k + 1)) s) t
    have happrox_sm : ∀ n, StronglyMeasurable (approx n) := fun n =>
      Finset.stronglyMeasurable_fun_sum _ fun k _ =>
        stronglyMeasurable_const.indicator measurableSet_Ioc
    refine stronglyMeasurable_of_tendsto atTop happrox_sm (tendsto_pi_nhds.2 fun t => ?_)
    by_cases hts : t ∈ Ioo (0 : ℝ) s
    · rw [Set.indicator_of_mem hts]
      have ht0 : 0 < t := hts.1
      have hts' : t < s := hts.2
      have hpow_lim : Tendsto (fun n : ℕ => s * (1 / 2 : ℝ) ^ n) atTop (𝓝 0) := by
        simpa only [mul_zero] using
          (tendsto_pow_atTop_nhds_zero_of_lt_one
            (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)).const_mul s
      have hev_small : ∀ᶠ n : ℕ in atTop, s / (2 : ℝ) ^ n < (s - t) / 2 := by
        have hpos : 0 < (s - t) / 2 := by linarith
        filter_upwards [hpow_lim.eventually (Iio_mem_nhds hpos)] with n hn
        have heq : s / (2 : ℝ) ^ n = s * (1 / 2 : ℝ) ^ n := by
          rw [one_div, inv_pow, div_eq_mul_inv]
        rwa [heq]
      let m_idx : ℕ → ℕ := fun n => ⌈t * (2 : ℝ) ^ n / s⌉₊
      let k_idx : ℕ → ℕ := fun n => m_idx n - 1
      let τ_seq : ℕ → ℝ := fun n => apt n (k_idx n + 1)
      have hm_pos : ∀ n : ℕ, 1 ≤ m_idx n := fun n =>
        Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 (by positivity)).ne'
      have hk_succ : ∀ n : ℕ, k_idx n + 1 = m_idx n := fun n => Nat.sub_add_cancel (hm_pos n)
      have ht_in : ∀ n : ℕ, t ∈ Ioc (apt n (k_idx n)) (apt n (k_idx n + 1)) := by
        intro n
        have h2n : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
        refine ⟨?_, ?_⟩
        · dsimp [apt]
          rw [div_lt_iff₀ h2n]
          have hlt : (k_idx n : ℝ) < t * (2 : ℝ) ^ n / s := by
            by_contra hle
            have hle' : t * (2 : ℝ) ^ n / s ≤ (k_idx n : ℝ) := le_of_not_gt hle
            have hceil : m_idx n ≤ k_idx n := Nat.ceil_le.2 hle'
            dsimp only [k_idx] at hceil
            have := hm_pos n
            omega
          exact (lt_div_iff₀ hs0).1 hlt
        · dsimp [apt]
          rw [hk_succ n, le_div_iff₀ h2n]
          have hle := Nat.le_ceil (t * (2 : ℝ) ^ n / s)
          have := (div_le_iff₀ hs0).1 hle
          linarith
      have hτ_ub : ∀ n : ℕ, τ_seq n < t + s / (2 : ℝ) ^ n := by
        intro n
        have h1 := (ht_in n).1
        dsimp [τ_seq, apt] at h1 ⊢
        have : ((k_idx n + 1 : ℕ) : ℝ) * s / (2 : ℝ) ^ n =
            (k_idx n : ℝ) * s / (2 : ℝ) ^ n + s / (2 : ℝ) ^ n := by
          push_cast; ring
        linarith
      have hτ_tendsto : Tendsto τ_seq atTop (𝓝 t) := by
        have hub_lim : Tendsto (fun n : ℕ => t + s / (2 : ℝ) ^ n) atTop (𝓝 t) := by
          have heq_fn : (fun n : ℕ => t + s / (2 : ℝ) ^ n) =
              fun n => t + s * (1 / 2 : ℝ) ^ n := by
            funext n; rw [one_div, inv_pow, div_eq_mul_inv]
          rw [heq_fn]
          simpa only [add_zero] using tendsto_const_nhds.add hpow_lim
        exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
          hub_lim (fun n => (ht_in n).2) (fun n => (hτ_ub n).le)
      have hτ_nhdsWithin : Tendsto τ_seq atTop (𝓝[Ici t] t) :=
        tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hτ_tendsto
          (Eventually.of_forall fun n => (ht_in n).2)
      have ht_Ioc : t ∈ Ioc (0 : ℝ) H := ⟨ht0, hts'.le.trans hs.2.le⟩
      have hlim_w : Tendsto (fun n => (xNorm c 9 (w_fam t (τ_seq n) - w_fam t t)).toReal)
          atTop (𝓝 0) := by
        have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
          (((hw_fam ht_Ioc).strongCont t le_rfl).comp hτ_nhdsWithin)
        rw [ENNReal.toReal_zero] at h
        exact h
      have hlim_f : Tendsto (fun n => (xNorm c 9 (f (τ_seq n) - f t)).toReal) atTop (𝓝 0) := by
        have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
          ((hf_cont t ⟨ht0, hts'.trans hs.2⟩).comp hτ_tendsto)
        rw [ENNReal.toReal_zero] at h
        exact h
      have happrox_eq : ∀ᶠ n : ℕ in atTop, approx n t = wZ (τ_seq n) s ∧
          (s - t) / 2 ≤ s - τ_seq n := by
        filter_upwards [hev_small] with n hn
        have hτ_lt : τ_seq n < s - s / (2 : ℝ) ^ n := by linarith [hτ_ub n]
        have hk_lt : k_idx n < 2 ^ n - 1 := by
          have h2n : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
          have h1n : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by norm_num)
          have hlt_real : ((k_idx n + 1 : ℕ) : ℝ) < ((2 ^ n - 1 : ℕ) : ℝ) := by
            have heq_rhs : s - s / (2 : ℝ) ^ n = ((2 ^ n - 1 : ℕ) : ℝ) * s / (2 : ℝ) ^ n := by
              rw [Nat.cast_sub h1n]
              push_cast
              field_simp
            dsimp [τ_seq, apt] at hτ_lt
            rw [heq_rhs, div_lt_div_iff_of_pos_right h2n] at hτ_lt
            nlinarith
          have hk1 : k_idx n + 1 < 2 ^ n - 1 := by exact_mod_cast hlt_real
          omega
        refine ⟨?_, by linarith [hτ_ub n]⟩
        dsimp [approx]
        rw [Finset.sum_eq_single (k_idx n)]
        · rw [Set.indicator_of_mem (ht_in n)]
        · intro k _ hkne
          rw [Set.indicator_of_notMem]
          intro htk
          have h2n : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
          rcases lt_or_gt_of_ne hkne with hlt | hgt
          · have hle_k : ((k + 1 : ℕ) : ℝ) ≤ (k_idx n : ℝ) := by exact_mod_cast hlt
            have hle_apt : apt n (k + 1) ≤ apt n (k_idx n) :=
              div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hle_k hs0.le) h2n.le
            linarith [htk.2, (ht_in n).1]
          · have hle_k : ((k_idx n + 1 : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast hgt
            have hle_apt : apt n (k_idx n + 1) ≤ apt n k :=
              div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hle_k hs0.le) h2n.le
            linarith [htk.1, (ht_in n).2]
        · intro hnot
          exact absurd (Finset.mem_range.2 hk_lt) hnot
      rw [tendsto_iff_norm_sub_tendsto_zero]
      set C_t : ℝ := C_clk * (1 + ((s - t) / 2) ^ (-1 / 2 : ℝ))
      have hzero_lim : Tendsto (fun n => C_t *
          ((xNorm c 9 (w_fam t (τ_seq n) - w_fam t t)).toReal +
            (xNorm c 9 (f (τ_seq n) - f t)).toReal)) atTop (𝓝 0) := by
        simpa using (hlim_w.add hlim_f).const_mul C_t
      refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hzero_lim
      filter_upwards [happrox_eq] with n ⟨heq, hgap⟩
      rw [heq, norm_sub_rev]
      have hgap_pos : 0 < (s - t) / 2 := by linarith
      have hτs : τ_seq n < s := by linarith
      have hrpow_le : (s - τ_seq n) ^ (-1 / 2 : ℝ) ≤ ((s - t) / 2) ^ (-1 / 2 : ℝ) := by
        have hneg : (-1 / 2 : ℝ) = -(1 / 2 : ℝ) := by norm_num
        rw [hneg, Real.rpow_neg (sub_pos.2 hτs).le, Real.rpow_neg hgap_pos.le]
        exact inv_anti₀ (Real.rpow_pos_of_pos hgap_pos _)
          (Real.rpow_le_rpow hgap_pos.le hgap (by norm_num))
      have hbd := hwZ_restart_diff ht0 (ht_in n).2 hτs hs.2.le
      refine hbd.trans (mul_le_mul_of_nonneg_right ?_
        (add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg))
      exact mul_le_mul_of_nonneg_left (by linarith) hC_clk_nn
    · rw [Set.indicator_of_notMem hts]
      have hall0 : ∀ n, approx n t = 0 := by
        intro n
        dsimp [approx]
        refine Finset.sum_eq_zero fun k hk => Set.indicator_of_notMem ?_ _
        intro htk
        apply hts
        have hk_lt : k < 2 ^ n - 1 := Finset.mem_range.1 hk
        have h1n : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by norm_num)
        have h2n : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
        have h0_le : 0 ≤ apt n k := by dsimp [apt]; positivity
        have hk1_lt : ((k + 1 : ℕ) : ℝ) < (2 : ℝ) ^ n := by
          have : k + 1 < 2 ^ n := by omega
          exact_mod_cast this
        have h_lt_s : apt n (k + 1) < s := by
          dsimp [apt]
          rw [div_lt_iff₀ h2n]
          nlinarith
        exact ⟨h0_le.trans_lt htk.1, htk.2.trans_lt h_lt_s⟩
      simp_rw [hall0]
      exact tendsto_const_nhds

  -- 4. Raw & normalized Duhamel integrands and continuity of `W_Z` on `Ioo 0 H`
  let rawInt : ℝ → ℝ → ZC c := fun s t =>
    (Ioo (0 : ℝ) s).indicator (fun τ => rawScalar μ γ ν τ • wZ τ s) t
  let kerInt : ℝ → ℝ → ZC c := fun s t =>
    (Ioo (0 : ℝ) s).indicator (fun τ => duhamelFactor μ γ ν s τ • wZ τ s) t

  set M_raw : ℝ := H ^ μ.re * M_exp * C_clk * M_f
  have hM_raw_nn : 0 ≤ M_raw := by
    have : 0 ≤ H ^ μ.re := Real.rpow_nonneg hH_pos.le _
    positivity

  have hrawInt_sm : ∀ {s : ℝ}, s ∈ Ioo (0 : ℝ) H → StronglyMeasurable (rawInt s) := by
    intro s hs
    have hsc_sm : StronglyMeasurable ((Ioo (0 : ℝ) s).indicator (rawScalar μ γ ν)) :=
      UnforcedLeray.Infra.JointMeasurableRep.stronglyMeasurable_indicator_of_continuousOn
        ((continuousOn_rawScalar μ hν0).mono (fun t ht => ht.1)) measurableSet_Ioo
    have heq : rawInt s = fun t =>
        ((Ioo (0 : ℝ) s).indicator (rawScalar μ γ ν) t) •
          ((Ioo (0 : ℝ) s).indicator (fun τ => wZ τ s) t) := by
      funext t
      by_cases ht : t ∈ Ioo (0 : ℝ) s <;> simp [rawInt, ht]
    rw [heq]
    exact hsc_sm.smul (hwZ_sm hs)

  have hrawInt_norm : ∀ {s t : ℝ}, s ∈ Ioo (0 : ℝ) H → t ∈ Ioo (0 : ℝ) s →
      ‖rawInt s t‖ ≤ M_raw * (1 + (s - t) ^ (-1 / 2 : ℝ)) := by
    intro s t hs ht
    dsimp only [rawInt]
    rw [Set.indicator_of_mem ht]
    change ‖rawScalar μ γ ν t • (wZ t s).1‖ ≤ _
    rw [norm_smul]
    have h1 := norm_rawScalar_le (γ := γ) hμ_pos hν0 ht.1 (ht.2.le.trans hs.2.le)
    have h2 := hwZ_bound ht.1 ht.2 hs.2.le
    calc ‖rawScalar μ γ ν t‖ * ‖(wZ t s).1‖
        ≤ (H ^ μ.re * M_exp) * (C_clk * (1 + (s - t) ^ (-1 / 2 : ℝ)) * M_f) :=
          mul_le_mul h1 h2 (norm_nonneg _) (by
            have : 0 ≤ H ^ μ.re := Real.rpow_nonneg hH_pos.le _
            positivity)
      _ = M_raw * (1 + (s - t) ^ (-1 / 2 : ℝ)) := by dsimp [M_raw]; ring

  have hrawInt_integrable : ∀ {s : ℝ}, s ∈ Ioo (0 : ℝ) H →
      IntegrableOn (rawInt s) (Ioo (0 : ℝ) s) volume := by
    intro s hs
    refine ((integrableOn_one_add_inv_sqrt hs.1.le).1.const_mul M_raw).mono'
      (hrawInt_sm hs).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact hrawInt_norm hs ht

  have hkerInt_eq : ∀ {s : ℝ}, s ∈ Ioo (0 : ℝ) H →
      kerInt s = fun t => invScalar μ γ ν s • rawInt s t := by
    intro s hs
    funext t
    by_cases ht : t ∈ Ioo (0 : ℝ) s
    · simp only [kerInt, rawInt, Set.indicator_of_mem ht,
        duhamelFactor_eq_mul ht.1 hs.1 μ γ ν, mul_smul]
    · simp [kerInt, rawInt, ht]

  have hkerInt_sm : ∀ {s : ℝ}, s ∈ Ioo (0 : ℝ) H → StronglyMeasurable (kerInt s) := by
    intro s hs
    rw [hkerInt_eq hs]
    exact (smulZCLM c (invScalar μ γ ν s)).continuous.comp_stronglyMeasurable (hrawInt_sm hs)

  have hkerInt_integrable : ∀ {s : ℝ}, s ∈ Ioo (0 : ℝ) H →
      IntegrableOn (kerInt s) (Ioo (0 : ℝ) s) volume := by
    intro s hs
    rw [hkerInt_eq hs]
    exact (smulZCLM c (invScalar μ γ ν s)).integrable_comp (hrawInt_integrable hs)

  let W_raw : ℝ → ZC c := fun s => if s ∈ Ioo (0 : ℝ) H then ∫ t in Ioo 0 s, rawInt s t else 0
  let W_Z : ℝ → ZC c := fun s => invScalar μ γ ν s • W_raw s

  have hW_Z_zero : ∀ {s : ℝ}, s ≤ a_zero → W_Z s = 0 := by
    intro s hsa
    dsimp [W_Z, W_raw]
    split_ifs with hs
    · have h0 : ∀ t ∈ Ioo (0 : ℝ) s, rawInt s t = 0 := by
        intro t ht
        dsimp [rawInt]
        rw [Set.indicator_of_mem ht, hwZ_zero (ht.2.le.trans hsa), smul_zero]
      rw [setIntegral_congr_fun measurableSet_Ioo h0, integral_zero, smul_zero]
    · exact smul_zero _

  have hW_Z_eq_ker : ∀ {s : ℝ}, s ∈ Ioo (0 : ℝ) H →
      W_Z s = ∫ t in Ioo (0 : ℝ) s, kerInt s t := by
    intro s hs
    simp only [W_Z, W_raw, hs, ↓reduceIte]
    rw [hkerInt_eq hs]
    exact ((smulZCLM c (invScalar μ γ ν s)).integral_comp_comm (hrawInt_integrable hs)).symm

  set C_W : ℝ := M_exp ^ 2 * C_clk * M_f * (H + 2 * H ^ (1 / 2 : ℝ))
  have hC_W_nn : 0 ≤ C_W := by
    have : 0 ≤ H ^ (1 / 2 : ℝ) := Real.rpow_nonneg hH_pos.le _
    positivity

  have hW_Z_bound : ∀ {s : ℝ}, s ∈ Ioo (0 : ℝ) H → ‖W_Z s‖ ≤ C_W := by
    intro s hs
    rw [hW_Z_eq_ker hs]
    have hdom : IntegrableOn (fun t : ℝ => (M_exp ^ 2 * C_clk * M_f) *
        (1 + (s - t) ^ (-1 / 2 : ℝ))) (Ioo (0 : ℝ) s) volume :=
      (integrableOn_one_add_inv_sqrt hs.1.le).1.const_mul _
    have hle : ∀ᵐ t ∂(volume.restrict (Ioo (0 : ℝ) s)),
        ‖kerInt s t‖ ≤ (M_exp ^ 2 * C_clk * M_f) * (1 + (s - t) ^ (-1 / 2 : ℝ)) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      dsimp only [kerInt]
      rw [Set.indicator_of_mem ht]
      change ‖duhamelFactor μ γ ν s t • (wZ t s).1‖ ≤ _
      rw [norm_smul]
      have h1 := norm_duhamelFactor_le (γ := γ) hμ_pos hν0 ht.1 ht.2 hs.2.le
      have h2 := hwZ_bound ht.1 ht.2 hs.2.le
      calc ‖duhamelFactor μ γ ν s t‖ * ‖(wZ t s).1‖
          ≤ M_exp ^ 2 * (C_clk * (1 + (s - t) ^ (-1 / 2 : ℝ)) * M_f) :=
            mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
        _ = (M_exp ^ 2 * C_clk * M_f) * (1 + (s - t) ^ (-1 / 2 : ℝ)) := by ring
    calc ‖∫ t in Ioo (0 : ℝ) s, kerInt s t‖
        ≤ ∫ t in Ioo (0 : ℝ) s, (M_exp ^ 2 * C_clk * M_f) * (1 + (s - t) ^ (-1 / 2 : ℝ)) :=
          norm_integral_le_of_norm_le hdom hle
      _ = (M_exp ^ 2 * C_clk * M_f) * ((s - 0) + 2 * (s - 0) ^ (1 / 2 : ℝ)) := by
          rw [integral_const_mul, (integrableOn_one_add_inv_sqrt hs.1.le).2]
      _ ≤ C_W := by
          rw [sub_zero]
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          have hr : s ^ (1 / 2 : ℝ) ≤ H ^ (1 / 2 : ℝ) :=
            Real.rpow_le_rpow hs.1.le hs.2.le (by norm_num)
          linarith [hs.2]

  have hsplit_raw : ∀ {a s : ℝ}, 0 < a → a < s → s ∈ Ioo (0 : ℝ) H →
      ∫ t in Ioo (0 : ℝ) s, rawInt s t =
        (∫ t in Ioo (0 : ℝ) a, rawInt s t) + ∫ t in Ioo a s, rawInt s t := by
    intro a s ha0' has hs
    have hint_Ioc : IntegrableOn (rawInt s) (Ioc (0 : ℝ) s) volume := by
      rw [IntegrableOn, Measure.restrict_congr_set Ioo_ae_eq_Ioc.symm]
      exact hrawInt_integrable hs
    have hint_0a : IntegrableOn (rawInt s) (Ioc (0 : ℝ) a) volume :=
      hint_Ioc.mono_set (Ioc_subset_Ioc_right has.le)
    have hint_as : IntegrableOn (rawInt s) (Ioc a s) volume :=
      hint_Ioc.mono_set (Ioc_subset_Ioc_left ha0'.le)
    rw [← integral_Ioc_eq_integral_Ioo, ← Ioc_union_Ioc_eq_Ioc ha0'.le has.le,
      setIntegral_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc hint_0a hint_as,
      integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]

  have htail_raw : ∀ {a s : ℝ}, 0 < a → a < s → s ∈ Ioo (0 : ℝ) H →
      ‖∫ t in Ioo a s, rawInt s t‖ ≤ M_raw * ((s - a) + 2 * Real.sqrt (s - a)) := by
    intro a s ha0' has hs
    have hdom : IntegrableOn (fun t : ℝ => M_raw * (1 + (s - t) ^ (-1 / 2 : ℝ))) (Ioo a s) volume :=
      (integrableOn_one_add_inv_sqrt has.le).1.const_mul M_raw
    have hle : ∀ᵐ t ∂(volume.restrict (Ioo a s)),
        ‖rawInt s t‖ ≤ M_raw * (1 + (s - t) ^ (-1 / 2 : ℝ)) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      exact hrawInt_norm hs ⟨ha0'.trans ht.1, ht.2⟩
    calc ‖∫ t in Ioo a s, rawInt s t‖
        ≤ ∫ t in Ioo a s, M_raw * (1 + (s - t) ^ (-1 / 2 : ℝ)) :=
          norm_integral_le_of_norm_le hdom hle
      _ = M_raw * ((s - a) + 2 * (s - a) ^ (1 / 2 : ℝ)) := by
          rw [integral_const_mul, (integrableOn_one_add_inv_sqrt has.le).2]
      _ = M_raw * ((s - a) + 2 * Real.sqrt (s - a)) := by
          rw [Real.sqrt_eq_rpow]

  have hW_raw_cont : ContinuousOn W_raw (Ioo (0 : ℝ) H) := by
    intro s₀ hs₀
    refine ContinuousAt.continuousWithinAt ?_
    rw [Metric.continuousAt_iff]
    intro ε hε
    have hm_pos : 0 < min s₀ (H - s₀) / 4 := by
      have : 0 < min s₀ (H - s₀) := lt_min hs₀.1 (sub_pos.2 hs₀.2)
      linarith
    let d_seq : ℕ → ℝ := fun n => (min s₀ (H - s₀) / 4) * (1 / 2 : ℝ) ^ n
    have hd_lim : Tendsto d_seq atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).const_mul
        (min s₀ (H - s₀) / 4)
    have htail_lim : Tendsto (fun n => M_raw * (2 * d_seq n + 2 * Real.sqrt (2 * d_seq n)))
        atTop (𝓝 0) := by
      have hc : Continuous (fun d : ℝ => M_raw * (2 * d + 2 * Real.sqrt (2 * d))) :=
        continuous_const.mul ((continuous_const.mul continuous_id).add
          (continuous_const.mul (Real.continuous_sqrt.comp (continuous_const.mul continuous_id))))
      have h0 : M_raw * (2 * (0 : ℝ) + 2 * Real.sqrt (2 * 0)) = 0 := by simp
      have h := (hc.tendsto 0).comp hd_lim
      rw [h0] at h
      exact h
    obtain ⟨n₀, hn₀⟩ := (htail_lim.eventually (Iio_mem_nhds (by linarith : (0 : ℝ) < ε / 3))).exists
    set δ : ℝ := d_seq n₀
    have hδ_pos : 0 < δ := by dsimp [δ, d_seq]; positivity
    have hδ_le : δ ≤ min s₀ (H - s₀) / 4 := by
      dsimp [δ, d_seq]
      have h1 : (1 / 2 : ℝ) ^ n₀ ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      nlinarith
    have hδ_s0 : δ ≤ s₀ / 4 := hδ_le.trans (by linarith [min_le_left s₀ (H - s₀)])
    have hδ_Hs0 : δ ≤ (H - s₀) / 4 := hδ_le.trans (by linarith [min_le_right s₀ (H - s₀)])
    have hδ_tail : M_raw * (2 * δ + 2 * Real.sqrt (2 * δ)) < ε / 3 := hn₀
    set a : ℝ := s₀ - δ
    have ha0' : 0 < a := by linarith
    have has₀ : a < s₀ := by linarith
    have : IsFiniteMeasure (volume.restrict (Ioo (0 : ℝ) a)) :=
      ⟨by rw [Measure.restrict_apply_univ, Real.volume_Ioo]; exact ENNReal.ofReal_lt_top⟩
    set C_dom : ℝ := M_raw * (1 + (δ / 2) ^ (-1 / 2 : ℝ))
    have hball_mem : Ioo (s₀ - δ / 2) (s₀ + δ / 2) ∈ 𝓝 s₀ :=
      Ioo_mem_nhds (by linarith) (by linarith)
    have hmain_lim : Tendsto (fun s => ∫ t in Ioo (0 : ℝ) a, rawInt s t) (𝓝 s₀)
        (𝓝 (∫ t in Ioo (0 : ℝ) a, rawInt s₀ t)) := by
      refine tendsto_integral_filter_of_dominated_convergence (fun _ : ℝ => C_dom) ?_ ?_
        (integrable_const C_dom) ?_
      · filter_upwards [hball_mem] with s hs_b
        have hs_Ioo : s ∈ Ioo (0 : ℝ) H := ⟨by linarith [hs_b.1], by linarith [hs_b.2]⟩
        exact (hrawInt_sm hs_Ioo).aestronglyMeasurable
      · filter_upwards [hball_mem] with s hs_b
        have hs_Ioo : s ∈ Ioo (0 : ℝ) H := ⟨by linarith [hs_b.1], by linarith [hs_b.2]⟩
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
        have hts : t ∈ Ioo (0 : ℝ) s := ⟨ht.1, by linarith [ht.2, hs_b.1]⟩
        have hgap : δ / 2 ≤ s - t := by linarith [ht.2, hs_b.1]
        have hd2 : 0 < δ / 2 := by linarith
        have hrpow : (s - t) ^ (-1 / 2 : ℝ) ≤ (δ / 2) ^ (-1 / 2 : ℝ) := by
          have hneg : (-1 / 2 : ℝ) = -(1 / 2 : ℝ) := by norm_num
          rw [hneg, Real.rpow_neg (by linarith : 0 ≤ s - t), Real.rpow_neg hd2.le]
          exact inv_anti₀ (Real.rpow_pos_of_pos hd2 _)
            (Real.rpow_le_rpow hd2.le hgap (by norm_num))
        exact (hrawInt_norm hs_Ioo hts).trans
          (mul_le_mul_of_nonneg_left (by linarith) hM_raw_nn)
      · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
        have hts₀ : t < s₀ := ht.2.trans has₀
        have ht_Ioc : t ∈ Ioc (0 : ℝ) H := ⟨ht.1, hts₀.le.trans hs₀.2.le⟩
        have hsc : Tendsto (fun s => xNorm c 9 (w_fam t s - w_fam t s₀)) (𝓝 s₀) (𝓝 0) := by
          have h1 := (hw_fam ht_Ioc).strongCont s₀ hts₀.le
          rwa [nhdsWithin_eq_nhds.2 (Ici_mem_nhds hts₀)] at h1
        have hsc_real : Tendsto (fun s => (xNorm c 9 (w_fam t s - w_fam t s₀)).toReal)
            (𝓝 s₀) (𝓝 0) := by
          have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hsc
          rw [ENNReal.toReal_zero] at h
          exact h
        have hwZ_lim : Tendsto (fun s => wZ t s) (𝓝 s₀) (𝓝 (wZ t s₀)) := by
          rw [tendsto_iff_norm_sub_tendsto_zero]
          refine hsc_real.congr' ?_
          filter_upwards [hball_mem] with s hs_b
          have hts_le : t ≤ s := by linarith [ht.2, hs_b.1]
          simp only [wZ, ht_Ioc, hts_le, hts₀.le, ↓reduceDIte, norm_sub_toZC]
        have hsmul_lim : Tendsto (fun s => rawScalar μ γ ν t • wZ t s) (𝓝 s₀)
            (𝓝 (rawScalar μ γ ν t • wZ t s₀)) :=
          ((smulZCLM c (rawScalar μ γ ν t)).continuous.tendsto (wZ t s₀)).comp hwZ_lim
        have ht_s0 : t ∈ Ioo (0 : ℝ) s₀ := ⟨ht.1, hts₀⟩
        have h_init_eq : rawScalar μ γ ν t • wZ t s₀ = rawInt s₀ t := by
          dsimp [rawInt]; rw [Set.indicator_of_mem ht_s0]
        rw [← h_init_eq]
        refine hsmul_lim.congr' ?_
        filter_upwards [hball_mem] with s hs_b
        have hts_Ioo : t ∈ Ioo (0 : ℝ) s := ⟨ht.1, by linarith [ht.2, hs_b.1]⟩
        dsimp [rawInt]
        rw [Set.indicator_of_mem hts_Ioo]
    have hmain_ev : ∀ᶠ s in 𝓝 s₀,
        ‖(∫ t in Ioo (0 : ℝ) a, rawInt s t) - ∫ t in Ioo (0 : ℝ) a, rawInt s₀ t‖ < ε / 3 := by
      have := (tendsto_iff_norm_sub_tendsto_zero.1 hmain_lim).eventually
        (Iio_mem_nhds (by linarith : (0 : ℝ) < ε / 3))
      exact this
    have hboth_ev : ∀ᶠ s in 𝓝 s₀, s ∈ Ioo (s₀ - δ / 2) (s₀ + δ / 2) ∧
        ‖(∫ t in Ioo (0 : ℝ) a, rawInt s t) - ∫ t in Ioo (0 : ℝ) a, rawInt s₀ t‖ < ε / 3 :=
      Filter.Eventually.and hball_mem hmain_ev
    obtain ⟨δ₁, hδ₁_pos, hδ₁⟩ := Metric.eventually_nhds_iff.1 hboth_ev
    refine ⟨δ₁, hδ₁_pos, fun {s} hs_dist => ?_⟩
    obtain ⟨hs_b, hs_main⟩ := hδ₁ hs_dist
    have hs_Ioo : s ∈ Ioo (0 : ℝ) H := ⟨by linarith [hs_b.1], by linarith [hs_b.2]⟩
    have has : a < s := by linarith [hs_b.1]
    rw [dist_eq_norm]
    simp only [W_raw, hs_Ioo, hs₀, ↓reduceIte]
    rw [hsplit_raw ha0' has hs_Ioo, hsplit_raw ha0' has₀ hs₀]
    have h_alg : ((∫ t in Ioo (0 : ℝ) a, rawInt s t) + ∫ t in Ioo a s, rawInt s t) -
        ((∫ t in Ioo (0 : ℝ) a, rawInt s₀ t) + ∫ t in Ioo a s₀, rawInt s₀ t) =
      ((∫ t in Ioo (0 : ℝ) a, rawInt s t) - ∫ t in Ioo (0 : ℝ) a, rawInt s₀ t) +
        ((∫ t in Ioo a s, rawInt s t) - ∫ t in Ioo a s₀, rawInt s₀ t) := by abel
    rw [h_alg]
    have htail_s : ‖∫ t in Ioo a s, rawInt s t‖ < ε / 3 := by
      have hsa_le : s - a ≤ 2 * δ := by linarith [hs_b.2]
      have hsq_le : Real.sqrt (s - a) ≤ Real.sqrt (2 * δ) := Real.sqrt_le_sqrt hsa_le
      exact (htail_raw ha0' has hs_Ioo).trans_lt
        (lt_of_le_of_lt (mul_le_mul_of_nonneg_left (by linarith) hM_raw_nn) hδ_tail)
    have htail_s0 : ‖∫ t in Ioo a s₀, rawInt s₀ t‖ < ε / 3 := by
      have hs0a_le : s₀ - a ≤ 2 * δ := by linarith
      have hsq_le : Real.sqrt (s₀ - a) ≤ Real.sqrt (2 * δ) := Real.sqrt_le_sqrt hs0a_le
      exact (htail_raw ha0' has₀ hs₀).trans_lt
        (lt_of_le_of_lt (mul_le_mul_of_nonneg_left (by linarith) hM_raw_nn) hδ_tail)
    calc ‖((∫ t in Ioo (0 : ℝ) a, rawInt s t) - ∫ t in Ioo (0 : ℝ) a, rawInt s₀ t) +
            ((∫ t in Ioo a s, rawInt s t) - ∫ t in Ioo a s₀, rawInt s₀ t)‖
        ≤ ‖(∫ t in Ioo (0 : ℝ) a, rawInt s t) - ∫ t in Ioo (0 : ℝ) a, rawInt s₀ t‖ +
            (‖∫ t in Ioo a s, rawInt s t‖ + ‖∫ t in Ioo a s₀, rawInt s₀ t‖) :=
          (norm_add_le _ _).trans (add_le_add le_rfl (norm_sub_le _ _))
      _ < ε / 3 + (ε / 3 + ε / 3) := add_lt_add hs_main (add_lt_add htail_s htail_s0)
      _ = ε := by ring

  have hW_Z_cont : ContinuousOn W_Z (Ioo (0 : ℝ) H) :=
    ((continuousOn_invScalar μ hν0).mono (fun s hs => hs.1)).smul hW_raw_cont

  -- 5. Construct `k_ker`, `ω_duh`, `u_duh`, `G_duh` and prove measurability + slice properties
  have hk_ex : ∀ s : ℝ, s ∈ Ioo (0 : ℝ) H →
      ∃ K_s : ℝ × (ℝ × ℝ) → ℂ, StronglyMeasurable K_s ∧
        ∀ t, (fun x => K_s (t, x)) =ᵐ[B0579.cellMeasure c 9] ((kerInt s t).1 : ℝ × ℝ → ℂ) := by
    intro s hs
    exact UnforcedLeray.Infra.JointMeasurableRep.exists_stronglyMeasurable_rep
      ((zcValCLM c).continuous.comp_stronglyMeasurable (hkerInt_sm hs))

  let k_ker : ℝ → ℝ → ℝ × ℝ → ℂ := fun s t x =>
    if hs : s ∈ Ioo (0 : ℝ) H then (Classical.choose (hk_ex s hs)) (t, x) else 0
  let ω_duh : ℝ → ℝ × ℝ → ℂ := fun s x => ((W_Z s).1 : ℝ × ℝ → ℂ) x

  obtain ⟨U_rep, hU_sm, hU_rep⟩ :=
    UnforcedLeray.Infra.JointMeasurableRep.exists_stronglyMeasurable_rep_of_continuousOn_Ioo
      ((velCCLM c).continuous.comp_continuousOn hW_Z_cont)
  obtain ⟨GQ_rep, hGQ_sm, hGQ_rep⟩ :=
    UnforcedLeray.Infra.JointMeasurableRep.exists_stronglyMeasurable_rep_of_continuousOn_Ioo
      ((gqCCLM c).continuous.comp_continuousOn hW_Z_cont)
  obtain ⟨GE_rep, hGE_sm, hGE_rep⟩ :=
    UnforcedLeray.Infra.JointMeasurableRep.exists_stronglyMeasurable_rep_of_continuousOn_Ioo
      ((geCCLM c).continuous.comp_continuousOn hW_Z_cont)

  let u_duh : ℝ × (ℝ × ℝ) → Fin 2 → ℂ := fun p i =>
    if a_zero < p.1 then U_rep p i else 0
  let G_duh : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ := fun p i j =>
    if a_zero < p.1 then (if j = 0 then GQ_rep p i else GE_rep p i) else 0

  have hu_meas : ∀ i, Measurable fun p => u_duh p i := fun i =>
    Measurable.ite (measurableSet_lt measurable_const measurable_fst)
      ((PiLp.continuous_apply 2 (fun _ : Fin 2 => ℂ) i).measurable.comp hU_sm.measurable)
      measurable_const

  have hG_meas : ∀ i j, Measurable fun p => G_duh p i j := by
    intro i j
    fin_cases j
    · exact Measurable.ite (measurableSet_lt measurable_const measurable_fst)
        ((PiLp.continuous_apply 2 (fun _ : Fin 2 => ℂ) i).measurable.comp hGQ_sm.measurable)
        measurable_const
    · exact Measurable.ite (measurableSet_lt measurable_const measurable_fst)
        ((PiLp.continuous_apply 2 (fun _ : Fin 2 => ℂ) i).measurable.comp hGE_sm.measurable)
        measurable_const

  have hu_zero : ∀ s ≤ a_zero, ∀ x i, u_duh (s, x) i = 0 := fun s hs x i => by
    have hna : ¬ a_zero < s := not_lt.2 hs
    simp only [u_duh, hna, ↓reduceIte]

  have hG_zero : ∀ s ≤ a_zero, ∀ x i j, G_duh (s, x) i j = 0 := fun s hs x i j => by
    have hna : ¬ a_zero < s := not_lt.2 hs
    simp only [G_duh, hna, ↓reduceIte]

  have hu_ae : ∀ {s : ℝ}, s ∈ Ioo (0 : ℝ) H → ∀ i : Fin 2,
      (fun x => u_duh (s, x) i) =ᵐ[volume.restrict (B0579.cell c)]
        fun x => (velCCLM c (W_Z s) : B0579.Plane → B0581.Vel) x i := by
    intro s hs i
    by_cases hsa : a_zero < s
    · filter_upwards [hU_rep s hs] with x hx
      simp only [u_duh, hsa, ↓reduceIte, hx]
      rfl
    · have h0 : W_Z s = 0 := hW_Z_zero (not_lt.1 hsa)
      rw [h0, (velCCLM c).map_zero]
      filter_upwards [Lp.coeFn_zero B0581.Vel 2 (B0581.cellVol c)] with x hx
      simp only [u_duh, hsa, ↓reduceIte, hx]
      rfl

  have hGQ_ae : ∀ {s : ℝ}, s ∈ Ioo (0 : ℝ) H → ∀ i : Fin 2,
      (fun x => G_duh (s, x) i 0) =ᵐ[volume.restrict (B0579.cell c)]
        fun x => (gqCCLM c (W_Z s) : B0579.Plane → B0581.Vel) x i := by
    intro s hs i
    by_cases hsa : a_zero < s
    · filter_upwards [hGQ_rep s hs] with x hx
      simp only [G_duh, hsa, ↓reduceIte, hx]
      rfl
    · have h0 : W_Z s = 0 := hW_Z_zero (not_lt.1 hsa)
      rw [h0, (gqCCLM c).map_zero]
      filter_upwards [Lp.coeFn_zero B0581.Vel 2 (B0581.cellVol c)] with x hx
      simp only [G_duh, hsa, ↓reduceIte, hx]
      rfl

  have hGE_ae : ∀ {s : ℝ}, s ∈ Ioo (0 : ℝ) H → ∀ i : Fin 2,
      (fun x => G_duh (s, x) i 1) =ᵐ[volume.restrict (B0579.cell c)]
        fun x => (geCCLM c (W_Z s) : B0579.Plane → B0581.Vel) x i := by
    intro s hs i
    by_cases hsa : a_zero < s
    · filter_upwards [hGE_rep s hs] with x hx
      simp only [G_duh, hsa, one_ne_zero, ↓reduceIte, hx]
      rfl
    · have h0 : W_Z s = 0 := hW_Z_zero (not_lt.1 hsa)
      rw [h0, (geCCLM c).map_zero]
      filter_upwards [Lp.coeFn_zero B0581.Vel 2 (B0581.cellVol c)] with x hx
      simp only [G_duh, hsa, ↓reduceIte, hx]
      rfl

  have hu2_slice : ∀ {s : ℝ}, s ∈ Ioo (0 : ℝ) H → ∀ i,
      MemLp (fun x => u_duh (s, x) i) 2 (volume.restrict (B0579.cell c)) := fun hs i =>
    (BiotSavartH1Aux.memLp_lp_coord (velCCLM c (W_Z _)) i).ae_eq (hu_ae hs i).symm

  have hG2_slice : ∀ {s : ℝ}, s ∈ Ioo (0 : ℝ) H → ∀ i j,
      MemLp (fun x => G_duh (s, x) i j) 2 (volume.restrict (B0579.cell c)) := by
    intro s hs i j
    fin_cases j
    · exact (BiotSavartH1Aux.memLp_lp_coord (gqCCLM c (W_Z s)) i).ae_eq (hGQ_ae hs i).symm
    · exact (BiotSavartH1Aux.memLp_lp_coord (geCCLM c (W_Z s)) i).ae_eq (hGE_ae hs i).symm

  have hbs_slice : ∀ {s : ℝ}, s ∈ Ioo (0 : ℝ) H →
      IsBiotSavart c (ω_duh s) (fun x => u_duh (s, x)) := fun hs =>
    isBiotSavart_congr_ae (Eventually.of_forall fun _ => rfl)
      (fun j => (hu_ae hs j).symm) (isBiotSavart_velCCLM c (W_Z _))

  have hgrad_slice : ∀ {s : ℝ}, s ∈ Ioo (0 : ℝ) H → ∀ i j,
      HasWeakCellDerivC c j (fun x => u_duh (s, x) i) (fun x => G_duh (s, x) i j) := by
    intro s hs i j
    fin_cases j
    · exact HasWeakCellDerivC.congr_ae (hu_ae hs i) (hGQ_ae hs i)
        (hasWeakCellDerivC_velCCLM_q c (W_Z s) i)
    · exact HasWeakCellDerivC.congr_ae (hu_ae hs i) (hGE_ae hs i)
        (hasWeakCellDerivC_velCCLM_eta c (W_Z s) i)

  have hcurl_slice : ∀ {s : ℝ}, s ∈ Ioo (0 : ℝ) H →
      (fun x => G_duh (s, x) 1 0 - G_duh (s, x) 0 1)
        =ᵐ[volume.restrict (B0579.cell c)] ω_duh s := by
    intro s hs
    have hbs1 : IsBiotSavart c (fun x => G_duh (s, x) 1 0 - G_duh (s, x) 0 1)
        (fun x => u_duh (s, x)) :=
      isBiotSavart_of_weakGrad (hu2_slice hs) (hbs_slice hs).2.1 (hgrad_slice hs)
    have hm1 : MemLp (fun x => G_duh (s, x) 1 0 - G_duh (s, x) 0 1) 2
        (volume.restrict (B0579.cell c)) :=
      (hG2_slice hs 1 0).sub (hG2_slice hs 0 1)
    have hm2 : MemLp (ω_duh s) 2 (volume.restrict (B0579.cell c)) :=
      (Lp.memLp (W_Z s).1).mono_measure (B0581.cellVol_le_cellMeasure c (by norm_num))
    exact ae_eq_of_isBiotSavart_same_vel hm1 hm2 hbs1 (hbs_slice hs)

  obtain ⟨C_BS, hC_BS, hBS⟩ := coreBiotSavartH1Uniform
  set M_duh : ℝ := 2 * (C_BS * C_W) ^ 2
  have hM_duh_nn : 0 ≤ M_duh := by positivity

  have hM_duh_bound : ∀ s ∈ Ioo (0 : ℝ) H,
      ∫⁻ x in B0579.cell c,
        ENNReal.ofReal (vnorm2 (u_duh (s, x)) ^ 2 + tnorm2 (G_duh (s, x)) ^ 2) ≤
          ENNReal.ofReal M_duh := by
    intro s hs
    have hu_s_meas : ∀ i, Measurable fun x => u_duh (s, x) i := fun i =>
      (hu_meas i).comp (measurable_const.prodMk measurable_id)
    have hG_s_meas : ∀ i j, Measurable fun x => G_duh (s, x) i j := fun i j =>
      (hG_meas i j).comp (measurable_const.prodMk measurable_id)
    have hcurl_ae := hcurl_slice hs
    have hcurl_ae9 : (fun x => G_duh (s, x) 1 0 - G_duh (s, x) 0 1)
        =ᵐ[B0579.cellMeasure c 9] ω_duh s :=
      (B0579.cellMeasure_ac c 9).ae_le hcurl_ae
    have hcurl_mem : MemLp (fun x => G_duh (s, x) 1 0 - G_duh (s, x) 0 1) 2
        (B0579.cellMeasure c 9) :=
      (Lp.memLp (W_Z s).1).ae_eq hcurl_ae9.symm
    have hcurl_zc : HasZeroCirculation c (fun x => G_duh (s, x) 1 0 - G_duh (s, x) 0 1) :=
      ⟨(integrableOn_of_XC c (W_Z s).1).congr_fun_ae hcurl_ae.symm,
        by rw [integral_congr_ae hcurl_ae]; exact (mem_ZC_iff c (W_Z s).1).1 (W_Z s).2⟩
    obtain ⟨hbu, hbG⟩ := coreBiotSavartSliceBound C_BS hC_BS hBS c hc_ge_one
      (fun x => u_duh (s, x)) (fun x => G_duh (s, x)) hu_s_meas hG_s_meas
      (hu2_slice hs) (hG2_slice hs) (hbs_slice hs).2.1 (hgrad_slice hs) hcurl_mem hcurl_zc
    have hx_le : xNorm c 9 (fun x => G_duh (s, x) 1 0 - G_duh (s, x) 0 1) ≤
        ENNReal.ofReal C_W := by
      rw [xNorm, eLpNorm_congr_ae hcurl_ae9]
      have heq : eLpNorm (ω_duh s) 2 (B0579.cellMeasure c 9) = ENNReal.ofReal ‖W_Z s‖ := by
        change eLpNorm ((W_Z s).1 : ℝ × ℝ → ℂ) 2 (B0579.cellMeasure c 9) =
          ENNReal.ofReal ‖(W_Z s).1‖
        rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _)]
      rw [heq]
      exact ENNReal.ofReal_le_ofReal (hW_Z_bound hs)
    have hprod_le : (ENNReal.ofReal C_BS *
        xNorm c 9 (fun x => G_duh (s, x) 1 0 - G_duh (s, x) 0 1)) ^ (2 : ℝ) ≤
          ENNReal.ofReal ((C_BS * C_W) ^ 2) := by
      calc (ENNReal.ofReal C_BS * xNorm c 9 (fun x => G_duh (s, x) 1 0 - G_duh (s, x) 0 1)) ^ (2 : ℝ)
          ≤ (ENNReal.ofReal C_BS * ENNReal.ofReal C_W) ^ (2 : ℝ) :=
            ENNReal.rpow_le_rpow (mul_le_mul_of_nonneg_left hx_le bot_le) (by norm_num)
        _ = ENNReal.ofReal ((C_BS * C_W) ^ 2) := by
            rw [← ENNReal.ofReal_mul hC_BS, ENNReal.rpow_two,
              ← ENNReal.ofReal_pow (mul_nonneg hC_BS hC_W_nn)]
    have hpt : ∀ x, ENNReal.ofReal (vnorm2 (u_duh (s, x)) ^ 2 + tnorm2 (G_duh (s, x)) ^ 2) =
        ENNReal.ofReal (vnorm2 (u_duh (s, x)) ^ 2) +
          ENNReal.ofReal (tnorm2 (G_duh (s, x)) ^ 2) := fun _ =>
      ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)
    simp_rw [hpt]
    rw [lintegral_add_left (((causalLin_measurable_vnorm2 hu_s_meas).pow_const 2).ennreal_ofReal)]
    calc (∫⁻ x in B0579.cell c, ENNReal.ofReal (vnorm2 (u_duh (s, x)) ^ 2)) +
            ∫⁻ x in B0579.cell c, ENNReal.ofReal (tnorm2 (G_duh (s, x)) ^ 2)
        ≤ ENNReal.ofReal ((C_BS * C_W) ^ 2) + ENNReal.ofReal ((C_BS * C_W) ^ 2) :=
          add_le_add (hbu.trans hprod_le) (hbG.trans hprod_le)
      _ = ENNReal.ofReal M_duh := by
          rw [← ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)]
          dsimp [M_duh]
          ring_nf

  refine ⟨k_ker, ω_duh, u_duh, G_duh, hu_meas, hG_meas, hu_zero, hG_zero,
    ⟨M_duh, hM_duh_nn, hM_duh_bound⟩, ?_, ?_⟩
  · intro s hs
    have hsH' : s ∈ Ioo (0 : ℝ) H := hs
    have hk_spec := Classical.choose_spec (hk_ex s hsH')
    have hk_m : Measurable (Function.uncurry (k_ker s)) := by
      have heq : Function.uncurry (k_ker s) = Classical.choose (hk_ex s hsH') := by
        funext ⟨t, x⟩
        simp only [Function.uncurry, k_ker, hsH', ↓reduceDIte]
      rw [heq]
      exact hk_spec.1.measurable
    have hk_rep_s : ∀ t, k_ker s t =ᵐ[B0579.cellMeasure c 9] ((kerInt s t).1 : ℝ × ℝ → ℂ) := by
      intro t
      have heq : k_ker s t = fun x => Classical.choose (hk_ex s hsH') (t, x) := by
        funext x; simp only [k_ker, hsH', ↓reduceDIte]
      rw [heq]
      exact hk_spec.2 t
    refine ⟨hu2_slice hs, hG2_slice hs, Lp.memLp (W_Z s).1, (hbs_slice hs).2.1,
      hgrad_slice hs, hcurl_slice hs, hk_m, ?_, ?_⟩
    · refine Eventually.of_forall fun t ht => ?_
      have ht_Ioc : t ∈ Ioc (0 : ℝ) H := ⟨ht.1, ht.2.le.trans hs.2.le⟩
      refine ⟨w_fam t, u_fam t, hw_fam ht_Ioc, ?_⟩
      have hker_t : (kerInt s t).1 = duhamelFactor μ γ ν s t • (wZ t s).1 := by
        dsimp [kerInt]; rw [Set.indicator_of_mem ht]; rfl
      have hsmul_ae : ((kerInt s t).1 : ℝ × ℝ → ℂ) =ᵐ[B0579.cellMeasure c 9]
          fun x => duhamelFactor μ γ ν s t * ((wZ t s).1 : ℝ × ℝ → ℂ) x := by
        rw [hker_t]
        exact Lp.coeFn_smul (duhamelFactor μ γ ν s t) (wZ t s).1
      have hae9 : k_ker s t =ᵐ[B0579.cellMeasure c 9]
          fun x => duhamelFactor μ γ ν s t * w_fam t s x := by
        filter_upwards [hk_rep_s t, hsmul_ae, hwZ_rep ht_Ioc ht.2.le] with x hx1 hx2 hx3
        rw [hx1, hx2, hx3]
      exact (B0579.ac_cellMeasure c 9).ae_le hae9
    · have hint_xc : IntegrableOn (fun t => (kerInt s t).1) (Ioo (0 : ℝ) s) volume :=
        ((zcValCLM c).restrictScalars ℝ).integrable_comp (hkerInt_integrable hs)
      have hval_int : (W_Z s).1 = ∫ t in Ioo (0 : ℝ) s, (kerInt s t).1 := by
        change zcValCLM c (W_Z s) = _
        rw [hW_Z_eq_ker hs]
        exact (((zcValCLM c).restrictScalars ℝ).integral_comp_comm (hkerInt_integrable hs)).symm
      change ((W_Z s).1 : ℝ × ℝ → ℂ) =ᵐ[volume.restrict (B0579.cell c)] _
      rw [hval_int]
      exact bochner_integral_ae_eq_pointwise hint_xc hk_m (fun t _ => hk_rep_s t)

  -- 6. Spacetime weak Duhamel identity
  · intro ψ s₁ s₂ R₁ hs₁ hs₁₂ hs₂H hR₁ hψ_smooth hψ_per hψ_supp
    set r : ℝ := (s₂ + H) / 2
    have hs₂r : s₂ < r := by dsimp [r]; linarith
    have hrH : r < H := by dsimp [r]; linarith
    have hr0 : 0 < r := (hs₁.trans hs₁₂).trans hs₂r
    set R_lad : ℝ := R₁ + 1
    have hR_lad : 0 < R_lad := by dsimp [R_lad]; linarith
    let φ_test : ℝ → ℝ × ℝ → ℂ := fun ρ x => ((ρ : ℂ) ^ (-μ)) * (ψ ρ x : ℂ)

    have hφ_smooth : ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => φ_test p.1 p.2) := by
      rw [contDiff_iff_contDiffAt]
      intro p
      by_cases hp : 0 < p.1
      · have h1 : ContDiffAt ℝ ∞ (fun q : ℝ × (ℝ × ℝ) => ((q.1 : ℂ) ^ (-μ))) p :=
          (ofReal_cpow_contDiffAt (-μ) hp).comp p contDiffAt_fst
        have h2 : ContDiffAt ℝ ∞ (fun q : ℝ × (ℝ × ℝ) => (ψ q.1 q.2 : ℂ)) p :=
          (Complex.ofRealCLM.contDiff.comp hψ_smooth).contDiffAt
        exact h1.mul h2
      · have hlt : p.1 < s₁ := lt_of_le_of_lt (not_lt.1 hp) hs₁
        have hev : (fun q : ℝ × (ℝ × ℝ) => φ_test q.1 q.2) =ᶠ[𝓝 p] fun _ => (0 : ℂ) := by
          filter_upwards [(isOpen_lt continuous_fst continuous_const).mem_nhds hlt] with q hq
          have h0 : ψ q.1 q.2 = 0 := hψ_supp q.1 q.2 (Or.inl hq)
          simp [φ_test, h0]
        exact contDiffAt_const.congr_of_eventuallyEq hev

    have hφ_per : ∀ ρ : ℝ, ∀ x : ℝ × ℝ, φ_test ρ (x.1 + c, x.2) = φ_test ρ x := by
      intro ρ x; dsimp [φ_test]; rw [hψ_per ρ x]

    obtain ⟨_K_cut, _hK_cut, hCut⟩ := ladCutProps
    have hcut_eq_one : ∀ {x : ℝ × ℝ}, |x.2| ≤ R₁ → ladCut R_lad x = 1 := by
      intro x hx
      refine (hCut R_lad hR_lad).2.2.1 x ?_
      have h1 : x.2 ^ 2 ≤ R₁ ^ 2 := by nlinarith [sq_abs x.2, abs_nonneg x.2]
      have h2 : R₁ ^ 2 ≤ R_lad ^ 2 := by dsimp [R_lad]; nlinarith
      exact h1.trans h2

    have hcutPhi_eq : ∀ ρ x, ladCutPhi φ_test R_lad ρ x = φ_test ρ x := by
      intro ρ x
      by_cases hx : |x.2| ≤ R₁
      · unfold ladCutPhi; rw [hcut_eq_one hx]; simp
      · unfold ladCutPhi
        simp [φ_test, hψ_supp ρ x (Or.inr (Or.inr (not_le.1 hx)))]

    have hladDt_eq : ∀ {ρ : ℝ}, 0 < ρ → ∀ x : ℝ × ℝ,
        ladDt φ_test ρ x =
          ((ρ : ℂ) ^ (-μ)) * (-(μ / (ρ : ℂ)) * (ψ ρ x : ℂ) + (deriv (fun ρ' => ψ ρ' x) ρ : ℂ)) := by
      intro ρ hρ x
      have hρ_ne : (ρ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hρ.ne'
      have hk := ofReal_cpow_hasDerivAt (-μ) hρ
      have hψ_t : DifferentiableAt ℝ (fun ρ' => ψ ρ' x) ρ :=
        (hψ_smooth.comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp) ρ
      have hψc_t : DifferentiableAt ℝ (fun ρ' => (ψ ρ' x : ℂ)) ρ :=
        Complex.ofRealCLM.differentiableAt.comp ρ hψ_t
      have hψ_d : HasDerivAt (fun ρ' => (ψ ρ' x : ℂ)) (deriv (fun ρ' => (ψ ρ' x : ℂ)) ρ) ρ :=
        hψc_t.hasDerivAt
      have hprod_d : HasDerivAt (fun r => φ_test r x)
          (-μ * (ρ : ℂ) ^ (-μ - 1) * (ψ ρ x : ℂ) +
            (ρ : ℂ) ^ (-μ) * deriv (fun ρ' => (ψ ρ' x : ℂ)) ρ) ρ :=
        hk.mul hψ_d
      have hd := ladDt_eq_of_hasDerivAt (φ := φ_test) (x := x) hprod_d
      have hcs : (ρ : ℂ) ^ (-μ - 1) = (ρ : ℂ) ^ (-μ) / (ρ : ℂ) := by
        rw [Complex.cpow_sub (-μ) 1 hρ_ne, Complex.cpow_one]
      rw [hd, hcs]
      ring

    have hcut_ladDt_eq : ∀ {ρ : ℝ}, 0 < ρ → ∀ x : ℝ × ℝ,
        (ladCut R_lad x : ℂ) * ladDt φ_test ρ x = ladDt φ_test ρ x := by
      intro ρ hρ x
      by_cases hx : |x.2| ≤ R₁
      · rw [hcut_eq_one hx]; simp
      · have hx' : R₁ < |x.2| := not_le.1 hx
        have hall0 : (fun ρ' : ℝ => (ψ ρ' x : ℂ)) = fun _ => 0 :=
          funext fun ρ' => by simp [hψ_supp ρ' x (Or.inr (Or.inr hx'))]
        have h0_pt : ψ ρ x = 0 := hψ_supp ρ x (Or.inr (Or.inr hx'))
        rw [hladDt_eq hρ x, hall0, h0_pt]
        simp

    -- Clamped `L²(cell c)` test blocks on `[0, r]`
    have hSc : IsCompact (Icc (0 : ℝ) r ×ˢ Icc (0 : ℝ) r : Set (ℝ × ℝ)) :=
      isCompact_Icc.prod isCompact_Icc
    have hzero_cut : ∀ ρ : ℝ, ∀ x : ℝ × ℝ, 2 * R_lad < |x.2| →
        ladCutPhi φ_test R_lad ρ x = 0 := fun ρ x hx => by
      unfold ladCutPhi
      rw [LadPRPairAux.cut_zero hR_lad hx]
      simp
    have hφs_0H : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => φ_test p.1 p.2) (Ico 0 H ×ˢ univ) :=
      hφ_smooth.contDiffOn
    obtain ⟨hTf_c, hDf_c⟩ := GContAux.blocks_cont tr hR_lad hφs_0H hrH le_rfl hr0
    obtain ⟨hTc', hTs', M_T, hMT0, hTb⟩ :=
      GContAux.clamp_facts (T := GContAux.ladTf tr φ_test R_lad) hc_pos.le hSc hTf_c
        (fun p _ x hx => GContAux.ladTf_zero_of tr R_lad p.1 (ladCutPhi φ_test R_lad p.2)
          (fun y hy => hzero_cut p.2 y hy) x hx)
    obtain ⟨hD0c, hD0s, M_D0, hMD00, hD0b⟩ :=
      GContAux.clamp_facts (T := GContAux.ladDf tr φ_test R_lad 0) hc_pos.le hSc (hDf_c 0)
        (fun p _ x hx => by unfold GContAux.ladDf; rw [hzero_cut p.2 x hx, mul_zero])
    obtain ⟨hD1c, hD1s, M_D1, hMD10, hD1b⟩ :=
      GContAux.clamp_facts (T := GContAux.ladDf tr φ_test R_lad 1) hc_pos.le hSc (hDf_c 1)
        (fun p _ x hx => by unfold GContAux.ladDf; rw [hzero_cut p.2 x hx, mul_zero])

    let T_blk : ℝ → ℝ × ℝ → ℂ := fun ρ x =>
      GContAux.ladTf tr φ_test R_lad (ρ, ρ) (GContAux.clampQ c x)
    let D0_blk : ℝ → ℝ × ℝ → ℂ := fun ρ x =>
      GContAux.ladDf tr φ_test R_lad 0 (ρ, ρ) (GContAux.clampQ c x)
    let D1_blk : ℝ → ℝ × ℝ → ℂ := fun ρ x =>
      GContAux.ladDf tr φ_test R_lad 1 (ρ, ρ) (GContAux.clampQ c x)
    let K_blk : ℝ → ℝ × ℝ → ℂ := fun ρ x =>
      ladCutPhi (LadPRKAux.ladDW 0 H φ_test) R_lad ρ x

    have hDW_cont := LadPRKAux.ladDW_continuousOn hφs_0H
    have hK_box_compact : IsCompact (Icc (0 : ℝ) r ×ˢ B0579.box c (2 * R_lad)) :=
      isCompact_Icc.prod (B0579.isCompact_box c (2 * R_lad))
    have hK_joint_cont : ContinuousOn (fun q : ℝ × (ℝ × ℝ) => K_blk q.1 q.2)
        (Icc (0 : ℝ) r ×ˢ B0579.box c (2 * R_lad)) := by
      have hc1 : ContinuousOn (fun q : ℝ × (ℝ × ℝ) => (ladCut R_lad q.2 : ℂ))
          (Icc (0 : ℝ) r ×ˢ B0579.box c (2 * R_lad)) :=
        (Complex.continuous_ofReal.comp (LadPRPairAux.cut_continuous R_lad)).comp_continuousOn
          continuousOn_snd
      have hc2 : ContinuousOn (fun q : ℝ × (ℝ × ℝ) => LadPRKAux.ladDW 0 H φ_test q.1 q.2)
          (Icc (0 : ℝ) r ×ˢ B0579.box c (2 * R_lad)) :=
        hDW_cont.mono (prod_mono (fun ρ hρ => ⟨hρ.1, hρ.2.trans_lt hrH⟩) (subset_univ _))
      exact hc1.mul hc2
    obtain ⟨M_K0, hMK0⟩ := hK_box_compact.exists_bound_of_continuousOn hK_joint_cont
    set M_K : ℝ := max M_K0 0
    have hMK_nn : 0 ≤ M_K := le_max_right _ _

    have hT_mem : ∀ {ρ : ℝ}, ρ ∈ Icc (0 : ℝ) r → MemLp (T_blk ρ) 2 (B0581.cellVol c) := by
      intro ρ hρ
      have hm := GCont1Aux.memLp_T (c := c) (p := (ρ, ρ))
        (T := fun p x => GContAux.ladTf tr φ_test R_lad p (GContAux.clampQ c x))
        hTs' hTb hTc' ⟨hρ, hρ⟩ hMT0
      rwa [GCont1Aux.cellMeasure_zero] at hm
    have hD0_mem : ∀ {ρ : ℝ}, ρ ∈ Icc (0 : ℝ) r → MemLp (D0_blk ρ) 2 (B0581.cellVol c) := by
      intro ρ hρ
      have hm := GCont1Aux.memLp_T (c := c) (p := (ρ, ρ))
        (T := fun p x => GContAux.ladDf tr φ_test R_lad 0 p (GContAux.clampQ c x))
        hD0s hD0b hD0c ⟨hρ, hρ⟩ hMD00
      rwa [GCont1Aux.cellMeasure_zero] at hm
    have hD1_mem : ∀ {ρ : ℝ}, ρ ∈ Icc (0 : ℝ) r → MemLp (D1_blk ρ) 2 (B0581.cellVol c) := by
      intro ρ hρ
      have hm := GCont1Aux.memLp_T (c := c) (p := (ρ, ρ))
        (T := fun p x => GContAux.ladDf tr φ_test R_lad 1 p (GContAux.clampQ c x))
        hD1s hD1b hD1c ⟨hρ, hρ⟩ hMD10
      rwa [GCont1Aux.cellMeasure_zero] at hm
    have hK_mem : ∀ {ρ : ℝ}, ρ ∈ Icc (0 : ℝ) r → MemLp (K_blk ρ) 2 (B0581.cellVol c) := by
      intro ρ hρ
      have hm := LadPRKAux.memLp_cutDW (c := c) hR_lad hDW_cont ⟨hρ.1, hρ.2.trans_lt hrH⟩ 0
      rwa [GCont1Aux.cellMeasure_zero] at hm

    let boxFactor : ℝ :=
      (((volume.restrict (B0579.cell c)) (B0579.box c (2 * R_lad))).toReal) ^ (2⁻¹ : ℝ)
    have hbox_fin : B0579.cellMeasure c 0 (B0579.box c (2 * R_lad)) < ⊤ :=
      LadPRPairAux.cellMeasure_lt_top (B0579.isCompact_box c (2 * R_lad))

    have hT_norm : ∀ {ρ : ℝ}, ρ ∈ Icc (0 : ℝ) r →
        (eLpNorm (T_blk ρ) 2 (B0581.cellVol c)).toReal ≤ M_T * boxFactor := by
      intro ρ hρ
      have hb := GCont1Aux.toReal_T_le (c := c) (p := (ρ, ρ))
        (T := fun p x => GContAux.ladTf tr φ_test R_lad p (GContAux.clampQ c x))
        hTs' hTb hTc' ⟨hρ, hρ⟩ hMT0
      rwa [GCont1Aux.cellMeasure_zero] at hb
    have hD0_norm : ∀ {ρ : ℝ}, ρ ∈ Icc (0 : ℝ) r →
        (eLpNorm (D0_blk ρ) 2 (B0581.cellVol c)).toReal ≤ M_D0 * boxFactor := by
      intro ρ hρ
      have hb := GCont1Aux.toReal_T_le (c := c) (p := (ρ, ρ))
        (T := fun p x => GContAux.ladDf tr φ_test R_lad 0 p (GContAux.clampQ c x))
        hD0s hD0b hD0c ⟨hρ, hρ⟩ hMD00
      rwa [GCont1Aux.cellMeasure_zero] at hb
    have hD1_norm : ∀ {ρ : ℝ}, ρ ∈ Icc (0 : ℝ) r →
        (eLpNorm (D1_blk ρ) 2 (B0581.cellVol c)).toReal ≤ M_D1 * boxFactor := by
      intro ρ hρ
      have hb := GCont1Aux.toReal_T_le (c := c) (p := (ρ, ρ))
        (T := fun p x => GContAux.ladDf tr φ_test R_lad 1 p (GContAux.clampQ c x))
        hD1s hD1b hD1c ⟨hρ, hρ⟩ hMD10
      rwa [GCont1Aux.cellMeasure_zero] at hb
    have hK_norm : ∀ {ρ : ℝ}, ρ ∈ Icc (0 : ℝ) r →
        (eLpNorm (K_blk ρ) 2 (B0581.cellVol c)).toReal ≤ M_K * boxFactor := by
      intro ρ hρ
      have hb := LadPRPairAux.eLpNorm_le_of_bdd (c := c) (m := 0)
        (B0579.isCompact_box c (2 * R_lad)) hMK_nn (F := K_blk ρ)
        (fun x hx hxK => by
          dsimp [K_blk, ladCutPhi]
          rw [LadPRPairAux.cut_zero hR_lad (LadPRPairAux.not_mem_box_gt hx hxK),
            Complex.ofReal_zero, zero_mul])
        (fun x hx => (hMK0 (ρ, x) ⟨hρ, hx⟩).trans (le_max_left _ _))
      have hreal := ENNReal.toReal_mono
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
          (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hbox_fin.ne)) hb
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hMK_nn, ← ENNReal.toReal_rpow] at hreal
      rwa [GCont1Aux.cellMeasure_zero] at hreal

    -- Continuous `ℂ`-linear rate functional `L_rate ρ : ZC c →L[ℂ] ℂ`
    let L_rate : ℝ → ZC c →L[ℂ] ℂ := fun ρ =>
      if hρ : ρ ∈ Ioo (0 : ℝ) r then
        ((pairCellCLM c (T_blk ρ) (hT_mem ⟨hρ.1.le, hρ.2.le⟩)).comp
            ((xcToCellL2 c).comp (zcValCLM c)) -
          ((pairCellCLM c (D0_blk ρ) (hD0_mem ⟨hρ.1.le, hρ.2.le⟩)).comp
              ((projVelLp c 0).comp (velCCLM c)) +
            (pairCellCLM c (D1_blk ρ) (hD1_mem ⟨hρ.1.le, hρ.2.le⟩)).comp
              ((projVelLp c 1).comp (velCCLM c)))) +
          (pairCellCLM c (K_blk ρ) (hK_mem ⟨hρ.1.le, hρ.2.le⟩)).comp
            ((xcToCellL2 c).comp (zcValCLM c))
      else 0

    have hproj_norm : ∀ j : Fin 2, ∀ U : Lp B0581.Vel 2 (B0581.cellVol c),
        ‖projVelLp c j U‖ ≤ ‖U‖ := by
      intro j U
      have hop : ‖projVelLp c j‖ ≤ 1 := by
        refine (ContinuousLinearMap.norm_compLpL_le _).trans ?_
        refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => ?_
        simpa [one_mul] using PiLp.norm_apply_le v j
      exact (projVelLp c j).le_opNorm U |>.trans (by nlinarith [norm_nonneg U])

    set C_rate : ℝ := (M_T + (M_D0 + M_D1) * ‖velCCLM c‖ + M_K) * boxFactor
    have hC_rate_nn : 0 ≤ C_rate := by
      have : 0 ≤ boxFactor := Real.rpow_nonneg ENNReal.toReal_nonneg _
      positivity

    have hL_rate_bound : ∀ {ρ : ℝ}, ρ ∈ Ioo (0 : ℝ) r → ∀ W : ZC c,
        ‖L_rate ρ W‖ ≤ C_rate * ‖W‖ := by
      intro ρ hρ W
      have hρ_cc : ρ ∈ Icc (0 : ℝ) r := ⟨hρ.1.le, hρ.2.le⟩
      simp only [L_rate, hρ, ↓reduceDIte]
      simp only [add_apply, sub_apply, ContinuousLinearMap.comp_apply]
      have hxc_le : ‖xcToCellL2 c (zcValCLM c W)‖ ≤ ‖W‖ := by
        have hop : ‖xcToCellL2 c‖ ≤ 1 := by
          unfold xcToCellL2
          exact LinearMap.mkContinuous_norm_le _ zero_le_one _
        exact ((xcToCellL2 c).le_opNorm W.1).trans
          ((mul_le_mul_of_nonneg_right hop (norm_nonneg W.1)).trans_eq (one_mul ‖W.1‖))
      have hp0_le : ‖projVelLp c 0 (velCCLM c W)‖ ≤ ‖velCCLM c‖ * ‖W‖ :=
        (hproj_norm 0 _).trans ((velCCLM c).le_opNorm W)
      have hp1_le : ‖projVelLp c 1 (velCCLM c W)‖ ≤ ‖velCCLM c‖ * ‖W‖ :=
        (hproj_norm 1 _).trans ((velCCLM c).le_opNorm W)
      have hb_nn : 0 ≤ boxFactor := Real.rpow_nonneg ENNReal.toReal_nonneg _
      have h1 : ‖pairCellCLM c (T_blk ρ) (hT_mem hρ_cc) (xcToCellL2 c (zcValCLM c W))‖ ≤
          (M_T * boxFactor) * ‖W‖ :=
        (norm_pairCellCLM_apply_le _ _).trans
          (mul_le_mul (hT_norm hρ_cc) hxc_le (norm_nonneg _) (mul_nonneg hMT0 hb_nn))
      have h2 : ‖pairCellCLM c (D0_blk ρ) (hD0_mem hρ_cc) (projVelLp c 0 (velCCLM c W))‖ ≤
          (M_D0 * boxFactor) * (‖velCCLM c‖ * ‖W‖) :=
        (norm_pairCellCLM_apply_le _ _).trans
          (mul_le_mul (hD0_norm hρ_cc) hp0_le (norm_nonneg _) (mul_nonneg hMD00 hb_nn))
      have h3 : ‖pairCellCLM c (D1_blk ρ) (hD1_mem hρ_cc) (projVelLp c 1 (velCCLM c W))‖ ≤
          (M_D1 * boxFactor) * (‖velCCLM c‖ * ‖W‖) :=
        (norm_pairCellCLM_apply_le _ _).trans
          (mul_le_mul (hD1_norm hρ_cc) hp1_le (norm_nonneg _) (mul_nonneg hMD10 hb_nn))
      have h4 : ‖pairCellCLM c (K_blk ρ) (hK_mem hρ_cc) (xcToCellL2 c (zcValCLM c W))‖ ≤
          (M_K * boxFactor) * ‖W‖ :=
        (norm_pairCellCLM_apply_le _ _).trans
          (mul_le_mul (hK_norm hρ_cc) hxc_le (norm_nonneg _) (mul_nonneg hMK_nn hb_nn))
      calc ‖(pairCellCLM c (T_blk ρ) (hT_mem hρ_cc) (xcToCellL2 c (zcValCLM c W)) -
              (pairCellCLM c (D0_blk ρ) (hD0_mem hρ_cc) (projVelLp c 0 (velCCLM c W)) +
                pairCellCLM c (D1_blk ρ) (hD1_mem hρ_cc) (projVelLp c 1 (velCCLM c W)))) +
            pairCellCLM c (K_blk ρ) (hK_mem hρ_cc) (xcToCellL2 c (zcValCLM c W))‖
          ≤ (‖pairCellCLM c (T_blk ρ) (hT_mem hρ_cc) (xcToCellL2 c (zcValCLM c W))‖ +
              (‖pairCellCLM c (D0_blk ρ) (hD0_mem hρ_cc) (projVelLp c 0 (velCCLM c W))‖ +
                ‖pairCellCLM c (D1_blk ρ) (hD1_mem hρ_cc) (projVelLp c 1 (velCCLM c W))‖)) +
            ‖pairCellCLM c (K_blk ρ) (hK_mem hρ_cc) (xcToCellL2 c (zcValCLM c W))‖ :=
            (norm_add_le _ _).trans (add_le_add
              ((norm_sub_le _ _).trans (add_le_add le_rfl (norm_add_le _ _))) le_rfl)
        _ ≤ ((M_T * boxFactor) * ‖W‖ +
              ((M_D0 * boxFactor) * (‖velCCLM c‖ * ‖W‖) +
                (M_D1 * boxFactor) * (‖velCCLM c‖ * ‖W‖))) +
            (M_K * boxFactor) * ‖W‖ :=
            add_le_add (add_le_add h1 (add_le_add h2 h3)) h4
        _ = C_rate * ‖W‖ := by dsimp [C_rate]; ring

    -- Pointwise evaluation of `L_rate ρ W` as `ladRate`
    have hL_rate_eval : ∀ {ρ : ℝ} (hρ : ρ ∈ Ioo (0 : ℝ) r) (W : ZC c)
        {om : ℝ × ℝ → ℂ} {uu : ℝ × ℝ → Fin 2 → ℂ}
        (hom : (W.1 : ℝ × ℝ → ℂ) =ᵐ[volume.restrict (B0579.cell c)] om)
        (huu : ∀ j : Fin 2,
          (fun x => (velCCLM c W : B0579.Plane → B0581.Vel) x j)
            =ᵐ[volume.restrict (B0579.cell c)] fun x => uu x j),
        L_rate ρ W =
          (∫ x in B0579.cell c, ladFlowCx tr om uu ρ (ladCutPhi φ_test R_lad ρ) x) +
            ∫ x in B0579.cell c, om x * ((ladCut R_lad x : ℂ) * ladDt φ_test ρ x) := by
      intro ρ hρ W om uu hom huu
      have hρ_cc : ρ ∈ Icc (0 : ℝ) r := ⟨hρ.1.le, hρ.2.le⟩
      have hρ_0H : ρ ∈ Ioo (0 : ℝ) H := ⟨hρ.1, hρ.2.trans hrH⟩
      simp only [L_rate, hρ, ↓reduceDIte]
      simp only [add_apply, sub_apply, ContinuousLinearMap.comp_apply]
      rw [pairCellCLM_apply, pairCellCLM_apply, pairCellCLM_apply, pairCellCLM_apply]
      have hae_W : (xcToCellL2 c (zcValCLM c W) : ℝ × ℝ → ℂ) =ᵐ[volume.restrict (B0579.cell c)] om :=
        (coeFn_xcToCellL2 c W.1).trans hom
      have hae_u0 : (projVelLp c 0 (velCCLM c W) : ℝ × ℝ → ℂ)
          =ᵐ[volume.restrict (B0579.cell c)] fun x => uu x 0 :=
        (coeFn_projVelLp c 0 (velCCLM c W)).trans (huu 0)
      have hae_u1 : (projVelLp c 1 (velCCLM c W) : ℝ × ℝ → ℂ)
          =ᵐ[volume.restrict (B0579.cell c)] fun x => uu x 1 :=
        (coeFn_projVelLp c 1 (velCCLM c W)).trans (huu 1)
      have hI_T : IntegrableOn (fun x => om x * T_blk ρ x) (B0579.cell c) :=
        (pairCellCLM_integrable (hT_mem hρ_cc) (xcToCellL2 c (zcValCLM c W))).congr_fun_ae
          (by filter_upwards [hae_W] with x hx; rw [hx])
      have hI_0 : IntegrableOn (fun x => uu x 0 * D0_blk ρ x) (B0579.cell c) :=
        (pairCellCLM_integrable (hD0_mem hρ_cc) (projVelLp c 0 (velCCLM c W))).congr_fun_ae
          (by filter_upwards [hae_u0] with x hx; rw [hx])
      have hI_1 : IntegrableOn (fun x => uu x 1 * D1_blk ρ x) (B0579.cell c) :=
        (pairCellCLM_integrable (hD1_mem hρ_cc) (projVelLp c 1 (velCCLM c W))).congr_fun_ae
          (by filter_upwards [hae_u1] with x hx; rw [hx])
      have hI_01 : IntegrableOn (fun a => uu a 0 * D0_blk ρ a + uu a 1 * D1_blk ρ a)
          (B0579.cell c) := hI_0.add hI_1
      have heq_T : ∫ x in B0579.cell c, (xcToCellL2 c (zcValCLM c W) : ℝ × ℝ → ℂ) x * T_blk ρ x =
          ∫ x in B0579.cell c, om x * T_blk ρ x :=
        integral_congr_ae (by filter_upwards [hae_W] with x hx; rw [hx])
      have heq_0 : ∫ x in B0579.cell c, (projVelLp c 0 (velCCLM c W) : ℝ × ℝ → ℂ) x * D0_blk ρ x =
          ∫ x in B0579.cell c, uu x 0 * D0_blk ρ x :=
        integral_congr_ae (by filter_upwards [hae_u0] with x hx; rw [hx])
      have heq_1 : ∫ x in B0579.cell c, (projVelLp c 1 (velCCLM c W) : ℝ × ℝ → ℂ) x * D1_blk ρ x =
          ∫ x in B0579.cell c, uu x 1 * D1_blk ρ x :=
        integral_congr_ae (by filter_upwards [hae_u1] with x hx; rw [hx])
      have heq_K : ∫ x in B0579.cell c, (xcToCellL2 c (zcValCLM c W) : ℝ × ℝ → ℂ) x * K_blk ρ x =
          ∫ x in B0579.cell c, om x * ((ladCut R_lad x : ℂ) * ladDt φ_test ρ x) := by
        refine integral_congr_ae ?_
        filter_upwards [hae_W] with x hx
        dsimp [K_blk, ladCutPhi]
        rw [hx, LadPRKAux.ladDt_eq_ladDW hφs_0H hρ_0H x]
      rw [heq_T, heq_0, heq_1, heq_K, ← integral_add hI_0 hI_1, ← integral_sub hI_T hI_01]
      congr 1
      refine setIntegral_congr_fun (B0579.measurableSet_cell c) fun x hx => ?_
      dsimp [T_blk, D0_blk, D1_blk, GContAux.ladTf, GContAux.ladDf]
      rw [GContAux.clampQ_of_mem_cell hx, GContAux.ladFlowCx_eq]

    have hL_rate_wZ : ∀ {t ρ : ℝ}, 0 < t → t < ρ → ρ < r →
        L_rate ρ (rawInt ρ t) =
          rawScalar μ γ ν t * ladRate tr (w_fam t) (u_fam t) φ_test R_lad ρ := by
      intro t ρ ht0 htp hρr
      have hρ : ρ ∈ Ioo (0 : ℝ) r := ⟨ht0.trans htp, hρr⟩
      have ht_Ioo : t ∈ Ioo (0 : ℝ) ρ := ⟨ht0, htp⟩
      have ht_Ioc : t ∈ Ioc (0 : ℝ) H := ⟨ht0, (htp.trans hρr).le.trans hrH.le⟩
      dsimp [rawInt]
      rw [Set.indicator_of_mem ht_Ioo, (L_rate ρ).map_smul, smul_eq_mul]
      congr 1
      have hom_ae : ((wZ t ρ).1 : ℝ × ℝ → ℂ) =ᵐ[volume.restrict (B0579.cell c)] w_fam t ρ :=
        (B0579.ac_cellMeasure c 9).ae_le (hwZ_rep ht_Ioc htp.le)
      have hbs_vel : IsBiotSavart c (w_fam t ρ)
          (fun x i => (velCCLM c (wZ t ρ) : B0579.Plane → B0581.Vel) x i) :=
        isBiotSavart_congr_ae hom_ae (fun _ => Eventually.of_forall fun _ => rfl)
          (isBiotSavart_velCCLM c (wZ t ρ))
      have hu_uniq := CTE.isBiotSavart_unique c hc_pos (w_fam t ρ)
        (fun x i => (velCCLM c (wZ t ρ) : B0579.Plane → B0581.Vel) x i) (u_fam t ρ)
        hbs_vel ((hw_fam ht_Ioc).biotSavart ρ htp.le)
      have huu_ae : ∀ j : Fin 2,
          (fun x => (velCCLM c (wZ t ρ) : B0579.Plane → B0581.Vel) x j)
            =ᵐ[volume.restrict (B0579.cell c)] fun x => u_fam t ρ x j := by
        intro j
        filter_upwards [hu_uniq] with x hx
        exact congrFun hx j
      exact hL_rate_eval hρ (wZ t ρ) hom_ae huu_ae

    -- Setup for `LadProductRule` / `LadPRG` / `LadPRK` for any `t ∈ Ioo 0 r`
    have hSetup : ∀ {t : ℝ}, t ∈ Ioo (0 : ℝ) r →
        LadPRSetup ν c 9 tr t H (f t) (w_fam t) (u_fam t) φ_test := by
      intro t ht
      have ht_Ioc : t ∈ Ioc (0 : ℝ) H := ⟨ht.1, (ht.2.trans hrH).le⟩
      exact
        { hν := hν0
          hc := hc_pos
          ht := ht.1.le
          hts := ht.2.trans hrH
          flow := hw_fam ht_Ioc
          lip := ladVelLip 9 (by norm_num) ν c tr t (f t) (w_fam t) (u_fam t)
            hc_ge_one (hf_slice t ht_Ioc).2.1 (hw_fam ht_Ioc)
          smooth := hφ_smooth.contDiffOn
          periodic := fun ρ' _ x => hφ_per ρ' x }

    -- Kernel `J (t, ρ)` on `(0, r) × (0, r)`, its joint measurability, and product integrability
    let J : ℝ → ℝ → ℂ := fun t ρ =>
      if 0 < t ∧ t < ρ ∧ ρ < r then
        rawScalar μ γ ν t * ladRate tr (w_fam t) (u_fam t) φ_test R_lad ρ
      else 0

    have hJ_eq_L : ∀ {t ρ : ℝ}, 0 < t → t < ρ → ρ < r →
        J t ρ = L_rate ρ (rawInt ρ t) := by
      intro t ρ ht0 htp hρr
      simp only [J, ht0, htp, hρr, and_self, ↓reduceIte]
      exact (hL_rate_wZ ht0 htp hρr).symm

    have hJ_sm : StronglyMeasurable (Function.uncurry J) := by
      let b_pt : ℕ → ℕ → ℝ := fun n k => (k : ℝ) * r / (2 : ℝ) ^ n
      let J_approx : ℕ → ℝ × ℝ → ℂ := fun n p =>
        if 0 < p.1 ∧ p.1 < p.2 ∧ p.2 < r then
          ∑ k ∈ Finset.range (2 ^ n - 1),
            (Ioc (b_pt n k) (b_pt n (k + 1))).indicator
              (fun _ => L_rate (b_pt n (k + 1)) (rawInt (b_pt n (k + 1)) p.1)) p.2
        else 0
      have htri_meas : MeasurableSet {p : ℝ × ℝ | 0 < p.1 ∧ p.1 < p.2 ∧ p.2 < r} :=
        (measurableSet_lt measurable_const measurable_fst).inter
          ((measurableSet_lt measurable_fst measurable_snd).inter
            (measurableSet_lt measurable_snd measurable_const))
      have hJ_approx_sm : ∀ n, StronglyMeasurable (J_approx n) := by
        intro n
        refine StronglyMeasurable.ite htri_meas ?_ stronglyMeasurable_const
        refine Finset.stronglyMeasurable_fun_sum _ fun k hk => ?_
        have hk_lt : k < 2 ^ n - 1 := Finset.mem_range.1 hk
        have h2n : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
        have hb_pos : 0 < b_pt n (k + 1) := by dsimp [b_pt]; positivity
        have hb_lt_r : b_pt n (k + 1) < r := by
          have hk1_lt : ((k + 1 : ℕ) : ℝ) < (2 : ℝ) ^ n := by
            have : k + 1 < 2 ^ n := by omega
            exact_mod_cast this
          dsimp [b_pt]
          rw [div_lt_iff₀ h2n]
          nlinarith
        have hb_H : b_pt n (k + 1) ∈ Ioo (0 : ℝ) H := ⟨hb_pos, hb_lt_r.trans hrH⟩
        have ht_sm : StronglyMeasurable
            (fun p : ℝ × ℝ => L_rate (b_pt n (k + 1)) (rawInt (b_pt n (k + 1)) p.1)) :=
          ((L_rate (b_pt n (k + 1))).continuous.comp_stronglyMeasurable
            (hrawInt_sm hb_H)).comp_measurable measurable_fst
        have hset : MeasurableSet {p : ℝ × ℝ | p.2 ∈ Ioc (b_pt n k) (b_pt n (k + 1))} :=
          measurable_snd measurableSet_Ioc
        have heq : (fun p : ℝ × ℝ => (Ioc (b_pt n k) (b_pt n (k + 1))).indicator
              (fun _ => L_rate (b_pt n (k + 1)) (rawInt (b_pt n (k + 1)) p.1)) p.2) =
            {p : ℝ × ℝ | p.2 ∈ Ioc (b_pt n k) (b_pt n (k + 1))}.indicator
              (fun p => L_rate (b_pt n (k + 1)) (rawInt (b_pt n (k + 1)) p.1)) := by
          funext p
          by_cases hp : p.2 ∈ Ioc (b_pt n k) (b_pt n (k + 1))
          · have hp' : p ∈ {q : ℝ × ℝ | q.2 ∈ Ioc (b_pt n k) (b_pt n (k + 1))} := hp
            rw [Set.indicator_of_mem hp, Set.indicator_of_mem hp']
          · have hp' : p ∉ {q : ℝ × ℝ | q.2 ∈ Ioc (b_pt n k) (b_pt n (k + 1))} := hp
            rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem hp']
        rw [heq]
        exact ht_sm.indicator hset
      refine stronglyMeasurable_of_tendsto atTop hJ_approx_sm (tendsto_pi_nhds.2 fun p => ?_)
      rcases p with ⟨t, ρ⟩
      by_cases hcond : 0 < t ∧ t < ρ ∧ ρ < r
      · obtain ⟨ht0, htp, hρr⟩ := hcond
        have hρ0 : 0 < ρ := ht0.trans htp
        have ht_Ioo : t ∈ Ioo (0 : ℝ) r := ⟨ht0, htp.trans hρr⟩
        have hS_t := hSetup ht_Ioo
        have hr_Ico : r ∈ Ico t H := ⟨(htp.trans hρr).le, hrH⟩
        have hG_c := ladPRG ν c 9 tr t H (f t) (w_fam t) (u_fam t) φ_test hS_t R_lad hR_lad r hr_Ico
        have hK_c := (ladPRK ν c 9 tr t H (f t) (w_fam t) (u_fam t) φ_test hS_t R_lad hR_lad r hr_Ico).1
        have hRate_cont : ContinuousOn (fun σ => ladRate tr (w_fam t) (u_fam t) φ_test R_lad σ)
            (Ioc t r) := by
          have hdiag : ContinuousOn (fun σ => ladG tr (w_fam t) (u_fam t) φ_test R_lad (σ, σ))
              (Ioc t r) :=
            (hG_c.comp (continuousOn_id.prodMk continuousOn_id) (fun σ hσ => ⟨hσ, hσ⟩)).mono
              Ioc_subset_Icc_self
          exact (hdiag.add hK_c).congr (fun σ _ => ladRate_eq tr (w_fam t) (u_fam t) φ_test R_lad σ)
        have hRate_at : ContinuousAt (fun σ => ladRate tr (w_fam t) (u_fam t) φ_test R_lad σ) ρ :=
          (hRate_cont ρ ⟨htp, hρr.le⟩).continuousAt (Ioc_mem_nhds htp hρr)
        have hpow_lim : Tendsto (fun n : ℕ => r * (1 / 2 : ℝ) ^ n) atTop (𝓝 0) := by
          simpa only [mul_zero] using
            (tendsto_pow_atTop_nhds_zero_of_lt_one
              (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)).const_mul r
        have hev_small : ∀ᶠ n : ℕ in atTop, r / (2 : ℝ) ^ n < (r - ρ) / 2 := by
          have hpos : 0 < (r - ρ) / 2 := by linarith
          filter_upwards [hpow_lim.eventually (Iio_mem_nhds hpos)] with n hn
          have heq : r / (2 : ℝ) ^ n = r * (1 / 2 : ℝ) ^ n := by
            rw [one_div, inv_pow, div_eq_mul_inv]
          rwa [heq]
        let m_idx : ℕ → ℕ := fun n => ⌈ρ * (2 : ℝ) ^ n / r⌉₊
        let k_idx : ℕ → ℕ := fun n => m_idx n - 1
        let β_seq : ℕ → ℝ := fun n => b_pt n (k_idx n + 1)
        have hm_pos : ∀ n : ℕ, 1 ≤ m_idx n := fun n =>
          Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 (by positivity)).ne'
        have hk_succ : ∀ n : ℕ, k_idx n + 1 = m_idx n := fun n => Nat.sub_add_cancel (hm_pos n)
        have hρ_in : ∀ n : ℕ, ρ ∈ Ioc (b_pt n (k_idx n)) (b_pt n (k_idx n + 1)) := by
          intro n
          have h2n : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
          refine ⟨?_, ?_⟩
          · dsimp [b_pt]
            rw [div_lt_iff₀ h2n]
            have hlt : (k_idx n : ℝ) < ρ * (2 : ℝ) ^ n / r := by
              by_contra hle
              have hle' : ρ * (2 : ℝ) ^ n / r ≤ (k_idx n : ℝ) := le_of_not_gt hle
              have hceil : m_idx n ≤ k_idx n := Nat.ceil_le.2 hle'
              dsimp only [k_idx] at hceil
              have := hm_pos n
              omega
            exact (lt_div_iff₀ hr0).1 hlt
          · dsimp [b_pt]
            rw [hk_succ n, le_div_iff₀ h2n]
            have hle := Nat.le_ceil (ρ * (2 : ℝ) ^ n / r)
            have := (div_le_iff₀ hr0).1 hle
            linarith
        have hβ_ub : ∀ n : ℕ, β_seq n < ρ + r / (2 : ℝ) ^ n := by
          intro n
          have h1 := (hρ_in n).1
          dsimp [β_seq, b_pt] at h1 ⊢
          have : ((k_idx n + 1 : ℕ) : ℝ) * r / (2 : ℝ) ^ n =
              (k_idx n : ℝ) * r / (2 : ℝ) ^ n + r / (2 : ℝ) ^ n := by
            push_cast; ring
          linarith
        have hβ_lim : Tendsto β_seq atTop (𝓝 ρ) := by
          have hub_lim : Tendsto (fun n : ℕ => ρ + r / (2 : ℝ) ^ n) atTop (𝓝 ρ) := by
            have heq_fn : (fun n : ℕ => ρ + r / (2 : ℝ) ^ n) =
                fun n => ρ + r * (1 / 2 : ℝ) ^ n := by
              funext n; rw [one_div, inv_pow, div_eq_mul_inv]
            rw [heq_fn]
            simpa only [add_zero] using tendsto_const_nhds.add hpow_lim
          exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
            hub_lim (fun n => (hρ_in n).2) (fun n => (hβ_ub n).le)
        have hval_lim : Tendsto (fun n =>
            rawScalar μ γ ν t * ladRate tr (w_fam t) (u_fam t) φ_test R_lad (β_seq n))
            atTop (𝓝 (Function.uncurry J (t, ρ))) := by
          simp only [Function.uncurry, J, ht0, htp, hρr, and_self, ↓reduceIte]
          exact (hRate_at.tendsto.comp hβ_lim).const_mul (rawScalar μ γ ν t)
        refine hval_lim.congr' ?_
        filter_upwards [hev_small] with n hn
        have hβ_lt : β_seq n < r - r / (2 : ℝ) ^ n := by linarith [hβ_ub n]
        have hβ_r : β_seq n < r := by linarith [hβ_ub n]
        have hk_lt : k_idx n < 2 ^ n - 1 := by
          have h2n : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
          have h1n : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by norm_num)
          have hlt_real : ((k_idx n + 1 : ℕ) : ℝ) < ((2 ^ n - 1 : ℕ) : ℝ) := by
            have heq_rhs : r - r / (2 : ℝ) ^ n = ((2 ^ n - 1 : ℕ) : ℝ) * r / (2 : ℝ) ^ n := by
              rw [Nat.cast_sub h1n]
              push_cast
              field_simp
            dsimp [β_seq, b_pt] at hβ_lt
            rw [heq_rhs, div_lt_div_iff_of_pos_right h2n] at hβ_lt
            nlinarith
          have hk1 : k_idx n + 1 < 2 ^ n - 1 := by exact_mod_cast hlt_real
          omega
        simp only [J_approx, ht0, htp, hρr, and_self, ↓reduceIte]
        rw [Finset.sum_eq_single (k_idx n)]
        · rw [Set.indicator_of_mem (hρ_in n)]
          exact (hL_rate_wZ ht0 (htp.trans_le (hρ_in n).2) hβ_r).symm
        · intro k _ hkne
          rw [Set.indicator_of_notMem]
          intro hρk
          have h2n : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
          rcases lt_or_gt_of_ne hkne with hlt | hgt
          · have hle_k : ((k + 1 : ℕ) : ℝ) ≤ (k_idx n : ℝ) := by exact_mod_cast hlt
            have hle_b : b_pt n (k + 1) ≤ b_pt n (k_idx n) :=
              div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hle_k hr0.le) h2n.le
            linarith [hρk.2, (hρ_in n).1]
          · have hle_k : ((k_idx n + 1 : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast hgt
            have hle_b : b_pt n (k_idx n + 1) ≤ b_pt n k :=
              div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hle_k hr0.le) h2n.le
            linarith [hρk.1, (hρ_in n).2]
        · intro hnot
          exact absurd (Finset.mem_range.2 hk_lt) hnot
      · simp only [Function.uncurry, J_approx, J, hcond, ↓reduceIte]
        exact tendsto_const_nhds

    let μ_r := volume.restrict (Ioo (0 : ℝ) r)
    have : IsFiniteMeasure μ_r :=
      ⟨by rw [Measure.restrict_apply_univ, Real.volume_Ioo]; exact ENNReal.ofReal_lt_top⟩

    have hJ_int : Integrable (Function.uncurry J) (μ_r.prod μ_r) := by
      refine ⟨hJ_sm.aestronglyMeasurable, ?_⟩
      rw [HasFiniteIntegral, lintegral_prod_symm _ hJ_sm.enorm.aemeasurable]
      set C_JM : ℝ := C_rate * M_raw
      have hC_JM_nn : 0 ≤ C_JM := mul_nonneg hC_rate_nn hM_raw_nn
      set B_J : ℝ := C_JM * (r + 2 * r ^ (1 / 2 : ℝ))
      have hsec : ∀ ρ ∈ Ioo (0 : ℝ) r,
          ∫⁻ t in Ioo (0 : ℝ) r, ‖J t ρ‖ₑ ≤ ENNReal.ofReal B_J := by
        intro ρ hρ
        have hρ_0H : ρ ∈ Ioo (0 : ℝ) H := ⟨hρ.1, hρ.2.trans hrH⟩
        let g_ρ : ℝ → ℝ := (Ioo (0 : ℝ) ρ).indicator
          (fun t => C_JM * (1 + (ρ - t) ^ (-1 / 2 : ℝ)))
        have hg_int_on : IntegrableOn (fun t => C_JM * (1 + (ρ - t) ^ (-1 / 2 : ℝ)))
            (Ioo (0 : ℝ) ρ) volume :=
          (integrableOn_one_add_inv_sqrt hρ.1.le).1.const_mul C_JM
        have hg_int : Integrable g_ρ volume := hg_int_on.integrable_indicator measurableSet_Ioo
        have hg_nn : 0 ≤ g_ρ := fun t => by
          by_cases ht : t ∈ Ioo (0 : ℝ) ρ
          · dsimp [g_ρ]; rw [Set.indicator_of_mem ht]
            have : 0 ≤ (ρ - t) ^ (-1 / 2 : ℝ) := Real.rpow_nonneg (sub_pos.2 ht.2).le _
            positivity
          · dsimp [g_ρ]; rw [Set.indicator_of_notMem ht]
        have hpt : ∀ t ∈ Ioo (0 : ℝ) r, ‖J t ρ‖ₑ ≤ ENNReal.ofReal (g_ρ t) := by
          intro t ht
          by_cases htp : t < ρ
          · have ht_Ioo : t ∈ Ioo (0 : ℝ) ρ := ⟨ht.1, htp⟩
            rw [← ofReal_norm, hJ_eq_L ht.1 htp hρ.2]
            dsimp [g_ρ]
            rw [Set.indicator_of_mem ht_Ioo]
            refine ENNReal.ofReal_le_ofReal ?_
            calc ‖L_rate ρ (rawInt ρ t)‖
                ≤ C_rate * ‖rawInt ρ t‖ := hL_rate_bound hρ _
              _ ≤ C_rate * (M_raw * (1 + (ρ - t) ^ (-1 / 2 : ℝ))) :=
                  mul_le_mul_of_nonneg_left (hrawInt_norm hρ_0H ht_Ioo) hC_rate_nn
              _ = C_JM * (1 + (ρ - t) ^ (-1 / 2 : ℝ)) := by dsimp [C_JM]; ring
          · have hcond : ¬ (0 < t ∧ t < ρ ∧ ρ < r) := fun h => htp h.2.1
            simp only [J, hcond, ↓reduceIte, enorm_zero]
            exact bot_le
        calc ∫⁻ t in Ioo (0 : ℝ) r, ‖J t ρ‖ₑ
            ≤ ∫⁻ t in Ioo (0 : ℝ) r, ENNReal.ofReal (g_ρ t) :=
              setLIntegral_mono' measurableSet_Ioo hpt
          _ ≤ ∫⁻ t, ENNReal.ofReal (g_ρ t) := setLIntegral_le_lintegral _ _
          _ = ENNReal.ofReal (∫ t, g_ρ t) :=
              (ofReal_integral_eq_lintegral_ofReal hg_int (Eventually.of_forall hg_nn)).symm
          _ = ENNReal.ofReal (C_JM * ((ρ - 0) + 2 * (ρ - 0) ^ (1 / 2 : ℝ))) := by
              rw [integral_indicator measurableSet_Ioo, integral_const_mul,
                (integrableOn_one_add_inv_sqrt hρ.1.le).2]
          _ ≤ ENNReal.ofReal B_J := by
              rw [sub_zero]
              refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ hC_JM_nn)
              have hrp : ρ ^ (1 / 2 : ℝ) ≤ r ^ (1 / 2 : ℝ) :=
                Real.rpow_le_rpow hρ.1.le hρ.2.le (by norm_num)
              linarith [hρ.2]
      calc ∫⁻ ρ in Ioo (0 : ℝ) r, ∫⁻ t in Ioo (0 : ℝ) r, ‖J t ρ‖ₑ
          ≤ ∫⁻ _ in Ioo (0 : ℝ) r, ENNReal.ofReal B_J :=
            setLIntegral_mono' measurableSet_Ioo hsec
        _ = ENNReal.ofReal B_J * volume (Ioo (0 : ℝ) r) := setLIntegral_const _ _
        _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
            (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_lt_top)

    -- Slice evaluation in `ρ`: relate `∫ t in Ioo 0 r, J t ρ` to Terms 1 + 2
    have hJ_col : ∀ {ρ : ℝ}, ρ ∈ Ioo (0 : ℝ) r →
        (∫ x in B0579.cell c,
            flowIntegrand tr
              (fun y => (gainG γ ν ρ : ℂ) * ω_duh ρ y)
              (fun y => (gainG γ ν ρ : ℂ) • u_duh (ρ, y))
              ρ (ψ ρ) x) +
          (∫ x in B0579.cell c,
            ((gainG γ ν ρ : ℂ) * ω_duh ρ x) *
              (-(μ / (ρ : ℂ)) * (ψ ρ x : ℂ) + (deriv (fun ρ' => ψ ρ' x) ρ : ℂ))) =
        ∫ t in Ioo (0 : ℝ) r, J t ρ := by
      intro ρ hρ
      have hρ_0H : ρ ∈ Ioo (0 : ℝ) H := ⟨hρ.1, hρ.2.trans hrH⟩
      have hLHS_eq_L : L_rate ρ (W_raw ρ) =
          (∫ x in B0579.cell c,
              flowIntegrand tr
                (fun y => (gainG γ ν ρ : ℂ) * ω_duh ρ y)
                (fun y => (gainG γ ν ρ : ℂ) • u_duh (ρ, y))
                ρ (ψ ρ) x) +
            (∫ x in B0579.cell c,
              ((gainG γ ν ρ : ℂ) * ω_duh ρ x) *
                (-(μ / (ρ : ℂ)) * (ψ ρ x : ℂ) + (deriv (fun ρ' => ψ ρ' x) ρ : ℂ))) := by
        have hraw_inv : rawScalar μ γ ν ρ * invScalar μ γ ν ρ = 1 := by
          unfold rawScalar invScalar
          have hg_ne : (gainG γ ν ρ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (gainG_pos γ ν ρ).ne'
          calc (((ρ : ℂ) ^ μ) * (gainG γ ν ρ : ℂ)) * (((ρ : ℂ) ^ (-μ)) * ((gainG γ ν ρ)⁻¹ : ℂ))
              = (((ρ : ℂ) ^ μ) * ((ρ : ℂ) ^ (-μ))) *
                  ((gainG γ ν ρ : ℂ) * ((gainG γ ν ρ : ℂ))⁻¹) := by ring
            _ = 1 * 1 := by rw [cpow_mul_neg_ofReal_pos hρ.1 μ, mul_inv_cancel₀ hg_ne]
            _ = 1 := one_mul 1
        have hW_raw_eq : W_raw ρ = rawScalar μ γ ν ρ • W_Z ρ := by
          dsimp [W_Z]
          rw [← mul_smul, hraw_inv, one_smul]
        rw [hW_raw_eq, (L_rate ρ).map_smul, smul_eq_mul,
          hL_rate_eval hρ (W_Z ρ) (Eventually.of_forall fun _ => rfl)
            (fun j => (hu_ae hρ_0H j).symm)]
        have hψ_cyl : B0579.IsCylTest c (ψ ρ) :=
          ⟨hψ_smooth.comp (contDiff_const.prodMk contDiff_id),
            fun x => hψ_per ρ x,
            ⟨R₁, fun x hx => hψ_supp ρ x (Or.inr (Or.inr hx))⟩⟩
        have hterm1 : rawScalar μ γ ν ρ *
            (∫ x in B0579.cell c, ladFlowCx tr (ω_duh ρ) (fun y => u_duh (ρ, y)) ρ
              (ladCutPhi φ_test R_lad ρ) x) =
            ∫ x in B0579.cell c,
              flowIntegrand tr
                (fun y => (gainG γ ν ρ : ℂ) * ω_duh ρ y)
                (fun y => (gainG γ ν ρ : ℂ) • u_duh (ρ, y))
                ρ (ψ ρ) x := by
          have hcut_ρ : ladCutPhi φ_test R_lad ρ = fun y => ((ρ : ℂ) ^ (-μ)) * (ψ ρ y : ℂ) :=
            funext fun y => hcutPhi_eq ρ y
          rw [hcut_ρ]
          have hcongr1 : (fun x => ladFlowCx tr (ω_duh ρ) (fun y => u_duh (ρ, y)) ρ
                (fun y => ((ρ : ℂ) ^ (-μ)) * (ψ ρ y : ℂ)) x) =
              fun x => ((ρ : ℂ) ^ (-μ)) *
                flowIntegrand tr (ω_duh ρ) (fun y => u_duh (ρ, y)) ρ (ψ ρ) x :=
            funext fun x => ladFlowCx_const_mul_ofReal tr (ω_duh ρ) (fun y => u_duh (ρ, y))
              ρ ((ρ : ℂ) ^ (-μ)) hψ_cyl x
          rw [hcongr1, integral_const_mul, ← mul_assoc]
          have hscalar1 : rawScalar μ γ ν ρ * ((ρ : ℂ) ^ (-μ)) = (gainG γ ν ρ : ℂ) := by
            unfold rawScalar
            calc (((ρ : ℂ) ^ μ) * (gainG γ ν ρ : ℂ)) * ((ρ : ℂ) ^ (-μ))
                = (((ρ : ℂ) ^ μ) * ((ρ : ℂ) ^ (-μ))) * (gainG γ ν ρ : ℂ) := by ring
              _ = (gainG γ ν ρ : ℂ) := by rw [cpow_mul_neg_ofReal_pos hρ.1 μ, one_mul]
          rw [hscalar1, ← integral_const_mul]
          exact integral_congr_ae (Eventually.of_forall fun x =>
            (flowIntegrand_const_smul tr (ω_duh ρ) (fun y => u_duh (ρ, y))
              ρ (gainG γ ν ρ : ℂ) (ψ ρ) x).symm)
        have hterm2 : rawScalar μ γ ν ρ *
            (∫ x in B0579.cell c, ω_duh ρ x * ((ladCut R_lad x : ℂ) * ladDt φ_test ρ x)) =
            ∫ x in B0579.cell c,
              ((gainG γ ν ρ : ℂ) * ω_duh ρ x) *
                (-(μ / (ρ : ℂ)) * (ψ ρ x : ℂ) + (deriv (fun ρ' => ψ ρ' x) ρ : ℂ)) := by
          have hcongr2 : (fun x => ω_duh ρ x * ((ladCut R_lad x : ℂ) * ladDt φ_test ρ x)) =
              fun x => ((ρ : ℂ) ^ (-μ)) * (ω_duh ρ x *
                (-(μ / (ρ : ℂ)) * (ψ ρ x : ℂ) + (deriv (fun ρ' => ψ ρ' x) ρ : ℂ))) := by
            funext x
            rw [hcut_ladDt_eq hρ.1 x, hladDt_eq hρ.1 x]
            ring
          rw [hcongr2, integral_const_mul, ← mul_assoc]
          have hscalar1 : rawScalar μ γ ν ρ * ((ρ : ℂ) ^ (-μ)) = (gainG γ ν ρ : ℂ) := by
            unfold rawScalar
            calc (((ρ : ℂ) ^ μ) * (gainG γ ν ρ : ℂ)) * ((ρ : ℂ) ^ (-μ))
                = (((ρ : ℂ) ^ μ) * ((ρ : ℂ) ^ (-μ))) * (gainG γ ν ρ : ℂ) := by ring
              _ = (gainG γ ν ρ : ℂ) := by rw [cpow_mul_neg_ofReal_pos hρ.1 μ, one_mul]
          rw [hscalar1, ← integral_const_mul]
          exact integral_congr_ae (Eventually.of_forall fun x => by dsimp; ring)
        rw [mul_add, hterm1, hterm2]
      rw [← hLHS_eq_L]
      simp only [W_raw, hρ_0H, ↓reduceIte]
      have hcomm : L_rate ρ (∫ t in Ioo (0 : ℝ) ρ, rawInt ρ t) =
          ∫ t in Ioo (0 : ℝ) ρ, L_rate ρ (rawInt ρ t) :=
        (((L_rate ρ).restrictScalars ℝ).integral_comp_comm (hrawInt_integrable hρ_0H)).symm
      rw [hcomm]
      have hind : ∀ t ∈ Ioo (0 : ℝ) r,
          J t ρ = (Ioo (0 : ℝ) ρ).indicator (fun τ => L_rate ρ (rawInt ρ τ)) t := by
        intro t ht
        by_cases htp : t < ρ
        · have ht_ρ : t ∈ Ioo (0 : ℝ) ρ := ⟨ht.1, htp⟩
          rw [Set.indicator_of_mem ht_ρ]
          exact hJ_eq_L ht.1 htp hρ.2
        · have ht_nρ : t ∉ Ioo (0 : ℝ) ρ := fun h => htp h.2
          rw [Set.indicator_of_notMem ht_nρ]
          have hc_J : ¬ (0 < t ∧ t < ρ ∧ ρ < r) := fun h => htp h.2.1
          simp only [J, hc_J, ↓reduceIte]
      have hinter : Ioo (0 : ℝ) r ∩ Ioo (0 : ℝ) ρ = Ioo (0 : ℝ) ρ :=
        inter_eq_right.2 (Ioo_subset_Ioo_right hρ.2.le)
      rw [setIntegral_congr_fun measurableSet_Ioo hind, setIntegral_indicator measurableSet_Ioo,
        hinter]

    -- Row evaluation in `t`: relate `∫ σ in Ioo 0 r, J t σ` to `-Term 3` via `ladProductRule`
    have hJ_row : ∀ {t : ℝ}, t ∈ Ioo (0 : ℝ) r →
        (gainG γ ν t : ℂ) * ∫ x in B0579.cell c, f t x * (ψ t x : ℂ) =
          -∫ σ in Ioo (0 : ℝ) r, J t σ := by
      intro t ht
      have ht_Ioc : t ∈ Ioc (0 : ℝ) H := ⟨ht.1, (ht.2.trans hrH).le⟩
      have hS_t := hSetup ht
      obtain ⟨_hInt_rate, hPR⟩ := ladProductRule ν c 9 tr t H (f t) (w_fam t) (u_fam t) φ_test
        hν0 hc_pos ht.1.le (ht.2.trans hrH) (hw_fam ht_Ioc) hS_t.lip
        hφ_smooth.contDiffOn (fun ρ' _ x => hφ_per ρ' x) R_lad hR_lad r ⟨ht.2.le, hrH⟩
      have hP_r : ladCutPair c R_lad (w_fam t) φ_test r = 0 := by
        unfold ladCutPair
        have h0 : ∀ x : ℝ × ℝ, ladCutPhi φ_test R_lad r x = 0 := fun x => by
          rw [hcutPhi_eq r x]
          simp [φ_test, hψ_supp r x (Or.inr (Or.inl hs₂r))]
        simp [h0]
      have hP_t : ladCutPair c R_lad (w_fam t) φ_test t =
          ((t : ℂ) ^ (-μ)) * ∫ x in B0579.cell c, f t x * (ψ t x : ℂ) := by
        unfold ladCutPair
        have hae : ∀ᵐ x ∂(volume.restrict (B0579.cell c)),
            w_fam t t x * ladCutPhi φ_test R_lad t x =
              ((t : ℂ) ^ (-μ)) * (f t x * (ψ t x : ℂ)) := by
          filter_upwards [(hw_fam ht_Ioc).initial] with x hx
          rw [hx, hcutPhi_eq t x]
          dsimp [φ_test]
          ring
        rw [integral_congr_ae hae, integral_const_mul]
      have hRHS_eq : rawScalar μ γ ν t * ∫ σ in t..r,
            ladRate tr (w_fam t) (u_fam t) φ_test R_lad σ =
          ∫ σ in Ioo (0 : ℝ) r, J t σ := by
        rw [intervalIntegral.integral_of_le ht.2.le, integral_Ioc_eq_integral_Ioo,
          ← integral_const_mul]
        have hind : ∀ σ ∈ Ioo (0 : ℝ) r,
            J t σ = (Ioo t r).indicator
              (fun s' => rawScalar μ γ ν t * ladRate tr (w_fam t) (u_fam t) φ_test R_lad s') σ := by
          intro σ hσ
          by_cases htσ : t < σ
          · have hσ_tr : σ ∈ Ioo t r := ⟨htσ, hσ.2⟩
            rw [Set.indicator_of_mem hσ_tr]
            simp only [J, ht.1, htσ, hσ.2, and_self, ↓reduceIte]
          · have hσ_ntr : σ ∉ Ioo t r := fun h => htσ h.1
            rw [Set.indicator_of_notMem hσ_ntr]
            have hc_J : ¬ (0 < t ∧ t < σ ∧ σ < r) := fun h => htσ h.2.1
            simp only [J, hc_J, ↓reduceIte]
        have hinter : Ioo (0 : ℝ) r ∩ Ioo t r = Ioo t r :=
          inter_eq_right.2 (Ioo_subset_Ioo_left ht.1.le)
        rw [setIntegral_congr_fun measurableSet_Ioo hind, setIntegral_indicator measurableSet_Ioo,
          hinter]
      have hPR_scaled := congrArg (fun z : ℂ => rawScalar μ γ ν t * z) hPR
      rw [hP_r, hP_t, zero_sub, mul_neg, ← mul_assoc, hRHS_eq] at hPR_scaled
      have hscalar_t : rawScalar μ γ ν t * ((t : ℂ) ^ (-μ)) = (gainG γ ν t : ℂ) := by
        unfold rawScalar
        calc (((t : ℂ) ^ μ) * (gainG γ ν t : ℂ)) * ((t : ℂ) ^ (-μ))
            = (((t : ℂ) ^ μ) * ((t : ℂ) ^ (-μ))) * (gainG γ ν t : ℂ) := by ring
          _ = (gainG γ ν t : ℂ) := by rw [cpow_mul_neg_ofReal_pos ht.1 μ, one_mul]
      rw [hscalar_t] at hPR_scaled
      have := congrArg Neg.neg hPR_scaled
      simpa using this

    -- Combine via Fubini on `Ioo 0 r × Ioo 0 r` and extend `Ioo 0 r` to `Ioo 0 H`
    let totalInt : ℝ → ℂ := fun ρ =>
      (∫ x in B0579.cell c,
          flowIntegrand tr
            (fun y => (gainG γ ν ρ : ℂ) * ω_duh ρ y)
            (fun y => (gainG γ ν ρ : ℂ) • u_duh (ρ, y))
            ρ (ψ ρ) x) +
        (∫ x in B0579.cell c,
          ((gainG γ ν ρ : ℂ) * ω_duh ρ x) *
            (-(μ / (ρ : ℂ)) * (ψ ρ x : ℂ) + (deriv (fun ρ' => ψ ρ' x) ρ : ℂ))) +
        (gainG γ ν ρ : ℂ) * ∫ x in B0579.cell c, f ρ x * (ψ ρ x : ℂ)

    have hzero_ge_r : ∀ {ρ : ℝ}, r ≤ ρ → totalInt ρ = 0 := by
      intro ρ hρ
      have hs₂ρ : s₂ < ρ := hs₂r.trans_le hρ
      have hψ_ρ : ψ ρ = fun _ => 0 := funext fun x => hψ_supp ρ x (Or.inr (Or.inl hs₂ρ))
      have hderiv_ρ : ∀ x : ℝ × ℝ, deriv (fun ρ' => (ψ ρ' x : ℂ)) ρ = 0 := by
        intro x
        have hev : (fun ρ' => (ψ ρ' x : ℂ)) =ᶠ[𝓝 ρ] fun _ => (0 : ℂ) := by
          filter_upwards [Ioi_mem_nhds hs₂ρ] with ρ' hρ'
          simp [hψ_supp ρ' x (Or.inr (Or.inl hρ'))]
        rw [hev.deriv_eq, deriv_const]
      dsimp only [totalInt]
      simp_rw [hderiv_ρ]
      rw [hψ_ρ]
      have hp0 : ∀ j, B0579.pd j (fun _ : ℝ × ℝ => (0 : ℝ)) = fun _ => 0 := fun j => by
        funext y; simp [B0579.pd]
      have hfi0 : ∀ x : ℝ × ℝ, flowIntegrand tr
          (fun y => (gainG γ ν ρ : ℂ) * ω_duh ρ y)
          (fun y => (gainG γ ν ρ : ℂ) • u_duh (ρ, y))
          ρ (fun _ => 0) x = 0 := fun x => by
        simp [flowIntegrand, lapP, hp0]
      have hint0 : (∫ x in B0579.cell c, flowIntegrand tr
          (fun y => (gainG γ ν ρ : ℂ) * ω_duh ρ y)
          (fun y => (gainG γ ν ρ : ℂ) • u_duh (ρ, y))
          ρ (fun _ => 0) x) = 0 := by
        simp_rw [hfi0]
        exact integral_zero _ _
      rw [hint0]
      simp

    have hind_H : ∀ ρ ∈ Ioo (0 : ℝ) H, totalInt ρ = (Ioo (0 : ℝ) r).indicator totalInt ρ := by
      intro ρ hρ
      by_cases hρr : ρ < r
      · have hρ_in : ρ ∈ Ioo (0 : ℝ) r := ⟨hρ.1, hρr⟩
        rw [Set.indicator_of_mem hρ_in]
      · rw [Set.indicator_of_notMem (fun h => hρr h.2)]
        exact hzero_ge_r (not_lt.1 hρr)

    have hinter_rH : Ioo (0 : ℝ) H ∩ Ioo (0 : ℝ) r = Ioo (0 : ℝ) r :=
      inter_eq_right.2 (Ioo_subset_Ioo_right hrH.le)

    change ∫ ρ in Ioo (0 : ℝ) H, totalInt ρ = 0
    rw [setIntegral_congr_fun measurableSet_Ioo hind_H, setIntegral_indicator measurableSet_Ioo,
      hinter_rH]
    have hcongr_r : ∀ ρ ∈ Ioo (0 : ℝ) r,
        totalInt ρ = (∫ t in Ioo (0 : ℝ) r, J t ρ) + (-∫ σ in Ioo (0 : ℝ) r, J ρ σ) := by
      intro ρ hρ
      dsimp only [totalInt]
      rw [hJ_col hρ, hJ_row hρ]
    have hint_col : IntegrableOn (fun ρ => ∫ t in Ioo (0 : ℝ) r, J t ρ) (Ioo (0 : ℝ) r) volume :=
      hJ_int.integral_prod_right
    have hint_row : IntegrableOn (fun ρ => -∫ σ in Ioo (0 : ℝ) r, J ρ σ) (Ioo (0 : ℝ) r) volume :=
      hJ_int.integral_prod_left.neg
    rw [setIntegral_congr_fun measurableSet_Ioo hcongr_r,
      integral_add hint_col hint_row, integral_neg]
    have hswap : (∫ ρ in Ioo (0 : ℝ) r, ∫ t in Ioo (0 : ℝ) r, J t ρ) =
        ∫ t in Ioo (0 : ℝ) r, ∫ σ in Ioo (0 : ℝ) r, J t σ :=
      (integral_integral_swap (f := J) hJ_int).symm
    rw [hswap, add_neg_cancel]

end UnforcedLeray.Short.IIIa.CoreDuhamelNiceAux
end
