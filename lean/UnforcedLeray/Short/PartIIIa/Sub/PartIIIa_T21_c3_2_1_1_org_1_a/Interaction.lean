import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_1_org_1_a.LpMeas
import UnforcedLeray.Short.PartIIb.Tasks.InteractionCylinder.CylWeightedKernel
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_3_1

/-!
# Helper for `PartIII-a:T21/c3/2/1/1/org/1/a`: the localized interaction on `X_{m,d}`

The complex interaction `-(K_d W)·b` (SP 2863-2865, 2974-2976) splits into real and imaginary
parts, each given by the bounded cylinder operator `IIb.cylWeightedOp` (PartII-b, SP 2117-2137).
For the rescaled train coefficient `b = ∇E_mov(r)` the weighted coefficient bound comes from
`RescaledTrainBounds` (SP 3050-3051).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter UnforcedLeray.Blueprint.Planar
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa.BlockPropagatorInteriorSub.OrgSplit.RelIntA

open UnforcedLeray.Short.IIIa.CompactDuhamelGapSub

/-- The complex localized interaction `-(K_d W)·b` with a real vector coefficient `b`. -/
def cxInter (d : ℝ) (b : ℝ × ℝ → ℝ × ℝ) (W : ℝ × ℝ → ℂ) (y : ℝ × ℝ) : ℂ :=
  -(kerVelCx d W y 0 * (((b y).1 : ℝ) : ℂ) + kerVelCx d W y 1 * (((b y).2 : ℝ) : ℂ))

theorem measurable_kerD_comp (d : ℝ) (y : ℝ × ℝ) (k : Fin 2) :
    Measurable (fun z : ℝ × ℝ => kerD d (y - z) k) := by
  unfold kerD
  exact (EuclideanSpace.proj k).continuous.measurable.comp
    ((UnforcedLeray.Cyl.measurable_bsKernel d).comp (measurable_const.sub measurable_id))

theorem abs_kerD_le (d : ℝ) (z : ℝ × ℝ) (k : Fin 2) :
    |kerD d z k| ≤ ‖UnforcedLeray.Cyl.bsKernel d z‖ := by
  unfold kerD
  simpa [Real.norm_eq_abs] using PiLp.norm_apply_le (UnforcedLeray.Cyl.bsKernel d z) k

/-- For `W ∈ X_{m,d}`, the kernel integrand `z ↦ W z K_d(y - z)` is integrable on the cell for
almost every `y` in the cell. -/
theorem ae_integrableOn_kerVelCx {d m : ℝ} (hd : 1 ≤ d) (hm : 1 < m) {W : ℝ × ℝ → ℂ}
    (hW : MemLp W 2 (B0579.cellMeasure d m)) :
    ∀ᵐ y ∂(volume.restrict (B0579.cell d)), ∀ k : Fin 2,
      IntegrableOn (fun z => W z * ((kerD d (y - z) k : ℝ) : ℂ)) (B0579.cell d) := by
  have hWn : MemLp (fun x => ‖W x‖) 2 (B0579.cellMeasure d m) := hW.norm
  set f : IIb.Xmc d m := hWn.toLp _ with hfdef
  have hf : (f : ℝ × ℝ → ℝ) =ᵐ[volume.restrict (B0579.cell d)] fun x => ‖W x‖ :=
    (B0579.ac_cellMeasure d m).ae_le (MemLp.coeFn_toLp hWn)
  have hWm : AEStronglyMeasurable W (volume.restrict (B0579.cell d)) :=
    hW.1.mono_ac (B0579.ac_cellMeasure d m)
  filter_upwards [IIb.ae_integrable_bsKernel hd hm f] with y hy k
  refine Integrable.mono' hy.norm ?_ ?_
  · exact hWm.mul ((Complex.measurable_ofReal.comp (measurable_kerD_comp d y k)).aestronglyMeasurable)
  · filter_upwards [hf] with z hz
    rw [norm_mul, Complex.norm_real, norm_smul, hz, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg _)]
    exact mul_le_mul_of_nonneg_left (abs_kerD_le d (y - z) k) (norm_nonneg _)

/-- Component of the real cylinder velocity as a scalar integral. -/
theorem cylK_apply {d : ℝ} {u : ℝ × ℝ → ℝ} {y : ℝ × ℝ}
    (hu : Integrable (fun z => u z • UnforcedLeray.Cyl.bsKernel d (y - z))
      (volume.restrict (B0579.cell d))) (k : Fin 2) :
    UnforcedLeray.Cyl.K d u y k = ∫ z in B0579.cell d, u z * kerD d (y - z) k := by
  unfold UnforcedLeray.Cyl.K
  rw [← IIb.cell_eq_cylCell]
  have h := (EuclideanSpace.proj k : UnforcedLeray.Cyl.Vec2 →L[ℝ] ℝ).integral_comp_comm hu
  have h' : (EuclideanSpace.proj k : UnforcedLeray.Cyl.Vec2 →L[ℝ] ℝ)
      (∫ z in B0579.cell d, u z • UnforcedLeray.Cyl.bsKernel d (y - z)) =
      ∫ z in B0579.cell d, u z * kerD d (y - z) k := by
    rw [← h]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp [kerD]
  exact h'

/-- Pointwise splitting of the complex kernel velocity into the real cylinder velocities of the
real and imaginary parts. -/
theorem kerVelCx_eq_re_im {d : ℝ} {W : ℝ × ℝ → ℂ} {y : ℝ × ℝ}
    (hu : Integrable (fun z => (W z).re • UnforcedLeray.Cyl.bsKernel d (y - z))
      (volume.restrict (B0579.cell d)))
    (hv : Integrable (fun z => (W z).im • UnforcedLeray.Cyl.bsKernel d (y - z))
      (volume.restrict (B0579.cell d))) (k : Fin 2) :
    kerVelCx d W y k =
      ((UnforcedLeray.Cyl.K d (fun z => (W z).re) y k : ℝ) : ℂ) +
        Complex.I * ((UnforcedLeray.Cyl.K d (fun z => (W z).im) y k : ℝ) : ℂ) := by
  rw [cylK_apply hu k, cylK_apply hv k]
  have hu' : Integrable (fun z => (W z).re * kerD d (y - z) k) (volume.restrict (B0579.cell d)) := by
    have := (EuclideanSpace.proj k : UnforcedLeray.Cyl.Vec2 →L[ℝ] ℝ).integrable_comp hu
    exact this.congr (Eventually.of_forall fun z => by simp [kerD])
  have hv' : Integrable (fun z => (W z).im * kerD d (y - z) k) (volume.restrict (B0579.cell d)) := by
    have := (EuclideanSpace.proj k : UnforcedLeray.Cyl.Vec2 →L[ℝ] ℝ).integrable_comp hv
    exact this.congr (Eventually.of_forall fun z => by simp [kerD])
  unfold kerVelCx
  have hsplit : (fun z => W z * ((kerD d (y - z) k : ℝ) : ℂ)) = fun z =>
      (((W z).re * kerD d (y - z) k : ℝ) : ℂ) +
        Complex.I * (((W z).im * kerD d (y - z) k : ℝ) : ℂ) := by
    funext z
    conv_lhs => rw [← Complex.re_add_im (W z)]
    push_cast
    ring
  rw [hsplit, integral_add ?_ ?_, integral_const_mul, integral_complex_ofReal,
    integral_complex_ofReal]
  · exact hu'.ofReal
  · exact hv'.ofReal.const_mul Complex.I

/-- **Bound of the complex localized interaction on `X_{m,d}`** from the cylinder operator. -/
theorem cxInter_bound {d m B : ℝ} (hd : 1 ≤ d) (hm : 1 < m) (hB : 0 ≤ B)
    {b : ℝ × ℝ → ℝ × ℝ} (hb : IIb.IsCylWeightedCoeff d m B b)
    {W : ℝ × ℝ → ℂ} (hW : MemLp W 2 (B0579.cellMeasure d m)) :
    AEStronglyMeasurable (cxInter d b W) (B0579.cellMeasure d m) ∧
      xNorm d m (cxInter d b W) ≤
        ENNReal.ofReal (2 * IIb.cylKernelBoundConst m * B) * xNorm d m W := by
  set μ := B0579.cellMeasure d m with hμ
  have hu : MemLp (fun z => (W z).re) 2 μ := by
    exact Complex.reCLM.comp_memLp' hW
  have hv : MemLp (fun z => (W z).im) 2 μ := by
    exact Complex.imCLM.comp_memLp' hW
  set U : IIb.Xmc d m := hu.toLp _ with hUdef
  set V : IIb.Xmc d m := hv.toLp _ with hVdef
  have hUe : (U : ℝ × ℝ → ℝ) =ᵐ[μ] fun z => (W z).re := MemLp.coeFn_toLp hu
  have hVe : (V : ℝ × ℝ → ℝ) =ᵐ[μ] fun z => (W z).im := MemLp.coeFn_toLp hv
  have hUe' : (U : ℝ × ℝ → ℝ) =ᵐ[volume.restrict (B0579.cell d)] fun z => (W z).re :=
    (B0579.ac_cellMeasure d m).ae_le hUe
  have hVe' : (V : ℝ × ℝ → ℝ) =ᵐ[volume.restrict (B0579.cell d)] fun z => (W z).im :=
    (B0579.ac_cellMeasure d m).ae_le hVe
  set T := IIb.cylWeightedOp hd hm hB hb with hTdef
  have hTU := IIb.isCylWeightedOp_cylWeightedOp hd hm hB hb U
  have hTV := IIb.isCylWeightedOp_cylWeightedOp hd hm hB hb V
  -- the cylinder velocities of `U` and of `re W` coincide
  have hKU : ∀ x, UnforcedLeray.Cyl.K d U x = UnforcedLeray.Cyl.K d (fun z => (W z).re) x := by
    intro x
    unfold UnforcedLeray.Cyl.K
    rw [← IIb.cell_eq_cylCell]
    refine integral_congr_ae ?_
    filter_upwards [hUe'] with z hz
    rw [hz]
  have hKV : ∀ x, UnforcedLeray.Cyl.K d V x = UnforcedLeray.Cyl.K d (fun z => (W z).im) x := by
    intro x
    unfold UnforcedLeray.Cyl.K
    rw [← IIb.cell_eq_cylCell]
    refine integral_congr_ae ?_
    filter_upwards [hVe'] with z hz
    rw [hz]
  -- integrability of the real kernel integrands for a.e. `y`
  have hIu : ∀ᵐ y ∂μ, Integrable (fun z => (W z).re • UnforcedLeray.Cyl.bsKernel d (y - z))
      (volume.restrict (B0579.cell d)) := by
    have h := (B0579.cellMeasure_ac d m).ae_le (IIb.ae_integrable_bsKernel hd hm U)
    filter_upwards [h] with y hy
    refine hy.congr ?_
    filter_upwards [hUe'] with z hz
    rw [hz]
  have hIv : ∀ᵐ y ∂μ, Integrable (fun z => (W z).im • UnforcedLeray.Cyl.bsKernel d (y - z))
      (volume.restrict (B0579.cell d)) := by
    have h := (B0579.cellMeasure_ac d m).ae_le (IIb.ae_integrable_bsKernel hd hm V)
    filter_upwards [h] with y hy
    refine hy.congr ?_
    filter_upwards [hVe'] with z hz
    rw [hz]
  -- the a.e. identity
  have hEq : cxInter d b W =ᵐ[μ] fun y =>
      (((T U : ℝ × ℝ → ℝ) y : ℝ) : ℂ) + Complex.I * (((T V : ℝ × ℝ → ℝ) y : ℝ) : ℂ) := by
    filter_upwards [hIu, hIv, hTU, hTV] with y hyu hyv hyU hyV
    rw [hyU, hyV]
    unfold cxInter IIb.cylWeightedOpFun
    rw [kerVelCx_eq_re_im hyu hyv 0, kerVelCx_eq_re_im hyu hyv 1, hKU, hKV]
    push_cast
    ring
  have hmeasU : AEStronglyMeasurable (fun y => (((T U : ℝ × ℝ → ℝ) y : ℝ) : ℂ)) μ :=
    Complex.continuous_ofReal.comp_aestronglyMeasurable (Lp.aestronglyMeasurable (T U))
  have hmeasV : AEStronglyMeasurable
      (fun y => Complex.I * (((T V : ℝ × ℝ → ℝ) y : ℝ) : ℂ)) μ :=
    (Complex.continuous_ofReal.comp_aestronglyMeasurable (Lp.aestronglyMeasurable (T V))).const_mul _
  refine ⟨(hmeasU.add hmeasV).congr hEq.symm, ?_⟩
  -- the norm bound
  have hW_fin : xNorm d m W ≠ ⊤ := hW.2.ne
  have hnU : ENNReal.ofReal ‖U‖ ≤ xNorm d m W := by
    rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top U)]
    unfold xNorm
    rw [eLpNorm_congr_ae hUe]
    exact eLpNorm_mono fun z => by
      rw [Real.norm_eq_abs]; exact Complex.abs_re_le_norm (W z)
  have hnV : ENNReal.ofReal ‖V‖ ≤ xNorm d m W := by
    rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top V)]
    unfold xNorm
    rw [eLpNorm_congr_ae hVe]
    exact eLpNorm_mono fun z => by
      rw [Real.norm_eq_abs]; exact Complex.abs_im_le_norm (W z)
  have hCB : 0 ≤ IIb.cylKernelBoundConst m * B :=
    mul_nonneg (IIb.cylKernelBoundConst_pos m).le hB
  have hTn : ‖T‖ ≤ IIb.cylKernelBoundConst m * B := IIb.norm_cylWeightedOp_le hd hm hB hb
  have hTUn : ENNReal.ofReal ‖T U‖ ≤
      ENNReal.ofReal (IIb.cylKernelBoundConst m * B) * xNorm d m W := by
    calc ENNReal.ofReal ‖T U‖ ≤ ENNReal.ofReal (IIb.cylKernelBoundConst m * B * ‖U‖) :=
          ENNReal.ofReal_le_ofReal ((T.le_opNorm U).trans
            (mul_le_mul_of_nonneg_right hTn (norm_nonneg _)))
      _ = ENNReal.ofReal (IIb.cylKernelBoundConst m * B) * ENNReal.ofReal ‖U‖ :=
          ENNReal.ofReal_mul hCB
      _ ≤ _ := by gcongr
  have hTVn : ENNReal.ofReal ‖T V‖ ≤
      ENNReal.ofReal (IIb.cylKernelBoundConst m * B) * xNorm d m W := by
    calc ENNReal.ofReal ‖T V‖ ≤ ENNReal.ofReal (IIb.cylKernelBoundConst m * B * ‖V‖) :=
          ENNReal.ofReal_le_ofReal ((T.le_opNorm V).trans
            (mul_le_mul_of_nonneg_right hTn (norm_nonneg _)))
      _ = ENNReal.ofReal (IIb.cylKernelBoundConst m * B) * ENNReal.ofReal ‖V‖ :=
          ENNReal.ofReal_mul hCB
      _ ≤ _ := by gcongr
  have hEU : eLpNorm (fun y => (((T U : ℝ × ℝ → ℝ) y : ℝ) : ℂ)) 2 μ = ENNReal.ofReal ‖T U‖ := by
    rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _)]
    exact eLpNorm_congr_norm_ae (Eventually.of_forall fun y => by simp)
  have hEV : eLpNorm (fun y => Complex.I * (((T V : ℝ × ℝ → ℝ) y : ℝ) : ℂ)) 2 μ =
      ENNReal.ofReal ‖T V‖ := by
    rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _)]
    exact eLpNorm_congr_norm_ae (Eventually.of_forall fun y => by simp)
  unfold xNorm
  rw [eLpNorm_congr_ae hEq]
  calc eLpNorm (fun y => (((T U : ℝ × ℝ → ℝ) y : ℝ) : ℂ) +
        Complex.I * (((T V : ℝ × ℝ → ℝ) y : ℝ) : ℂ)) 2 μ
      ≤ eLpNorm (fun y => (((T U : ℝ × ℝ → ℝ) y : ℝ) : ℂ)) 2 μ +
          eLpNorm (fun y => Complex.I * (((T V : ℝ × ℝ → ℝ) y : ℝ) : ℂ)) 2 μ :=
        eLpNorm_add_le hmeasU hmeasV (by norm_num)
    _ = ENNReal.ofReal ‖T U‖ + ENNReal.ofReal ‖T V‖ := by rw [hEU, hEV]
    _ ≤ ENNReal.ofReal (IIb.cylKernelBoundConst m * B) * xNorm d m W +
          ENNReal.ofReal (IIb.cylKernelBoundConst m * B) * xNorm d m W := add_le_add hTUn hTVn
    _ = ENNReal.ofReal (2 * IIb.cylKernelBoundConst m * B) * xNorm d m W := by
        rw [← two_mul, ← mul_assoc]
        congr 1
        rw [mul_assoc, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
        norm_num

end UnforcedLeray.Short.IIIa.BlockPropagatorInteriorSub.OrgSplit.RelIntA
