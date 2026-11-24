import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_1_org3_b_L4.Leaves
import UnforcedLeray.Short.PartI.Tasks.EulerRegularityTransfer.CouplingIntertwine
import UnforcedLeray.Short.PartIIIa.Clock.FrameStableProof.ShortBlock.EulerError.Tail
import UnforcedLeray.Short.PartIIb.Tasks.InteractionCylinder.PlanarCompact
import UnforcedLeray.Short.PartIIb.Tasks.InteractionCylinder.PlanarKernel
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_1_org_1_a.Interaction

/-!
# Leaf B4, interaction part: `couplingW` through the real planar interaction (SP 2974-2976)

`couplingW W = -(K W)·∇E₀` a.e. (`PartI.aeZero_neg_couplingW`, `B0061.AEj_value_ae`). For a smooth
compactly supported `Φ` representing `W`, the planar Biot–Savart velocity of `Φ` splits into the
real planar velocities of `Re Φ` and `Im Φ`, so `couplingW W = A_pl(Re Φ) + i A_pl(Im Φ)` with the
real planar interaction `IIb.Apl 0` (`∇E_{1+0} = ∇E₀`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Metric UnforcedLeray.Blueprint.Planar

namespace UnforcedLeray.Short.IIIa

open FrameShortBlockSub FrameBlockContractSub CompactDuhamelGapSub

namespace BlockPropagatorInteriorSub

open OrgSplit
open scoped ComplexConjugate ContDiff InnerProductSpace InnerProduct ENNReal

namespace OrgSplit3

namespace PlanarB

namespace L4

theorem planarGradE_zero (x : ℝ × ℝ) :
    IIb.planarGradE 0 x = B0009.gradE0 (planeToC x) := by
  unfold IIb.planarGradE IIb.scalePlane
  have h1 : ((1 : ℝ) + 0) ^ (-5 / 2 : ℝ) = 1 := by norm_num
  rw [h1]
  simp only [add_zero, Real.sqrt_one, div_one, one_mul]
  rfl

/-- Scalar component of the real planar Biot–Savart velocity. -/
theorem planarK_apply {u : ℝ × ℝ → ℝ} {x : ℝ × ℝ}
    (hu : Integrable (fun y => u y • IIb.planarBSKernel (x - y))) (k : Fin 2) :
    IIb.planarK u x k = ∫ y, u y * IIb.planarBSKernel (x - y) k := by
  unfold IIb.planarK
  have h := (EuclideanSpace.proj k : UnforcedLeray.Cyl.Vec2 →L[ℝ] ℝ).integral_comp_comm hu
  change (EuclideanSpace.proj k : UnforcedLeray.Cyl.Vec2 →L[ℝ] ℝ)
    (∫ y, u y • IIb.planarBSKernel (x - y)) = _
  rw [← h]
  simp

/-- The complex planar Biot–Savart velocity of `Φ ∘ cToPlane` splits into the real planar
velocities of `Re Φ` and `Im Φ`. -/
theorem biotSavart_eq_re_im {Φ : ℝ × ℝ → ℂ} (z : ℂ)
    (hu : Integrable (fun y => (Φ y).re • IIb.planarBSKernel (cToPlane z - y)))
    (hv : Integrable (fun y => (Φ y).im • IIb.planarBSKernel (cToPlane z - y))) (k : Fin 2) :
    B0009.biotSavart (fun w => Φ (cToPlane w)) k z =
      ((IIb.planarK (fun y => (Φ y).re) (cToPlane z) k : ℝ) : ℂ) +
        Complex.I * ((IIb.planarK (fun y => (Φ y).im) (cToPlane z) k : ℝ) : ℂ) := by
  rw [B0009.biotSavart_apply,
    ← EulerErrorTail.integral_planeToC (fun w => B0009.kernel k (z - w) * Φ (cToPlane w))]
  simp only [cToPlane_planeToC]
  have hk : ∀ x : ℝ × ℝ, B0009.kernel k (z - planeToC x) =
      ((IIb.planarBSKernel (cToPlane z - x) k : ℝ) : ℂ) := by
    intro x
    rw [← EulerErrorTail.kernel_planeToC_eq, EulerErrorTail.planeToC_sub, planeToC_cToPlane]
  simp_rw [hk]
  rw [planarK_apply hu k, planarK_apply hv k]
  have hu' : Integrable (fun y => (Φ y).re * IIb.planarBSKernel (cToPlane z - y) k) := by
    have := (EuclideanSpace.proj k : UnforcedLeray.Cyl.Vec2 →L[ℝ] ℝ).integrable_comp hu
    exact this.congr (Eventually.of_forall fun y => by simp)
  have hv' : Integrable (fun y => (Φ y).im * IIb.planarBSKernel (cToPlane z - y) k) := by
    have := (EuclideanSpace.proj k : UnforcedLeray.Cyl.Vec2 →L[ℝ] ℝ).integrable_comp hv
    exact this.congr (Eventually.of_forall fun y => by simp)
  have hsplit : (fun y => ((IIb.planarBSKernel (cToPlane z - y) k : ℝ) : ℂ) * Φ y) = fun y =>
      (((Φ y).re * IIb.planarBSKernel (cToPlane z - y) k : ℝ) : ℂ) +
        Complex.I * (((Φ y).im * IIb.planarBSKernel (cToPlane z - y) k : ℝ) : ℂ) := by
    funext y
    conv_lhs => rw [← Complex.re_add_im (Φ y)]
    push_cast
    ring
  rw [hsplit]
  rw [integral_add ?_ ?_, integral_const_mul, integral_complex_ofReal, integral_complex_ofReal]
  · exact hu'.ofReal
  · exact hv'.ofReal.const_mul Complex.I

/-- Pointwise: `-(K(Φ∘cToPlane))·∇E₀ = A_pl(Re Φ) + i A_pl(Im Φ)`. -/
theorem neg_perturbation_eq {Φ : ℝ × ℝ → ℂ} (z : ℂ)
    (hu : Integrable (fun y => (Φ y).re • IIb.planarBSKernel (cToPlane z - y)))
    (hv : Integrable (fun y => (Φ y).im • IIb.planarBSKernel (cToPlane z - y))) :
    -B0009.perturbation (fun w => Φ (cToPlane w)) z =
      ((IIb.Apl 0 (fun y => (Φ y).re) (cToPlane z) : ℝ) : ℂ) +
        Complex.I * ((IIb.Apl 0 (fun y => (Φ y).im) (cToPlane z) : ℝ) : ℂ) := by
  unfold B0009.perturbation IIb.Apl
  rw [biotSavart_eq_re_im z hu hv 0, biotSavart_eq_re_im z hu hv 1, planarGradE_zero,
    planeToC_cToPlane]
  push_cast
  ring

/-! ## The `L²` representative of a smooth field on the plane -/

theorem memLp_plane_of_rep {m : ℝ} {Φ : ℝ × ℝ → ℂ} (W : Planar.L2w m)
    (hW : ⇑W =ᵐ[volume] fun z => Φ (cToPlane z)) :
    MemLp Φ 2 (IIb.planeMeasure m) ∧ eLpNorm Φ 2 (IIb.planeMeasure m) = ENNReal.ofReal ‖W‖ := by
  have hWw : ⇑W =ᵐ[Planar.wMeasure m] fun z => Φ (cToPlane z) := (Planar.wMeasure_ac m).ae_le hW
  have hmem : MemLp (fun z => Φ (cToPlane z)) 2 (Planar.wMeasure m) := (Lp.memLp W).ae_eq hWw
  have hmp := BlockPropagatorSub.measurePreserving_planeToC_wMeasure m
  have hcomp : ((fun z => Φ (cToPlane z)) ∘ planeToC) = Φ := by
    funext y; simp
  refine ⟨?_, ?_⟩
  · have h := hmem.comp_measurePreserving hmp
    rw [hcomp] at h
    exact h
  · have h := eLpNorm_comp_measurePreserving (p := 2) hmem.1 hmp
    rw [hcomp] at h
    change eLpNorm Φ 2 (volume.withDensity fun y => (B0579.density m y : ℝ≥0∞)) = _
    rw [h, Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top W), eLpNorm_congr_ae hWw]

/-- `couplingW W = A_pl(Re Φ) + i A_pl(Im Φ)` a.e., with the real planar interaction `IIb.Apl 0`. -/
theorem couplingW_ae_eq {m : ℝ} (hm : 1 < m) {Φ : ℝ × ℝ → ℂ} (W : Planar.L2w m)
    (hW : ⇑W =ᵐ[volume] fun z => Φ (cToPlane z))
    (U V : IIb.Xm m) (hU : ⇑U =ᵐ[IIb.planeMeasure m] fun x => (Φ x).re)
    (hV : ⇑V =ᵐ[IIb.planeMeasure m] fun x => (Φ x).im) :
    ⇑(Planar.couplingW hm W) =ᵐ[Planar.wMeasure m] fun z =>
      ((IIb.Apl 0 (fun x => (Φ x).re) (cToPlane z) : ℝ) : ℂ) +
        Complex.I * ((IIb.Apl 0 (fun x => (Φ x).im) (cToPlane z) : ℝ) : ℂ) := by
  -- `couplingW W = -(K W)·∇E₀`
  have h1 : ⇑(-(Planar.couplingW hm W)) =ᵐ[volume] B0009.perturbation (⇑W) := by
    have h := B0061.AEj_value_ae hm (PartI.TransportGroupHjMZero.ofL2 m W)
    rw [PartI.aeZero_neg_couplingW, PartI.TransportGroupHjMZero.value_ofL2] at h
    exact h
  have h1' : ⇑(Planar.couplingW hm W) =ᵐ[volume]
      fun z => -B0009.perturbation (fun w => Φ (cToPlane w)) z := by
    have hn := (Planar.volume_ac m).ae_le (Lp.coeFn_neg (Planar.couplingW hm W))
    rw [B0009.perturbation_congr_ae hW] at h1
    filter_upwards [hn, h1] with z a b
    rw [← b, a, Pi.neg_apply, neg_neg]
  -- integrability of the planar kernel integrands
  have hUv : ⇑U =ᵐ[volume] fun x => (Φ x).re := (IIb.volume_ac_planeMeasure m).ae_le hU
  have hVv : ⇑V =ᵐ[volume] fun x => (Φ x).im := (IIb.volume_ac_planeMeasure m).ae_le hV
  have hIu : ∀ᵐ x ∂(volume : Measure (ℝ × ℝ)),
      Integrable (fun y => (Φ y).re • IIb.planarBSKernel (x - y)) := by
    filter_upwards [IIb.ae_integrable_planarBSKernel hm U] with x hx
    refine hx.congr ?_
    filter_upwards [hUv] with y hy
    rw [hy]
  have hIv : ∀ᵐ x ∂(volume : Measure (ℝ × ℝ)),
      Integrable (fun y => (Φ y).im • IIb.planarBSKernel (x - y)) := by
    filter_upwards [IIb.ae_integrable_planarBSKernel hm V] with x hx
    refine hx.congr ?_
    filter_upwards [hVv] with y hy
    rw [hy]
  have hqmp := (BlockPropagatorSub.measurePreserving_cToPlane_volume).quasiMeasurePreserving
  have hIu' := hqmp.ae hIu
  have hIv' := hqmp.ae hIv
  filter_upwards [(Planar.wMeasure_ac m).ae_le h1', (Planar.wMeasure_ac m).ae_le hIu',
    (Planar.wMeasure_ac m).ae_le hIv'] with z e1 iu iv
  rw [e1]
  exact neg_perturbation_eq z iu iv

/-- On the cell, the complex Gaussian-coefficient interaction splits into the real cylinder
interactions `IIb.AcGauss d 0` of `Re Φ` and `Im Φ`. -/
theorem cxInter_g0_ae {m d : ℝ} (hd : 1 ≤ d) (hm : 1 < m) {Φ : ℝ × ℝ → ℂ}
    (hΦ : MemLp Φ 2 (IIb.planeMeasure m)) :
    ∀ᵐ x ∂IIb.planeMeasure m,
      (B0579.cell d).indicator (RelIntA.cxInter d (IIb.planarGradE 0) Φ) x =
        (((B0579.cell d).indicator (IIb.AcGauss d 0 fun y => (Φ y).re) x : ℝ) : ℂ) +
          Complex.I *
            (((B0579.cell d).indicator (IIb.AcGauss d 0 fun y => (Φ y).im) x : ℝ) : ℂ) := by
  have hΦc : MemLp Φ 2 (B0579.cellMeasure d m) := by
    rw [IIb.cellMeasure_eq_restrict_planeMeasure]; exact hΦ.restrict _
  have hu : MemLp (fun z => (Φ z).re) 2 (B0579.cellMeasure d m) := Complex.reCLM.comp_memLp' hΦc
  have hv : MemLp (fun z => (Φ z).im) 2 (B0579.cellMeasure d m) := Complex.imCLM.comp_memLp' hΦc
  set Uc : IIb.Xmc d m := hu.toLp _ with hUc
  set Vc : IIb.Xmc d m := hv.toLp _ with hVc
  have hUe : (Uc : ℝ × ℝ → ℝ) =ᵐ[volume.restrict (B0579.cell d)] fun z => (Φ z).re :=
    (B0579.ac_cellMeasure d m).ae_le (MemLp.coeFn_toLp hu)
  have hVe : (Vc : ℝ × ℝ → ℝ) =ᵐ[volume.restrict (B0579.cell d)] fun z => (Φ z).im :=
    (B0579.ac_cellMeasure d m).ae_le (MemLp.coeFn_toLp hv)
  have hIu : ∀ᵐ y ∂(volume.restrict (B0579.cell d)),
      Integrable (fun z => (Φ z).re • UnforcedLeray.Cyl.bsKernel d (y - z))
        (volume.restrict (B0579.cell d)) := by
    filter_upwards [IIb.ae_integrable_bsKernel hd hm Uc] with y hy
    refine hy.congr ?_
    filter_upwards [hUe] with z hz
    rw [hz]
  have hIv : ∀ᵐ y ∂(volume.restrict (B0579.cell d)),
      Integrable (fun z => (Φ z).im • UnforcedLeray.Cyl.bsKernel d (y - z))
        (volume.restrict (B0579.cell d)) := by
    filter_upwards [IIb.ae_integrable_bsKernel hd hm Vc] with y hy
    refine hy.congr ?_
    filter_upwards [hVe] with z hz
    rw [hz]
  have hcell : ∀ᵐ y ∂(volume.restrict (B0579.cell d)),
      RelIntA.cxInter d (IIb.planarGradE 0) Φ y =
        ((IIb.AcGauss d 0 (fun y => (Φ y).re) y : ℝ) : ℂ) +
          Complex.I * ((IIb.AcGauss d 0 (fun y => (Φ y).im) y : ℝ) : ℂ) := by
    filter_upwards [hIu, hIv] with y hyu hyv
    unfold RelIntA.cxInter IIb.AcGauss
    rw [RelIntA.kerVelCx_eq_re_im hyu hyv 0, RelIntA.kerVelCx_eq_re_im hyu hyv 1]
    push_cast
    ring
  have h2 := (ae_restrict_iff' (B0579.measurableSet_cell d)).mp hcell
  have h3 := (IIb.planeMeasure_ac m).ae_le h2
  filter_upwards [h3] with x hx
  by_cases hxc : x ∈ B0579.cell d
  · rw [Set.indicator_of_mem hxc, Set.indicator_of_mem hxc, Set.indicator_of_mem hxc]
    exact hx hxc
  · rw [Set.indicator_of_notMem hxc, Set.indicator_of_notMem hxc, Set.indicator_of_notMem hxc]
    simp

/-- **Cylinder-to-plane bound** for the Gaussian coefficient: the cell zero extension of
`-(K_d Φ)·∇E₀` is `2C‖W‖`-close to `couplingW W`, when `‖J_d A_d^G R_d - A_pl‖ ≤ C`. -/
theorem coupling_cyl_bound {m d : ℝ} (hm : 1 < m) (hd : 1 ≤ d) {B C : ℝ} (hB : 0 ≤ B)
    (hb : IIb.IsCylWeightedCoeff d m B (IIb.planarGradE 0))
    (A : IIb.Xm m →L[ℝ] IIb.Xm m) (hA : IIb.IsPlanarInteractionOp m 0 A)
    (hC : ‖(IIb.Jc d m).comp ((IIb.cylWeightedOp hd hm hB hb).comp (IIb.Rc d m)) - A‖ ≤ C)
    {Φ : ℝ × ℝ → ℂ} (W : Planar.L2w m) (hW : ⇑W =ᵐ[volume] fun z => Φ (cToPlane z)) :
    AEStronglyMeasurable (fun z => cellZeroExt d (RelIntA.cxInter d (IIb.planarGradE 0) Φ)
        (cToPlane z) - Planar.couplingW hm W z) (Planar.wMeasure m) ∧
    eLpNorm (fun z => cellZeroExt d (RelIntA.cxInter d (IIb.planarGradE 0) Φ) (cToPlane z) -
        Planar.couplingW hm W z) 2 (Planar.wMeasure m) ≤ ENNReal.ofReal (2 * C * ‖W‖) := by
  obtain ⟨hΦm, hΦn⟩ := memLp_plane_of_rep W hW
  have hu : MemLp (fun x => (Φ x).re) 2 (IIb.planeMeasure m) := Complex.reCLM.comp_memLp' hΦm
  have hv : MemLp (fun x => (Φ x).im) 2 (IIb.planeMeasure m) := Complex.imCLM.comp_memLp' hΦm
  set U : IIb.Xm m := hu.toLp _ with hUdef
  set V : IIb.Xm m := hv.toLp _ with hVdef
  have hU : ⇑U =ᵐ[IIb.planeMeasure m] fun x => (Φ x).re := MemLp.coeFn_toLp hu
  have hV : ⇑V =ᵐ[IIb.planeMeasure m] fun x => (Φ x).im := MemLp.coeFn_toLp hv
  set T := IIb.cylWeightedOp hd hm hB hb with hTdef
  have hT : IIb.IsGaussCylInteractionOp d m 0 T := IIb.isCylWeightedOp_cylWeightedOp hd hm hB hb
  set D := (IIb.Jc d m).comp (T.comp (IIb.Rc d m)) - A with hDdef
  have hDU := IIb.coeFn_Jc_AcG_Rc_sub_Apl_ae hT hA U hU
  have hDV := IIb.coeFn_Jc_AcG_Rc_sub_Apl_ae hT hA V hV
  have hcpl := couplingW_ae_eq hm W hW U V hU hV
  have hcyl := cxInter_g0_ae (d := d) hd hm hΦm
  have hmp := BlockPropagatorSub.measurePreserving_cToPlane_wMeasure m
  have hqw := hmp.quasiMeasurePreserving
  have hDU' : ∀ᵐ z ∂Planar.wMeasure m, (D U : ℝ × ℝ → ℝ) (cToPlane z) =
      (B0579.cell d).indicator (IIb.AcGauss d 0 fun y => (Φ y).re) (cToPlane z) -
        IIb.Apl 0 (fun y => (Φ y).re) (cToPlane z) :=
    hqw.ae (p := fun x => (D U : ℝ × ℝ → ℝ) x =
      (B0579.cell d).indicator (IIb.AcGauss d 0 fun y => (Φ y).re) x -
        IIb.Apl 0 (fun y => (Φ y).re) x) hDU
  have hDV' : ∀ᵐ z ∂Planar.wMeasure m, (D V : ℝ × ℝ → ℝ) (cToPlane z) =
      (B0579.cell d).indicator (IIb.AcGauss d 0 fun y => (Φ y).im) (cToPlane z) -
        IIb.Apl 0 (fun y => (Φ y).im) (cToPlane z) :=
    hqw.ae (p := fun x => (D V : ℝ × ℝ → ℝ) x =
      (B0579.cell d).indicator (IIb.AcGauss d 0 fun y => (Φ y).im) x -
        IIb.Apl 0 (fun y => (Φ y).im) x) hDV
  have hcyl' : ∀ᵐ z ∂Planar.wMeasure m,
      (B0579.cell d).indicator (RelIntA.cxInter d (IIb.planarGradE 0) Φ) (cToPlane z) =
        (((B0579.cell d).indicator (IIb.AcGauss d 0 fun y => (Φ y).re) (cToPlane z) : ℝ) : ℂ) +
          Complex.I * (((B0579.cell d).indicator (IIb.AcGauss d 0 fun y => (Φ y).im)
            (cToPlane z) : ℝ) : ℂ) :=
    hqw.ae (p := fun x => (B0579.cell d).indicator (RelIntA.cxInter d (IIb.planarGradE 0) Φ) x =
        (((B0579.cell d).indicator (IIb.AcGauss d 0 fun y => (Φ y).re) x : ℝ) : ℂ) +
          Complex.I * (((B0579.cell d).indicator (IIb.AcGauss d 0 fun y => (Φ y).im) x : ℝ) : ℂ))
      hcyl
  set G : ℂ → ℂ := fun z => (((D U : ℝ × ℝ → ℝ) (cToPlane z) : ℝ) : ℂ) +
    Complex.I * (((D V : ℝ × ℝ → ℝ) (cToPlane z) : ℝ) : ℂ) with hGdef
  have hEq : (fun z => cellZeroExt d (RelIntA.cxInter d (IIb.planarGradE 0) Φ) (cToPlane z) -
      Planar.couplingW hm W z) =ᵐ[Planar.wMeasure m] G := by
    filter_upwards [hcpl, hDU', hDV', hcyl'] with z e1 e2 e3 e4
    simp only [hGdef]
    unfold cellZeroExt
    rw [e1, e2, e3, e4]
    push_cast
    ring
  have hmU : AEStronglyMeasurable (fun z => (D U : ℝ × ℝ → ℝ) (cToPlane z)) (Planar.wMeasure m) :=
    (Lp.aestronglyMeasurable (D U)).comp_measurePreserving hmp
  have hmV : AEStronglyMeasurable (fun z => (D V : ℝ × ℝ → ℝ) (cToPlane z)) (Planar.wMeasure m) :=
    (Lp.aestronglyMeasurable (D V)).comp_measurePreserving hmp
  have hmU' : AEStronglyMeasurable (fun z => (((D U : ℝ × ℝ → ℝ) (cToPlane z) : ℝ) : ℂ))
      (Planar.wMeasure m) := Complex.continuous_ofReal.comp_aestronglyMeasurable hmU
  have hmV' : AEStronglyMeasurable (fun z => Complex.I * (((D V : ℝ × ℝ → ℝ) (cToPlane z) : ℝ) : ℂ))
      (Planar.wMeasure m) := (Complex.continuous_ofReal.comp_aestronglyMeasurable hmV).const_mul _
  have hmG : AEStronglyMeasurable G (Planar.wMeasure m) := hmU'.add hmV'
  refine ⟨hmG.congr hEq.symm, ?_⟩
  rw [eLpNorm_congr_ae hEq]
  have hC0 : 0 ≤ C := (norm_nonneg _).trans hC
  -- the norms of the real parts
  have hnU : ENNReal.ofReal ‖U‖ ≤ ENNReal.ofReal ‖W‖ := by
    rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top U), eLpNorm_congr_ae hU, ← hΦn]
    exact eLpNorm_mono fun z => by
      rw [Real.norm_eq_abs]; exact Complex.abs_re_le_norm (Φ z)
  have hnV : ENNReal.ofReal ‖V‖ ≤ ENNReal.ofReal ‖W‖ := by
    rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top V), eLpNorm_congr_ae hV, ← hΦn]
    exact eLpNorm_mono fun z => by
      rw [Real.norm_eq_abs]; exact Complex.abs_im_le_norm (Φ z)
  have hnU' : ‖U‖ ≤ ‖W‖ := (ENNReal.ofReal_le_ofReal_iff (norm_nonneg _)).1 hnU
  have hnV' : ‖V‖ ≤ ‖W‖ := (ENNReal.ofReal_le_ofReal_iff (norm_nonneg _)).1 hnV
  have hDUn : ‖D U‖ ≤ C * ‖W‖ :=
    (D.le_opNorm U).trans (mul_le_mul hC hnU' (norm_nonneg _) hC0)
  have hDVn : ‖D V‖ ≤ C * ‖W‖ :=
    (D.le_opNorm V).trans (mul_le_mul hC hnV' (norm_nonneg _) hC0)
  have e1 : eLpNorm (fun z => (((D U : ℝ × ℝ → ℝ) (cToPlane z) : ℝ) : ℂ)) 2 (Planar.wMeasure m) =
      ENNReal.ofReal ‖D U‖ := by
    rw [eLpNorm_congr_norm_ae (g := fun z => (D U : ℝ × ℝ → ℝ) (cToPlane z))
      (Eventually.of_forall fun z => by simp [Real.norm_eq_abs])]
    rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _)]
    exact eLpNorm_comp_measurePreserving (Lp.aestronglyMeasurable (D U)) hmp
  have e2 : eLpNorm (fun z => Complex.I * (((D V : ℝ × ℝ → ℝ) (cToPlane z) : ℝ) : ℂ)) 2
      (Planar.wMeasure m) = ENNReal.ofReal ‖D V‖ := by
    rw [eLpNorm_congr_norm_ae (g := fun z => (D V : ℝ × ℝ → ℝ) (cToPlane z))
      (Eventually.of_forall fun z => by simp [Real.norm_eq_abs])]
    rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _)]
    exact eLpNorm_comp_measurePreserving (Lp.aestronglyMeasurable (D V)) hmp
  calc eLpNorm G 2 (Planar.wMeasure m)
      ≤ eLpNorm (fun z => (((D U : ℝ × ℝ → ℝ) (cToPlane z) : ℝ) : ℂ)) 2 (Planar.wMeasure m) +
          eLpNorm (fun z => Complex.I * (((D V : ℝ × ℝ → ℝ) (cToPlane z) : ℝ) : ℂ)) 2
            (Planar.wMeasure m) := eLpNorm_add_le hmU' hmV' (by norm_num)
    _ = ENNReal.ofReal ‖D U‖ + ENNReal.ofReal ‖D V‖ := by rw [e1, e2]
    _ ≤ ENNReal.ofReal (C * ‖W‖) + ENNReal.ofReal (C * ‖W‖) :=
        add_le_add (ENNReal.ofReal_le_ofReal hDUn) (ENNReal.ofReal_le_ofReal hDVn)
    _ = ENNReal.ofReal (2 * C * ‖W‖) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1; ring

end L4

end PlanarB

end OrgSplit3
end BlockPropagatorInteriorSub
end UnforcedLeray.Short.IIIa
