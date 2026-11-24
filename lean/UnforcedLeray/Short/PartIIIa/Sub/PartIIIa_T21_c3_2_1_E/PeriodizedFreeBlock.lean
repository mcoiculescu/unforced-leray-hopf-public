import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_1_org3_a_N
import UnforcedLeray.Short.PartIIIa.Clock.FrameStableProof.BlockContraction.CompactDuhamelGap.VariationOfConstants.RelLeafB1c
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F2_2

/-!
# `PeriodizedRelFreeBlockInterior` (`SP` lines 2937-2962)

Source of record: `the November 2 reference manuscript` (SP), lines 2937-2962.

Constructs the periodized relative free block evolution `F_rel` on `Planar.L2w m` (`m > 8`) from:
* the weak free cylinder flow `IIb.free_cyl_exists_approx`, uniqueness `IIb.free_cyl_exists_unique`,
  and linearity `IIb.IsFreeCylFlow.add` / `IIb.IsFreeCylFlow.smul`;
* the cell lift `RelB4locAux.liftC`, planar dilations `Planar.dilW`, and exterior dilation `extDilW`;
* the sub-block energy bound `FrameBlockContractSub.relFreeMovingEnergy` together with
  `RelFreeNormSub.opNorm_le_of_cell_ext` / `RelFreeNormSub.norm_apply_le_of_tests`, and the
  full-block interior cell bound from the block hypothesis.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

open FrameShortBlockSub FrameBlockContractSub CompactDuhamelGapSub BlockPropagatorSub
  BlockPropagatorInteriorSub OrgSplit OrgSplit3 RelExteriorSub RelBlockDiagonalSub
  VariationOfConstantsSub RelFreeNormSub

namespace PeriodizedFreeBlockAux

/-! ## 1. Congruence and linearity of `RelB4locAux.liftC` -/

theorem liftC_congr_ae {c m : ℝ} {g₁ g₂ : B0579.Plane → ℝ}
    (h₁ : MemLp g₁ 2 (B0579.cellMeasure c m)) (h₂ : MemLp g₂ 2 (B0579.cellMeasure c m))
    (hae : g₁ =ᵐ[B0579.cellMeasure c m] g₂) :
    RelB4locAux.liftC c m g₁ = RelB4locAux.liftC c m g₂ := by
  have h0 : eLpNorm (g₁ - g₂) 2 (B0579.cellMeasure c m) = 0 := by
    have hsub : g₁ - g₂ =ᵐ[B0579.cellMeasure c m] (0 : B0579.Plane → ℝ) := by
      filter_upwards [hae] with x hx
      simp [hx]
    rw [eLpNorm_congr_ae hsub, eLpNorm_zero]
  apply sub_eq_zero.1
  rw [← norm_eq_zero, RelB4locAux.norm_liftC_sub h₁ h₂, h0, ENNReal.toReal_zero]

theorem liftFun_add (c : ℝ) (g₁ g₂ : ℝ × ℝ → ℝ) :
    RelB4locAux.liftFun c (g₁ + g₂) = RelB4locAux.liftFun c g₁ + RelB4locAux.liftFun c g₂ := by
  funext z
  simp only [RelB4locAux.liftFun, cellZeroExt, Pi.add_apply]
  by_cases h : cToPlane z ∈ B0579.cell c
  · simp [indicator_of_mem h]
  · simp [indicator_of_notMem h]

theorem liftFun_smul (c : ℝ) (a : ℝ) (g : ℝ × ℝ → ℝ) :
    RelB4locAux.liftFun c (a • g) = (a : ℂ) • RelB4locAux.liftFun c g := by
  funext z
  simp only [RelB4locAux.liftFun, cellZeroExt, Pi.smul_apply, smul_eq_mul]
  by_cases h : cToPlane z ∈ B0579.cell c
  · simp [indicator_of_mem h]
  · simp [indicator_of_notMem h]

/-- `RelB4locAux.liftC` as a continuous `ℝ`-linear map `B0579.X c m →L[ℝ] Planar.L2w m`. -/
def liftCCLM (c m : ℝ) : B0579.X c m →L[ℝ] Planar.L2w m :=
  LinearMap.mkContinuous
    { toFun := fun g => RelB4locAux.liftC c m g
      map_add' := fun g₁ g₂ => by
        have hsum : RelB4locAux.liftC c m ((g₁ + g₂ : B0579.X c m) : B0579.Plane → ℝ) =
            RelB4locAux.liftC c m ((g₁ : B0579.Plane → ℝ) + (g₂ : B0579.Plane → ℝ)) :=
          liftC_congr_ae (Lp.memLp (g₁ + g₂)) ((Lp.memLp g₁).add (Lp.memLp g₂))
            (Lp.coeFn_add g₁ g₂)
        rw [hsum]
        apply Lp.ext
        filter_upwards [RelB4locAux.coeFn_liftC ((Lp.memLp g₁).add (Lp.memLp g₂)),
          Lp.coeFn_add (RelB4locAux.liftC c m g₁) (RelB4locAux.liftC c m g₂),
          RelB4locAux.coeFn_liftC (Lp.memLp g₁), RelB4locAux.coeFn_liftC (Lp.memLp g₂)]
          with z h12 hadd h1 h2
        rw [h12, liftFun_add, hadd, Pi.add_apply, Pi.add_apply, h1, h2]
      map_smul' := fun a g => by
        simp only [RingHom.id_apply]
        have hsm : RelB4locAux.liftC c m ((a • g : B0579.X c m) : B0579.Plane → ℝ) =
            RelB4locAux.liftC c m (a • (g : B0579.Plane → ℝ)) :=
          liftC_congr_ae (Lp.memLp (a • g)) ((Lp.memLp g).const_smul a) (Lp.coeFn_smul a g)
        rw [hsm]
        have hcsm : (a : ℝ) • RelB4locAux.liftC c m g = (a : ℂ) • RelB4locAux.liftC c m g := rfl
        rw [hcsm]
        apply Lp.ext
        filter_upwards [RelB4locAux.coeFn_liftC ((Lp.memLp g).const_smul a),
          Lp.coeFn_smul (a : ℂ) (RelB4locAux.liftC c m g),
          RelB4locAux.coeFn_liftC (Lp.memLp g)] with z ha hsmul h1
        rw [ha, liftFun_smul, hsmul, Pi.smul_apply, Pi.smul_apply, h1] } 1
    (fun g => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk, one_mul]
      rw [RelRegularityOrg2.RelB1cAux.b1c_norm_liftC_eq (Lp.memLp g), Lp.norm_def])

/-! ## 2. Real/imaginary cell restriction maps `Planar.L2w m →L[ℝ] B0579.X c m` -/

theorem memLp_planeToC_cell (c m : ℝ) (U : Planar.L2w m) :
    MemLp (fun y : B0579.Plane => (U : ℂ → ℂ) (planeToC y)) 2 (B0579.cellMeasure c m) := by
  have h1 : MemLp (fun y : B0579.Plane => (U : ℂ → ℂ) (planeToC y)) 2
      (volume.withDensity fun y => (B0579.density m y : ℝ≥0∞)) :=
    (Lp.memLp U).comp_measurePreserving (measurePreserving_planeToC_wMeasure m)
  unfold B0579.cellMeasure
  rw [← restrict_withDensity (B0579.measurableSet_cell c)]
  exact h1.restrict (B0579.cell c)

theorem memLp_re_planeToC_cell (c m : ℝ) (U : Planar.L2w m) :
    MemLp (fun y : B0579.Plane => ((U : ℂ → ℂ) (planeToC y)).re) 2 (B0579.cellMeasure c m) :=
  Complex.reCLM.comp_memLp' (memLp_planeToC_cell c m U)

theorem memLp_im_planeToC_cell (c m : ℝ) (U : Planar.L2w m) :
    MemLp (fun y : B0579.Plane => ((U : ℂ → ℂ) (planeToC y)).im) 2 (B0579.cellMeasure c m) :=
  Complex.imCLM.comp_memLp' (memLp_planeToC_cell c m U)

theorem ae_planeToC_cell_of_wMeasure {c m : ℝ} {P : ℂ → Prop}
    (hP : ∀ᵐ z ∂(Planar.wMeasure m), P z) :
    ∀ᵐ y ∂(B0579.cellMeasure c m), P (planeToC y) := by
  have h1 : ∀ᵐ y ∂(volume.withDensity fun y => (B0579.density m y : ℝ≥0∞)), P (planeToC y) :=
    (measurePreserving_planeToC_wMeasure m).quasiMeasurePreserving.ae hP
  unfold B0579.cellMeasure
  rw [← restrict_withDensity (B0579.measurableSet_cell c)]
  exact ae_restrict_of_ae h1

def projReCLM (c m : ℝ) : Planar.L2w m →L[ℝ] B0579.X c m :=
  LinearMap.mkContinuous
    { toFun := fun U => (memLp_re_planeToC_cell c m U).toLp _
      map_add' := fun U V => by
        apply Lp.ext
        filter_upwards [(memLp_re_planeToC_cell c m (U + V)).coeFn_toLp,
          Lp.coeFn_add ((memLp_re_planeToC_cell c m U).toLp _)
            ((memLp_re_planeToC_cell c m V).toLp _),
          (memLp_re_planeToC_cell c m U).coeFn_toLp,
          (memLp_re_planeToC_cell c m V).coeFn_toLp,
          ae_planeToC_cell_of_wMeasure (c := c) (Lp.coeFn_add U V)]
          with y huv hadd hu hv hUV
        rw [huv, hadd, Pi.add_apply, hu, hv, hUV, Pi.add_apply, Complex.add_re]
      map_smul' := fun a U => by
        simp only [RingHom.id_apply]
        apply Lp.ext
        filter_upwards [(memLp_re_planeToC_cell c m (a • U)).coeFn_toLp,
          Lp.coeFn_smul a ((memLp_re_planeToC_cell c m U).toLp _),
          (memLp_re_planeToC_cell c m U).coeFn_toLp,
          ae_planeToC_cell_of_wMeasure (c := c) (Lp.coeFn_smul a U)]
          with y haU hsm hu hsmR
        rw [haU, hsm, Pi.smul_apply, hu, hsmR, Pi.smul_apply, Complex.smul_re, smul_eq_mul] } 1
    (fun U => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk, one_mul]
      rw [Lp.norm_def, eLpNorm_congr_ae (memLp_re_planeToC_cell c m U).coeFn_toLp]
      have hle1 : eLpNorm (fun y : B0579.Plane => ((U : ℂ → ℂ) (planeToC y)).re) 2
          (B0579.cellMeasure c m) ≤ xNorm c m (fun y => (U : ℂ → ℂ) (planeToC y)) := by
        unfold xNorm
        exact eLpNorm_mono_ae (Eventually.of_forall fun y => by
          rw [Real.norm_eq_abs]
          exact Complex.abs_re_le_norm _)
      have hle2 := hle1.trans (xNorm_planeToC_le_norm c m U)
      exact ENNReal.toReal_le_of_le_ofReal (norm_nonneg U) hle2)

def projImCLM (c m : ℝ) : Planar.L2w m →L[ℝ] B0579.X c m :=
  LinearMap.mkContinuous
    { toFun := fun U => (memLp_im_planeToC_cell c m U).toLp _
      map_add' := fun U V => by
        apply Lp.ext
        filter_upwards [(memLp_im_planeToC_cell c m (U + V)).coeFn_toLp,
          Lp.coeFn_add ((memLp_im_planeToC_cell c m U).toLp _)
            ((memLp_im_planeToC_cell c m V).toLp _),
          (memLp_im_planeToC_cell c m U).coeFn_toLp,
          (memLp_im_planeToC_cell c m V).coeFn_toLp,
          ae_planeToC_cell_of_wMeasure (c := c) (Lp.coeFn_add U V)]
          with y huv hadd hu hv hUV
        rw [huv, hadd, Pi.add_apply, hu, hv, hUV, Pi.add_apply, Complex.add_im]
      map_smul' := fun a U => by
        simp only [RingHom.id_apply]
        apply Lp.ext
        filter_upwards [(memLp_im_planeToC_cell c m (a • U)).coeFn_toLp,
          Lp.coeFn_smul a ((memLp_im_planeToC_cell c m U).toLp _),
          (memLp_im_planeToC_cell c m U).coeFn_toLp,
          ae_planeToC_cell_of_wMeasure (c := c) (Lp.coeFn_smul a U)]
          with y haU hsm hu hsmR
        rw [haU, hsm, Pi.smul_apply, hu, hsmR, Pi.smul_apply, Complex.smul_im, smul_eq_mul] } 1
    (fun U => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk, one_mul]
      rw [Lp.norm_def, eLpNorm_congr_ae (memLp_im_planeToC_cell c m U).coeFn_toLp]
      have hle1 : eLpNorm (fun y : B0579.Plane => ((U : ℂ → ℂ) (planeToC y)).im) 2
          (B0579.cellMeasure c m) ≤ xNorm c m (fun y => (U : ℂ → ℂ) (planeToC y)) := by
        unfold xNorm
        exact eLpNorm_mono_ae (Eventually.of_forall fun y => by
          rw [Real.norm_eq_abs]
          exact Complex.abs_im_le_norm _)
      have hle2 := hle1.trans (xNorm_planeToC_le_norm c m U)
      exact ENNReal.toReal_le_of_le_ofReal (norm_nonneg U) hle2)

theorem projReCLM_I_smul (c m : ℝ) (U : Planar.L2w m) :
    projReCLM c m (Complex.I • U) = -projImCLM c m U := by
  apply Lp.ext
  filter_upwards [(memLp_re_planeToC_cell c m (Complex.I • U)).coeFn_toLp,
    Lp.coeFn_neg ((memLp_im_planeToC_cell c m U).toLp _),
    (memLp_im_planeToC_cell c m U).coeFn_toLp,
    ae_planeToC_cell_of_wMeasure (c := c) (Lp.coeFn_smul Complex.I U)]
    with y hre hneg him hsm
  rw [show projReCLM c m (Complex.I • U) = (memLp_re_planeToC_cell c m (Complex.I • U)).toLp _
    from rfl, show projImCLM c m U = (memLp_im_planeToC_cell c m U).toLp _ from rfl,
    hre, hneg, Pi.neg_apply, him, hsm, Pi.smul_apply, smul_eq_mul]
  simp

theorem projImCLM_I_smul (c m : ℝ) (U : Planar.L2w m) :
    projImCLM c m (Complex.I • U) = projReCLM c m U := by
  apply Lp.ext
  filter_upwards [(memLp_im_planeToC_cell c m (Complex.I • U)).coeFn_toLp,
    (memLp_re_planeToC_cell c m U).coeFn_toLp,
    ae_planeToC_cell_of_wMeasure (c := c) (Lp.coeFn_smul Complex.I U)]
    with y him hre hsm
  rw [show projImCLM c m (Complex.I • U) = (memLp_im_planeToC_cell c m (Complex.I • U)).toLp _
    from rfl, show projReCLM c m U = (memLp_re_planeToC_cell c m U).toLp _ from rfl,
    him, hre, hsm, Pi.smul_apply, smul_eq_mul]
  simp

private lemma complex_smul_re_im {E : Type*} [AddCommGroup E] [Module ℂ E] (z : ℂ) (A B : E) :
    (z.re : ℂ) • A - (z.im : ℂ) • B + Complex.I • ((z.re : ℂ) • B + (z.im : ℂ) • A) =
      z • (A + Complex.I • B) := by
  have hz : z = (z.re : ℂ) + (z.im : ℂ) * Complex.I := (Complex.re_add_im z).symm
  calc (z.re : ℂ) • A - (z.im : ℂ) • B + Complex.I • ((z.re : ℂ) • B + (z.im : ℂ) • A)
      = ((z.re : ℂ) + Complex.I * (z.im : ℂ)) • A +
          (-(z.im : ℂ) + Complex.I * (z.re : ℂ)) • B := by
        rw [smul_add, smul_smul, smul_smul, add_smul, add_smul, neg_smul, sub_eq_add_neg]
        abel
    _ = z • A + (z * Complex.I) • B := by
        congr 2
        · conv_rhs => rw [hz]
          ring
        · conv_rhs => rw [hz]
          rw [add_mul, mul_assoc, Complex.I_mul_I, mul_neg_one]
          ring
    _ = z • (A + Complex.I • B) := by
        rw [smul_add, smul_smul]

/-- Complexification of an `ℝ`-linear cell operator `T : B0579.X c m →L[ℝ] B0579.X c m` as a
`ℂ`-linear operator on `Planar.L2w m`. -/
def liftComplexCLM {c m : ℝ} (T : B0579.X c m →L[ℝ] B0579.X c m) :
    Planar.L2w m →L[ℂ] Planar.L2w m :=
  LinearMap.mkContinuous
    { toFun := fun U =>
        liftCCLM c m (T (projReCLM c m U)) + Complex.I • liftCCLM c m (T (projImCLM c m U))
      map_add' := fun U V => by
        simp only [map_add, smul_add]
        abel
      map_smul' := fun z U => by
        simp only [RingHom.id_apply]
        have hzU : z • U = z.re • U + z.im • (Complex.I • U) := by
          have hz : ((z.re : ℂ) + (z.im : ℂ) * Complex.I) = z := Complex.re_add_im z
          calc z • U = ((z.re : ℂ) + (z.im : ℂ) * Complex.I) • U := by rw [hz]
            _ = (z.re : ℂ) • U + ((z.im : ℂ) * Complex.I) • U := add_smul _ _ U
            _ = z.re • U + z.im • (Complex.I • U) := by rw [mul_smul]; rfl
        have hre : projReCLM c m (z • U) = z.re • projReCLM c m U - z.im • projImCLM c m U := by
          rw [hzU, map_add, map_smul, map_smul, projReCLM_I_smul, smul_neg, sub_eq_add_neg]
        have him : projImCLM c m (z • U) = z.re • projImCLM c m U + z.im • projReCLM c m U := by
          rw [hzU, map_add, map_smul, map_smul, projImCLM_I_smul]
        rw [hre, him, map_sub, map_add, map_smul, map_smul, map_smul, map_smul,
          map_sub, map_add, map_smul, map_smul, map_smul, map_smul]
        have hreal : ∀ (r : ℝ) (X : Planar.L2w m), r • X = (r : ℂ) • X := fun _ _ => rfl
        simp only [hreal]
        exact complex_smul_re_im z
          (liftCCLM c m (T (projReCLM c m U)))
          (liftCCLM c m (T (projImCLM c m U))) } (2 * ‖T‖)
    (fun U => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk]
      have hL : ‖liftCCLM c m‖ ≤ 1 := LinearMap.mkContinuous_norm_le _ zero_le_one _
      have hR : ‖projReCLM c m‖ ≤ 1 := LinearMap.mkContinuous_norm_le _ zero_le_one _
      have hI : ‖projImCLM c m‖ ≤ 1 := LinearMap.mkContinuous_norm_le _ zero_le_one _
      have hb1 : ‖liftCCLM c m (T (projReCLM c m U))‖ ≤ ‖T‖ * ‖U‖ := by
        calc ‖liftCCLM c m (T (projReCLM c m U))‖
            ≤ 1 * ‖T (projReCLM c m U)‖ :=
              ((liftCCLM c m).le_opNorm _).trans
                (mul_le_mul_of_nonneg_right hL (norm_nonneg _))
          _ ≤ 1 * (‖T‖ * ‖projReCLM c m U‖) :=
              mul_le_mul_of_nonneg_left (T.le_opNorm _) zero_le_one
          _ ≤ 1 * (‖T‖ * (1 * ‖U‖)) :=
              mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left
                  (((projReCLM c m).le_opNorm _).trans
                    (mul_le_mul_of_nonneg_right hR (norm_nonneg _)))
                  (norm_nonneg T)) zero_le_one
          _ = ‖T‖ * ‖U‖ := by ring
      have hb2 : ‖Complex.I • liftCCLM c m (T (projImCLM c m U))‖ ≤ ‖T‖ * ‖U‖ := by
        rw [norm_smul, Complex.norm_I, one_mul]
        calc ‖liftCCLM c m (T (projImCLM c m U))‖
            ≤ 1 * ‖T (projImCLM c m U)‖ :=
              ((liftCCLM c m).le_opNorm _).trans
                (mul_le_mul_of_nonneg_right hL (norm_nonneg _))
          _ ≤ 1 * (‖T‖ * ‖projImCLM c m U‖) :=
              mul_le_mul_of_nonneg_left (T.le_opNorm _) zero_le_one
          _ ≤ 1 * (‖T‖ * (1 * ‖U‖)) :=
              mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left
                  (((projImCLM c m).le_opNorm _).trans
                    (mul_le_mul_of_nonneg_right hI (norm_nonneg _)))
                  (norm_nonneg T)) zero_le_one
          _ = ‖T‖ * ‖U‖ := by ring
      calc ‖liftCCLM c m (T (projReCLM c m U)) +
              Complex.I • liftCCLM c m (T (projImCLM c m U))‖
          ≤ ‖liftCCLM c m (T (projReCLM c m U))‖ +
              ‖Complex.I • liftCCLM c m (T (projImCLM c m U))‖ := norm_add_le _ _
        _ ≤ ‖T‖ * ‖U‖ + ‖T‖ * ‖U‖ := add_le_add hb1 hb2
        _ = 2 * ‖T‖ * ‖U‖ := by ring)

/-! ## 3. Free cylinder propagator step `freeCylStepCLM` on `B0579.X c m` -/

section FreeStep

variable {m ν c : ℝ} (hm : 8 < m) (hν : 0 < ν) (hc : 0 < c)
  (tr : UnforcedLeray.B0140.TrainSol ν c) (hbu : UnforcedLeray.Short.PartI.IsBUCTrain tr)
  {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)

def chosenFreeTraj (g : B0579.X c m) : ℝ → B0579.Plane → ℝ :=
  Classical.choose (UnforcedLeray.Short.IIb.free_cyl_exists_approx
    m ν c hm hν hc tr hbu s hs g (Lp.memLp g))

theorem chosenFreeTraj_spec (g : B0579.X c m) :
    ∃ (fn : ℕ → B0579.Plane → ℝ) (ωn : ℕ → ℝ → B0579.Plane → ℝ),
      UnforcedLeray.Short.IIb.IsFreeCylFlow m tr s (g : B0579.Plane → ℝ)
        (chosenFreeTraj hm hν hc tr hbu hs g) ∧
      (∀ n, B0579.IsCylTest c (fn n)) ∧
      Tendsto (fun n => eLpNorm (fn n - (g : B0579.Plane → ℝ)) 2 (B0579.cellMeasure c m))
        atTop (𝓝 0) ∧
      (∀ n, UnforcedLeray.Short.IIb.IsFreeCylFlow m tr s (fn n) (ωn n)) ∧
      (∀ t' : ℝ, s ≤ t' →
        Tendsto (fun n => eLpNorm (ωn n t' - chosenFreeTraj hm hν hc tr hbu hs g t')
          2 (B0579.cellMeasure c m)) atTop (𝓝 0)) :=
  Classical.choose_spec (UnforcedLeray.Short.IIb.free_cyl_exists_approx
    m ν c hm hν hc tr hbu s hs (g : B0579.Plane → ℝ) (Lp.memLp g))

theorem chosenFreeTraj_isFlow (g : B0579.X c m) :
    UnforcedLeray.Short.IIb.IsFreeCylFlow m tr s g (chosenFreeTraj hm hν hc tr hbu hs g) := by
  obtain ⟨_, _, hfl, _, _, _, _⟩ := chosenFreeTraj_spec hm hν hc tr hbu hs g
  exact hfl

def freeCylStepVal (g : B0579.X c m) : B0579.X c m :=
  ((chosenFreeTraj_isFlow hm hν hc tr hbu hs g).memX t hst).toLp
    (chosenFreeTraj hm hν hc tr hbu hs g t)

theorem coeFn_freeCylStepVal (g : B0579.X c m) :
    (freeCylStepVal hm hν hc tr hbu hs hst g : B0579.Plane → ℝ) =ᵐ[B0579.cellMeasure c m]
      chosenFreeTraj hm hν hc tr hbu hs g t :=
  MemLp.coeFn_toLp _

theorem freeCylStepVal_ae_of_flow (g : B0579.X c m) {f' : B0579.Plane → ℝ}
    (hf' : (g : B0579.Plane → ℝ) =ᵐ[volume.restrict (B0579.cell c)] f')
    {ω' : ℝ → B0579.Plane → ℝ} (hω' : UnforcedLeray.Short.IIb.IsFreeCylFlow m tr s f' ω') :
    (freeCylStepVal hm hν hc tr hbu hs hst g : B0579.Plane → ℝ) =ᵐ[B0579.cellMeasure c m]
      ω' t := by
  have hfl' : UnforcedLeray.Short.IIb.IsFreeCylFlow m tr s f'
      (chosenFreeTraj hm hν hc tr hbu hs g) :=
    (chosenFreeTraj_isFlow hm hν hc tr hbu hs g).congr_initial hf'
  have huniq := (UnforcedLeray.Short.IIb.free_cyl_exists_unique m ν c hm hν hc tr hbu s hs f'
    hω'.memLp_initial).2 (chosenFreeTraj hm hν hc tr hbu hs g) ω' hfl' hω' t hst
  exact (coeFn_freeCylStepVal hm hν hc tr hbu hs hst g).trans
    ((B0579.cellMeasure_ac c m).ae_le huniq)

theorem exists_freeCylStep_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g : B0579.X c m,
      ‖freeCylStepVal hm hν hc tr hbu hs hst g‖ ≤ C * ‖g‖ := by
  have ht0 : 0 ≤ t := hs.trans hst
  obtain ⟨K, hK, hWE⟩ := RelB4locAux.weak_energy (m := m) hm hν hc hbu ht0
  refine ⟨Real.exp (K * t), (Real.exp_pos _).le, fun g => ?_⟩
  obtain ⟨fn, ωn, hfl, hfn, hconv0, hωn, hconvt⟩ := chosenFreeTraj_spec hm hν hc tr hbu hs g
  have hl0 : Tendsto (fun n => ‖RelB4locAux.liftC c m (fn n)‖) atTop
      (𝓝 ‖RelB4locAux.liftC c m g‖) :=
    (continuous_norm.tendsto _).comp
      (RelB4locAux.tendsto_liftC (Lp.memLp g) (Eventually.of_forall fun n => (hfn n).memLp m)
        hconv0)
  have hlt : Tendsto (fun n => ‖RelB4locAux.liftC c m (ωn n t)‖) atTop
      (𝓝 ‖RelB4locAux.liftC c m (chosenFreeTraj hm hν hc tr hbu hs g t)‖) :=
    (continuous_norm.tendsto _).comp
      (RelB4locAux.tendsto_liftC (hfl.memX t hst)
        (Eventually.of_forall fun n => (hωn n).memX t hst) (hconvt t hst))
  have hbd_n : ∀ n, ‖RelB4locAux.liftC c m (ωn n t)‖ ≤
      Real.exp (K * t) * ‖RelB4locAux.liftC c m (fn n)‖ := fun n =>
    RelRegularityOrg2.RelB1cAux.b1c_liftC_flow_le hK hs hst le_rfl (hfn n) (hωn n)
      (hWE s t hs hst le_rfl (fn n) (hfn n) (ωn n) (hωn n))
  have hlim : ‖RelB4locAux.liftC c m (chosenFreeTraj hm hν hc tr hbu hs g t)‖ ≤
      Real.exp (K * t) * ‖RelB4locAux.liftC c m g‖ :=
    le_of_tendsto_of_tendsto hlt (hl0.const_mul (Real.exp (K * t))) (Eventually.of_forall hbd_n)
  have heq_t : ‖freeCylStepVal hm hν hc tr hbu hs hst g‖ =
      ‖RelB4locAux.liftC c m (chosenFreeTraj hm hν hc tr hbu hs g t)‖ := by
    rw [Lp.norm_def, RelRegularityOrg2.RelB1cAux.b1c_norm_liftC_eq (hfl.memX t hst),
      eLpNorm_congr_ae (coeFn_freeCylStepVal hm hν hc tr hbu hs hst g)]
  have heq_0 : ‖g‖ = ‖RelB4locAux.liftC c m g‖ := by
    rw [Lp.norm_def, RelRegularityOrg2.RelB1cAux.b1c_norm_liftC_eq (Lp.memLp g)]
  rw [heq_t, heq_0]
  exact hlim

def freeCylStepCLM : B0579.X c m →L[ℝ] B0579.X c m :=
  let C := Classical.choose (exists_freeCylStep_bound hm hν hc tr hbu hs hst)
  have hC := Classical.choose_spec (exists_freeCylStep_bound hm hν hc tr hbu hs hst)
  LinearMap.mkContinuous
    { toFun := freeCylStepVal hm hν hc tr hbu hs hst
      map_add' := fun f g => by
        apply Lp.ext
        have hadd_fl : UnforcedLeray.Short.IIb.IsFreeCylFlow m tr s (f + g : B0579.X c m)
            (fun r x => chosenFreeTraj hm hν hc tr hbu hs f r x +
              chosenFreeTraj hm hν hc tr hbu hs g r x) :=
          ((chosenFreeTraj_isFlow hm hν hc tr hbu hs f).add
            (chosenFreeTraj_isFlow hm hν hc tr hbu hs g)).congr_initial
              ((B0579.ac_cellMeasure c m).ae_le (Lp.coeFn_add f g).symm)
        filter_upwards [freeCylStepVal_ae_of_flow hm hν hc tr hbu hs hst (f + g)
            EventuallyEq.rfl hadd_fl,
          Lp.coeFn_add (freeCylStepVal hm hν hc tr hbu hs hst f)
            (freeCylStepVal hm hν hc tr hbu hs hst g),
          coeFn_freeCylStepVal hm hν hc tr hbu hs hst f,
          coeFn_freeCylStepVal hm hν hc tr hbu hs hst g] with x hfg hadd hf hg
        rw [hfg, hadd, Pi.add_apply, hf, hg]
      map_smul' := fun a f => by
        simp only [RingHom.id_apply]
        apply Lp.ext
        have hsm_fl : UnforcedLeray.Short.IIb.IsFreeCylFlow m tr s (a • f : B0579.X c m)
            (fun r x => a * chosenFreeTraj hm hν hc tr hbu hs f r x) :=
          ((chosenFreeTraj_isFlow hm hν hc tr hbu hs f).smul a).congr_initial
            ((B0579.ac_cellMeasure c m).ae_le (Lp.coeFn_smul a f).symm)
        filter_upwards [freeCylStepVal_ae_of_flow hm hν hc tr hbu hs hst (a • f)
            EventuallyEq.rfl hsm_fl,
          Lp.coeFn_smul a (freeCylStepVal hm hν hc tr hbu hs hst f),
          coeFn_freeCylStepVal hm hν hc tr hbu hs hst f] with x haf hsm hf
        rw [haf, hsm, Pi.smul_apply, smul_eq_mul, hf] } C hC.2

end FreeStep

/-! ## 4. Pinned block operator `rawFreeBlock` and verification of `IsPeriodizedRelFreeBlockEvol` -/

theorem cellProjW_eq_b1cCellPart {m c a : ℝ} (hm1 : 1 < m) (hc : 0 < c) (ha : 0 < a)
    {f : ℝ × ℝ → ℝ} (hf : MemLp f 2 (B0579.cellMeasure c m)) (W : Planar.L2w m)
    (hW : ∀ᵐ z ∂volume, cToPlane z ∈ B0579.cell (cellLen c a) →
      (W : ℂ → ℂ) z = JscaleInv a (fun x => ((f x : ℝ) : ℂ)) (cToPlane z)) :
    cellProjW m (cellLen c a) W = RelRegularityOrg2.RelB1cAux.b1cCellPart hm1 c a f := by
  have happ : cellProjW m (cellLen c a) W =
      ((Lp.memLp W).indicator (measurableSet_cellC (cellLen c a))).toLp _ := rfl
  rw [happ]
  apply Lp.ext
  filter_upwards [((Lp.memLp W).indicator (measurableSet_cellC (cellLen c a))).coeFn_toLp,
    RelRegularityOrg2.RelB1cAux.b1c_coeFn_cellPart hm1 hc ha hf,
    (Planar.wMeasure_ac m).ae_le hW] with z h1 h2 h3
  rw [h1, h2]
  by_cases hz : cToPlane z ∈ B0579.cell (cellLen c a)
  · rw [Set.indicator_of_mem (show z ∈ {z : ℂ | cToPlane z ∈ B0579.cell (cellLen c a)} from hz),
      cellZeroExt, Set.indicator_of_mem hz, h3 hz]
  · rw [Set.indicator_of_notMem
        (show z ∉ {z : ℂ | cToPlane z ∈ B0579.cell (cellLen c a)} from hz),
      cellZeroExt, Set.indicator_of_notMem hz]

theorem dilW_exterior_ae_zero_on_cell {m c a : ℝ} (hm1 : 1 < m) (hc : 0 < c) (ha : 0 < a)
    {Y : Planar.L2w m} (hY : IsExteriorSupportedW (cellLen c a) Y) :
    (fun y : B0579.Plane => (Planar.dilW hm1 ha Y : ℂ → ℂ) (planeToC y))
      =ᵐ[B0579.cellMeasure c m] 0 := by
  have hsa : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  have hd : 0 < cellLen c a := div_pos hc hsa
  have hratio : cellLen c a / c = (Real.sqrt a)⁻¹ := by
    unfold cellLen; field_simp
  have hY' : ∀ᵐ z ∂(volume : Measure ℂ),
      cToPlane ((Real.sqrt a)⁻¹ • z) ∈ B0579.cell (cellLen c a) →
        (Y : ℂ → ℂ) ((Real.sqrt a)⁻¹ • z) = 0 :=
    (Measure.quasiMeasurePreserving_smul (μ := (volume : Measure ℂ)) (inv_pos.2 hsa).ne').ae hY
  have hdil : ∀ᵐ z ∂(Planar.wMeasure m),
      (Planar.dilW hm1 ha Y : ℂ → ℂ) z =
        (((a ^ 2)⁻¹ : ℝ) : ℂ) * (Y : ℂ → ℂ) ((Real.sqrt a)⁻¹ • z) :=
    Planar.coeFn_dilW hm1 ha Y
  have hcomb : ∀ᵐ z ∂(Planar.wMeasure m), cToPlane z ∈ B0579.cell c →
      (Planar.dilW hm1 ha Y : ℂ → ℂ) z = 0 := by
    filter_upwards [hdil, (Planar.wMeasure_ac m).ae_le hY'] with z hz1 hz2 hmem
    have hsc : cToPlane ((Real.sqrt a)⁻¹ • z) ∈ B0579.cell (cellLen c a) := by
      have h1 := (scaleMem_cell_iff hd hc (cToPlane z)).2 hmem
      rw [hratio] at h1
      simpa [cToPlane] using h1
    rw [hz1, hz2 hsc, mul_zero]
  have hp := ae_planeToC_cell_of_wMeasure (c := c) hcomb
  have hmem_ae : ∀ᵐ y ∂(B0579.cellMeasure c m), y ∈ B0579.cell c :=
    (B0579.cellMeasure_ac c m).ae_le (ae_restrict_mem (B0579.measurableSet_cell c))
  filter_upwards [hp, hmem_ae] with y hy hmem
  have hcp : cToPlane (planeToC y) = y := cToPlane_planeToC y
  exact hy (by rwa [hcp])

theorem projReCLM_liftC {c m : ℝ} {f : B0579.Plane → ℝ} (hf : MemLp f 2 (B0579.cellMeasure c m)) :
    projReCLM c m (RelB4locAux.liftC c m f) = hf.toLp f := by
  apply Lp.ext
  have hmem_ae : ∀ᵐ y ∂(B0579.cellMeasure c m), y ∈ B0579.cell c :=
    (B0579.cellMeasure_ac c m).ae_le (ae_restrict_mem (B0579.measurableSet_cell c))
  filter_upwards [(memLp_re_planeToC_cell c m (RelB4locAux.liftC c m f)).coeFn_toLp,
    hf.coeFn_toLp, ae_planeToC_cell_of_wMeasure (c := c) (RelB4locAux.coeFn_liftC hf),
    hmem_ae] with y h1 h2 h3 hmem
  rw [show projReCLM c m (RelB4locAux.liftC c m f) =
    (memLp_re_planeToC_cell c m (RelB4locAux.liftC c m f)).toLp _ from rfl, h1, h2, h3]
  simp [RelB4locAux.liftFun, cellZeroExt, cToPlane_planeToC, Set.indicator_of_mem hmem]

theorem projImCLM_liftC {c m : ℝ} {f : B0579.Plane → ℝ} (hf : MemLp f 2 (B0579.cellMeasure c m)) :
    projImCLM c m (RelB4locAux.liftC c m f) = 0 := by
  apply Lp.ext
  have hmem_ae : ∀ᵐ y ∂(B0579.cellMeasure c m), y ∈ B0579.cell c :=
    (B0579.cellMeasure_ac c m).ae_le (ae_restrict_mem (B0579.measurableSet_cell c))
  filter_upwards [(memLp_im_planeToC_cell c m (RelB4locAux.liftC c m f)).coeFn_toLp,
    Lp.coeFn_zero ℝ 2 (B0579.cellMeasure c m),
    ae_planeToC_cell_of_wMeasure (c := c) (RelB4locAux.coeFn_liftC hf),
    hmem_ae] with y h1 h0 h3 hmem
  rw [show projImCLM c m (RelB4locAux.liftC c m f) =
    (memLp_im_planeToC_cell c m (RelB4locAux.liftC c m f)).toLp _ from rfl, h1, h0, h3]
  simp [RelB4locAux.liftFun, cellZeroExt, cToPlane_planeToC, Set.indicator_of_mem hmem]

/-- The periodized relative free block operator family `F_rel` on `[t₁, t₂]` (zero outside the
triangle `0 ≤ σ ≤ τ ≤ B`). -/
def rawFreeBlock (P : PlanarData) {ν m : ℝ} (hm : 8 < m) (hν : 0 < ν)
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)))
    (htr : UnforcedLeray.Short.PartI.IsBUCTrain tr)
    {t₁ t₂ B : ℝ} (ht₁ : 0 ≤ t₁) (h12 : t₁ ≤ t₂) (hBeq : movingZ ν t₂ - movingZ ν t₁ = B)
    (τ σ : ℝ) : Planar.L2w m →L[ℂ] Planar.L2w m :=
  if htri : 0 ≤ σ ∧ σ ≤ τ ∧ τ ≤ B then
    let hm1 : 1 < m := by linarith
    let c := ν ^ (-2 : ℝ)
    have hc : 0 < c := Real.rpow_pos_of_pos hν _
    let s := ageAt ν t₁ σ
    let t := ageAt ν t₁ τ
    have ht₂ : 0 ≤ t₂ := ht₁.trans h12
    have hs : 0 ≤ s := ht₁.trans (ageAt_mem_Icc hν ht₁ h12 hBeq ⟨htri.1, htri.2.1.trans htri.2.2⟩).1
    have ht : 0 ≤ t := ht₁.trans (ageAt_mem_Icc hν ht₁ h12 hBeq ⟨htri.1.trans htri.2.1, htri.2.2⟩).1
    have hst : s ≤ t := ageAt_mono_on_block hν ht₁ ht₂ hBeq htri.1 htri.2.1 htri.2.2
    have has : 0 < clockA ν s := by unfold clockA; positivity
    have hat : 0 < clockA ν t := by unfold clockA; positivity
    have hds : 0 < cellLen c (clockA ν s) := cellLen_pos hν hs
    have hdt : 0 < cellLen c (clockA ν t) := cellLen_pos hν ht
    ((clockN P ν s t : ℂ)⁻¹) •
      ((Planar.dilW hm1 (inv_pos.2 hat)).comp
          ((liftComplexCLM (freeCylStepCLM hm hν hc tr htr hs hst)).comp (Planar.dilW hm1 has)) +
        (extDilW hm1 hds hdt).comp
          (ContinuousLinearMap.id ℂ (Planar.L2w m) - cellProjW m (cellLen c (clockA ν s))))
  else 0

theorem rawFreeBlock_isPeriodized (P : PlanarData) {ν m : ℝ} (hm : 8 < m) (hν : 0 < ν)
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)))
    (htr : UnforcedLeray.Short.PartI.IsBUCTrain tr)
    {t₁ t₂ B : ℝ} (ht₁ : 0 ≤ t₁) (h12 : t₁ ≤ t₂) (hBeq : movingZ ν t₂ - movingZ ν t₁ = B) :
    IsPeriodizedRelFreeBlockEvol P ν m tr t₁ B
      (rawFreeBlock P hm hν tr htr ht₁ h12 hBeq) := by
  unfold IsPeriodizedRelFreeBlockEvol
  dsimp only
  intro σ τ hσ hστ hτB f hf ω₀ hω₀ W hW
  have htri : 0 ≤ σ ∧ σ ≤ τ ∧ τ ≤ B := ⟨hσ, hστ, hτB⟩
  have hm1 : 1 < m := by linarith
  let c := ν ^ (-2 : ℝ)
  have hc : 0 < c := Real.rpow_pos_of_pos hν _
  let s := ageAt ν t₁ σ
  let t := ageAt ν t₁ τ
  have ht₂ : 0 ≤ t₂ := ht₁.trans h12
  have hs : 0 ≤ s := ht₁.trans (ageAt_mem_Icc hν ht₁ h12 hBeq ⟨hσ, hστ.trans hτB⟩).1
  have ht : 0 ≤ t := ht₁.trans (ageAt_mem_Icc hν ht₁ h12 hBeq ⟨hσ.trans hστ, hτB⟩).1
  have hst : s ≤ t := ageAt_mono_on_block hν ht₁ ht₂ hBeq hσ hστ hτB
  have has : 0 < clockA ν s := by unfold clockA; positivity
  have hat : 0 < clockA ν t := by unfold clockA; positivity
  have hds : 0 < cellLen c (clockA ν s) := cellLen_pos hν hs
  have hdt : 0 < cellLen c (clockA ν t) := cellLen_pos hν ht
  have hf_lp : MemLp f 2 (B0579.cellMeasure c m) := hf.memLp m
  have hwf_lp : MemLp (ω₀ t) 2 (B0579.cellMeasure c m) := hω₀.memX t hst
  -- Identify `cellProjW` with `b1cCellPart`
  set E := RelRegularityOrg2.RelB1cAux.b1cCellPart hm1 c (clockA ν s) f with hEdef
  have hproj : cellProjW m (cellLen c (clockA ν s)) W = E :=
    cellProjW_eq_b1cCellPart hm1 hc has hf_lp W hW
  -- On `W - E`, `Planar.dilW hm1 has (W - E)` vanishes on `cellMeasure c m`
  have hWE_ext : IsExteriorSupportedW (cellLen c (clockA ν s)) (W - E) := by
    rw [← hproj]; exact sub_cellProjW_exteriorSupported _ W
  have hdil_WE_zero := dilW_exterior_ae_zero_on_cell hm1 hc has hWE_ext
  have hRe_WE : projReCLM c m (Planar.dilW hm1 has (W - E)) = 0 := by
    apply Lp.ext
    filter_upwards [(memLp_re_planeToC_cell c m (Planar.dilW hm1 has (W - E))).coeFn_toLp,
      Lp.coeFn_zero ℝ 2 (B0579.cellMeasure c m), hdil_WE_zero] with y h1 h0 hz
    have hz' : (Planar.dilW hm1 has (W - E) : ℂ → ℂ) (planeToC y) = 0 := hz
    rw [show projReCLM c m (Planar.dilW hm1 has (W - E)) =
      (memLp_re_planeToC_cell c m (Planar.dilW hm1 has (W - E))).toLp _ from rfl, h1, h0, hz']
    simp
  have hIm_WE : projImCLM c m (Planar.dilW hm1 has (W - E)) = 0 := by
    apply Lp.ext
    filter_upwards [(memLp_im_planeToC_cell c m (Planar.dilW hm1 has (W - E))).coeFn_toLp,
      Lp.coeFn_zero ℝ 2 (B0579.cellMeasure c m), hdil_WE_zero] with y h1 h0 hz
    have hz' : (Planar.dilW hm1 has (W - E) : ℂ → ℂ) (planeToC y) = 0 := hz
    rw [show projImCLM c m (Planar.dilW hm1 has (W - E)) =
      (memLp_im_planeToC_cell c m (Planar.dilW hm1 has (W - E))).toLp _ from rfl, h1, h0, hz']
    simp
  -- And `Planar.dilW hm1 has E = liftC c m f`
  have hdil_E : Planar.dilW hm1 has E = RelB4locAux.liftC c m f := by
    rw [hEdef, RelRegularityOrg2.RelB1cAux.b1cCellPart, RelB4locAux.dilW'_of_pos hm1 (inv_pos.2 has)]
    have h := congrArg (fun T : Planar.L2w m →L[ℂ] Planar.L2w m => T (RelB4locAux.liftC c m f))
      (Planar.dilW_comp_inv hm1 has)
    simpa using h
  have hdil_W : Planar.dilW hm1 has W = RelB4locAux.liftC c m f + Planar.dilW hm1 has (W - E) := by
    rw [← hdil_E, ← map_add, add_sub_cancel]
  have hRe_W : projReCLM c m (Planar.dilW hm1 has W) = hf_lp.toLp f := by
    rw [hdil_W, map_add, hRe_WE, add_zero, projReCLM_liftC hf_lp]
  have hIm_W : projImCLM c m (Planar.dilW hm1 has W) = 0 := by
    rw [hdil_W, map_add, hIm_WE, add_zero, projImCLM_liftC hf_lp]
  -- Evaluate `liftComplexCLM (freeCylStepCLM ...) (Planar.dilW hm1 has W)`
  set T := freeCylStepCLM hm hν hc tr htr hs hst with hTdef
  have hTf_ae : (T (hf_lp.toLp f) : B0579.Plane → ℝ) =ᵐ[B0579.cellMeasure c m] ω₀ t :=
    freeCylStepVal_ae_of_flow hm hν hc tr htr hs hst (hf_lp.toLp f)
      ((B0579.ac_cellMeasure c m).ae_le hf_lp.coeFn_toLp) hω₀
  have hcell_val : liftComplexCLM T (Planar.dilW hm1 has W) = RelB4locAux.liftC c m (ω₀ t) := by
    change liftCCLM c m (T (projReCLM c m (Planar.dilW hm1 has W))) +
        Complex.I • liftCCLM c m (T (projImCLM c m (Planar.dilW hm1 has W))) =
      RelB4locAux.liftC c m (ω₀ t)
    rw [hRe_W, hIm_W, map_zero, map_zero, smul_zero, add_zero]
    exact liftC_congr_ae (Lp.memLp (T (hf_lp.toLp f))) hwf_lp hTf_ae
  -- Rewrite `rawFreeBlock` at `(τ, σ)` into planar dilations
  have hraw : rawFreeBlock P hm hν tr htr ht₁ h12 hBeq τ σ W =
      ((clockN P ν s t : ℂ)⁻¹) •
        (Planar.dilW hm1 (inv_pos.2 hat) (RelB4locAux.liftC c m (ω₀ t)) +
          extDilW hm1 hds hdt (W - E)) := by
    unfold rawFreeBlock
    rw [dite_cond_eq_true (eq_true htri)]
    simp only [smul_apply, add_apply, ContinuousLinearMap.comp_apply, sub_apply,
      ContinuousLinearMap.id_apply]
    rw [← hTdef, hcell_val, hproj]
  rw [hraw]
  -- Pointwise a.e. identification with `periodizedExt`
  have hα : 0 < (clockA ν t)⁻¹ := inv_pos.2 hat
  have hβ : 0 < ((cellLen c (clockA ν s) / cellLen c (clockA ν t)) ^ 2)⁻¹ :=
    inv_pos.2 (sq_pos_of_pos (div_pos hds hdt))
  have heS : (fun w => (W : ℂ → ℂ) w -
      cellZeroExt (cellLen c (clockA ν s)) (fun y => (W : ℂ → ℂ) (planeToC y)) (cToPlane w))
        =ᵐ[Planar.wMeasure m] ⇑(W - E) := by
    filter_upwards [Lp.coeFn_sub W E,
      RelRegularityOrg2.RelB1cAux.b1c_coeFn_cellPart hm1 hc has hf_lp,
      (Planar.wMeasure_ac m).ae_le hW] with w h1 h2 h3
    rw [h1, Pi.sub_apply, h2]
    congr 1
    simp only [cellZeroExt]
    by_cases hin : cToPlane w ∈ B0579.cell (cellLen c (clockA ν s))
    · simp only [indicator_of_mem hin, planeToC_cToPlane]
      exact h3 hin
    · simp only [indicator_of_notMem hin]
  have hw_ae : ⇑(((clockN P ν s t : ℂ)⁻¹) •
      (Planar.dilW hm1 hα (RelB4locAux.liftC c m (ω₀ t)) +
        Planar.dilW hm1 hβ (W - E))) =ᵐ[Planar.wMeasure m]
      fun z : ℂ => ((clockN P ν s t : ℂ)⁻¹) *
        periodizedExt (cellLen c (clockA ν s)) (cellLen c (clockA ν t))
          (JscaleInv (clockA ν t) (fun x => ((ω₀ t x : ℝ) : ℂ)))
          (fun y => (W : ℂ → ℂ) (planeToC y)) (cToPlane z) := by
    filter_upwards [Lp.coeFn_smul ((clockN P ν s t : ℂ)⁻¹)
        (Planar.dilW hm1 hα (RelB4locAux.liftC c m (ω₀ t)) + Planar.dilW hm1 hβ (W - E)),
      Lp.coeFn_add (Planar.dilW hm1 hα (RelB4locAux.liftC c m (ω₀ t))) (Planar.dilW hm1 hβ (W - E)),
      Planar.coeFn_dilW hm1 hα (RelB4locAux.liftC c m (ω₀ t)),
      Planar.coeFn_dilW hm1 hβ (W - E),
      Planar.dilWFun_congr hα (RelB4locAux.coeFn_liftC hwf_lp),
      Planar.dilWFun_congr hβ heS] with z h2 h3 h4 h5 h6 h7
    have h4' : (Planar.dilW hm1 hα (RelB4locAux.liftC c m (ω₀ t)) : ℂ → ℂ) z =
        Planar.dilWFun (clockA ν t)⁻¹ (RelB4locAux.liftFun c (ω₀ t)) z := h4.trans h6
    have h5' : (Planar.dilW hm1 hβ (W - E) : ℂ → ℂ) z =
        Planar.dilWFun ((cellLen c (clockA ν s) / cellLen c (clockA ν t)) ^ 2)⁻¹
          (fun w => (W : ℂ → ℂ) w - cellZeroExt (cellLen c (clockA ν s))
            (fun y => (W : ℂ → ℂ) (planeToC y)) (cToPlane w)) z := h5.trans h7.symm
    rw [h2, Pi.smul_apply, h3, Pi.add_apply, h4', h5', smul_eq_mul]
    congr 1
    simp only [periodizedExt]
    rw [RelB4locAux.cellZeroExt_JscaleInv_eq hc hat (ω₀ t) z,
      RelB4locAux.extDil_eq_dilWFun hds hdt (W : ℂ → ℂ) z]
  exact (Planar.volume_ac m).ae_le hw_ae

end PeriodizedFreeBlockAux

open PeriodizedFreeBlockAux

/-- **Proof of `PeriodizedRelFreeBlockInterior`** (SP 2937-2962, zero sorry). -/
theorem periodizedRelFreeBlockInterior : PeriodizedRelFreeBlockInterior := by
  intro P _hP m hm B α_free δ_free hB hα hδ hFreeHyp
  have hm1 : 1 < m := by linarith
  have hCm : 0 ≤ normGrowthConst m := by unfold normGrowthConst; nlinarith
  obtain ⟨b_f, hb_f, hHyp_b⟩ := hFreeHyp
  obtain ⟨b_sub, hb_sub, hSub_b⟩ := relFreeMovingEnergy P hm one_pos
  set R_grow := |P.eigenvalue.re| + normGrowthConst m + |P.kappa.re| + 3 / 2 + 1
  have hR_pos : 0 < R_grow := by positivity
  set M_free := Real.exp (R_grow * B)
  have hM_nonneg : 0 ≤ M_free := (Real.exp_pos _).le
  set b_free := max b_f b_sub
  have hb_free : 1 ≤ b_free := hb_f.trans (le_max_left _ _)
  refine ⟨M_free, b_free, hM_nonneg, hb_free, fun b hb => ?_⟩
  have hb1 : 1 ≤ b := hb_free.trans hb
  have hb0 : 0 < b := lt_of_lt_of_le zero_lt_one hb1
  obtain ⟨ν_f, hν_f, hHyp_ν⟩ := hHyp_b b ((le_max_left _ _).trans hb)
  obtain ⟨ν_s, hν_s, hSub_ν⟩ := hSub_b b ((le_max_right _ _).trans hb)
  refine ⟨min ν_f ν_s, lt_min hν_f hν_s, fun ν hν tr htr t₁ t₂ ht₁ h12 hbt₂ hBeq => ?_⟩
  have hν0 : 0 < ν := hν.1
  have hν_in_f : ν ∈ Ioc 0 ν_f := ⟨hν0, hν.2.trans (min_le_left _ _)⟩
  have hν_in_s : ν ∈ Ioc 0 ν_s := ⟨hν0, hν.2.trans (min_le_right _ _)⟩
  have ht₂ : 0 ≤ t₂ := ht₁.trans h12
  set F_rel := rawFreeBlock P hm hν0 tr htr ht₁ h12 hBeq
  have hF_pin : IsPeriodizedRelFreeBlockEvol P ν m tr t₁ B F_rel :=
    rawFreeBlock_isPeriodized P hm hν0 tr htr ht₁ h12 hBeq
  refine ⟨F_rel, hF_pin, ?_, ?_⟩
  · -- Sub-block uniform bound `‖F_rel τ σ‖ ≤ M_free`
    intro σ τ hστ _hτ_le
    by_cases htri : 0 ≤ σ ∧ σ ≤ τ ∧ τ ≤ B
    · rcases htri with ⟨hσ0, _, hτB⟩
      have hsI := ageAt_mem_Icc hν0 ht₁ h12 hBeq ⟨hσ0, hστ.trans hτB⟩
      have htI := ageAt_mem_Icc hν0 ht₁ h12 hBeq ⟨hσ0.trans hστ, hτB⟩
      have hs : 0 ≤ ageAt ν t₁ σ := ht₁.trans hsI.1
      have ht : 0 ≤ ageAt ν t₁ τ := ht₁.trans htI.1
      have hst : ageAt ν t₁ σ ≤ ageAt ν t₁ τ := ageAt_mono_on_block hν0 ht₁ ht₂ hBeq hσ0 hστ hτB
      have hbt' : b ≤ clockTheta ν (ageAt ν t₁ τ) := hbt₂.trans (theta_anti hν0 ht htI.2)
      have hΔ : movingZ ν (ageAt ν t₁ τ) - movingZ ν (ageAt ν t₁ σ) = τ - σ := by
        have h1 := movingZ_ageAt_sub hν0 ht₂ hBeq hτB
        have h2 := movingZ_ageAt_sub hν0 ht₂ hBeq (hστ.trans hτB)
        linarith
      have hΔ0 : 0 ≤ τ - σ := sub_nonneg.2 hστ
      have hΔB : τ - σ ≤ B := by linarith
      have hds : 0 < cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ σ)) := cellLen_pos hν0 hs
      have hdt : 0 < cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ τ)) := cellLen_pos hν0 ht
      refine opNorm_le_of_cell_ext
        (d_s := cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ σ)))
        (d_t := cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ τ)))
        (F_rel τ σ) hM_nonneg (fun V hV => ⟨?_, ?_⟩) (fun Y hY => ⟨?_, ?_⟩)
      · set K_sub := Real.exp
          ((-P.eigenvalue.re + (normGrowthConst m + |P.kappa.re|) / b + 1) * (τ - σ))
        have hK0 : 0 ≤ K_sub := (Real.exp_pos _).le
        have hEK : ∀ f : B0579.Plane → ℝ, B0579.IsCylTest (ν ^ (-2 : ℝ)) f →
            ∀ ω₀ : ℝ → B0579.Plane → ℝ,
              UnforcedLeray.Short.IIb.IsFreeCylFlow m tr (ageAt ν t₁ σ) f ω₀ →
              xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ τ))) m
                  (JscaleInv (clockA ν (ageAt ν t₁ τ))
                    (fun x => ((ω₀ (ageAt ν t₁ τ) x : ℝ) : ℂ))) ≤
                ENNReal.ofReal (clockN P ν (ageAt ν t₁ σ) (ageAt ν t₁ τ)) *
                  (ENNReal.ofReal K_sub *
                    xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ σ))) m
                      (JscaleInv (clockA ν (ageAt ν t₁ σ)) (fun x => ((f x : ℝ) : ℂ)))) := by
          intro f hf ω₀ hω₀
          have h := hSub_ν ν hν_in_s tr htr (ageAt ν t₁ σ) (ageAt ν t₁ τ) hs hst hbt' f hf ω₀ hω₀
          rwa [hΔ] at h
        have hVK := norm_apply_le_of_tests hds hK0 (F_rel τ σ)
          (fun φ hφ => freeBlock_testW_bound hF_pin hν0 hm htr hσ0 hστ hτB hs hst hK0 hEK φ hφ) V hV
        have hKM : K_sub ≤ M_free := by
          refine Real.exp_le_exp.2 ?_
          have hdiv : (normGrowthConst m + |P.kappa.re|) / b ≤ normGrowthConst m + |P.kappa.re| :=
            div_le_self (by positivity) hb1
          have hrate : -P.eigenvalue.re + (normGrowthConst m + |P.kappa.re|) / b + 1 ≤ R_grow := by
            have := neg_le_abs P.eigenvalue.re
            dsimp [R_grow]
            linarith
          calc (-P.eigenvalue.re + (normGrowthConst m + |P.kappa.re|) / b + 1) * (τ - σ)
              ≤ R_grow * (τ - σ) := mul_le_mul_of_nonneg_right hrate hΔ0
            _ ≤ R_grow * B := mul_le_mul_of_nonneg_left hΔB hR_pos.le
        exact hVK.trans (mul_le_mul_of_nonneg_right hKM (norm_nonneg _))
      · exact freeBlock_cell_to_cell hF_pin hν0 hm htr hσ0 hστ hτB hs ht V hV
      · rw [freeBlock_ext_eq_smul hF_pin hσ0 hστ hτB hm1 hds hdt Y hY, norm_smul]
        set N := clockN P ν (ageAt ν t₁ σ) (ageAt ν t₁ τ) with hNdef
        have hN : 0 < N := clockN_pos P hν0 hs ht
        have hNinv : ‖((N : ℂ))⁻¹‖ = N⁻¹ := by
          rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg hN.le]
        rw [hNinv]
        have hS := norm_extDilW_cellLen_le_exp (c := ν ^ (-2 : ℝ)) hm1
          (Real.rpow_pos_of_pos hν0 _) hν0 hs hst hb0 hbt'
        rw [hΔ] at hS
        have hNlow := exp_beta0_le_clockN P hν0 hs hst hb0 hbt'
        rw [hΔ, ← hNdef] at hNlow
        have hfac : N⁻¹ * Real.exp ((3 / (2 * b)) * (τ - σ)) ≤ M_free := by
          rw [inv_mul_le_iff₀ hN]
          have hdiv1 : |P.kappa.re| / b ≤ |P.kappa.re| := div_le_self (abs_nonneg _) hb1
          have hdiv2 : (|P.kappa.re| + 3 / 2) / b ≤ |P.kappa.re| + 3 / 2 :=
            div_le_self (by positivity) hb1
          have hrate : -P.eigenvalue.re + (|P.kappa.re| + 3 / 2) / b ≤ R_grow := by
            have := neg_le_abs P.eigenvalue.re
            dsimp [R_grow]
            linarith
          have hexp_le : Real.exp ((-P.eigenvalue.re + (|P.kappa.re| + 3 / 2) / b) * (τ - σ)) ≤
              M_free := by
            refine Real.exp_le_exp.2 ?_
            calc (-P.eigenvalue.re + (|P.kappa.re| + 3 / 2) / b) * (τ - σ)
                ≤ R_grow * (τ - σ) := mul_le_mul_of_nonneg_right hrate hΔ0
              _ ≤ R_grow * B := mul_le_mul_of_nonneg_left hΔB hR_pos.le
          calc Real.exp ((3 / (2 * b)) * (τ - σ))
              = Real.exp ((P.eigenvalue.re - |P.kappa.re| / b) * (τ - σ)) *
                  Real.exp ((-P.eigenvalue.re + (|P.kappa.re| + 3 / 2) / b) * (τ - σ)) := by
                rw [← Real.exp_add]
                congr 1
                field_simp
                ring
            _ ≤ N * M_free :=
                mul_le_mul hNlow hexp_le (Real.exp_pos _).le hN.le
        calc N⁻¹ * ‖extDilW hm1 hds hdt Y‖
            ≤ N⁻¹ * (‖extDilW hm1 hds hdt‖ * ‖Y‖) :=
              mul_le_mul_of_nonneg_left ((extDilW hm1 hds hdt).le_opNorm Y) (inv_nonneg.2 hN.le)
          _ ≤ N⁻¹ * (Real.exp ((3 / (2 * b)) * (τ - σ)) * ‖Y‖) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hS (norm_nonneg _))
                (inv_nonneg.2 hN.le)
          _ = (N⁻¹ * Real.exp ((3 / (2 * b)) * (τ - σ))) * ‖Y‖ := by ring
          _ ≤ M_free * ‖Y‖ := mul_le_mul_of_nonneg_right hfac (norm_nonneg _)
      · exact freeBlock_ext_exteriorSupported hF_pin hσ0 hστ hτB hds hdt Y hY
    · have hzero : F_rel τ σ = 0 := by simp [F_rel, rawFreeBlock, htri]
      rw [hzero, norm_zero]
      exact hM_nonneg
  · -- Full-block cell-supported bound `‖F_rel B 0 W‖ ≤ (α_free + δ_free) * ‖W‖`
    intro W hW
    have hs0 : ageAt ν t₁ 0 = t₁ := ageAt_zero hν0 ht₁
    have htB : ageAt ν t₁ B = t₂ := ageAt_eq_of_movingZ_sub hν0 ht₂ hBeq
    have hs_pos : 0 ≤ ageAt ν t₁ 0 := hs0.symm ▸ ht₁
    have hst_B : ageAt ν t₁ 0 ≤ ageAt ν t₁ B := by rw [hs0, htB]; exact h12
    have hd1 : 0 < cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ 0)) := cellLen_pos hν0 hs_pos
    have hE_B : ∀ f : B0579.Plane → ℝ, B0579.IsCylTest (ν ^ (-2 : ℝ)) f →
        ∀ ω₀ : ℝ → B0579.Plane → ℝ,
          UnforcedLeray.Short.IIb.IsFreeCylFlow m tr (ageAt ν t₁ 0) f ω₀ →
          xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ B))) m
              (JscaleInv (clockA ν (ageAt ν t₁ B))
                (fun x => ((ω₀ (ageAt ν t₁ B) x : ℝ) : ℂ))) ≤
            ENNReal.ofReal (clockN P ν (ageAt ν t₁ 0) (ageAt ν t₁ B)) *
              (ENNReal.ofReal α_free *
                xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ 0))) m
                  (JscaleInv (clockA ν (ageAt ν t₁ 0)) (fun x => ((f x : ℝ) : ℂ)))) := by
      intro f hf ω₀ hω₀
      rw [hs0] at hω₀
      rw [hs0, htB]
      exact hHyp_ν ν hν_in_f tr htr t₁ t₂ ht₁ h12 hbt₂ hBeq f hf ω₀ hω₀
    have hW' : IsCellSupportedW (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ 0))) W := by
      rwa [hs0]
    have hW_bd : ‖F_rel B 0 W‖ ≤ α_free * ‖W‖ :=
      norm_apply_le_of_tests hd1 hα.le (F_rel B 0)
        (fun φ hφ => freeBlock_testW_bound hF_pin hν0 hm htr le_rfl hB.le le_rfl hs_pos hst_B
          hα.le hE_B φ hφ) W hW'
    exact hW_bd.trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg W))

end UnforcedLeray.Short.IIIa

end
