import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F8_1_org.DuhamelRegularity.UnitWeakUnique.StreamCutoff
import UnforcedLeray.Lib.BochnerTime.Energy

/-!
# `PartII-b:F8/1/org/3/2` (`UnitWeakUnique.lean`): Unit-horizon weak homogeneous Oseen uniqueness

Proves `CylUnitWeakHomogeneousUnique` (`SP 2301–2305`): any weak homogeneous
`L^∞((σ, σ + 1); H¹_σ(C_c))` solution `δ` of `∂_s δ - ν Δ_{q,η} δ + P_0 B_{v_c(s)} δ = 0` on
`(σ, σ + 1)` with right-Lebesgue zero `L²(cell)` trace at `σ⁺` vanishes `volume`-a.e. on
`(σ, σ + 1) × ℝ²`, via cylinder Gaussian mollification on `Cyl.L2v p.c`, `rotT` stream-function
testing, Hilbert energy identity (`HasWeakDerivTime.norm_sq_sub'`), and Grönwall's inequality.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff InnerProductSpace intervalIntegral

namespace UnforcedLeray.Short.IIb.UnitWeakUniqueAux

open UnforcedLeray.Short.IIb
open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cyl (L2v cellμ divFree P0 Vec2)
open UnforcedLeray.GaussianVortex (Plane)
open UnforcedLeray.HeatCylinder
open UnforcedLeray.B0284 (heatKernel2)

local instance : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
local instance : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩

/-! ## 1. Uniform `[0, 2]` drift bounds and `L²(cell)` convective-stretching estimate -/

lemma uniform_drift_bounds {c : ℝ} {V : ℝ → B0579.Plane → F8Ex.RMerid}
    (hV : F8Ex.IsSmoothBUCDrift c V) :
    ∃ M : ℝ, 0 ≤ M ∧
      (∀ r ∈ Icc (0 : ℝ) 2, ContDiff ℝ ∞ (V r)) ∧
      (∀ r ∈ Icc (0 : ℝ) 2, ∀ k : Fin 2, ∀ y : B0579.Plane, |V r y k| ≤ M) ∧
      (∀ r ∈ Icc (0 : ℝ) 2, ∀ j k : Fin 2, ∀ y : B0579.Plane,
        |fderiv ℝ (fun z => V r z k) y (B0579.dir j)| ≤ M) := by
  obtain ⟨M0, hM0_nn, hM0⟩ := hV.deriv_bound 0
  obtain ⟨M1, _, hM1⟩ := hV.deriv_bound 1
  refine ⟨max M0 M1, le_trans hM0_nn (le_max_left M0 M1), ?_, ?_, ?_⟩
  · intro r hr
    have hc := hV.smooth.comp (contDiff_const.prodMk contDiff_id).contDiffOn
      (s := univ) (fun y _ => ⟨hr, mem_univ y⟩)
    exact contDiffOn_univ.1 hc
  · intro r hr k y
    calc |V r y k| = ‖V r y k‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖V r y‖ := PiLp.norm_apply_le (V r y) k
      _ = ‖iteratedFDeriv ℝ 0 (V r) y‖ := (norm_iteratedFDeriv_zero (f := V r) (x := y)).symm
      _ ≤ M0 := hM0 r hr y
      _ ≤ max M0 M1 := le_max_left M0 M1
  · intro r hr j k y
    have hVr : ContDiff ℝ ∞ (V r) := by
      have hc := hV.smooth.comp (contDiff_const.prodMk contDiff_id).contDiffOn
        (s := univ) (fun w _ => ⟨hr, mem_univ w⟩)
      exact contDiffOn_univ.1 hc
    have hproj : fderiv ℝ (fun z => V r z k) y (B0579.dir j) =
        fderiv ℝ (V r) y (B0579.dir j) k := by
      have hc := ((F8Ex.πR k).hasFDerivAt.comp y
        (hVr.contDiffAt.differentiableAt (by simp)).hasFDerivAt).fderiv
      change fderiv ℝ ((F8Ex.πR k) ∘ (V r)) y (B0579.dir j) =
        F8Ex.πR k (fderiv ℝ (V r) y (B0579.dir j))
      rw [hc, ContinuousLinearMap.comp_apply]
    have hdir_norm : ‖B0579.dir j‖ = 1 := by
      fin_cases j <;> simp [B0579.dir]
    rw [hproj]
    calc |fderiv ℝ (V r) y (B0579.dir j) k|
        = ‖fderiv ℝ (V r) y (B0579.dir j) k‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖fderiv ℝ (V r) y (B0579.dir j)‖ := PiLp.norm_apply_le _ k
      _ = ‖iteratedFDeriv ℝ 1 (V r) y ![B0579.dir j]‖ := by
          rw [iteratedFDeriv_one_apply, Matrix.cons_val_zero]
      _ ≤ ‖iteratedFDeriv ℝ 1 (V r) y‖ *
          ∏ l : Fin 1, ‖(![B0579.dir j] : Fin 1 → B0579.Plane) l‖ :=
          ContinuousMultilinearMap.le_opNorm _ _
      _ = ‖iteratedFDeriv ℝ 1 (V r) y‖ := by simp [hdir_norm]
      _ ≤ M1 := hM1 r hr y
      _ ≤ max M0 M1 := le_max_right M0 M1

private lemma eLpNorm_mulRealR_le {c M : ℝ} (hM : 0 ≤ M) {a : B0579.Plane → ℝ}
    {G : B0579.Plane → F8Ex.RMerid} (ha : Continuous a) (hbdd : ∀ y, |a y| ≤ M)
    (_hG : MemLp G 2 (F8Ex.cellMeas c)) :
    eLpNorm (fun y => a y • G y) 2 (F8Ex.cellMeas c) ≤
      ENNReal.ofReal M * eLpNorm G 2 (F8Ex.cellMeas c) := by
  have _ := ha
  calc eLpNorm (fun y => a y • G y) 2 (F8Ex.cellMeas c)
      ≤ eLpNorm (M • G) 2 (F8Ex.cellMeas c) := eLpNorm_mono fun y => by
        simp only [Pi.smul_apply, norm_smul, Real.norm_eq_abs, Real.norm_of_nonneg hM]
        exact mul_le_mul_of_nonneg_right (hbdd y) (norm_nonneg _)
    _ = ‖M‖ₑ * eLpNorm G 2 (F8Ex.cellMeas c) := eLpNorm_const_smul M G 2 (F8Ex.cellMeas c)
    _ = ENNReal.ofReal M * eLpNorm G 2 (F8Ex.cellMeas c) := by
        rw [← ofReal_norm, Real.norm_of_nonneg hM]

lemma memLp_and_norm_realBvSlice {c M : ℝ} (hM : 0 ≤ M)
    {v : B0579.Plane → F8Ex.RMerid} (hv : ContDiff ℝ ∞ v)
    (hb0 : ∀ k : Fin 2, ∀ y : B0579.Plane, |v y k| ≤ M)
    (hb1 : ∀ j k : Fin 2, ∀ y : B0579.Plane,
      |fderiv ℝ (fun z => v z k) y (B0579.dir j)| ≤ M)
    {u uq uη : B0579.Plane → F8Ex.RMerid}
    (hu : MemLp u 2 (cellμ c)) (huq : MemLp uq 2 (cellμ c)) (huη : MemLp uη 2 (cellμ c)) :
    ∃ hbv : MemLp (F8Ex.realBvSlice v u uq uη) 2 (cellμ c),
      ‖hbv.toLp (F8Ex.realBvSlice v u uq uη)‖ ≤
        M * ‖huq.toLp uq‖ + M * ‖huη.toLp uη‖ + 4 * M * ‖hu.toLp u‖ := by
  have hu' : MemLp u 2 (F8Ex.cellMeas c) := by rwa [cellMeas_eq_cellμ]
  have huq' : MemLp uq 2 (F8Ex.cellMeas c) := by rwa [cellMeas_eq_cellμ]
  have huη' : MemLp uη 2 (F8Ex.cellMeas c) := by rwa [cellMeas_eq_cellμ]
  have hcv0 : Continuous (fun y => v y 0) := (F8Ex.πR 0).continuous.comp hv.continuous
  have hcv1 : Continuous (fun y => v y 1) := (F8Ex.πR 1).continuous.comp hv.continuous
  have mt0 : MemLp (fun y => v y 0 • uq y) 2 (cellμ c) := by
    rw [← cellMeas_eq_cellμ]; exact F8Ex.memLp_mulRealR hcv0 (hb0 0) huq'
  have mt1 : MemLp (fun y => v y 1 • uη y) 2 (cellμ c) := by
    rw [← cellMeas_eq_cellμ]; exact F8Ex.memLp_mulRealR hcv1 (hb0 1) huη'
  let dV (j : Fin 2) : B0579.Plane → F8Ex.RMerid := fun y => fderiv ℝ v y (B0579.dir j)
  have hcdV (j : Fin 2) : Continuous (dV j) :=
    ((contDiff_infty_iff_fderiv.1 hv).2.clm_apply contDiff_const).continuous
  have hdV_eq (j i : Fin 2) (y : B0579.Plane) :
      fderiv ℝ (fun z => v z i) y (B0579.dir j) = dV j y i := by
    have hc := ((F8Ex.πR i).hasFDerivAt.comp y
      (hv.contDiffAt.differentiableAt (by simp)).hasFDerivAt).fderiv
    change fderiv ℝ ((F8Ex.πR i) ∘ v) y (B0579.dir j) = F8Ex.πR i (fderiv ℝ v y (B0579.dir j))
    rw [hc, ContinuousLinearMap.comp_apply]
  let P_ji (j i : Fin 2) : F8Ex.RMerid →L[ℝ] F8Ex.RMerid :=
    (F8Ex.πR j).smulRight (EuclideanSpace.single i (1 : ℝ))
  have hP_norm (j i : Fin 2) (w : F8Ex.RMerid) : ‖P_ji j i w‖ ≤ ‖w‖ := by
    dsimp [P_ji]
    rw [norm_smul, Real.norm_eq_abs, PiLp.norm_single 2 (fun _ : Fin 2 => ℝ) i (1 : ℝ),
      norm_one, mul_one]
    exact (Real.norm_eq_abs (w j)).symm ▸ PiLp.norm_apply_le w j
  have ms_coord (j i : Fin 2) :
      MemLp (fun y => dV j y i • P_ji j i (u y)) 2 (cellμ c) := by
    rw [← cellMeas_eq_cellμ]
    have hcj : Continuous (fun y => dV j y i) := (F8Ex.πR i).continuous.comp (hcdV j)
    have hbj : ∀ y, |dV j y i| ≤ M := fun y => by rw [← hdV_eq j i y]; exact hb1 j i y
    exact F8Ex.memLp_mulRealR hcj hbj ((P_ji j i).comp_memLp' hu')
  have heq : F8Ex.realBvSlice v u uq uη =
      fun y => ((v y 0 • uq y + v y 1 • uη y) +
        (dV 0 y 0 • P_ji 0 0 (u y) + dV 0 y 1 • P_ji 0 1 (u y))) +
        (dV 1 y 0 • P_ji 1 0 (u y) + dV 1 y 1 • P_ji 1 1 (u y)) := by
    funext y
    ext i
    have hd0 : ((1 : ℝ), (0 : ℝ)) = B0579.dir 0 := rfl
    have hd1 : ((0 : ℝ), (1 : ℝ)) = B0579.dir 1 := rfl
    fin_cases i <;>
      simp [F8Ex.realBvSlice, hd0, hd1, hdV_eq, P_ji, F8Ex.πR] <;> ring
  have hbv : MemLp (F8Ex.realBvSlice v u uq uη) 2 (cellμ c) := by
    rw [heq]
    exact ((mt0.add mt1).add ((ms_coord 0 0).add (ms_coord 0 1))).add
      ((ms_coord 1 0).add (ms_coord 1 1))
  refine ⟨hbv, ?_⟩
  have hnorm_term : ∀ {a : B0579.Plane → ℝ} {G : B0579.Plane → F8Ex.RMerid}
      (ha : Continuous a) (hbdd : ∀ y, |a y| ≤ M) (hG : MemLp G 2 (cellμ c))
      (h : MemLp (fun y => a y • G y) 2 (cellμ c)),
      ‖h.toLp (fun y => a y • G y)‖ ≤ M * ‖hG.toLp G‖ := by
    intro a G ha hbdd hG h
    simp only [Lp.norm_toLp, ← cellMeas_eq_cellμ]
    have hG' : MemLp G 2 (F8Ex.cellMeas c) := by rwa [cellMeas_eq_cellμ]
    have h' : MemLp (fun y => a y • G y) 2 (F8Ex.cellMeas c) := by rwa [cellMeas_eq_cellμ]
    have hle := eLpNorm_mulRealR_le hM ha hbdd hG'
    have htop : ENNReal.ofReal M * eLpNorm G 2 (F8Ex.cellMeas c) ≠ ⊤ :=
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hG'.eLpNorm_lt_top).ne
    have htr := (ENNReal.toReal_le_toReal h'.eLpNorm_lt_top.ne htop).2 hle
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hM] at htr
  have hnorm_P : ∀ (j i : Fin 2),
      ‖((P_ji j i).comp_memLp' hu).toLp (fun y => P_ji j i (u y))‖ ≤ ‖hu.toLp u‖ := by
    intro j i
    rw [Lp.norm_toLp, Lp.norm_toLp]
    exact (ENNReal.toReal_le_toReal (((P_ji j i).comp_memLp' hu).eLpNorm_lt_top.ne)
      hu.eLpNorm_lt_top.ne).2 (eLpNorm_mono fun y => hP_norm j i (u y))
  have htoLp_eq : hbv.toLp (F8Ex.realBvSlice v u uq uη) =
      ((mt0.toLp _ + mt1.toLp _) + ((ms_coord 0 0).toLp _ + (ms_coord 0 1).toLp _)) +
        ((ms_coord 1 0).toLp _ + (ms_coord 1 1).toLp _) := by
    have h_congr : hbv.toLp (F8Ex.realBvSlice v u uq uη) =
        (((mt0.add mt1).add ((ms_coord 0 0).add (ms_coord 0 1))).add
          ((ms_coord 1 0).add (ms_coord 1 1))).toLp _ :=
      MemLp.toLp_congr hbv _ (Eventually.of_forall (congrFun heq))
    rw [h_congr,
      MemLp.toLp_add ((mt0.add mt1).add ((ms_coord 0 0).add (ms_coord 0 1)))
        ((ms_coord 1 0).add (ms_coord 1 1)),
      MemLp.toLp_add (mt0.add mt1) ((ms_coord 0 0).add (ms_coord 0 1)),
      MemLp.toLp_add mt0 mt1,
      MemLp.toLp_add (ms_coord 0 0) (ms_coord 0 1),
      MemLp.toLp_add (ms_coord 1 0) (ms_coord 1 1)]
  rw [htoLp_eq]
  have n0 := hnorm_term hcv0 (hb0 0) huq mt0
  have n1 := hnorm_term hcv1 (hb0 1) huη mt1
  have n00 : ‖(ms_coord 0 0).toLp _‖ ≤ M * ‖hu.toLp u‖ :=
    (hnorm_term (a := fun y => dV 0 y 0) ((F8Ex.πR 0).continuous.comp (hcdV 0))
      (fun y => by rw [← hdV_eq 0 0 y]; exact hb1 0 0 y)
      ((P_ji 0 0).comp_memLp' hu) (ms_coord 0 0)).trans
      (mul_le_mul_of_nonneg_left (hnorm_P 0 0) hM)
  have n01 : ‖(ms_coord 0 1).toLp _‖ ≤ M * ‖hu.toLp u‖ :=
    (hnorm_term (a := fun y => dV 0 y 1) ((F8Ex.πR 1).continuous.comp (hcdV 0))
      (fun y => by rw [← hdV_eq 0 1 y]; exact hb1 0 1 y)
      ((P_ji 0 1).comp_memLp' hu) (ms_coord 0 1)).trans
      (mul_le_mul_of_nonneg_left (hnorm_P 0 1) hM)
  have n10 : ‖(ms_coord 1 0).toLp _‖ ≤ M * ‖hu.toLp u‖ :=
    (hnorm_term (a := fun y => dV 1 y 0) ((F8Ex.πR 0).continuous.comp (hcdV 1))
      (fun y => by rw [← hdV_eq 1 0 y]; exact hb1 1 0 y)
      ((P_ji 1 0).comp_memLp' hu) (ms_coord 1 0)).trans
      (mul_le_mul_of_nonneg_left (hnorm_P 1 0) hM)
  have n11 : ‖(ms_coord 1 1).toLp _‖ ≤ M * ‖hu.toLp u‖ :=
    (hnorm_term (a := fun y => dV 1 y 1) ((F8Ex.πR 1).continuous.comp (hcdV 1))
      (fun y => by rw [← hdV_eq 1 1 y]; exact hb1 1 1 y)
      ((P_ji 1 1).comp_memLp' hu) (ms_coord 1 1)).trans
      (mul_le_mul_of_nonneg_left (hnorm_P 1 1) hM)
  have tri1 := norm_add_le
    (((mt0.toLp _ + mt1.toLp _) + ((ms_coord 0 0).toLp _ + (ms_coord 0 1).toLp _)))
    ((ms_coord 1 0).toLp _ + (ms_coord 1 1).toLp _)
  have tri2 := norm_add_le (mt0.toLp _ + mt1.toLp _) ((ms_coord 0 0).toLp _ + (ms_coord 0 1).toLp _)
  have tri3 := norm_add_le (mt0.toLp _) (mt1.toLp _)
  have tri4 := norm_add_le ((ms_coord 0 0).toLp _) ((ms_coord 0 1).toLp _)
  have tri5 := norm_add_le ((ms_coord 1 0).toLp _) ((ms_coord 1 1).toLp _)
  linarith

/-! ## 2. Shifted `rotT` tests and mollified weak time derivative on `Ioo 0 1` -/

private lemma shift_sob_cylTest {c : ℝ} {φ : B0579.Plane → ℝ}
    (hφ : UnforcedLeray.Sob.IsCylTest c φ) (w : Plane) :
    UnforcedLeray.Sob.IsCylTest c (fun z => φ (z + w)) where
  smooth := hφ.smooth.comp (contDiff_id.add contDiff_const)
  periodic z := by
    have hz : z + (c, 0) + w = z + w + (c, 0) := by (ext <;> simp); ring
    rw [hz, hφ.periodic]
  bounded := by
    obtain ⟨R, hR⟩ := hφ.bounded
    refine ⟨R + |w.2|, fun z hz => ?_⟩
    apply hR
    have htri : |z.2| ≤ |(z + w).2| + |w.2| := by
      have heq : z.2 = (z + w).2 - w.2 := by simp
      calc |z.2| = |(z + w).2 - w.2| := by rw [heq]
        _ ≤ |(z + w).2| + |w.2| := abs_sub _ _
    linarith

private lemma rotT_comp_add {φ : B0579.Plane → ℝ} (hdφ : Differentiable ℝ φ)
    (w z : B0579.Plane) :
    UnforcedLeray.Cyl.rotT (fun y => φ (y + w)) z = UnforcedLeray.Cyl.rotT φ (z + w) := by
  have hd_sh : Differentiable ℝ (fun y : B0579.Plane => φ (y + w)) :=
    hdφ.comp (differentiable_id.add (differentiable_const w))
  ext i
  fin_cases i
  · change UnforcedLeray.Cyl.partialEta (fun y => φ (y + w)) z =
      UnforcedLeray.Cyl.partialEta φ (z + w)
    rw [UnforcedLeray.Cyl.partialEta_eq_fderiv hd_sh z,
      UnforcedLeray.Cyl.partialEta_eq_fderiv hdφ (z + w),
      fderiv_comp_add_right (𝕜 := ℝ) (f := φ) (x := z) w]
  · change -UnforcedLeray.Cyl.partialQ (fun y => φ (y + w)) z =
      -UnforcedLeray.Cyl.partialQ φ (z + w)
    rw [UnforcedLeray.Cyl.partialQ_eq_fderiv hd_sh z,
      UnforcedLeray.Cyl.partialQ_eq_fderiv hdφ (z + w),
      fderiv_comp_add_right (𝕜 := ℝ) (f := φ) (x := z) w]

private lemma cylSmoothToL2_rotT_shift {c : ℝ} (hc : 0 < c) {φ : B0579.Plane → ℝ}
    (hφ : UnforcedLeray.Sob.IsCylTest c φ) (w : Plane) :
    cylSmoothToL2 (isCylSmooth_of_solTest (isRealSolCylTest_rotT (shift_sob_cylTest hφ w))) =
      planeShiftL2CLM hc (-w)
        (cylSmoothToL2 (isCylSmooth_of_solTest (isRealSolCylTest_rotT hφ))) := by
  let hΦ := isCylSmooth_of_solTest (isRealSolCylTest_rotT hφ)
  let hΦw := isCylSmooth_of_solTest (isRealSolCylTest_rotT (shift_sob_cylTest hφ w))
  symm
  apply Lp.ext
  have hae := planeShiftL2_ae_sub_of_cylSmooth hc hΦ (memLp_of_cylSmooth hΦ) (-w)
  filter_upwards [hae, (memLp_of_cylSmooth hΦw).coeFn_toLp] with z h1 h2
  have hsub : z - (-w) = z + w := sub_neg_eq_add z w
  exact h1.trans ((congrArg (UnforcedLeray.Cyl.rotT φ) hsub).trans
    ((rotT_comp_add hφ.differentiable w z).symm.trans h2.symm))

private lemma cylSmoothToL2_rotT_dir_shift {c : ℝ} (hc : 0 < c) {φ : B0579.Plane → ℝ}
    (hφ : UnforcedLeray.Sob.IsCylTest c φ) (j : Fin 2) (w : Plane) :
    cylSmoothToL2 ((isCylSmooth_of_solTest
        (isRealSolCylTest_rotT (shift_sob_cylTest hφ w))).dir (B0579.dir j)) =
      planeShiftL2CLM hc (-w)
        (cylSmoothToL2 ((isCylSmooth_of_solTest (isRealSolCylTest_rotT hφ)).dir (B0579.dir j))) := by
  let hΦ := isCylSmooth_of_solTest (isRealSolCylTest_rotT hφ)
  let hΦw := isCylSmooth_of_solTest (isRealSolCylTest_rotT (shift_sob_cylTest hφ w))
  symm
  apply Lp.ext
  have hae := planeShiftL2_ae_sub_of_cylSmooth hc (hΦ.dir (B0579.dir j))
    (memLp_of_cylSmooth (hΦ.dir (B0579.dir j))) (-w)
  filter_upwards [hae, (memLp_of_cylSmooth (hΦw.dir (B0579.dir j))).coeFn_toLp] with z h1 h2
  have hfun : UnforcedLeray.Cyl.rotT (fun y => φ (y + w)) =
      fun y => UnforcedLeray.Cyl.rotT φ (y + w) :=
    funext (rotT_comp_add hφ.differentiable w)
  have hdir_eq : fderiv ℝ (UnforcedLeray.Cyl.rotT (fun y => φ (y + w))) z (B0579.dir j) =
      fderiv ℝ (UnforcedLeray.Cyl.rotT φ) (z - (-w)) (B0579.dir j) := by
    rw [hfun, fderiv_comp_add_right (𝕜 := ℝ) (f := UnforcedLeray.Cyl.rotT φ) (x := z) w,
      sub_neg_eq_add]
  exact h1.trans (hdir_eq.symm.trans h2.symm)

lemma hasWeakDerivTime_mollified {c ν θ : ℝ} (hc : 0 < c) (hθ : 0 < θ)
    {u₀ uq uη b : ℝ → L2v c}
    (hu₀_int : IntegrableOn u₀ (Ioo 0 1))
    (huq_int : IntegrableOn uq (Ioo 0 1))
    (huη_int : IntegrableOn uη (Ioo 0 1))
    (hb_int : IntegrableOn b (Ioo 0 1))
    (hu₀_div : ∀ᵐ r ∂(volume.restrict (Ioo 0 1)), u₀ r ∈ divFree c)
    (hwk : ∀ (α : ℝ → ℝ), ContDiff ℝ ∞ α → HasCompactSupport α → tsupport α ⊆ Ioo 0 1 →
      ∀ (φ : B0579.Plane → ℝ) (hφ : UnforcedLeray.Sob.IsCylTest c φ),
        ∫ r : ℝ,
          (-deriv α r *
              ⟪cylSmoothToL2 (isCylSmooth_of_solTest (isRealSolCylTest_rotT hφ)), u₀ r⟫_ℝ +
            ν * α r *
              (⟪cylSmoothToL2 ((isCylSmooth_of_solTest (isRealSolCylTest_rotT hφ)).dir
                  (B0579.dir 0)), uq r⟫_ℝ +
                ⟪cylSmoothToL2 ((isCylSmooth_of_solTest (isRealSolCylTest_rotT hφ)).dir
                  (B0579.dir 1)), uη r⟫_ℝ) +
            α r *
              ⟪cylSmoothToL2 (isCylSmooth_of_solTest (isRealSolCylTest_rotT hφ)), b r⟫_ℝ) = 0) :
    UnforcedLeray.BochnerTime.HasWeakDerivTime 0 1
      (fun r => centeredHeatVecL2CLM hc θ (u₀ r))
      (fun r => P0 c (ν • (DHeatCLM hc 0 θ (uq r) + DHeatCLM hc 1 θ (uη r)) -
        centeredHeatVecL2CLM hc θ (b r))) := by
  let u_θ : ℝ → L2v c := fun r => centeredHeatVecL2CLM hc θ (u₀ r)
  let u'_θ : ℝ → L2v c := fun r =>
    P0 c (ν • (DHeatCLM hc 0 θ (uq r) + DHeatCLM hc 1 θ (uη r)) -
      centeredHeatVecL2CLM hc θ (b r))
  have huθ_int : IntegrableOn u_θ (Ioo 0 1) := (centeredHeatVecL2CLM hc θ).integrable_comp hu₀_int
  have hu'θ_int : IntegrableOn u'_θ (Ioo 0 1) :=
    (P0 c).integrable_comp
      (((((DHeatCLM hc 0 θ).integrable_comp huq_int).add
        ((DHeatCLM hc 1 θ).integrable_comp huη_int)).smul ν).sub
        ((centeredHeatVecL2CLM hc θ).integrable_comp hb_int))
  refine ⟨huθ_int, hu'θ_int, fun α hα_sm hα_cp hα_ts => ?_⟩
  have hi_du₀ := UnforcedLeray.BochnerTime.integrable_deriv_smul hα_sm hα_cp hα_ts hu₀_int
  have hi_uq := UnforcedLeray.BochnerTime.integrable_smul hα_sm hα_cp hα_ts huq_int
  have hi_uη := UnforcedLeray.BochnerTime.integrable_smul hα_sm hα_cp hα_ts huη_int
  have hi_b := UnforcedLeray.BochnerTime.integrable_smul hα_sm hα_cp hα_ts hb_int
  let I₀ : L2v c := ∫ r : ℝ, deriv α r • u₀ r
  let Iq : L2v c := ∫ r : ℝ, α r • uq r
  let Iη : L2v c := ∫ r : ℝ, α r • uη r
  let Ib : L2v c := ∫ r : ℝ, α r • b r
  have hI₀_P0 : P0 c I₀ = I₀ := by
    dsimp [I₀]
    rw [← (P0 c).integral_comp_comm hi_du₀]
    refine integral_congr_ae ?_
    filter_upwards [(ae_restrict_iff' measurableSet_Ioo).1 hu₀_div] with r hr
    rw [map_smul]
    by_cases hmem : r ∈ Ioo (0 : ℝ) 1
    · rw [UnforcedLeray.Cyl.P0_eq_self (hr hmem)]
    · have hd0 : deriv α r = 0 := image_eq_zero_of_notMem_tsupport
        (fun hm => hmem ((UnforcedLeray.BochnerTime.tsupport_deriv_subset_Ioo hα_ts) hm))
      simp [hd0]
  have htest_vec : ∀ (φ : B0579.Plane → ℝ) (hφ : UnforcedLeray.Sob.IsCylTest c φ),
      -⟪cylSmoothToL2 (isCylSmooth_of_solTest (isRealSolCylTest_rotT hφ)), I₀⟫_ℝ +
        ν * (⟪cylSmoothToL2 ((isCylSmooth_of_solTest (isRealSolCylTest_rotT hφ)).dir
            (B0579.dir 0)), Iq⟫_ℝ +
          ⟪cylSmoothToL2 ((isCylSmooth_of_solTest (isRealSolCylTest_rotT hφ)).dir
            (B0579.dir 1)), Iη⟫_ℝ) +
        ⟪cylSmoothToL2 (isCylSmooth_of_solTest (isRealSolCylTest_rotT hφ)), Ib⟫_ℝ = 0 := by
    intro φ hφ
    let ψ₀ := cylSmoothToL2 (isCylSmooth_of_solTest (isRealSolCylTest_rotT hφ))
    let ψq := cylSmoothToL2 ((isCylSmooth_of_solTest (isRealSolCylTest_rotT hφ)).dir (B0579.dir 0))
    let ψη := cylSmoothToL2 ((isCylSmooth_of_solTest (isRealSolCylTest_rotT hφ)).dir (B0579.dir 1))
    have e0 : -⟪ψ₀, I₀⟫_ℝ = ∫ r : ℝ, -deriv α r * ⟪ψ₀, u₀ r⟫_ℝ := by
      change -innerSL ℝ ψ₀ I₀ = _
      rw [← (innerSL ℝ ψ₀).integral_comp_comm hi_du₀, ← integral_neg]
      refine integral_congr_ae (Eventually.of_forall fun r => ?_)
      simp only [innerSL_apply_apply, inner_smul_right]; ring
    have eq_q : ⟪ψq, Iq⟫_ℝ = ∫ r : ℝ, α r * ⟪ψq, uq r⟫_ℝ := by
      change innerSL ℝ ψq Iq = _
      rw [← (innerSL ℝ ψq).integral_comp_comm hi_uq]
      refine integral_congr_ae (Eventually.of_forall fun r => ?_)
      simp only [innerSL_apply_apply, inner_smul_right]
    have eq_η : ⟪ψη, Iη⟫_ℝ = ∫ r : ℝ, α r * ⟪ψη, uη r⟫_ℝ := by
      change innerSL ℝ ψη Iη = _
      rw [← (innerSL ℝ ψη).integral_comp_comm hi_uη]
      refine integral_congr_ae (Eventually.of_forall fun r => ?_)
      simp only [innerSL_apply_apply, inner_smul_right]
    have eq_b : ⟪ψ₀, Ib⟫_ℝ = ∫ r : ℝ, α r * ⟪ψ₀, b r⟫_ℝ := by
      change innerSL ℝ ψ₀ Ib = _
      rw [← (innerSL ℝ ψ₀).integral_comp_comm hi_b]
      refine integral_congr_ae (Eventually.of_forall fun r => ?_)
      simp only [innerSL_apply_apply, inner_smul_right]
    have i0 : Integrable (fun r : ℝ => -deriv α r * ⟪ψ₀, u₀ r⟫_ℝ) :=
      (((innerSL ℝ ψ₀).integrable_comp hi_du₀).neg).congr
        (Eventually.of_forall fun r => by simp [neg_mul])
    have iq : Integrable (fun r : ℝ => α r * ⟪ψq, uq r⟫_ℝ) :=
      ((innerSL ℝ ψq).integrable_comp hi_uq).congr
        (Eventually.of_forall fun r => by simp)
    have iη : Integrable (fun r : ℝ => α r * ⟪ψη, uη r⟫_ℝ) :=
      ((innerSL ℝ ψη).integrable_comp hi_uη).congr
        (Eventually.of_forall fun r => by simp)
    have ib : Integrable (fun r : ℝ => α r * ⟪ψ₀, b r⟫_ℝ) :=
      ((innerSL ℝ ψ₀).integrable_comp hi_b).congr
        (Eventually.of_forall fun r => by simp)
    rw [e0, eq_q, eq_η, eq_b]
    have hsum_iqη : (∫ r : ℝ, α r * ⟪ψq, uq r⟫_ℝ) + (∫ r : ℝ, α r * ⟪ψη, uη r⟫_ℝ) =
        ∫ r : ℝ, (α r * ⟪ψq, uq r⟫_ℝ + α r * ⟪ψη, uη r⟫_ℝ) :=
      (integral_add iq iη).symm
    have hmul_iqη : ν * ∫ r : ℝ, (α r * ⟪ψq, uq r⟫_ℝ + α r * ⟪ψη, uη r⟫_ℝ) =
        ∫ r : ℝ, ν * (α r * ⟪ψq, uq r⟫_ℝ + α r * ⟪ψη, uη r⟫_ℝ) :=
      (integral_const_mul ν _).symm
    have hi_qη : Integrable (fun r : ℝ => ν * (α r * ⟪ψq, uq r⟫_ℝ + α r * ⟪ψη, uη r⟫_ℝ)) :=
      ((iq.add iη).const_mul ν).congr (Eventually.of_forall fun _ => rfl)
    have hi_0qη : Integrable (fun r : ℝ =>
        -deriv α r * ⟪ψ₀, u₀ r⟫_ℝ + ν * (α r * ⟪ψq, uq r⟫_ℝ + α r * ⟪ψη, uη r⟫_ℝ)) :=
      (i0.add hi_qη).congr (Eventually.of_forall fun _ => rfl)
    have hadd1 : (∫ r : ℝ, -deriv α r * ⟪ψ₀, u₀ r⟫_ℝ) +
        (∫ r : ℝ, ν * (α r * ⟪ψq, uq r⟫_ℝ + α r * ⟪ψη, uη r⟫_ℝ)) =
        ∫ r : ℝ, (-deriv α r * ⟪ψ₀, u₀ r⟫_ℝ + ν * (α r * ⟪ψq, uq r⟫_ℝ + α r * ⟪ψη, uη r⟫_ℝ)) :=
      (integral_add i0 hi_qη).symm
    have hadd2 : (∫ r : ℝ, (-deriv α r * ⟪ψ₀, u₀ r⟫_ℝ +
          ν * (α r * ⟪ψq, uq r⟫_ℝ + α r * ⟪ψη, uη r⟫_ℝ))) +
        (∫ r : ℝ, α r * ⟪ψ₀, b r⟫_ℝ) =
        ∫ r : ℝ, ((-deriv α r * ⟪ψ₀, u₀ r⟫_ℝ +
          ν * (α r * ⟪ψq, uq r⟫_ℝ + α r * ⟪ψη, uη r⟫_ℝ)) + α r * ⟪ψ₀, b r⟫_ℝ) :=
      (integral_add hi_0qη ib).symm
    rw [hsum_iqη, hmul_iqη, hadd1, hadd2]
    refine Eq.trans (integral_congr_ae (Eventually.of_forall fun r => ?_))
      (hwk α hα_sm hα_cp hα_ts φ hφ)
    dsimp only; ring
  let Z : L2v c := centeredHeatVecL2CLM hc θ I₀ +
    P0 c (ν • (DHeatCLM hc 0 θ Iq + DHeatCLM hc 1 θ Iη) - centeredHeatVecL2CLM hc θ Ib)
  have hZ_div : Z ∈ divFree c := by
    have h1 : P0 c (centeredHeatVecL2CLM hc θ I₀) = centeredHeatVecL2CLM hc θ I₀ := by
      rw [← centeredHeatVecL2CLM_P0_comm hc θ I₀, hI₀_P0]
    have hPZ : P0 c Z = Z := by
      dsimp [Z]
      rw [map_add, h1, UnforcedLeray.Cyl.P0_idem]
    rw [← hPZ]
    exact UnforcedLeray.Cyl.P0_mem Z
  have hZ_zero : Z = 0 := by
    refine eq_zero_of_divFree_and_ortho_rotT hc Z hZ_div fun φ hφ => ?_
    let hΦ := isCylSmooth_of_solTest (isRealSolCylTest_rotT hφ)
    let ψ₀ := cylSmoothToL2 hΦ
    let ψq := cylSmoothToL2 (hΦ.dir (B0579.dir 0))
    let ψη := cylSmoothToL2 (hΦ.dir (B0579.dir 1))
    have hiK : Integrable (heatKernel2 θ) volume :=
      integrable_prod_plane (UnforcedLeray.B0296.integrable_heatKernel1 hθ)
        (UnforcedLeray.B0296.integrable_heatKernel1 hθ)
    have h_avg : ∀ (X Y : L2v c),
        ⟪Y, centeredHeatVecL2CLM hc θ X⟫_ℝ =
          ∫ w : Plane, heatKernel2 θ w * ⟪planeShiftL2CLM hc (-w) Y, X⟫_ℝ := by
      intro X Y
      rw [real_inner_comm _ Y, centeredHeat_eq_shiftAvgCLM hc hθ X, inner_shiftAvgCLM hc hiK X Y]
      refine integral_congr_ae (Eventually.of_forall fun w => ?_)
      dsimp only
      rw [inner_planeShiftL2CLM_adj hc w X Y, real_inner_comm]
    have hi_term : ∀ (X Y : L2v c),
        Integrable (fun w : Plane => heatKernel2 θ w * ⟪planeShiftL2CLM hc (-w) Y, X⟫_ℝ) volume := by
      intro X Y
      have hsm : Integrable (fun w : Plane => heatKernel2 θ w • planeShiftL2CLM hc w X) volume :=
        integrable_kernel_smul_planeShift hc hiK X
      refine ((innerSL ℝ Y).integrable_comp hsm).congr (Eventually.of_forall fun w => ?_)
      dsimp only
      rw [innerSL_apply_apply, inner_smul_right, real_inner_comm _ Y,
        inner_planeShiftL2CLM_adj hc w X Y, real_inner_comm]
    have hsum_w :
        -⟪ψ₀, centeredHeatVecL2CLM hc θ I₀⟫_ℝ +
          ν * (⟪ψq, centeredHeatVecL2CLM hc θ Iq⟫_ℝ + ⟪ψη, centeredHeatVecL2CLM hc θ Iη⟫_ℝ) +
          ⟪ψ₀, centeredHeatVecL2CLM hc θ Ib⟫_ℝ = 0 := by
      rw [h_avg I₀ ψ₀, h_avg Iq ψq, h_avg Iη ψη, h_avg Ib ψ₀]
      have wn0 : -(∫ w : Plane, heatKernel2 θ w * ⟪planeShiftL2CLM hc (-w) ψ₀, I₀⟫_ℝ) =
          ∫ w : Plane, -(heatKernel2 θ w * ⟪planeShiftL2CLM hc (-w) ψ₀, I₀⟫_ℝ) :=
        (integral_neg _).symm
      have wa_qη : (∫ w : Plane, heatKernel2 θ w * ⟪planeShiftL2CLM hc (-w) ψq, Iq⟫_ℝ) +
          (∫ w : Plane, heatKernel2 θ w * ⟪planeShiftL2CLM hc (-w) ψη, Iη⟫_ℝ) =
          ∫ w : Plane, (heatKernel2 θ w * ⟪planeShiftL2CLM hc (-w) ψq, Iq⟫_ℝ +
            heatKernel2 θ w * ⟪planeShiftL2CLM hc (-w) ψη, Iη⟫_ℝ) :=
        (integral_add (hi_term Iq ψq) (hi_term Iη ψη)).symm
      have wm_qη : ν * ∫ w : Plane, (heatKernel2 θ w * ⟪planeShiftL2CLM hc (-w) ψq, Iq⟫_ℝ +
          heatKernel2 θ w * ⟪planeShiftL2CLM hc (-w) ψη, Iη⟫_ℝ) =
          ∫ w : Plane, ν * (heatKernel2 θ w * ⟪planeShiftL2CLM hc (-w) ψq, Iq⟫_ℝ +
            heatKernel2 θ w * ⟪planeShiftL2CLM hc (-w) ψη, Iη⟫_ℝ) :=
        (integral_const_mul ν _).symm
      have wi_0 : Integrable (fun w : Plane =>
          -(heatKernel2 θ w * ⟪planeShiftL2CLM hc (-w) ψ₀, I₀⟫_ℝ)) :=
        (hi_term I₀ ψ₀).neg
      have wi_qη : Integrable (fun w : Plane =>
          ν * (heatKernel2 θ w * ⟪planeShiftL2CLM hc (-w) ψq, Iq⟫_ℝ +
            heatKernel2 θ w * ⟪planeShiftL2CLM hc (-w) ψη, Iη⟫_ℝ)) :=
        (((hi_term Iq ψq).add (hi_term Iη ψη)).const_mul ν).congr (Eventually.of_forall fun _ => rfl)
      have wi_0qη : Integrable (fun w : Plane =>
          -(heatKernel2 θ w * ⟪planeShiftL2CLM hc (-w) ψ₀, I₀⟫_ℝ) +
            ν * (heatKernel2 θ w * ⟪planeShiftL2CLM hc (-w) ψq, Iq⟫_ℝ +
              heatKernel2 θ w * ⟪planeShiftL2CLM hc (-w) ψη, Iη⟫_ℝ)) :=
        (wi_0.add wi_qη).congr (Eventually.of_forall fun _ => rfl)
      have wa1 : (∫ w : Plane, -(heatKernel2 θ w * ⟪planeShiftL2CLM hc (-w) ψ₀, I₀⟫_ℝ)) +
          (∫ w : Plane, ν * (heatKernel2 θ w * ⟪planeShiftL2CLM hc (-w) ψq, Iq⟫_ℝ +
            heatKernel2 θ w * ⟪planeShiftL2CLM hc (-w) ψη, Iη⟫_ℝ)) =
          ∫ w : Plane, (-(heatKernel2 θ w * ⟪planeShiftL2CLM hc (-w) ψ₀, I₀⟫_ℝ) +
            ν * (heatKernel2 θ w * ⟪planeShiftL2CLM hc (-w) ψq, Iq⟫_ℝ +
              heatKernel2 θ w * ⟪planeShiftL2CLM hc (-w) ψη, Iη⟫_ℝ)) :=
        (integral_add wi_0 wi_qη).symm
      have wa2 : (∫ w : Plane, (-(heatKernel2 θ w * ⟪planeShiftL2CLM hc (-w) ψ₀, I₀⟫_ℝ) +
            ν * (heatKernel2 θ w * ⟪planeShiftL2CLM hc (-w) ψq, Iq⟫_ℝ +
              heatKernel2 θ w * ⟪planeShiftL2CLM hc (-w) ψη, Iη⟫_ℝ))) +
          (∫ w : Plane, heatKernel2 θ w * ⟪planeShiftL2CLM hc (-w) ψ₀, Ib⟫_ℝ) =
          ∫ w : Plane, ((-(heatKernel2 θ w * ⟪planeShiftL2CLM hc (-w) ψ₀, I₀⟫_ℝ) +
            ν * (heatKernel2 θ w * ⟪planeShiftL2CLM hc (-w) ψq, Iq⟫_ℝ +
              heatKernel2 θ w * ⟪planeShiftL2CLM hc (-w) ψη, Iη⟫_ℝ)) +
            heatKernel2 θ w * ⟪planeShiftL2CLM hc (-w) ψ₀, Ib⟫_ℝ) :=
        (integral_add wi_0qη (hi_term Ib ψ₀)).symm
      rw [wn0, wa_qη, wm_qη, wa1, wa2]
      have hzero_fn : (fun w : Plane =>
          (-(heatKernel2 θ w * ⟪planeShiftL2CLM hc (-w) ψ₀, I₀⟫_ℝ) +
            ν * (heatKernel2 θ w * ⟪planeShiftL2CLM hc (-w) ψq, Iq⟫_ℝ +
              heatKernel2 θ w * ⟪planeShiftL2CLM hc (-w) ψη, Iη⟫_ℝ)) +
            heatKernel2 θ w * ⟪planeShiftL2CLM hc (-w) ψ₀, Ib⟫_ℝ) = fun _ => 0 := by
        funext w
        have hw := htest_vec (fun z => φ (z + w)) (shift_sob_cylTest hφ w)
        rw [cylSmoothToL2_rotT_shift hc hφ w, cylSmoothToL2_rotT_dir_shift hc hφ 0 w,
          cylSmoothToL2_rotT_dir_shift hc hφ 1 w] at hw
        calc (-(heatKernel2 θ w * ⟪planeShiftL2CLM hc (-w) ψ₀, I₀⟫_ℝ) +
              ν * (heatKernel2 θ w * ⟪planeShiftL2CLM hc (-w) ψq, Iq⟫_ℝ +
                heatKernel2 θ w * ⟪planeShiftL2CLM hc (-w) ψη, Iη⟫_ℝ)) +
              heatKernel2 θ w * ⟪planeShiftL2CLM hc (-w) ψ₀, Ib⟫_ℝ
            = heatKernel2 θ w * (-⟪planeShiftL2CLM hc (-w) ψ₀, I₀⟫_ℝ +
                ν * (⟪planeShiftL2CLM hc (-w) ψq, Iq⟫_ℝ +
                  ⟪planeShiftL2CLM hc (-w) ψη, Iη⟫_ℝ) +
                ⟪planeShiftL2CLM hc (-w) ψ₀, Ib⟫_ℝ) := by ring
          _ = heatKernel2 θ w * 0 := by rw [hw]
          _ = 0 := mul_zero _
      rw [hzero_fn, integral_zero]
    rw [inner_dir_cylSmooth_centeredHeat hc hθ hΦ 0 Iq,
      inner_dir_cylSmooth_centeredHeat hc hθ hΦ 1 Iη] at hsum_w
    have hψ₀_P0 : P0 c ψ₀ = ψ₀ :=
      UnforcedLeray.Cyl.P0_eq_self (cylSmoothToL2_mem_divFree_of_solTest hc
        (isRealSolCylTest_rotT hφ))
    change ⟪ψ₀, Z⟫_ℝ = 0
    dsimp [Z]
    rw [inner_add_right, ← UnforcedLeray.Cyl.inner_P0_comm, hψ₀_P0,
      inner_sub_right, inner_smul_right, inner_add_right]
    linarith
  have heq1 : centeredHeatVecL2CLM hc θ I₀ = ∫ r : ℝ, deriv α r • u_θ r := by
    dsimp [I₀, u_θ]
    rw [← (centeredHeatVecL2CLM hc θ).integral_comp_comm hi_du₀]
    exact integral_congr_ae (Eventually.of_forall fun r => map_smul _ _ _)
  have heq2 : P0 c (ν • (DHeatCLM hc 0 θ Iq + DHeatCLM hc 1 θ Iη) -
      centeredHeatVecL2CLM hc θ Ib) = ∫ r : ℝ, α r • u'_θ r := by
    dsimp [Iq, Iη, Ib, u'_θ]
    have hq_c : DHeatCLM hc 0 θ (∫ r : ℝ, α r • uq r) =
        ∫ r : ℝ, α r • DHeatCLM hc 0 θ (uq r) := by
      rw [← (DHeatCLM hc 0 θ).integral_comp_comm hi_uq]
      exact integral_congr_ae (Eventually.of_forall fun r => map_smul _ _ _)
    have hη_c : DHeatCLM hc 1 θ (∫ r : ℝ, α r • uη r) =
        ∫ r : ℝ, α r • DHeatCLM hc 1 θ (uη r) := by
      rw [← (DHeatCLM hc 1 θ).integral_comp_comm hi_uη]
      exact integral_congr_ae (Eventually.of_forall fun r => map_smul _ _ _)
    have hb_c : centeredHeatVecL2CLM hc θ (∫ r : ℝ, α r • b r) =
        ∫ r : ℝ, α r • centeredHeatVecL2CLM hc θ (b r) := by
      rw [← (centeredHeatVecL2CLM hc θ).integral_comp_comm hi_b]
      exact integral_congr_ae (Eventually.of_forall fun r => map_smul _ _ _)
    have iq' : Integrable (fun r : ℝ => α r • DHeatCLM hc 0 θ (uq r)) := by
      simpa only [map_smul] using (DHeatCLM hc 0 θ).integrable_comp hi_uq
    have iη' : Integrable (fun r : ℝ => α r • DHeatCLM hc 1 θ (uη r)) := by
      simpa only [map_smul] using (DHeatCLM hc 1 θ).integrable_comp hi_uη
    have ib' : Integrable (fun r : ℝ => α r • centeredHeatVecL2CLM hc θ (b r)) := by
      simpa only [map_smul] using (centeredHeatVecL2CLM hc θ).integrable_comp hi_b
    rw [hq_c, hη_c, hb_c]
    have hs_qη : (∫ r : ℝ, α r • DHeatCLM hc 0 θ (uq r)) +
        (∫ r : ℝ, α r • DHeatCLM hc 1 θ (uη r)) =
        ∫ r : ℝ, (α r • DHeatCLM hc 0 θ (uq r) + α r • DHeatCLM hc 1 θ (uη r)) :=
      (integral_add iq' iη').symm
    have hsm_ν : ν • ∫ r : ℝ, (α r • DHeatCLM hc 0 θ (uq r) + α r • DHeatCLM hc 1 θ (uη r)) =
        ∫ r : ℝ, ν • (α r • DHeatCLM hc 0 θ (uq r) + α r • DHeatCLM hc 1 θ (uη r)) :=
      (integral_smul ν _).symm
    have i_νqη : Integrable (fun r : ℝ =>
        ν • (α r • DHeatCLM hc 0 θ (uq r) + α r • DHeatCLM hc 1 θ (uη r))) :=
      ((iq'.add iη').smul ν).congr (Eventually.of_forall fun _ => rfl)
    have hsub_b : (∫ r : ℝ, ν • (α r • DHeatCLM hc 0 θ (uq r) + α r • DHeatCLM hc 1 θ (uη r))) -
        (∫ r : ℝ, α r • centeredHeatVecL2CLM hc θ (b r)) =
        ∫ r : ℝ, (ν • (α r • DHeatCLM hc 0 θ (uq r) + α r • DHeatCLM hc 1 θ (uη r)) -
          α r • centeredHeatVecL2CLM hc θ (b r)) :=
      (integral_sub i_νqη ib').symm
    have i_tot : Integrable (fun r : ℝ =>
        ν • (α r • DHeatCLM hc 0 θ (uq r) + α r • DHeatCLM hc 1 θ (uη r)) -
          α r • centeredHeatVecL2CLM hc θ (b r)) :=
      (i_νqη.sub ib').congr (Eventually.of_forall fun _ => rfl)
    rw [hs_qη, hsm_ν, hsub_b, ← (P0 c).integral_comp_comm i_tot]
    refine integral_congr_ae (Eventually.of_forall fun r => ?_)
    dsimp only [Function.comp_apply]
    rw [← smul_add, smul_comm ν (α r), ← smul_sub, map_smul]
  dsimp [Z] at hZ_zero
  rw [heq1, heq2] at hZ_zero
  exact eq_neg_of_add_eq_zero_left hZ_zero

/-! ## 3. Real unit-window weak uniqueness on `Ioo 0 1` -/

lemma real_unit_weak_unique {c ν M_V B : ℝ} (hc : 0 < c) (hν : 0 < ν)
    (hMV : 0 ≤ M_V) (hB : 0 ≤ B)
    {u₀ uq uη b : ℝ → L2v c}
    (hu₀_sm : StronglyMeasurable u₀) (huq_sm : StronglyMeasurable uq)
    (huη_sm : StronglyMeasurable uη) (hb_sm : StronglyMeasurable b)
    {G_set : Set ℝ} (hG_sub : G_set ⊆ Ioo 0 1)
    (hG_ae : ∀ᵐ r ∂(volume.restrict (Ioo 0 1)), r ∈ G_set)
    (hG_props : ∀ r ∈ G_set,
      u₀ r ∈ divFree c ∧
      (∀ k : Fin 2, F8Ex.HasWeakCellDerivR c 0 (fun y => u₀ r y k) (fun y => uq r y k)) ∧
      (∀ k : Fin 2, F8Ex.HasWeakCellDerivR c 1 (fun y => u₀ r y k) (fun y => uη r y k)) ∧
      ‖u₀ r‖ ≤ B ∧ ‖uq r‖ ≤ B ∧ ‖uη r‖ ≤ B ∧
      ‖b r‖ ≤ M_V * ‖uq r‖ + M_V * ‖uη r‖ + 4 * M_V * ‖u₀ r‖)
    (hwk : ∀ (α : ℝ → ℝ), ContDiff ℝ ∞ α → HasCompactSupport α → tsupport α ⊆ Ioo 0 1 →
      ∀ (φ : B0579.Plane → ℝ) (hφ : UnforcedLeray.Sob.IsCylTest c φ),
        ∫ r : ℝ,
          (-deriv α r *
              ⟪cylSmoothToL2 (isCylSmooth_of_solTest (isRealSolCylTest_rotT hφ)), u₀ r⟫_ℝ +
            ν * α r *
              (⟪cylSmoothToL2 ((isCylSmooth_of_solTest (isRealSolCylTest_rotT hφ)).dir
                  (B0579.dir 0)), uq r⟫_ℝ +
                ⟪cylSmoothToL2 ((isCylSmooth_of_solTest (isRealSolCylTest_rotT hφ)).dir
                  (B0579.dir 1)), uη r⟫_ℝ) +
            α r *
              ⟪cylSmoothToL2 (isCylSmooth_of_solTest (isRealSolCylTest_rotT hφ)), b r⟫_ℝ) = 0)
    (htrace : Tendsto (fun h : ℝ => h⁻¹ * ∫ r in Ioc 0 h, ‖u₀ r‖ ^ 2) (𝓝[>] 0) (𝓝 0)) :
    ∀ᵐ r ∂(volume.restrict (Ioo 0 1)), u₀ r = 0 := by
  have hint_of_bdd : ∀ {f : ℝ → L2v c} (hf : StronglyMeasurable f) (C : ℝ)
      (hbdd : ∀ r ∈ G_set, ‖f r‖ ≤ C), IntegrableOn f (Ioo 0 1) := by
    intro f hf C hbdd
    have hconst : IntegrableOn (fun _ : ℝ => max C 0) (Ioo 0 1) := by simp
    refine hconst.mono' hf.aestronglyMeasurable ?_
    filter_upwards [hG_ae] with r hr
    exact (hbdd r hr).trans (le_max_left C 0)
  have hu₀_int : IntegrableOn u₀ (Ioo 0 1) :=
    hint_of_bdd hu₀_sm B fun r hr => (hG_props r hr).2.2.2.1
  have huq_int : IntegrableOn uq (Ioo 0 1) :=
    hint_of_bdd huq_sm B fun r hr => (hG_props r hr).2.2.2.2.1
  have huη_int : IntegrableOn uη (Ioo 0 1) :=
    hint_of_bdd huη_sm B fun r hr => (hG_props r hr).2.2.2.2.2.1
  have hb_bdd : ∀ r ∈ G_set, ‖b r‖ ≤ 6 * M_V * B := by
    intro r hr
    obtain ⟨_, _, _, n0, nq, nη, nb⟩ := hG_props r hr
    have _ := hB
    have h1 : M_V * ‖uq r‖ ≤ M_V * B := mul_le_mul_of_nonneg_left nq hMV
    have h2 : M_V * ‖uη r‖ ≤ M_V * B := mul_le_mul_of_nonneg_left nη hMV
    have h3 : 4 * M_V * ‖u₀ r‖ ≤ 4 * M_V * B :=
      mul_le_mul_of_nonneg_left n0 (by positivity)
    linarith
  have hb_int : IntegrableOn b (Ioo 0 1) := hint_of_bdd hb_sm (6 * M_V * B) hb_bdd
  have hu₀_div : ∀ᵐ r ∂(volume.restrict (Ioo 0 1)), u₀ r ∈ divFree c := by
    filter_upwards [hG_ae] with r hr using (hG_props r hr).1
  let θSeq : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hθ_pos : ∀ n : ℕ, 0 < θSeq n := fun n => by dsimp [θSeq]; positivity
  have hθ_lim : Tendsto θSeq atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hwk_n : ∀ n : ℕ, UnforcedLeray.BochnerTime.HasWeakDerivTime 0 1
      (fun r => centeredHeatVecL2CLM hc (θSeq n) (u₀ r))
      (fun r => P0 c (ν • (DHeatCLM hc 0 (θSeq n) (uq r) + DHeatCLM hc 1 (θSeq n) (uη r)) -
        centeredHeatVecL2CLM hc (θSeq n) (b r))) :=
    fun n => hasWeakDerivTime_mollified hc (hθ_pos n) hu₀_int huq_int huη_int hb_int hu₀_div hwk
  have hae_all : ∀ᵐ r ∂(volume.restrict (Ioo 0 1)),
      r ∈ G_set ∧ ∀ n : ℕ, centeredHeatVecL2CLM hc (θSeq n) (u₀ r) = (hwk_n n).rep r :=
    hG_ae.and (ae_all_iff.2 fun n => (hwk_n n).ae_eq_rep)
  let S_good : Set ℝ :=
    G_set ∩ {r : ℝ | ∀ n : ℕ, centeredHeatVecL2CLM hc (θSeq n) (u₀ r) = (hwk_n n).rep r}
  have hS_sub : S_good ⊆ Ioo 0 1 := inter_subset_left.trans hG_sub
  have hS_ae : ∀ᵐ r ∂(volume.restrict (Ioo 0 1)), r ∈ S_good := hae_all
  have hS_null : volume (Ioo 0 1 \ S_good) = 0 := by
    rw [ae_restrict_iff' measurableSet_Ioo, ae_iff] at hS_ae
    have heq : {r : ℝ | ¬ (r ∈ Ioo 0 1 → r ∈ S_good)} = Ioo 0 1 \ S_good := by
      ext r; change ¬ (r ∈ Ioo 0 1 → r ∈ S_good) ↔ r ∈ Ioo 0 1 ∧ r ∉ S_good; tauto
    rwa [heq] at hS_ae
  have hG_null : volume (Ioo 0 1 \ G_set) = 0 :=
    measure_mono_null (sdiff_subset_sdiff_right inter_subset_left) hS_null
  let f_lim : ℝ → ℝ := fun r => -ν * (‖uq r‖ ^ 2 + ‖uη r‖ ^ 2) - ⟪b r, u₀ r⟫_ℝ
  have h_energy_lim : ∀ {s t : ℝ}, s ∈ S_good → t ∈ S_good → s ≤ t →
      ‖u₀ t‖ ^ 2 - ‖u₀ s‖ ^ 2 = 2 * ∫ r in Ioc s t, f_lim r := by
    intro s t hs ht hst
    have hs_Ioo : s ∈ Ioo 0 1 := hS_sub hs
    have ht_Ioo : t ∈ Ioo 0 1 := hS_sub ht
    have hs_Icc : s ∈ Icc 0 1 := Ioo_subset_Icc_self hs_Ioo
    have ht_Icc : t ∈ Icc 0 1 := Ioo_subset_Icc_self ht_Ioo
    have hIoc_sub : Ioc s t ⊆ Ioo 0 1 := fun r hr =>
      ⟨lt_trans hs_Ioo.1 hr.1, lt_of_le_of_lt hr.2 ht_Ioo.2⟩
    have hG_Ioc : ∀ᵐ r ∂(volume.restrict (Ioc s t)), r ∈ G_set := by
      rw [ae_restrict_iff' measurableSet_Ioc, ae_iff]
      have heq : {r : ℝ | ¬ (r ∈ Ioc s t → r ∈ G_set)} = Ioc s t \ G_set := by
        ext r; change ¬ (r ∈ Ioc s t → r ∈ G_set) ↔ r ∈ Ioc s t ∧ r ∉ G_set; tauto
      rw [heq]
      exact measure_mono_null (sdiff_subset_sdiff_left hIoc_sub) hG_null
    let F_n : ℕ → ℝ → ℝ := fun n r =>
      -ν * (‖centeredHeatVecL2CLM hc (θSeq n) (uq r)‖ ^ 2 +
          ‖centeredHeatVecL2CLM hc (θSeq n) (uη r)‖ ^ 2) -
        ⟪centeredHeatVecL2CLM hc (θSeq n) (b r), centeredHeatVecL2CLM hc (θSeq n) (u₀ r)⟫_ℝ
    have hid_n : ∀ n : ℕ,
        ‖centeredHeatVecL2CLM hc (θSeq n) (u₀ t)‖ ^ 2 -
          ‖centeredHeatVecL2CLM hc (θSeq n) (u₀ s)‖ ^ 2 =
        2 * ∫ r in Ioc s t, F_n n r := by
      intro n
      have hsq := (hwk_n n).norm_sq_sub' hs_Icc ht_Icc
      rw [← hs.2 n, ← ht.2 n, intervalIntegral.integral_of_le hst] at hsq
      refine hsq.trans (congrArg (2 * ·) (integral_congr_ae ?_))
      filter_upwards [hG_Ioc] with r hrG
      dsimp only [F_n]
      obtain ⟨hdiv_r, hweak_q, hweak_η, _⟩ := hG_props r hrG
      have huθ_P0 : P0 c (centeredHeatVecL2CLM hc (θSeq n) (u₀ r)) =
          centeredHeatVecL2CLM hc (θSeq n) (u₀ r) := by
        rw [← centeredHeatVecL2CLM_P0_comm hc (θSeq n) (u₀ r),
          UnforcedLeray.Cyl.P0_eq_self hdiv_r]
      rw [UnforcedLeray.Cyl.inner_P0_comm, huθ_P0, inner_sub_left, inner_smul_left,
        inner_add_left, inner_DHeatCLM_heat_weak hc (hθ_pos n) hweak_q,
        inner_DHeatCLM_heat_weak hc (hθ_pos n) hweak_η]
      simp only [conj_trivial]
      ring
    have htend_heat : ∀ x : L2v c,
        Tendsto (fun n => centeredHeatVecL2CLM hc (θSeq n) x) atTop (𝓝 x) := by
      intro x
      have h0 : centeredHeatVecL2CLM hc 0 x = x := by
        rw [centeredHeatVecL2CLM_eq_id_of_nonpos hc le_rfl]; rfl
      simpa [Function.comp_def, h0] using
        ((continuous_centeredHeatVecL2CLM_apply hc x).tendsto 0).comp hθ_lim
    have hlhs : Tendsto (fun n =>
        ‖centeredHeatVecL2CLM hc (θSeq n) (u₀ t)‖ ^ 2 -
          ‖centeredHeatVecL2CLM hc (θSeq n) (u₀ s)‖ ^ 2)
        atTop (𝓝 (‖u₀ t‖ ^ 2 - ‖u₀ s‖ ^ 2)) :=
      (((htend_heat (u₀ t)).norm.pow 2).sub ((htend_heat (u₀ s)).norm.pow 2))
    let C_dom : ℝ := ν * (2 * B ^ 2) + 6 * M_V * B ^ 2
    have hFn_meas : ∀ n : ℕ, AEStronglyMeasurable (F_n n) (volume.restrict (Ioc s t)) := by
      intro n
      have mq : StronglyMeasurable (fun r => centeredHeatVecL2CLM hc (θSeq n) (uq r)) :=
        (centeredHeatVecL2CLM hc (θSeq n)).continuous.comp_stronglyMeasurable huq_sm
      have mη : StronglyMeasurable (fun r => centeredHeatVecL2CLM hc (θSeq n) (uη r)) :=
        (centeredHeatVecL2CLM hc (θSeq n)).continuous.comp_stronglyMeasurable huη_sm
      have mb : StronglyMeasurable (fun r => centeredHeatVecL2CLM hc (θSeq n) (b r)) :=
        (centeredHeatVecL2CLM hc (θSeq n)).continuous.comp_stronglyMeasurable hb_sm
      have m0 : StronglyMeasurable (fun r => centeredHeatVecL2CLM hc (θSeq n) (u₀ r)) :=
        (centeredHeatVecL2CLM hc (θSeq n)).continuous.comp_stronglyMeasurable hu₀_sm
      have mF : StronglyMeasurable (F_n n) :=
        (stronglyMeasurable_const.mul ((mq.norm.pow 2).add (mη.norm.pow 2))).sub (mb.inner m0)
      exact mF.aestronglyMeasurable
    have hdom_int : Integrable (fun _ : ℝ => C_dom) (volume.restrict (Ioc s t)) := by simp
    have hFn_bdd : ∀ n : ℕ, ∀ᵐ r ∂(volume.restrict (Ioc s t)), ‖F_n n r‖ ≤ C_dom := by
      intro n
      filter_upwards [hG_Ioc] with r hrG
      obtain ⟨_, _, _, n0, nq, nη, _⟩ := hG_props r hrG
      have nb := hb_bdd r hrG
      have hle1 : ∀ x : L2v c, ‖centeredHeatVecL2CLM hc (θSeq n) x‖ ≤ ‖x‖ := fun x =>
        ((centeredHeatVecL2CLM hc (θSeq n)).le_opNorm x).trans
          (mul_le_of_le_one_left (norm_nonneg x) (norm_centeredHeatVecL2CLM_le_one_all hc _))
      have hq_sq : ‖centeredHeatVecL2CLM hc (θSeq n) (uq r)‖ ^ 2 ≤ B ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) ((hle1 (uq r)).trans nq) 2
      have hη_sq : ‖centeredHeatVecL2CLM hc (θSeq n) (uη r)‖ ^ 2 ≤ B ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) ((hle1 (uη r)).trans nη) 2
      have hb0_ip : ‖⟪centeredHeatVecL2CLM hc (θSeq n) (b r),
          centeredHeatVecL2CLM hc (θSeq n) (u₀ r)⟫_ℝ‖ ≤ 6 * M_V * B ^ 2 := by
        calc ‖⟪centeredHeatVecL2CLM hc (θSeq n) (b r),
              centeredHeatVecL2CLM hc (θSeq n) (u₀ r)⟫_ℝ‖
            ≤ ‖centeredHeatVecL2CLM hc (θSeq n) (b r)‖ *
                ‖centeredHeatVecL2CLM hc (θSeq n) (u₀ r)‖ := norm_inner_le_norm _ _
          _ ≤ (6 * M_V * B) * B := mul_le_mul ((hle1 (b r)).trans nb) ((hle1 (u₀ r)).trans n0)
              (norm_nonneg _) (by positivity)
          _ = 6 * M_V * B ^ 2 := by ring
      dsimp only [F_n, C_dom]
      have htri := norm_sub_le
        (-ν * (‖centeredHeatVecL2CLM hc (θSeq n) (uq r)‖ ^ 2 +
          ‖centeredHeatVecL2CLM hc (θSeq n) (uη r)‖ ^ 2))
        ⟪centeredHeatVecL2CLM hc (θSeq n) (b r), centeredHeatVecL2CLM hc (θSeq n) (u₀ r)⟫_ℝ
      have hv_norm : ‖-ν * (‖centeredHeatVecL2CLM hc (θSeq n) (uq r)‖ ^ 2 +
          ‖centeredHeatVecL2CLM hc (θSeq n) (uη r)‖ ^ 2)‖ ≤ ν * (2 * B ^ 2) := by
        rw [norm_mul, norm_neg, Real.norm_of_nonneg hν.le, Real.norm_of_nonneg (by positivity)]
        exact mul_le_mul_of_nonneg_left (by linarith) hν.le
      linarith
    have hFn_lim : ∀ᵐ r ∂(volume.restrict (Ioc s t)),
        Tendsto (fun n => F_n n r) atTop (𝓝 (f_lim r)) := by
      refine Eventually.of_forall fun r => ?_
      dsimp only [F_n, f_lim]
      exact (tendsto_const_nhds.mul
        (((htend_heat (uq r)).norm.pow 2).add ((htend_heat (uη r)).norm.pow 2))).sub
        (Filter.Tendsto.inner (htend_heat (b r)) (htend_heat (u₀ r)))
    have hrhs_int := tendsto_integral_of_dominated_convergence (fun _ => C_dom)
      hFn_meas hdom_int hFn_bdd hFn_lim
    have hrhs : Tendsto (fun n => 2 * ∫ r in Ioc s t, F_n n r) atTop
        (𝓝 (2 * ∫ r in Ioc s t, f_lim r)) := tendsto_const_nhds.mul hrhs_int
    have hlhs' : Tendsto (fun n => 2 * ∫ r in Ioc s t, F_n n r) atTop
        (𝓝 (‖u₀ t‖ ^ 2 - ‖u₀ s‖ ^ 2)) := by
      simpa only [hid_n] using hlhs
    exact tendsto_nhds_unique hlhs' hrhs
  let K : ℝ := M_V ^ 2 / ν + 8 * M_V + 1
  have hK_pos : 0 < K := by dsimp [K]; positivity
  have hf_lim_le : ∀ r ∈ G_set, 2 * f_lim r ≤ K * ‖u₀ r‖ ^ 2 := by
    intro r hrG
    obtain ⟨_, _, _, _, _, _, nb⟩ := hG_props r hrG
    have hip : -⟪b r, u₀ r⟫_ℝ ≤
        M_V * ‖uq r‖ * ‖u₀ r‖ + M_V * ‖uη r‖ * ‖u₀ r‖ + 4 * M_V * ‖u₀ r‖ ^ 2 := by
      have h1 : -⟪b r, u₀ r⟫_ℝ ≤ ‖b r‖ * ‖u₀ r‖ := by
        have := abs_real_inner_le_norm (b r) (u₀ r)
        linarith [(neg_le_abs _).trans this]
      have h2 : ‖b r‖ * ‖u₀ r‖ ≤
          (M_V * ‖uq r‖ + M_V * ‖uη r‖ + 4 * M_V * ‖u₀ r‖) * ‖u₀ r‖ :=
        mul_le_mul_of_nonneg_right nb (norm_nonneg _)
      linarith
    have hy_q : M_V * ‖uq r‖ * ‖u₀ r‖ - ν * ‖uq r‖ ^ 2 ≤ (M_V ^ 2 / (4 * ν)) * ‖u₀ r‖ ^ 2 := by
      have hsq : 0 ≤ ν * (‖uq r‖ - (M_V / (2 * ν)) * ‖u₀ r‖) ^ 2 := by positivity
      have hexp : ν * (‖uq r‖ - (M_V / (2 * ν)) * ‖u₀ r‖) ^ 2 =
          ν * ‖uq r‖ ^ 2 - M_V * ‖uq r‖ * ‖u₀ r‖ + (M_V ^ 2 / (4 * ν)) * ‖u₀ r‖ ^ 2 := by
        field_simp [hν.ne']; ring
      linarith
    have hy_η : M_V * ‖uη r‖ * ‖u₀ r‖ - ν * ‖uη r‖ ^ 2 ≤ (M_V ^ 2 / (4 * ν)) * ‖u₀ r‖ ^ 2 := by
      have hsq : 0 ≤ ν * (‖uη r‖ - (M_V / (2 * ν)) * ‖u₀ r‖) ^ 2 := by positivity
      have hexp : ν * (‖uη r‖ - (M_V / (2 * ν)) * ‖u₀ r‖) ^ 2 =
          ν * ‖uη r‖ ^ 2 - M_V * ‖uη r‖ * ‖u₀ r‖ + (M_V ^ 2 / (4 * ν)) * ‖u₀ r‖ ^ 2 := by
        field_simp [hν.ne']; ring
      linarith
    have hK_ge : M_V ^ 2 / ν + 8 * M_V ≤ K := by dsimp [K]; linarith
    have h3 : (M_V ^ 2 / ν + 8 * M_V) * ‖u₀ r‖ ^ 2 ≤ K * ‖u₀ r‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hK_ge (sq_nonneg _)
    have hdiv_eq : 2 * ((M_V ^ 2 / (4 * ν)) * ‖u₀ r‖ ^ 2 + (M_V ^ 2 / (4 * ν)) * ‖u₀ r‖ ^ 2) =
        (M_V ^ 2 / ν) * ‖u₀ r‖ ^ 2 := by ring
    dsimp only [f_lim]
    linarith
  have hu₀_sq_int : IntegrableOn (fun r => ‖u₀ r‖ ^ 2) (Ioo 0 1) := by
    have hconst : IntegrableOn (fun _ : ℝ => B ^ 2) (Ioo 0 1) := by simp
    refine hconst.mono' (hu₀_sm.norm.pow 2).aestronglyMeasurable ?_
    filter_upwards [hG_ae] with r hr
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hG_props r hr).2.2.2.1 2
  have hf_lim_int : ∀ {s t : ℝ}, s ∈ S_good → t ∈ S_good → s ≤ t →
      IntegrableOn f_lim (Ioc s t) := by
    intro s t hs ht _
    have hs_Ioo := hS_sub hs
    have ht_Ioo := hS_sub ht
    have hIoc_sub : Ioc s t ⊆ Ioo 0 1 := fun r hr =>
      ⟨lt_trans hs_Ioo.1 hr.1, lt_of_le_of_lt hr.2 ht_Ioo.2⟩
    have hG_Ioc : ∀ᵐ r ∂(volume.restrict (Ioc s t)), r ∈ G_set := by
      rw [ae_restrict_iff' measurableSet_Ioc, ae_iff]
      have heq : {r : ℝ | ¬ (r ∈ Ioc s t → r ∈ G_set)} = Ioc s t \ G_set := by
        ext r; change ¬ (r ∈ Ioc s t → r ∈ G_set) ↔ r ∈ Ioc s t ∧ r ∉ G_set; tauto
      rw [heq]
      exact measure_mono_null (sdiff_subset_sdiff_left hIoc_sub) hG_null
    let C_dom : ℝ := ν * (2 * B ^ 2) + 6 * M_V * B ^ 2
    have hconst : IntegrableOn (fun _ : ℝ => C_dom) (Ioc s t) := by simp
    have mf : StronglyMeasurable f_lim :=
      (stronglyMeasurable_const.mul ((huq_sm.norm.pow 2).add (huη_sm.norm.pow 2))).sub
        (hb_sm.inner hu₀_sm)
    refine hconst.mono' mf.aestronglyMeasurable ?_
    filter_upwards [hG_Ioc] with r hrG
    obtain ⟨_, _, _, n0, nq, nη, _⟩ := hG_props r hrG
    have nb := hb_bdd r hrG
    have hq_sq : ‖uq r‖ ^ 2 ≤ B ^ 2 := pow_le_pow_left₀ (norm_nonneg _) nq 2
    have hη_sq : ‖uη r‖ ^ 2 ≤ B ^ 2 := pow_le_pow_left₀ (norm_nonneg _) nη 2
    have hb0_ip : ‖⟪b r, u₀ r⟫_ℝ‖ ≤ 6 * M_V * B ^ 2 := by
      calc ‖⟪b r, u₀ r⟫_ℝ‖ ≤ ‖b r‖ * ‖u₀ r‖ := norm_inner_le_norm _ _
        _ ≤ (6 * M_V * B) * B := mul_le_mul nb n0 (norm_nonneg _) (by positivity)
        _ = 6 * M_V * B ^ 2 := by ring
    dsimp only [f_lim, C_dom]
    have htri := norm_sub_le (-ν * (‖uq r‖ ^ 2 + ‖uη r‖ ^ 2)) ⟪b r, u₀ r⟫_ℝ
    have hv_norm : ‖-ν * (‖uq r‖ ^ 2 + ‖uη r‖ ^ 2)‖ ≤ ν * (2 * B ^ 2) := by
      rw [norm_mul, norm_neg, Real.norm_of_nonneg hν.le, Real.norm_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_left (by linarith) hν.le
    linarith
  have h_energy_ineq : ∀ {s t : ℝ}, s ∈ S_good → t ∈ S_good → s ≤ t →
      ‖u₀ t‖ ^ 2 ≤ ‖u₀ s‖ ^ 2 + K * ∫ r in Ioc 0 t, ‖u₀ r‖ ^ 2 := by
    intro s t hs ht hst
    have hs_Ioo := hS_sub hs
    have ht_Ioo := hS_sub ht
    have hIoc_sub : Ioc s t ⊆ Ioo 0 1 := fun r hr =>
      ⟨lt_trans hs_Ioo.1 hr.1, lt_of_le_of_lt hr.2 ht_Ioo.2⟩
    have hIoc0t_eq : IntegrableOn (fun r => ‖u₀ r‖ ^ 2) (Ioc 0 t) := by
      rw [integrableOn_Ioc_iff_integrableOn_Ioo]
      exact hu₀_sq_int.mono_set (Ioo_subset_Ioo_right ht_Ioo.2.le)
    have hG_Ioc : ∀ᵐ r ∂(volume.restrict (Ioc s t)), r ∈ G_set := by
      rw [ae_restrict_iff' measurableSet_Ioc, ae_iff]
      have heq : {r : ℝ | ¬ (r ∈ Ioc s t → r ∈ G_set)} = Ioc s t \ G_set := by
        ext r; change ¬ (r ∈ Ioc s t → r ∈ G_set) ↔ r ∈ Ioc s t ∧ r ∉ G_set; tauto
      rw [heq]
      exact measure_mono_null (sdiff_subset_sdiff_left hIoc_sub) hG_null
    have hid := h_energy_lim hs ht hst
    have hle1 : ∫ r in Ioc s t, 2 * f_lim r ≤ ∫ r in Ioc s t, K * ‖u₀ r‖ ^ 2 := by
      refine integral_mono_ae ((hf_lim_int hs ht hst).const_mul 2)
        ((hu₀_sq_int.mono_set hIoc_sub).const_mul K) ?_
      filter_upwards [hG_Ioc] with r hrG using hf_lim_le r hrG
    have hle2 : ∫ r in Ioc s t, ‖u₀ r‖ ^ 2 ≤ ∫ r in Ioc 0 t, ‖u₀ r‖ ^ 2 :=
      setIntegral_mono_set hIoc0t_eq (Eventually.of_forall fun _ => sq_nonneg _)
        (Eventually.of_forall fun r hr => ⟨lt_trans hs_Ioo.1 hr.1, hr.2⟩)
    rw [integral_const_mul, integral_const_mul] at hle1
    have hle3 : K * ∫ r in Ioc s t, ‖u₀ r‖ ^ 2 ≤ K * ∫ r in Ioc 0 t, ‖u₀ r‖ ^ 2 :=
      mul_le_mul_of_nonneg_left hle2 hK_pos.le
    linarith
  have h_gronwall_pt : ∀ t ∈ S_good, ‖u₀ t‖ ^ 2 ≤ K * ∫ r in Ioc 0 t, ‖u₀ r‖ ^ 2 := by
    intro t ht
    have ht_Ioo := hS_sub ht
    let R_t : ℝ := K * ∫ r in Ioc 0 t, ‖u₀ r‖ ^ 2
    have hev : ∀ᶠ h : ℝ in 𝓝[>] 0,
        ‖u₀ t‖ ^ 2 ≤ h⁻¹ * (∫ s in Ioc 0 h, ‖u₀ s‖ ^ 2) + R_t := by
      have hmem : Ioo 0 t ∈ 𝓝[>] (0 : ℝ) :=
        Filter.inter_mem self_mem_nhdsWithin (nhdsWithin_le_nhds (Iio_mem_nhds ht_Ioo.1))
      filter_upwards [hmem] with h hh
      have hIoc_sub : Ioc 0 h ⊆ Ioo 0 1 := fun s hs =>
        ⟨hs.1, lt_trans (lt_of_le_of_lt hs.2 hh.2) ht_Ioo.2⟩
      have hS_Ioc : ∀ᵐ s ∂(volume.restrict (Ioc 0 h)), s ∈ S_good := by
        rw [ae_restrict_iff' measurableSet_Ioc, ae_iff]
        have heq : {s : ℝ | ¬ (s ∈ Ioc 0 h → s ∈ S_good)} = Ioc 0 h \ S_good := by
          ext s; change ¬ (s ∈ Ioc 0 h → s ∈ S_good) ↔ s ∈ Ioc 0 h ∧ s ∉ S_good; tauto
        rw [heq]
        exact measure_mono_null (sdiff_subset_sdiff_left hIoc_sub) hS_null
      have hint_h : IntegrableOn (fun s => ‖u₀ s‖ ^ 2) (Ioc 0 h) :=
        hu₀_sq_int.mono_set hIoc_sub
      have hconst_L : IntegrableOn (fun _ : ℝ => ‖u₀ t‖ ^ 2) (Ioc 0 h) := by simp
      have hconst_R : IntegrableOn (fun _ : ℝ => R_t) (Ioc 0 h) := by simp
      have hint_le : ∫ s in Ioc 0 h, ‖u₀ t‖ ^ 2 ≤
          ∫ s in Ioc 0 h, (‖u₀ s‖ ^ 2 + R_t) := by
        refine integral_mono_ae hconst_L (hint_h.add hconst_R) ?_
        filter_upwards [hS_Ioc, ae_restrict_mem measurableSet_Ioc] with s hsS hs_mem
        exact h_energy_ineq hsS ht (hs_mem.2.trans hh.2.le)
      rw [setIntegral_const, integral_add hint_h hconst_R, setIntegral_const,
        Real.volume_real_Ioc_of_le hh.1.le, sub_zero, smul_eq_mul, smul_eq_mul] at hint_le
      have hinv := mul_le_mul_of_nonneg_left hint_le (inv_nonneg.2 hh.1.le)
      have hmul1 : h⁻¹ * (h * ‖u₀ t‖ ^ 2) = ‖u₀ t‖ ^ 2 := by field_simp [hh.1.ne']
      have hmul2 : h⁻¹ * ((∫ s in Ioc 0 h, ‖u₀ s‖ ^ 2) + h * R_t) =
          h⁻¹ * (∫ s in Ioc 0 h, ‖u₀ s‖ ^ 2) + R_t := by field_simp [hh.1.ne']
      linarith
    have hlim_R : Tendsto (fun h : ℝ => h⁻¹ * (∫ s in Ioc 0 h, ‖u₀ s‖ ^ 2) + R_t)
        (𝓝[>] 0) (𝓝 R_t) := by
      simpa only [zero_add] using htrace.add tendsto_const_nhds
    exact ge_of_tendsto hlim_R hev
  -- Grönwall via BochnerTime.integral_eq_sub_of_ae_hasDerivAt on [0, 1]
  let g : ℝ → ℝ := (Ioo (0 : ℝ) 1).indicator (fun r => ‖u₀ r‖ ^ 2)
  have hg_nonneg : ∀ r : ℝ, 0 ≤ g r := fun r =>
    indicator_nonneg (fun _ _ => sq_nonneg _) r
  have hg_Ioo : IntegrableOn g (Ioo 0 1) := by
    refine hu₀_sq_int.congr_fun (fun r hr => ?_) measurableSet_Ioo
    exact (indicator_of_mem hr (fun r => ‖u₀ r‖ ^ 2)).symm
  have hg_ii : IntervalIntegrable g volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).2 hg_Ioo
  let G : ℝ → ℝ := fun t => ∫ r in (0 : ℝ)..t, g r
  have hG_ac : AbsolutelyContinuousOnInterval G 0 1 :=
    UnforcedLeray.BochnerTime.absolutelyContinuousOnInterval_primitive hg_ii
      (left_mem_uIcc (a := 0) (b := 1))
  have hw_sm : ContDiff ℝ 1 (fun t : ℝ => Real.exp (-K * t)) :=
    Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)
  have hH_ac : AbsolutelyContinuousOnInterval (fun t => Real.exp (-K * t) * G t) 0 1 :=
    hw_sm.contDiffOn.absolutelyContinuousOnInterval.fun_mul hG_ac
  have hG_cont : ContinuousOn G (uIcc 0 1) := by
    rw [uIcc_of_le zero_le_one]
    exact UnforcedLeray.BochnerTime.continuousOn_primitive_Icc hg_Ioo
  let H' : ℝ → ℝ := fun t => Real.exp (-K * t) * (g t - K * G t)
  have hH'_ii : IntervalIntegrable H' volume 0 1 := by
    have hi_sub : IntervalIntegrable (fun t => g t - K * G t) volume 0 1 :=
      hg_ii.sub (hG_cont.intervalIntegrable.const_mul K)
    exact hi_sub.continuousOn_mul hw_sm.continuous.continuousOn
  have hH_deriv : ∀ᵐ t ∂volume, t ∈ uIcc 0 1 →
      HasDerivAt (fun s => Real.exp (-K * s) * G s) (H' t) t := by
    filter_upwards [hg_ii.ae_hasDerivAt_integral] with t ht hmem
    have hdG : HasDerivAt G (g t) t := ht hmem 0 left_mem_uIcc
    have hdw : HasDerivAt (fun s => Real.exp (-K * s)) (Real.exp (-K * t) * (-K)) t :=
      (((hasDerivAt_id t).const_mul (-K)).exp).congr_deriv (by simp)
    exact (hdw.mul hdG).congr_deriv (by dsimp [H']; ring)
  have hftc := UnforcedLeray.BochnerTime.integral_eq_sub_of_ae_hasDerivAt hH_ac hH_deriv hH'_ii
  have hG0 : G 0 = 0 := intervalIntegral.integral_same
  have hS_Ioc01 : ∀ᵐ t ∂(volume.restrict (Ioc 0 1)), t ∈ S_good := by
    have h1 : ∀ᵐ t ∂volume, t ≠ (1 : ℝ) := by simp [ae_iff, measure_singleton]
    rw [ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [(ae_restrict_iff' measurableSet_Ioo).1 hS_ae, h1] with t ht ht1 hmem
    exact ht ⟨hmem.1, lt_of_le_of_ne hmem.2 ht1⟩
  have hH'_nonpos : ∀ᵐ t ∂(volume.restrict (Ioc 0 1)), H' t ≤ 0 := by
    filter_upwards [hS_Ioc01] with t htS
    have ht_Ioo := hS_sub htS
    have hgt : g t = ‖u₀ t‖ ^ 2 := indicator_of_mem ht_Ioo _
    have hGt : G t = ∫ r in Ioc 0 t, ‖u₀ r‖ ^ 2 := by
      dsimp [G]
      rw [intervalIntegral.integral_of_le ht_Ioo.1.le,
        integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
      refine setIntegral_congr_fun measurableSet_Ioo fun r hr => ?_
      exact indicator_of_mem (s := Ioo 0 1) ⟨hr.1, lt_trans hr.2 ht_Ioo.2⟩
        (fun s => ‖u₀ s‖ ^ 2)
    have hle : g t - K * G t ≤ 0 := by
      rw [hgt, hGt]
      linarith [h_gronwall_pt t htS]
    exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le hle
  have hint_nonpos : ∫ t in (0 : ℝ)..1, H' t ≤ 0 := by
    rw [intervalIntegral.integral_of_le zero_le_one]
    have hi_Ioc : IntegrableOn H' (Ioc 0 1) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1 hH'_ii
    calc ∫ t in Ioc 0 1, H' t ≤ ∫ _ in Ioc 0 1, (0 : ℝ) :=
          integral_mono_ae hi_Ioc (by simp) hH'_nonpos
      _ = 0 := by simp
  have hG1_nonneg : 0 ≤ G 1 := by
    dsimp [G]
    rw [intervalIntegral.integral_of_le zero_le_one]
    exact setIntegral_nonneg measurableSet_Ioc fun r _ => hg_nonneg r
  have hG1_zero : G 1 = 0 := by
    rw [hG0, mul_zero, sub_zero] at hftc
    have hexp_pos : 0 < Real.exp (-K * 1) := Real.exp_pos _
    have hprod_le : Real.exp (-K * 1) * G 1 ≤ 0 := hftc ▸ hint_nonpos
    nlinarith
  have hg_int_zero : ∫ r in Ioo (0 : ℝ) 1, g r = 0 := by
    dsimp [G] at hG1_zero
    rwa [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo] at hG1_zero
  have hg_ae_zero : g =ᵐ[volume.restrict (Ioo 0 1)] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae (Eventually.of_forall hg_nonneg) hg_Ioo).1 hg_int_zero
  filter_upwards [hg_ae_zero, ae_restrict_mem measurableSet_Ioo] with r hgr hr_mem
  have hsq0 : ‖u₀ r‖ ^ 2 = 0 := by
    have h := hgr
    dsimp [g] at h
    rwa [indicator_of_mem hr_mem] at h
  exact norm_eq_zero.1 (sq_eq_zero_iff.1 hsq0)

/-! ## 4. Windowed `flatBv` measurability/periodicity and 1D weak identity extraction -/

private lemma fderiv_periodic_plane {c : ℝ} {f : B0579.Plane → ℝ}
    (hf : ContDiff ℝ ∞ f) (hper : ∀ z : B0579.Plane, f (z.1 + c, z.2) = f z)
    (d : ℝ × ℝ) (z : B0579.Plane) :
    fderiv ℝ f (z.1 + c, z.2) d = fderiv ℝ f z d := by
  have hshift : HasFDerivAt (fun w : B0579.Plane => w + (c, (0 : ℝ)))
      (ContinuousLinearMap.id ℝ B0579.Plane) z := by
    simpa using (hasFDerivAt_id z).add_const (c, (0 : ℝ))
  have hdiff : DifferentiableAt ℝ f (z + (c, (0 : ℝ))) :=
    (hf.differentiable (by simp)).differentiableAt
  have hcomp := hdiff.hasFDerivAt.comp z hshift
  have hfun : (f ∘ fun w : B0579.Plane => w + (c, (0 : ℝ))) = f := by
    funext w
    change f (w.1 + c, w.2 + 0) = f w
    rw [add_zero, hper w]
  rw [hfun] at hcomp
  have heq : fderiv ℝ f z = fderiv ℝ f (z + (c, (0 : ℝ))) := by
    simpa using hcomp.fderiv
  have hz : (z.1 + c, z.2) = z + (c, (0 : ℝ)) := by ext <;> simp
  rw [hz, ← heq]

lemma window_flatBv_props {dm dp : ℝ} {p : Params} {d σ : ℝ}
    (hreg : BgRegime p d dm dp) (hσ : 0 ≤ σ)
    {δ δq δη : CProf}
    (hsm0 : StronglyMeasurable δ) (hsmq : StronglyMeasurable δq) (hsmη : StronglyMeasurable δη)
    (hper0 : QPeriodic p.c δ) (hperq : QPeriodic p.c δq) (hperη : QPeriodic p.c δη) :
    let S_win : Set Coord := Ioo σ (σ + 1) ×ˢ univ
    let b_win : CProf := S_win.indicator (flatBv p.train δ δq δη)
    StronglyMeasurable b_win ∧ QPeriodic p.c b_win ∧
      ∀ r ∈ Ioo (0 : ℝ) 1, ∀ y : B0579.Plane,
        b_win (σ + r, y) =
          F8Ex.complexBvSlice (F8Ex.shiftedDrift p σ r)
            (F8U.slice δ (σ + r)) (F8U.slice δq (σ + r)) (F8U.slice δη (σ + r)) y := by
  intro S_win b_win
  let V := F8Ex.shiftedDrift p σ
  have hV : F8Ex.IsSmoothBUCDrift p.c V := F8Ex.isSmoothBUCDrift_shiftedDrift hreg hσ
  have hS_meas : MeasurableSet S_win := measurableSet_Ioo.prod MeasurableSet.univ
  let FV : Coord → F8Ex.RMerid := fun w => V w.1 w.2
  have hFV_sm : ContDiffOn ℝ ∞ FV F8Ex.strip0 :=
    hV.smooth.mono (prod_mono Ioo_subset_Icc_self Subset.rfl)
  let sh_sub : Coord → Coord := fun x => (x.1 - σ, x.2)
  have hsh_cont : Continuous sh_sub := (continuous_fst.sub continuous_const).prodMk continuous_snd
  have hsh_maps : MapsTo sh_sub S_win F8Ex.strip0 := fun x hx =>
    ⟨⟨by linarith [hx.1.1], by linarith [hx.1.2]⟩, trivial⟩
  have htr_eq : ∀ x ∈ S_win, ∀ z : B0579.Plane, p.train.v x.1 z = V (x.1 - σ) z := by
    intro x _ z
    dsimp [V, F8Ex.shiftedDrift, F8Ex.shiftedDriftTrain]
    rw [add_sub_cancel]
  have hfderiv_eq : ∀ x ∈ S_win, ∀ (i : Fin 2) (dir_p : B0579.Plane),
      fderiv ℝ (fun z => p.train.v x.1 z i) x.2 dir_p =
        F8Ex.πR i (fderiv ℝ FV (sh_sub x) ((0 : ℝ), dir_p)) := by
    intro x hx i dir_p
    have hy : sh_sub x ∈ F8Ex.strip0 := hsh_maps hx
    have hdFV : DifferentiableAt ℝ FV (sh_sub x) :=
      (hFV_sm.contDiffAt (F8Ex.isOpen_strip0.mem_nhds hy)).differentiableAt (by simp)
    have hin : HasFDerivAt (fun z : B0579.Plane => ((x.1 - σ, (0 : B0579.Plane)) : Coord) +
        ContinuousLinearMap.inr ℝ ℝ B0579.Plane z)
        (ContinuousLinearMap.inr ℝ ℝ B0579.Plane) x.2 :=
      ((ContinuousLinearMap.inr ℝ ℝ B0579.Plane).hasFDerivAt).const_add (x.1 - σ, (0 : B0579.Plane))
    have hin' : HasFDerivAt (fun z : B0579.Plane => ((x.1 - σ, z) : Coord))
        (ContinuousLinearMap.inr ℝ ℝ B0579.Plane) x.2 := by
      refine hin.congr_of_eventuallyEq (Eventually.of_forall fun z => ?_)
      ext <;> simp
    have hcomp := ((F8Ex.πR i).hasFDerivAt.comp (sh_sub x) hdFV.hasFDerivAt).comp x.2 hin'
    have hcomp' : HasFDerivAt (fun z : B0579.Plane => p.train.v x.1 z i)
        (((F8Ex.πR i).comp (fderiv ℝ FV (sh_sub x))).comp (ContinuousLinearMap.inr ℝ ℝ B0579.Plane))
        x.2 :=
      hcomp.congr_of_eventuallyEq (Eventually.of_forall fun z => by
        dsimp [FV]; rw [htr_eq x hx z]; rfl)
    rw [hcomp'.fderiv]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · -- StronglyMeasurable b_win
    have hm_coord : ∀ i : Fin 2, Measurable (fun x : Coord => b_win x i) := by
      intro i
      have h_ind_real : ∀ {A : Coord → ℝ}, ContinuousOn A S_win →
          Measurable (S_win.indicator A) := by
        intro A hA
        have hpw : S_win.indicator A = S_win.piecewise A 0 := by
          funext x; by_cases hx : x ∈ S_win <;> simp [hx, Set.piecewise]
        rw [hpw]
        exact hA.measurable_piecewise continuousOn_const hS_meas
      have h_mul1 : ∀ {A : Coord → ℝ} (hA : ContinuousOn A S_win) {w : CProf}
          (hw : StronglyMeasurable w) (j : Fin 2),
          Measurable (fun x : Coord => S_win.indicator (fun y => (A y : ℂ) * w y j) x) := by
        intro A hA w hw j
        have heq : (fun x : Coord => S_win.indicator (fun y => (A y : ℂ) * w y j) x) =
            fun x => ((S_win.indicator A x : ℝ) : ℂ) *
              ((EuclideanSpace.proj j : CMerid →L[ℂ] ℂ) (w x)) := by
          funext x; by_cases hx : x ∈ S_win <;> simp [hx]
        rw [heq]
        exact (Complex.measurable_ofReal.comp (h_ind_real hA)).mul
          (((EuclideanSpace.proj j : CMerid →L[ℂ] ℂ).continuous.comp_stronglyMeasurable hw).measurable)
      have h_mul2 : ∀ {A : Coord → ℝ} (hA : ContinuousOn A S_win) {w : CProf}
          (hw : StronglyMeasurable w) (j : Fin 2),
          Measurable (fun x : Coord => S_win.indicator (fun y => w y j * (A y : ℂ)) x) := by
        intro A hA w hw j
        have heq : (fun x : Coord => S_win.indicator (fun y => w y j * (A y : ℂ)) x) =
            fun x => S_win.indicator (fun y => (A y : ℂ) * w y j) x := by
          funext x; by_cases hx : x ∈ S_win <;> simp [hx, mul_comm]
        rw [heq]; exact h_mul1 hA hw j
      have hc_v : ∀ k : Fin 2, ContinuousOn (fun x : Coord => p.train.v x.1 x.2 k) S_win := by
        intro k
        have hc0 : ContinuousOn (fun x : Coord => FV (sh_sub x) k) S_win :=
          ((F8Ex.πR k).continuous.comp_continuousOn
            (hFV_sm.continuousOn.comp hsh_cont.continuousOn hsh_maps))
        exact hc0.congr fun x hx => congrArg (fun v => v k) (htr_eq x hx x.2)
      have hc_dv : ∀ (dir_p : B0579.Plane),
          ContinuousOn (fun x : Coord => fderiv ℝ (fun z => p.train.v x.1 z i) x.2 dir_p) S_win := by
        intro dir_p
        have hd_sm := F8Ex.contDiffOn_fderiv_dir hFV_sm ((0 : ℝ), dir_p)
        have hc0 : ContinuousOn
            (fun x : Coord => F8Ex.πR i (fderiv ℝ FV (sh_sub x) ((0 : ℝ), dir_p))) S_win :=
          (F8Ex.πR i).continuous.comp_continuousOn
            (hd_sm.continuousOn.comp hsh_cont.continuousOn hsh_maps)
        exact hc0.congr fun x hx => hfderiv_eq x hx i dir_p
      have heq_bi : (fun x : Coord => b_win x i) = fun x =>
          S_win.indicator (fun y => ((p.train.v y.1 y.2 0 : ℝ) : ℂ) * δq y i) x +
          S_win.indicator (fun y => ((p.train.v y.1 y.2 1 : ℝ) : ℂ) * δη y i) x +
          S_win.indicator (fun y =>
            δ y 0 * ((fderiv ℝ (fun z => p.train.v y.1 z i) y.2 ((1 : ℝ), (0 : ℝ)) : ℝ) : ℂ)) x +
          S_win.indicator (fun y =>
            δ y 1 * ((fderiv ℝ (fun z => p.train.v y.1 z i) y.2 ((0 : ℝ), (1 : ℝ)) : ℝ) : ℂ)) x := by
        funext x
        by_cases hx : x ∈ S_win
        · simp [b_win, hx, flatBv]
        · simp [b_win, hx]
      rw [heq_bi]
      exact (((h_mul1 (hc_v 0) hsmq i).add (h_mul1 (hc_v 1) hsmη i)).add
        (h_mul2 (hc_dv ((1 : ℝ), (0 : ℝ))) hsm0 0)).add
        (h_mul2 (hc_dv ((0 : ℝ), (1 : ℝ))) hsm0 1)
    have hm : Measurable b_win := by
      have heq : b_win = fun x => WithLp.toLp 2 (fun i : Fin 2 => b_win x i) := funext fun _ => rfl
      rw [heq]
      exact (PiLp.continuous_toLp 2 _).measurable.comp (measurable_pi_lambda _ hm_coord)
    exact hm.stronglyMeasurable
  · -- QPeriodic p.c b_win
    filter_upwards [hper0, hperq, hperη, ae_restrict_mem QPerHalf.measurableSet_pos]
      with x hx0 hxq hxη _
    by_cases hxS : x ∈ S_win
    · have hqS : qShift p.c x ∈ S_win := ⟨hxS.1, trivial⟩
      dsimp only [b_win]
      rw [indicator_of_mem hqS, indicator_of_mem hxS]
      have hs_nn : 0 ≤ x.1 := le_trans hσ hxS.1.1.le
      have hv_sm : ∀ i : Fin 2, ContDiff ℝ ∞ (fun z : B0579.Plane => p.train.v x.1 z i) := by
        intro i
        have hr_mem : x.1 - σ ∈ Icc (0 : ℝ) 2 := ⟨by linarith [hxS.1.1], by linarith [hxS.1.2]⟩
        have hVr : ContDiff ℝ ∞ (V (x.1 - σ)) := by
          have hc := hV.smooth.comp (contDiff_const.prodMk contDiff_id).contDiffOn
            (s := univ) (fun w _ => ⟨hr_mem, mem_univ w⟩)
          exact contDiffOn_univ.1 hc
        have hfn : (fun z : B0579.Plane => p.train.v x.1 z i) =
            fun z => F8Ex.πR i (V (x.1 - σ) z) := by
          funext z; rw [htr_eq x hxS z]; rfl
        rw [hfn]
        exact (F8Ex.πR i).contDiff.comp hVr
      ext i
      simp only [flatBv, qShift]
      change ((p.train.v x.1 (x.2.1 + p.c, x.2.2) 0 : ℝ) : ℂ) * δq (qShift p.c x) i +
          ((p.train.v x.1 (x.2.1 + p.c, x.2.2) 1 : ℝ) : ℂ) * δη (qShift p.c x) i +
          δ (qShift p.c x) 0 *
            ((fderiv ℝ (fun z => p.train.v x.1 z i) (x.2.1 + p.c, x.2.2) ((1 : ℝ), (0 : ℝ)) : ℝ) : ℂ) +
          δ (qShift p.c x) 1 *
            ((fderiv ℝ (fun z => p.train.v x.1 z i) (x.2.1 + p.c, x.2.2) ((0 : ℝ), (1 : ℝ)) : ℝ) : ℂ) = _
      have hp_v := p.train.isTrain.periodic_v x.1 hs_nn x.2
      have hp_d0 := fderiv_periodic_plane (hv_sm i)
        (fun w => congrArg (fun v => v i) (p.train.isTrain.periodic_v x.1 hs_nn w))
        ((1 : ℝ), (0 : ℝ)) x.2
      have hp_d1 := fderiv_periodic_plane (hv_sm i)
        (fun w => congrArg (fun v => v i) (p.train.isTrain.periodic_v x.1 hs_nn w))
        ((0 : ℝ), (1 : ℝ)) x.2
      rw [hp_v, hp_d0, hp_d1, hx0, hxq, hxη]
    · have hqS : qShift p.c x ∉ S_win := fun hm => hxS ⟨hm.1, trivial⟩
      dsimp only [b_win]
      rw [indicator_of_notMem hqS, indicator_of_notMem hxS]
  · -- Slice formula on r ∈ Ioo 0 1
    intro r hr y
    have hxS : ((σ + r, y) : Coord) ∈ S_win := ⟨⟨by linarith [hr.1], by linarith [hr.2]⟩, trivial⟩
    dsimp only [b_win]
    rw [indicator_of_mem hxS]
    ext i
    simp [flatBv, F8Ex.complexBvSlice, F8Ex.shiftedDrift, F8Ex.shiftedDriftTrain, F8U.slice]

private lemma hasWeakCellDerivR_congr_ae {c : ℝ} {j : Fin 2}
    {φ₁ φ₂ g₁ g₂ : B0579.Plane → ℝ}
    (hφ : φ₁ =ᵐ[cellμ c] φ₂) (hg : g₁ =ᵐ[cellμ c] g₂)
    (h : F8Ex.HasWeakCellDerivR c j φ₁ g₁) :
    F8Ex.HasWeakCellDerivR c j φ₂ g₂ := by
  have hφ' : φ₁ =ᵐ[volume.restrict (B0579.cell c)] φ₂ := by
    rwa [b0579_cell_eq_cyl_cell]
  have hg' : g₁ =ᵐ[volume.restrict (B0579.cell c)] g₂ := by
    rwa [b0579_cell_eq_cyl_cell]
  refine ⟨fun ψ hψ => ?_, fun ψ hψ => ?_⟩
  · obtain ⟨i1, i2⟩ := h.1 ψ hψ
    refine ⟨i1.congr_fun_ae ?_, i2.congr_fun_ae ?_⟩
    · filter_upwards [hφ'] with y hy; rw [hy]
    · filter_upwards [hg'] with y hy; rw [hy]
  · have e1 : ∫ y in B0579.cell c, φ₂ y * B0579.pd j ψ y =
        ∫ y in B0579.cell c, φ₁ y * B0579.pd j ψ y := by
      refine integral_congr_ae ?_
      filter_upwards [hφ'.symm] with y hy; rw [hy]
    have e2 : ∫ y in B0579.cell c, g₂ y * ψ y = ∫ y in B0579.cell c, g₁ y * ψ y := by
      refine integral_congr_ae ?_
      filter_upwards [hg'.symm] with y hy; rw [hy]
    rw [e1, e2, h.2 ψ hψ]

private lemma isRealCellSolenoidal_congr_ae {c : ℝ}
    {f₁ f₂ : B0579.Plane → F8Ex.RMerid}
    (hf : f₁ =ᵐ[cellμ c] f₂)
    (h : F8Ex.IsRealCellSolenoidal c f₁) :
    F8Ex.IsRealCellSolenoidal c f₂ := by
  have hf' : f₁ =ᵐ[volume.restrict (B0579.cell c)] f₂ := by rwa [b0579_cell_eq_cyl_cell]
  intro ψ hψ
  obtain ⟨hint, hzero⟩ := h ψ hψ
  have heq : (fun y => f₁ y 0 * B0579.pd 0 ψ y + f₁ y 1 * B0579.pd 1 ψ y) =ᵐ[
      volume.restrict (B0579.cell c)]
      fun y => f₂ y 0 * B0579.pd 0 ψ y + f₂ y 1 * B0579.pd 1 ψ y := by
    filter_upwards [hf'] with y hy; rw [hy]
  exact ⟨hint.congr_fun_ae heq, (integral_congr_ae heq.symm).trans hzero⟩

/-- Unified real/imaginary projection application of `real_unit_weak_unique` to `δ`. -/
lemma proj_slice_zero_ae {dm dp : ℝ} {p : Params} {d σ B : ℝ}
    (hreg : BgRegime p d dm dp) (hσ : 0 ≤ σ) (hB : 0 ≤ B)
    {δ δq δη : CProf}
    (hsm_δ : StronglyMeasurable δ) (hsm_δq : StronglyMeasurable δq)
    (hsm_δη : StronglyMeasurable δη)
    (hper_δ : QPeriodic p.c δ) (hper_δq : QPeriodic p.c δq) (hper_δη : QPeriodic p.c δη)
    (hslice_bdd : ∀ᵐ t ∂volume, t ∈ Ioo σ (σ + 1) →
      sliceH1Norm p.c δ δq δη t ≤ ENNReal.ofReal B)
    (hslice_dat : ∀ᵐ t ∂volume, t ∈ Ioo σ (σ + 1) →
      F8U.IsCylH1Datum p.c (F8U.slice δ t) (F8U.slice δq t) (F8U.slice δη t))
    (heq : ∀ Ψ, IsPlanarSolTest Ψ →
      (∀ i, tsupport (fun x => Ψ x i) ⊆ Ioo σ (σ + 1) ×ˢ univ) →
      Integrable (fun x => ∑ i : Fin 2, δ x i * meridTranspose p.ν Ψ x i) ∧
        Integrable (cdot (flatBv p.train δ δq δη) Ψ) ∧
        ∫ x, (∑ i : Fin 2, δ x i * meridTranspose p.ν Ψ x i +
            cdot (flatBv p.train δ δq δη) Ψ x) = 0)
    (htrace : Tendsto (fun h : ℝ => h⁻¹ *
      ∫ t in Ioc σ (σ + h), (F8U.cellL2 p.c (F8U.slice δ t)).toReal ^ 2)
      (𝓝[>] 0) (𝓝 0))
    (L : CMerid →L[ℝ] F8Ex.RMerid) (sc : ℂ →L[ℝ] ℝ)
    (hL_coord : ∀ (z : CMerid) (k : Fin 2), L z k = sc (z k))
    (hsc_mul_r : ∀ (w : ℂ) (a : ℝ), sc (w * (a : ℂ)) = sc w * a)
    (hsc_mul_l : ∀ (a : ℝ) (w : ℂ), sc ((a : ℂ) * w) = a * sc w)
    (hL_norm : ∀ z : CMerid, ‖L z‖ ≤ ‖z‖)
    (hL_dat : ∀ {u uq uη : B0579.Plane → CMerid},
      F8U.IsCylH1Datum p.c u uq uη →
      F8Ex.IsRealCylH1Datum p.c (fun y => L (u y)) (fun y => L (uq y)) (fun y => L (uη y))) :
    ∀ᵐ s ∂volume, s ∈ Ioo σ (σ + 1) →
      (fun y => L (δ (s, y))) =ᵐ[cellμ p.c] 0 := by
  have hc : 0 < p.c := p.c_pos
  have hν : 0 < p.ν := p.ν_pos
  let V := F8Ex.shiftedDrift p σ
  have hV : F8Ex.IsSmoothBUCDrift p.c V := F8Ex.isSmoothBUCDrift_shiftedDrift hreg hσ
  obtain ⟨M_V, hMV, hV_sm, hV_b0, hV_b1⟩ := uniform_drift_bounds hV
  let S_win : Set Coord := Ioo σ (σ + 1) ×ˢ univ
  let b_win : CProf := S_win.indicator (flatBv p.train δ δq δη)
  obtain ⟨hsm_bwin0, hper_bwin0, hbwin_slice0⟩ :=
    window_flatBv_props hreg hσ hsm_δ hsm_δq hsm_δη hper_δ hper_δq hper_δη
  have hsm_bwin : StronglyMeasurable b_win := hsm_bwin0
  have hper_bwin : QPeriodic p.c b_win := hper_bwin0
  have hbwin_slice : ∀ r ∈ Ioo (0 : ℝ) 1, ∀ y : B0579.Plane,
      b_win (σ + r, y) = F8Ex.complexBvSlice (F8Ex.shiftedDrift p σ r)
        (F8U.slice δ (σ + r)) (F8U.slice δq (σ + r)) (F8U.slice δη (σ + r)) y := hbwin_slice0
  let sh_add : Coord → Coord := fun w => (σ + w.1, w.2)
  have hsh_meas : Measurable sh_add := (measurable_const.add measurable_fst).prodMk measurable_snd
  let u₀ : ℝ → L2v p.c :=
    UnforcedLeray.BochnerTime.toPathLq 2 (cellμ p.c) (fun w => L (δ (sh_add w)))
  let uq : ℝ → L2v p.c :=
    UnforcedLeray.BochnerTime.toPathLq 2 (cellμ p.c) (fun w => L (δq (sh_add w)))
  let uη : ℝ → L2v p.c :=
    UnforcedLeray.BochnerTime.toPathLq 2 (cellμ p.c) (fun w => L (δη (sh_add w)))
  let b : ℝ → L2v p.c :=
    UnforcedLeray.BochnerTime.toPathLq 2 (cellμ p.c) (fun w => L (b_win (sh_add w)))
  have hu₀_sm : StronglyMeasurable u₀ :=
    UnforcedLeray.BochnerTime.stronglyMeasurable_toPathLq
      (L.continuous.comp_stronglyMeasurable (hsm_δ.comp_measurable hsh_meas))
  have huq_sm : StronglyMeasurable uq :=
    UnforcedLeray.BochnerTime.stronglyMeasurable_toPathLq
      (L.continuous.comp_stronglyMeasurable (hsm_δq.comp_measurable hsh_meas))
  have huη_sm : StronglyMeasurable uη :=
    UnforcedLeray.BochnerTime.stronglyMeasurable_toPathLq
      (L.continuous.comp_stronglyMeasurable (hsm_δη.comp_measurable hsh_meas))
  have hb_sm : StronglyMeasurable b :=
    UnforcedLeray.BochnerTime.stronglyMeasurable_toPathLq
      (L.continuous.comp_stronglyMeasurable (hsm_bwin.comp_measurable hsh_meas))
  -- Construct good age set G_set ⊆ Ioo 0 1
  have hae_s : ∀ᵐ s ∂volume, s ∈ Ioo σ (σ + 1) →
      sliceH1Norm p.c δ δq δη s ≤ ENNReal.ofReal B ∧
      F8U.IsCylH1Datum p.c (F8U.slice δ s) (F8U.slice δq s) (F8U.slice δη s) := by
    filter_upwards [hslice_bdd, hslice_dat] with s h1 h2 hs using ⟨h1 hs, h2 hs⟩
  have hae_r_unr : ∀ᵐ r ∂volume, σ + r ∈ Ioo σ (σ + 1) →
      sliceH1Norm p.c δ δq δη (σ + r) ≤ ENNReal.ofReal B ∧
      F8U.IsCylH1Datum p.c (F8U.slice δ (σ + r)) (F8U.slice δq (σ + r))
        (F8U.slice δη (σ + r)) :=
    (measurePreserving_add_left volume σ).quasiMeasurePreserving.ae hae_s
  let G_set : Set ℝ := {r : ℝ | r ∈ Ioo (0 : ℝ) 1 ∧
    sliceH1Norm p.c δ δq δη (σ + r) ≤ ENNReal.ofReal B ∧
    F8U.IsCylH1Datum p.c (F8U.slice δ (σ + r)) (F8U.slice δq (σ + r)) (F8U.slice δη (σ + r))}
  have hG_sub : G_set ⊆ Ioo 0 1 := fun _ hr => hr.1
  have hG_ae : ∀ᵐ r ∂(volume.restrict (Ioo 0 1)), r ∈ G_set := by
    rw [ae_restrict_iff' measurableSet_Ioo]
    filter_upwards [hae_r_unr] with r hr hr_mem
    exact ⟨hr_mem, hr ⟨by linarith [hr_mem.1], by linarith [hr_mem.2]⟩⟩
  have hL_slice_bv : ∀ r ∈ Ioo (0 : ℝ) 1, ∀ y : B0579.Plane,
      L (b_win (σ + r, y)) = F8Ex.realBvSlice (V r)
        (fun z => L (δ (σ + r, z))) (fun z => L (δq (σ + r, z)))
        (fun z => L (δη (σ + r, z))) y := by
    intro r hr y
    rw [hbwin_slice r hr y]
    ext i
    rw [hL_coord]
    dsimp [V, F8Ex.complexBvSlice, F8Ex.realBvSlice, F8U.slice]
    simp only [map_add, hsc_mul_l, hsc_mul_r, ← hL_coord]
  -- Properties on G_set
  have hG_props : ∀ r ∈ G_set,
      u₀ r ∈ divFree p.c ∧
      (∀ k : Fin 2, F8Ex.HasWeakCellDerivR p.c 0 (fun y => u₀ r y k) (fun y => uq r y k)) ∧
      (∀ k : Fin 2, F8Ex.HasWeakCellDerivR p.c 1 (fun y => u₀ r y k) (fun y => uη r y k)) ∧
      ‖u₀ r‖ ≤ B ∧ ‖uq r‖ ≤ B ∧ ‖uη r‖ ≤ B ∧
      ‖b r‖ ≤ M_V * ‖uq r‖ + M_V * ‖uη r‖ + 4 * M_V * ‖u₀ r‖ := by
    intro r ⟨hr_Ioo, hbdd_r, hdat_r⟩
    have hr_Icc : r ∈ Icc (0 : ℝ) 2 := ⟨hr_Ioo.1.le, by linarith [hr_Ioo.2]⟩
    have hrdat : F8Ex.IsRealCylH1Datum p.c
        (fun y => L (δ (σ + r, y))) (fun y => L (δq (σ + r, y)))
        (fun y => L (δη (σ + r, y))) := hL_dat hdat_r
    have hm0 : MemLp (fun y => L (δ (σ + r, y))) 2 (cellμ p.c) := by
      rw [← cellMeas_eq_cellμ]; exact hrdat.memL2.1
    have hmq : MemLp (fun y => L (δq (σ + r, y))) 2 (cellμ p.c) := by
      rw [← cellMeas_eq_cellμ]; exact hrdat.memL2.2.1
    have hmη : MemLp (fun y => L (δη (σ + r, y))) 2 (cellμ p.c) := by
      rw [← cellMeas_eq_cellμ]; exact hrdat.memL2.2.2
    have hu₀_eq : u₀ r = hm0.toLp _ := UnforcedLeray.BochnerTime.toPathLq_of_memLp hm0
    have huq_eq : uq r = hmq.toLp _ := UnforcedLeray.BochnerTime.toPathLq_of_memLp hmq
    have huη_eq : uη r = hmη.toLp _ := UnforcedLeray.BochnerTime.toPathLq_of_memLp hmη
    have hc0 : (fun y => L (δ (σ + r, y))) =ᵐ[cellμ p.c] u₀ r := by
      rw [hu₀_eq]; exact hm0.coeFn_toLp.symm
    have hcq : (fun y => L (δq (σ + r, y))) =ᵐ[cellμ p.c] uq r := by
      rw [huq_eq]; exact hmq.coeFn_toLp.symm
    have hcη : (fun y => L (δη (σ + r, y))) =ᵐ[cellμ p.c] uη r := by
      rw [huη_eq]; exact hmη.coeFn_toLp.symm
    have hdiv : u₀ r ∈ divFree p.c :=
      (mem_divFree_iff_solenoidal (u₀ r)).2 (isRealCellSolenoidal_congr_ae hc0 hrdat.solenoidal)
    have hwq : ∀ k : Fin 2,
        F8Ex.HasWeakCellDerivR p.c 0 (fun y => u₀ r y k) (fun y => uq r y k) := fun k =>
      hasWeakCellDerivR_congr_ae (hc0.mono fun _ h => congrArg (fun v => v k) h)
        (hcq.mono fun _ h => congrArg (fun v => v k) h) (hrdat.weak_q k)
    have hwη : ∀ k : Fin 2,
        F8Ex.HasWeakCellDerivR p.c 1 (fun y => u₀ r y k) (fun y => uη r y k) := fun k =>
      hasWeakCellDerivR_congr_ae (hc0.mono fun _ h => congrArg (fun v => v k) h)
        (hcη.mono fun _ h => congrArg (fun v => v k) h) (hrdat.weak_eta k)
    have hnorm_le_B : ∀ {W : CProf} (hm : MemLp (fun y => L (W (σ + r, y))) 2 (cellμ p.c))
        (hle : eLpNorm (fun z => W (σ + r, z)) 2 (volume.restrict (B0579.cell p.c)) ≤
          ENNReal.ofReal B),
        ‖hm.toLp (fun y => L (W (σ + r, y)))‖ ≤ B := by
      intro W hm hle
      rw [Lp.norm_toLp]
      have h1 : eLpNorm (fun y => L (W (σ + r, y))) 2 (cellμ p.c) ≤ ENNReal.ofReal B := by
        calc eLpNorm (fun y => L (W (σ + r, y))) 2 (cellμ p.c)
            ≤ eLpNorm (fun y => W (σ + r, y)) 2 (cellμ p.c) :=
              eLpNorm_mono fun y => hL_norm _
          _ = eLpNorm (fun y => W (σ + r, y)) 2 (volume.restrict (B0579.cell p.c)) := by
              rw [← cellMeas_eq_cellμ]
          _ ≤ ENNReal.ofReal B := hle
      exact (ENNReal.toReal_le_of_le_ofReal hB h1)
    have h0_le : eLpNorm (fun z => δ (σ + r, z)) 2 (volume.restrict (B0579.cell p.c)) ≤
        ENNReal.ofReal B :=
      (le_self_add.trans le_self_add).trans hbdd_r
    have hq_le : eLpNorm (fun z => δq (σ + r, z)) 2 (volume.restrict (B0579.cell p.c)) ≤
        ENNReal.ofReal B :=
      (le_add_self.trans le_self_add).trans hbdd_r
    have hη_le : eLpNorm (fun z => δη (σ + r, z)) 2 (volume.restrict (B0579.cell p.c)) ≤
        ENNReal.ofReal B :=
      le_add_self.trans hbdd_r
    have n0 : ‖u₀ r‖ ≤ B := hu₀_eq ▸ hnorm_le_B hm0 h0_le
    have nq : ‖uq r‖ ≤ B := huq_eq ▸ hnorm_le_B hmq hq_le
    have nη : ‖uη r‖ ≤ B := huη_eq ▸ hnorm_le_B hmη hη_le
    obtain ⟨hbv_lp, hbv_norm⟩ := memLp_and_norm_realBvSlice hMV (hV_sm r hr_Icc)
      (hV_b0 r hr_Icc) (hV_b1 r hr_Icc) (Lp.memLp (u₀ r)) (Lp.memLp (uq r)) (Lp.memLp (uη r))
    have hbv_ae : F8Ex.realBvSlice (V r) (u₀ r) (uq r) (uη r) =ᵐ[cellμ p.c]
        fun y => L (b_win (σ + r, y)) := by
      filter_upwards [hc0.symm, hcq.symm, hcη.symm] with y e0 eq eη
      rw [hL_slice_bv r hr_Ioo y]
      dsimp only [F8Ex.realBvSlice]
      rw [e0, eq, eη]
    have hmb : MemLp (fun y => L (b_win (σ + r, y))) 2 (cellμ p.c) := hbv_lp.ae_eq hbv_ae
    have hb_eq : b r = hbv_lp.toLp (F8Ex.realBvSlice (V r) (u₀ r) (uq r) (uη r)) := by
      change UnforcedLeray.BochnerTime.toPathLq 2 (cellμ p.c) (fun w => L (b_win (sh_add w))) r = _
      rw [UnforcedLeray.BochnerTime.toPathLq_of_memLp hmb]
      exact (MemLp.toLp_eq_toLp_iff hmb hbv_lp).2 hbv_ae.symm
    have htoLp_self : ∀ f : L2v p.c, (Lp.memLp f).toLp f = f := fun f =>
      Lp.toLp_coeFn f (Lp.memLp f)
    rw [htoLp_self (u₀ r), htoLp_self (uq r), htoLp_self (uη r)] at hbv_norm
    exact ⟨hdiv, hwq, hwη, n0, nq, nη, hb_eq ▸ hbv_norm⟩
  -- 1D weak identity on Ioo 0 1
  have hwk_1d : ∀ (α : ℝ → ℝ), ContDiff ℝ ∞ α → HasCompactSupport α → tsupport α ⊆ Ioo 0 1 →
      ∀ (φ : B0579.Plane → ℝ) (hφ_sob : UnforcedLeray.Sob.IsCylTest p.c φ),
        ∫ r : ℝ,
          (-deriv α r *
              ⟪cylSmoothToL2 (isCylSmooth_of_solTest (isRealSolCylTest_rotT hφ_sob)), u₀ r⟫_ℝ +
            p.ν * α r *
              (⟪cylSmoothToL2 ((isCylSmooth_of_solTest (isRealSolCylTest_rotT hφ_sob)).dir
                  (B0579.dir 0)), uq r⟫_ℝ +
                ⟪cylSmoothToL2 ((isCylSmooth_of_solTest (isRealSolCylTest_rotT hφ_sob)).dir
                  (B0579.dir 1)), uη r⟫_ℝ) +
            α r *
              ⟪cylSmoothToL2 (isCylSmooth_of_solTest (isRealSolCylTest_rotT hφ_sob)), b r⟫_ℝ) = 0 := by
    intro α hα_sm hα_cp hα_ts φ hφ_sob
    have hφ : B0579.IsCylTest p.c φ := (isCylTest_sob_iff p.c φ).1 hφ_sob
    let Ψ := streamPlanarTest p.c σ α φ
    obtain ⟨hΨ_sol, hΨ_supp, ⟨a₀, b₀, R, ha₀, hab₀, hb₀, hR, hα_van, hΨ_box⟩, hqPer_Ψ, hqPer_m⟩ :=
      streamPlanarTest_props hc hσ hα_sm hα_cp hα_ts hφ
    obtain ⟨hint_δΨ, hint_bΨ, heq_Ψ⟩ := heq Ψ hΨ_sol hΨ_supp
    have hcdot_eq : cdot (flatBv p.train δ δq δη) Ψ = cdot b_win Ψ := by
      funext x
      by_cases hxS : x ∈ S_win
      · dsimp [cdot, b_win]; rw [indicator_of_mem hxS]
      · have hΨ0 : ∀ i : Fin 2, Ψ x i = 0 := fun i =>
          image_eq_zero_of_notMem_tsupport (f := fun y => Ψ y i) (fun hm => hxS (hΨ_supp i hm))
        simp [cdot, hΨ0]
    rw [hcdot_eq] at hint_bΨ heq_Ψ
    have hloc_δ : ∀ i : Fin 2,
        (∫⁻ s in Icc (σ + a₀) (σ + b₀),
          eLpNorm (fun z => δ (s, z) i) 2 (volume.restrict (B0579.cell p.c))) < ⊤ := by
      intro i
      have hsub : Icc (σ + a₀) (σ + b₀) ⊆ Ioo σ (σ + 1) := fun s hs =>
        ⟨by linarith [hs.1], by linarith [hs.2]⟩
      have hle : ∀ᵐ s ∂(volume.restrict (Icc (σ + a₀) (σ + b₀))),
          eLpNorm (fun z => δ (s, z) i) 2 (volume.restrict (B0579.cell p.c)) ≤
            ENNReal.ofReal B := by
        rw [ae_restrict_iff' measurableSet_Icc]
        filter_upwards [hslice_bdd] with s hs hs_mem
        calc eLpNorm (fun z => δ (s, z) i) 2 (volume.restrict (B0579.cell p.c))
            ≤ eLpNorm (fun z => δ (s, z)) 2 (volume.restrict (B0579.cell p.c)) :=
              eLpNorm_mono fun z => PiLp.norm_apply_le (δ (s, z)) i
          _ ≤ sliceH1Norm p.c δ δq δη s := le_self_add.trans le_self_add
          _ ≤ ENNReal.ofReal B := hs (hsub hs_mem)
      calc ∫⁻ s in Icc (σ + a₀) (σ + b₀),
              eLpNorm (fun z => δ (s, z) i) 2 (volume.restrict (B0579.cell p.c))
          ≤ ∫⁻ _ in Icc (σ + a₀) (σ + b₀), ENNReal.ofReal B := lintegral_mono_ae hle
        _ = ENNReal.ofReal B * volume (Icc (σ + a₀) (σ + b₀)) := by simp
        _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (by simp)
    have hloc_b : ∀ i : Fin 2,
        (∫⁻ s in Icc (σ + a₀) (σ + b₀),
          eLpNorm (fun z => b_win (s, z) i) 2 (volume.restrict (B0579.cell p.c))) < ⊤ := by
      intro i
      have hsub : Icc (σ + a₀) (σ + b₀) ⊆ Ioo σ (σ + 1) := fun s hs =>
        ⟨by linarith [hs.1], by linarith [hs.2]⟩
      have hle : ∀ᵐ s ∂(volume.restrict (Icc (σ + a₀) (σ + b₀))),
          eLpNorm (fun z => b_win (s, z) i) 2 (volume.restrict (B0579.cell p.c)) ≤
            ENNReal.ofReal (4 * M_V * (3 * B)) := by
        rw [ae_restrict_iff' measurableSet_Icc]
        filter_upwards [hslice_bdd, hslice_dat] with s hs hd hs_mem
        have hs_Ioo := hsub hs_mem
        have hr_Ioo : s - σ ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hs_Ioo.1], by linarith [hs_Ioo.2]⟩
        have hr_Icc : s - σ ∈ Icc (0 : ℝ) 2 := ⟨hr_Ioo.1.le, by linarith [hr_Ioo.2]⟩
        have hs_eq : σ + (s - σ) = s := by ring
        have hpt : ∀ z : B0579.Plane,
            ‖b_win (s, z) i‖ ≤
              4 * M_V * (‖δ (s, z)‖ + ‖δq (s, z)‖ + ‖δη (s, z)‖) := by
          intro z
          have hb_eq := hbwin_slice (s - σ) hr_Ioo z
          rw [hs_eq] at hb_eq
          rw [hb_eq]
          dsimp [F8Ex.complexBvSlice, F8U.slice]
          have b00 := hV_b0 (s - σ) hr_Icc 0 z
          have b01 := hV_b0 (s - σ) hr_Icc 1 z
          have b10 := hV_b1 (s - σ) hr_Icc 0 i z
          have b11 := hV_b1 (s - σ) hr_Icc 1 i z
          have hd0 : ((1 : ℝ), (0 : ℝ)) = B0579.dir 0 := rfl
          have hd1 : ((0 : ℝ), (1 : ℝ)) = B0579.dir 1 := rfl
          rw [hd0, hd1]
          have t1 : ‖((V (s - σ) z 0 : ℝ) : ℂ) * δq (s, z) i‖ ≤ M_V * ‖δq (s, z)‖ := by
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
            exact mul_le_mul b00 (PiLp.norm_apply_le _ i) (norm_nonneg _) hMV
          have t2 : ‖((V (s - σ) z 1 : ℝ) : ℂ) * δη (s, z) i‖ ≤ M_V * ‖δη (s, z)‖ := by
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
            exact mul_le_mul b01 (PiLp.norm_apply_le _ i) (norm_nonneg _) hMV
          have t3 : ‖δ (s, z) 0 *
              ((fderiv ℝ (fun w => V (s - σ) w i) z (B0579.dir 0) : ℝ) : ℂ)‖ ≤
              M_V * ‖δ (s, z)‖ := by
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_comm]
            exact mul_le_mul b10 (PiLp.norm_apply_le _ 0) (norm_nonneg _) hMV
          have t4 : ‖δ (s, z) 1 *
              ((fderiv ℝ (fun w => V (s - σ) w i) z (B0579.dir 1) : ℝ) : ℂ)‖ ≤
              M_V * ‖δ (s, z)‖ := by
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_comm]
            exact mul_le_mul b11 (PiLp.norm_apply_le _ 1) (norm_nonneg _) hMV
          have tri1 := norm_add_le
            (((V (s - σ) z 0 : ℝ) : ℂ) * δq (s, z) i +
              ((V (s - σ) z 1 : ℝ) : ℂ) * δη (s, z) i +
              δ (s, z) 0 * ((fderiv ℝ (fun w => V (s - σ) w i) z (B0579.dir 0) : ℝ) : ℂ))
            (δ (s, z) 1 * ((fderiv ℝ (fun w => V (s - σ) w i) z (B0579.dir 1) : ℝ) : ℂ))
          have tri2 := norm_add_le
            (((V (s - σ) z 0 : ℝ) : ℂ) * δq (s, z) i +
              ((V (s - σ) z 1 : ℝ) : ℂ) * δη (s, z) i)
            (δ (s, z) 0 * ((fderiv ℝ (fun w => V (s - σ) w i) z (B0579.dir 0) : ℝ) : ℂ))
          have tri3 := norm_add_le
            (((V (s - σ) z 0 : ℝ) : ℂ) * δq (s, z) i)
            (((V (s - σ) z 1 : ℝ) : ℂ) * δη (s, z) i)
          nlinarith [norm_nonneg (δ (s, z)), norm_nonneg (δq (s, z)), norm_nonneg (δη (s, z))]
        have hdat_s := hd hs_Ioo
        have hm_sum : MemLp (fun z => ‖δ (s, z)‖ + ‖δq (s, z)‖ + ‖δη (s, z)‖) 2
            (volume.restrict (B0579.cell p.c)) :=
          ((hdat_s.memL2.1.norm.add hdat_s.memL2.2.1.norm).add hdat_s.memL2.2.2.norm)
        calc eLpNorm (fun z => b_win (s, z) i) 2 (volume.restrict (B0579.cell p.c))
            ≤ eLpNorm ((4 * M_V) • fun z => ‖δ (s, z)‖ + ‖δq (s, z)‖ + ‖δη (s, z)‖) 2
                (volume.restrict (B0579.cell p.c)) := by
              refine eLpNorm_mono fun z => ?_
              simp only [Pi.smul_apply, smul_eq_mul]
              rw [Real.norm_of_nonneg (by positivity)]
              exact hpt z
          _ = ENNReal.ofReal (4 * M_V) *
              eLpNorm (fun z => ‖δ (s, z)‖ + ‖δq (s, z)‖ + ‖δη (s, z)‖) 2
                (volume.restrict (B0579.cell p.c)) := by
              rw [eLpNorm_const_smul, ← ofReal_norm, Real.norm_of_nonneg (by positivity)]
          _ ≤ ENNReal.ofReal (4 * M_V) * (sliceH1Norm p.c δ δq δη s) := by
              gcongr
              have e_add1 := eLpNorm_add_le
                (hdat_s.memL2.1.norm.add hdat_s.memL2.2.1.norm).aestronglyMeasurable
                hdat_s.memL2.2.2.norm.aestronglyMeasurable one_le_two
              have e_add2 := eLpNorm_add_le
                hdat_s.memL2.1.norm.aestronglyMeasurable
                hdat_s.memL2.2.1.norm.aestronglyMeasurable one_le_two
              simp only [eLpNorm_norm] at e_add1 e_add2
              dsimp only [sliceH1Norm, F8U.cellL2]
              exact e_add1.trans (add_le_add e_add2 le_rfl)
          _ ≤ ENNReal.ofReal (4 * M_V) * ENNReal.ofReal B := by gcongr; exact hs hs_Ioo
          _ ≤ ENNReal.ofReal (4 * M_V * (3 * B)) := by
              rw [← ENNReal.ofReal_mul (by positivity)]
              exact ENNReal.ofReal_le_ofReal (by nlinarith)
      calc ∫⁻ s in Icc (σ + a₀) (σ + b₀),
              eLpNorm (fun z => b_win (s, z) i) 2 (volume.restrict (B0579.cell p.c))
          ≤ ∫⁻ _ in Icc (σ + a₀) (σ + b₀), ENNReal.ofReal (4 * M_V * (3 * B)) :=
            lintegral_mono_ae hle
        _ = ENNReal.ofReal (4 * M_V * (3 * B)) * volume (Icc (σ + a₀) (σ + b₀)) := by simp
        _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (by simp)
    have hcont_m : ∀ i : Fin 2, Continuous (fun x : Coord => meridTransposeR p.ν Ψ x i) := by
      intro i
      have hsm := (hΨ_sol.smooth i).smooth
      have hc0 : Continuous (cpd 0 (fun y => Ψ y i)) :=
        ((hsm.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).continuous
      have hc1_sm : ContDiff ℝ ∞ (cpd 1 (fun y => Ψ y i)) :=
        (hsm.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
      have hc2_sm : ContDiff ℝ ∞ (cpd 2 (fun y => Ψ y i)) :=
        (hsm.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
      have hc11 : Continuous (cpd 1 (cpd 1 (fun y => Ψ y i))) :=
        ((hc1_sm.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).continuous
      have hc22 : Continuous (cpd 2 (cpd 2 (fun y => Ψ y i))) :=
        ((hc2_sm.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).continuous
      unfold meridTransposeR
      exact hc0.neg.sub (continuous_const.mul (hc11.add hc22))
    have hunf_m : ∀ i : Fin 2,
        Integrable (fun x : Coord => δ x i * (meridTransposeR p.ν Ψ x i : ℂ)) volume ∧
        IntegrableOn (fun x : Coord =>
          δ x i * (TailPeriodizeAux.qPeriodize p.c (fun y => meridTransposeR p.ν Ψ y i) x.1 x.2 : ℂ))
          (Icc (σ + a₀) (σ + b₀) ×ˢ B0579.cell p.c) volume ∧
        ∫ x : Coord, δ x i * (meridTransposeR p.ν Ψ x i : ℂ) =
          ∫ s in Icc (σ + a₀) (σ + b₀), ∫ z in B0579.cell p.c,
            δ (s, z) i *
              (TailPeriodizeAux.qPeriodize p.c (fun y => meridTransposeR p.ν Ψ y i) s z : ℂ) := by
      intro i
      refine TailPeriodizeAux.integrable_and_integral_coord_eq_cell_qPeriodize
        hc (by linarith) (by linarith) hR
        (((F8Ex.πC i).continuous.comp_stronglyMeasurable hsm_δ).aestronglyMeasurable)
        (hper_δ.mono fun _ h => congrArg (fun v => v i) h)
        (hloc_δ i) (hcont_m i) fun x hx => (hΨ_box x hx i).2 p.ν
    have hunf_b : ∀ i : Fin 2,
        Integrable (fun x : Coord => b_win x i * (Ψ x i : ℂ)) volume ∧
        IntegrableOn (fun x : Coord =>
          b_win x i * (TailPeriodizeAux.qPeriodize p.c (fun y => Ψ y i) x.1 x.2 : ℂ))
          (Icc (σ + a₀) (σ + b₀) ×ˢ B0579.cell p.c) volume ∧
        ∫ x : Coord, b_win x i * (Ψ x i : ℂ) =
          ∫ s in Icc (σ + a₀) (σ + b₀), ∫ z in B0579.cell p.c,
            b_win (s, z) i * (TailPeriodizeAux.qPeriodize p.c (fun y => Ψ y i) s z : ℂ) := by
      intro i
      refine TailPeriodizeAux.integrable_and_integral_coord_eq_cell_qPeriodize
        hc (by linarith) (by linarith) hR
        (((F8Ex.πC i).continuous.comp_stronglyMeasurable hsm_bwin).aestronglyMeasurable)
        (hper_bwin.mono fun _ h => congrArg (fun v => v i) h)
        (hloc_b i) (hΨ_sol.smooth i).smooth.continuous fun x hx => (hΨ_box x hx i).1
    -- Split global integral into the 4 component integrals, apply sc, and rewrite on Icc a₀ b₀
    have hsplit_tot :
        ∫ x : Coord, (∑ i : Fin 2, δ x i * meridTranspose p.ν Ψ x i + cdot b_win Ψ x) =
          (∫ x, δ x 0 * (meridTransposeR p.ν Ψ x 0 : ℂ)) +
          (∫ x, δ x 1 * (meridTransposeR p.ν Ψ x 1 : ℂ)) +
          (∫ x, b_win x 0 * (Ψ x 0 : ℂ)) +
          (∫ x, b_win x 1 * (Ψ x 1 : ℂ)) := by
      rw [integral_add hint_δΨ hint_bΨ]
      have hm_eq : (fun x : Coord => ∑ i : Fin 2, δ x i * meridTranspose p.ν Ψ x i) =
          fun x => δ x 0 * (meridTransposeR p.ν Ψ x 0 : ℂ) +
            δ x 1 * (meridTransposeR p.ν Ψ x 1 : ℂ) := by
        funext x; simp [Fin.sum_univ_two, meridTranspose_eq_cast]
      have hb_eq : cdot b_win Ψ =
          fun x => b_win x 0 * (Ψ x 0 : ℂ) + b_win x 1 * (Ψ x 1 : ℂ) := by
        funext x; simp [cdot, Fin.sum_univ_two]
      rw [hm_eq, hb_eq, integral_add (hunf_m 0).1 (hunf_m 1).1,
        integral_add (hunf_b 0).1 (hunf_b 1).1]
      ring
    rw [(hunf_m 0).2.2, (hunf_m 1).2.2, (hunf_b 0).2.2, (hunf_b 1).2.2] at hsplit_tot
    -- Extract slice integrability on Icc (σ + a₀) (σ + b₀) from Fubini on prod measure
    have hslice_int_m : ∀ i : Fin 2, IntegrableOn
        (fun s : ℝ => ∫ z in B0579.cell p.c,
          δ (s, z) i *
            (TailPeriodizeAux.qPeriodize p.c (fun y => meridTransposeR p.ν Ψ y i) s z : ℂ))
        (Icc (σ + a₀) (σ + b₀)) := by
      intro i
      have hp : Integrable
          (fun x : Coord => δ x i *
            (TailPeriodizeAux.qPeriodize p.c (fun y => meridTransposeR p.ν Ψ y i) x.1 x.2 : ℂ))
          ((volume.restrict (Icc (σ + a₀) (σ + b₀))).prod
            (volume.restrict (B0579.cell p.c))) := by
        rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
        exact (hunf_m i).2.1
      exact hp.integral_prod_left
    have hslice_int_b : ∀ i : Fin 2, IntegrableOn
        (fun s : ℝ => ∫ z in B0579.cell p.c,
          b_win (s, z) i * (TailPeriodizeAux.qPeriodize p.c (fun y => Ψ y i) s z : ℂ))
        (Icc (σ + a₀) (σ + b₀)) := by
      intro i
      have hp : Integrable
          (fun x : Coord => b_win x i *
            (TailPeriodizeAux.qPeriodize p.c (fun y => Ψ y i) x.1 x.2 : ℂ))
          ((volume.restrict (Icc (σ + a₀) (σ + b₀))).prod
            (volume.restrict (B0579.cell p.c))) := by
        rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
        exact (hunf_b i).2.1
      exact hp.integral_prod_left
    have hcomb_s :
        ∫ s in Icc (σ + a₀) (σ + b₀),
          ((∫ z in B0579.cell p.c, δ (s, z) 0 *
              (TailPeriodizeAux.qPeriodize p.c (fun y => meridTransposeR p.ν Ψ y 0) s z : ℂ)) +
            (∫ z in B0579.cell p.c, δ (s, z) 1 *
              (TailPeriodizeAux.qPeriodize p.c (fun y => meridTransposeR p.ν Ψ y 1) s z : ℂ)) +
            (∫ z in B0579.cell p.c, b_win (s, z) 0 *
              (TailPeriodizeAux.qPeriodize p.c (fun y => Ψ y 0) s z : ℂ)) +
            (∫ z in B0579.cell p.c, b_win (s, z) 1 *
              (TailPeriodizeAux.qPeriodize p.c (fun y => Ψ y 1) s z : ℂ))) = 0 := by
      have i1 := integral_add (hslice_int_m 0) (hslice_int_m 1)
      have i2 := integral_add ((hslice_int_m 0).add (hslice_int_m 1)) (hslice_int_b 0)
      have i3 := integral_add (((hslice_int_m 0).add (hslice_int_m 1)).add (hslice_int_b 0))
        (hslice_int_b 1)
      simp only [Pi.add_apply] at i1 i2 i3
      rw [i3, i2, i1]
      exact hsplit_tot.symm.trans heq_Ψ
    have hsc_0 : ∫ s in Icc (σ + a₀) (σ + b₀),
        sc ((∫ z in B0579.cell p.c, δ (s, z) 0 *
              (TailPeriodizeAux.qPeriodize p.c (fun y => meridTransposeR p.ν Ψ y 0) s z : ℂ)) +
            (∫ z in B0579.cell p.c, δ (s, z) 1 *
              (TailPeriodizeAux.qPeriodize p.c (fun y => meridTransposeR p.ν Ψ y 1) s z : ℂ)) +
            (∫ z in B0579.cell p.c, b_win (s, z) 0 *
              (TailPeriodizeAux.qPeriodize p.c (fun y => Ψ y 0) s z : ℂ)) +
            (∫ z in B0579.cell p.c, b_win (s, z) 1 *
              (TailPeriodizeAux.qPeriodize p.c (fun y => Ψ y 1) s z : ℂ))) = 0 := by
      have h1 := sc.integral_comp_comm
        ((((hslice_int_m 0).add (hslice_int_m 1)).add (hslice_int_b 0)).add (hslice_int_b 1))
      simp only [Pi.add_apply] at h1
      rw [h1, hcomb_s, map_zero]
    -- Target 1D integrand g_target r
    let hΦ_sol := isRealSolCylTest_rotT hφ_sob
    let hΦ := isCylSmooth_of_solTest hΦ_sol
    let ψ₀ := cylSmoothToL2 hΦ
    let ψq := cylSmoothToL2 (hΦ.dir (B0579.dir 0))
    let ψη := cylSmoothToL2 (hΦ.dir (B0579.dir 1))
    let g_target : ℝ → ℝ := fun r =>
      -deriv α r * ⟪ψ₀, u₀ r⟫_ℝ +
        p.ν * α r * (⟪ψq, uq r⟫_ℝ + ⟪ψη, uη r⟫_ℝ) +
        α r * ⟪ψ₀, b r⟫_ℝ
    have hg_van : ∀ r ∉ Icc a₀ b₀, g_target r = 0 := by
      intro r hr
      obtain ⟨hα0, hdα0⟩ := hα_van r hr
      simp [g_target, hα0, hdα0]
    -- Show the shifted integrand agrees with g_target (s - σ) for a.e. s ∈ Icc (σ + a₀) (σ + b₀)
    have hae_Icc : ∀ᵐ s ∂(volume.restrict (Icc (σ + a₀) (σ + b₀))), s - σ ∈ G_set := by
      have hsub : Icc (σ + a₀) (σ + b₀) ⊆ Ioo σ (σ + 1) := fun s hs =>
        ⟨by linarith [hs.1], by linarith [hs.2]⟩
      rw [ae_restrict_iff' measurableSet_Icc]
      filter_upwards [hae_s] with s hs hs_mem
      have hs_Ioo := hsub hs_mem
      have hs_eq : σ + (s - σ) = s := by ring
      refine ⟨⟨by linarith [hs_Ioo.1], by linarith [hs_Ioo.2]⟩, ?_⟩
      rw [hs_eq]
      exact hs hs_Ioo
    have hcongr_s : ∫ s in Icc (σ + a₀) (σ + b₀), g_target (s - σ) = 0 := by
      rw [← hsc_0]
      refine integral_congr_ae ?_
      filter_upwards [hae_Icc] with s hrG
      set r := s - σ
      have hs_eq : s = σ + r := by dsimp [r]; ring
      have hr_Ioo := hrG.1
      have hdat_r := hrG.2.2
      obtain ⟨_, hwq, hwη, _⟩ := hG_props r hrG
      have h_cell_m : ∀ i : Fin 2,
          sc (∫ z in B0579.cell p.c, δ (s, z) i *
              (TailPeriodizeAux.qPeriodize p.c (fun y => meridTransposeR p.ν Ψ y i) s z : ℂ)) =
            -deriv α r * (∫ z in B0579.cell p.c, (u₀ r : Plane → Vec2) z i *
                UnforcedLeray.Cyl.rotT φ z i) +
              p.ν * α r *
                ((∫ z in B0579.cell p.c, (uq r : Plane → Vec2) z i *
                    B0579.pd 0 (fun w => UnforcedLeray.Cyl.rotT φ w i) z) +
                  (∫ z in B0579.cell p.c, (uη r : Plane → Vec2) z i *
                    B0579.pd 1 (fun w => UnforcedLeray.Cyl.rotT φ w i) z)) := by
        intro i
        have hm_δi : MemLp (fun z => δ (s, z) i) 2 (volume.restrict (B0579.cell p.c)) := by
          rw [hs_eq]
          exact ((EuclideanSpace.proj i : CMerid →L[ℂ] ℂ).restrictScalars ℝ).comp_memLp'
            hdat_r.memL2.1
        have hqp_test : B0579.IsCylTest p.c
            (TailPeriodizeAux.qPeriodize p.c (fun y => meridTransposeR p.ν Ψ y i) s) := by
          have hfn : TailPeriodizeAux.qPeriodize p.c (fun y => meridTransposeR p.ν Ψ y i) s =
              fun z => -deriv α (s - σ) * UnforcedLeray.Cyl.rotT φ z i -
                p.ν * α (s - σ) *
                  (B0579.pd 0 (B0579.pd 0 (fun w => UnforcedLeray.Cyl.rotT φ w i)) z +
                    B0579.pd 1 (B0579.pd 1 (fun w => UnforcedLeray.Cyl.rotT φ w i)) z) :=
            funext fun z => hqPer_m p.ν s z i
          rw [hfn]
          have ht0 := hΦ_sol.cyl_test i
          have ht11 := (ht0.pd 0).pd 0
          have ht22 := (ht0.pd 1).pd 1
          obtain ⟨R0, b0⟩ := ht0.band
          obtain ⟨R1, b1⟩ := ht11.band
          obtain ⟨R2, b2⟩ := ht22.band
          refine ⟨((contDiff_const.mul ht0.smooth).sub
            (contDiff_const.mul (ht11.smooth.add ht22.smooth))),
            fun z => by simp [ht0.periodic z, ht11.periodic z, ht22.periodic z],
            max R0 (max R1 R2), fun z hz => ?_⟩
          have z0 := b0 z (lt_of_le_of_lt (le_max_left _ _) hz)
          have z1 := b1 z (lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right _ _)) hz)
          have z2 := b2 z (lt_of_le_of_lt ((le_max_right _ _).trans (le_max_right _ _)) hz)
          simp [z0, z1, z2]
        have hm_qp : MemLp
            (fun z => (TailPeriodizeAux.qPeriodize p.c (fun y => meridTransposeR p.ν Ψ y i) s z : ℂ))
            2 (volume.restrict (B0579.cell p.c)) := by
          rw [← show F8Ex.cellMeas p.c = volume.restrict (B0579.cell p.c) from rfl,
            cellMeas_eq_cellμ]
          exact Complex.ofRealCLM.comp_memLp' (memLp_cellμ_of_test hqp_test)
        have hint_cell : IntegrableOn
            (fun z => δ (s, z) i *
              (TailPeriodizeAux.qPeriodize p.c (fun y => meridTransposeR p.ν Ψ y i) s z : ℂ))
            (B0579.cell p.c) := hm_δi.integrable_mul hm_qp
        rw [← sc.integral_comp_comm hint_cell]
        have hm_Lr : MemLp (fun z => L (δ (σ + r, z))) 2 (cellμ p.c) := by
          rw [← cellMeas_eq_cellμ]; exact (hL_dat hdat_r).memL2.1
        have hu₀_ae : (fun z => L (δ (σ + r, z))) =ᵐ[volume.restrict (B0579.cell p.c)] u₀ r := by
          rw [b0579_cell_eq_cyl_cell]
          change (fun z => L (δ (σ + r, z))) =ᵐ[cellμ p.c] u₀ r
          rw [show u₀ r = hm_Lr.toLp _ from UnforcedLeray.BochnerTime.toPathLq_of_memLp hm_Lr]
          exact hm_Lr.coeFn_toLp.symm
        have hstep1 : ∫ z in B0579.cell p.c,
            sc (δ (s, z) i *
              (TailPeriodizeAux.qPeriodize p.c (fun y => meridTransposeR p.ν Ψ y i) s z : ℂ)) =
            ∫ z in B0579.cell p.c,
              (u₀ r : Plane → Vec2) z i *
                (-deriv α r * UnforcedLeray.Cyl.rotT φ z i -
                  p.ν * α r *
                    (B0579.pd 0 (B0579.pd 0 (fun w => UnforcedLeray.Cyl.rotT φ w i)) z +
                      B0579.pd 1 (B0579.pd 1 (fun w => UnforcedLeray.Cyl.rotT φ w i)) z)) := by
          refine integral_congr_ae ?_
          filter_upwards [hu₀_ae] with z hz
          rw [hsc_mul_r, ← hL_coord, hs_eq, hz, hqPer_m p.ν (σ + r) z i]
          have hsr : σ + r - σ = r := by ring
          rw [hsr]
        rw [hstep1]
        have ht0 := hΦ_sol.cyl_test i
        have hi_u0_0 : IntegrableOn
            (fun z : B0579.Plane => (u₀ r : Plane → Vec2) z i * UnforcedLeray.Cyl.rotT φ z i)
            (B0579.cell p.c) := by
          rw [b0579_cell_eq_cyl_cell]
          exact (UnforcedLeray.Cyl.memLp_component (u₀ r) i).integrable_mul
            (memLp_cellμ_of_test ht0)
        have hi_11 : IntegrableOn
            (fun z : B0579.Plane => (u₀ r : Plane → Vec2) z i *
              B0579.pd 0 (B0579.pd 0 (fun w => UnforcedLeray.Cyl.rotT φ w i)) z)
            (B0579.cell p.c) := ((hwq i).1 _ (ht0.pd 0)).1
        have hi_22 : IntegrableOn
            (fun z : B0579.Plane => (u₀ r : Plane → Vec2) z i *
              B0579.pd 1 (B0579.pd 1 (fun w => UnforcedLeray.Cyl.rotT φ w i)) z)
            (B0579.cell p.c) := ((hwη i).1 _ (ht0.pd 1)).1
        have hfn_split : (fun z : B0579.Plane => (u₀ r : Plane → Vec2) z i *
            (-deriv α r * UnforcedLeray.Cyl.rotT φ z i -
              p.ν * α r *
                (B0579.pd 0 (B0579.pd 0 (fun w => UnforcedLeray.Cyl.rotT φ w i)) z +
                  B0579.pd 1 (B0579.pd 1 (fun w => UnforcedLeray.Cyl.rotT φ w i)) z))) =
            fun z : B0579.Plane =>
              ((-deriv α r) * ((u₀ r : Plane → Vec2) z i * UnforcedLeray.Cyl.rotT φ z i) -
                (p.ν * α r) *
                  ((u₀ r : Plane → Vec2) z i *
                    B0579.pd 0 (B0579.pd 0 (fun w => UnforcedLeray.Cyl.rotT φ w i)) z)) -
              (p.ν * α r) *
                ((u₀ r : Plane → Vec2) z i *
                  B0579.pd 1 (B0579.pd 1 (fun w => UnforcedLeray.Cyl.rotT φ w i)) z) := by
          funext z; ring
        have h_i0 := hi_u0_0.const_mul (-deriv α r)
        have h_i1 := hi_11.const_mul (p.ν * α r)
        have h_i2 := hi_22.const_mul (p.ν * α r)
        have h_i01 : IntegrableOn (fun z : B0579.Plane =>
            (-deriv α r) * ((u₀ r : Plane → Vec2) z i * UnforcedLeray.Cyl.rotT φ z i) -
              (p.ν * α r) *
                ((u₀ r : Plane → Vec2) z i *
                  B0579.pd 0 (B0579.pd 0 (fun w => UnforcedLeray.Cyl.rotT φ w i)) z))
            (B0579.cell p.c) := h_i0.sub h_i1
        rw [hfn_split,
          integral_sub h_i01 h_i2,
          integral_sub h_i0 h_i1,
          integral_const_mul, integral_const_mul, integral_const_mul,
          (hwq i).2 _ (ht0.pd 0), (hwη i).2 _ (ht0.pd 1)]
        ring
      have h_cell_b : ∀ i : Fin 2,
          sc (∫ z in B0579.cell p.c, b_win (s, z) i *
              (TailPeriodizeAux.qPeriodize p.c (fun y => Ψ y i) s z : ℂ)) =
            α r * ∫ z in B0579.cell p.c,
              (b r : Plane → Vec2) z i * UnforcedLeray.Cyl.rotT φ z i := by
        intro i
        have hmb_r : MemLp (fun z => L (b_win (σ + r, z))) 2 (cellμ p.c) := by
          obtain ⟨hbv_lp, _⟩ := memLp_and_norm_realBvSlice hMV (hV_sm r ⟨hr_Ioo.1.le, by linarith [hr_Ioo.2]⟩)
            (hV_b0 r ⟨hr_Ioo.1.le, by linarith [hr_Ioo.2]⟩)
            (hV_b1 r ⟨hr_Ioo.1.le, by linarith [hr_Ioo.2]⟩)
            (by rw [← cellMeas_eq_cellμ]; exact (hL_dat hdat_r).memL2.1)
            (by rw [← cellMeas_eq_cellμ]; exact (hL_dat hdat_r).memL2.2.1)
            (by rw [← cellMeas_eq_cellμ]; exact (hL_dat hdat_r).memL2.2.2)
          exact hbv_lp.ae_eq (Eventually.of_forall fun z => (hL_slice_bv r hr_Ioo z).symm)
        have hb_ae : (fun z => L (b_win (σ + r, z))) =ᵐ[volume.restrict (B0579.cell p.c)] b r := by
          rw [b0579_cell_eq_cyl_cell]
          change (fun z => L (b_win (σ + r, z))) =ᵐ[cellμ p.c] b r
          rw [show b r = hmb_r.toLp _ from UnforcedLeray.BochnerTime.toPathLq_of_memLp hmb_r]
          exact hmb_r.coeFn_toLp.symm
        -- Complex MemLp of b_win (s, ·) i via combineMerid of reMerid and imMerid
        have hm_b_re : MemLp (fun z => F8Ex.reMerid (b_win (σ + r, z))) 2 (cellμ p.c) := by
          obtain ⟨hbv_lp, _⟩ := memLp_and_norm_realBvSlice hMV (hV_sm r ⟨hr_Ioo.1.le, by linarith [hr_Ioo.2]⟩)
            (hV_b0 r ⟨hr_Ioo.1.le, by linarith [hr_Ioo.2]⟩)
            (hV_b1 r ⟨hr_Ioo.1.le, by linarith [hr_Ioo.2]⟩)
            (by rw [← cellMeas_eq_cellμ]; exact (F8Ex.split_cylH1Datum hdat_r).1.memL2.1)
            (by rw [← cellMeas_eq_cellμ]; exact (F8Ex.split_cylH1Datum hdat_r).1.memL2.2.1)
            (by rw [← cellMeas_eq_cellμ]; exact (F8Ex.split_cylH1Datum hdat_r).1.memL2.2.2)
          refine hbv_lp.ae_eq (Eventually.of_forall fun z => ?_)
          dsimp only [V]
          rw [hbwin_slice r hr_Ioo z]
          ext k; simp [F8Ex.complexBvSlice, F8Ex.realBvSlice, F8U.slice, Complex.mul_re]
        have hm_b_im : MemLp (fun z => F8Ex.imMerid (b_win (σ + r, z))) 2 (cellμ p.c) := by
          obtain ⟨hbv_lp, _⟩ := memLp_and_norm_realBvSlice hMV (hV_sm r ⟨hr_Ioo.1.le, by linarith [hr_Ioo.2]⟩)
            (hV_b0 r ⟨hr_Ioo.1.le, by linarith [hr_Ioo.2]⟩)
            (hV_b1 r ⟨hr_Ioo.1.le, by linarith [hr_Ioo.2]⟩)
            (by rw [← cellMeas_eq_cellμ]; exact (F8Ex.split_cylH1Datum hdat_r).2.memL2.1)
            (by rw [← cellMeas_eq_cellμ]; exact (F8Ex.split_cylH1Datum hdat_r).2.memL2.2.1)
            (by rw [← cellMeas_eq_cellμ]; exact (F8Ex.split_cylH1Datum hdat_r).2.memL2.2.2)
          refine hbv_lp.ae_eq (Eventually.of_forall fun z => ?_)
          dsimp only [V]
          rw [hbwin_slice r hr_Ioo z]
          ext k; simp [F8Ex.complexBvSlice, F8Ex.realBvSlice, F8U.slice, Complex.mul_im]
        have hm_b_c : MemLp (fun z => b_win (s, z) i) 2 (volume.restrict (B0579.cell p.c)) := by
          rw [hs_eq, ← show F8Ex.cellMeas p.c = volume.restrict (B0579.cell p.c) from rfl,
            cellMeas_eq_cellμ]
          have hcomb : (fun z => b_win (σ + r, z)) =
              fun z => F8Ex.ofRealMerid (F8Ex.reMerid (b_win (σ + r, z))) +
                F8Ex.ofImagMerid (F8Ex.imMerid (b_win (σ + r, z))) :=
            funext fun z => (F8Ex.combineMerid_re_im _).symm
          have hm_vec : MemLp (fun z => b_win (σ + r, z)) 2 (cellμ p.c) := by
            rw [hcomb]
            exact (F8Ex.ofRealMerid.comp_memLp' hm_b_re).add
              (F8Ex.ofImagMerid.comp_memLp' hm_b_im)
          exact ((EuclideanSpace.proj i : CMerid →L[ℂ] ℂ).restrictScalars ℝ).comp_memLp' hm_vec
        have hm_qp : MemLp (fun z => (TailPeriodizeAux.qPeriodize p.c (fun y => Ψ y i) s z : ℂ))
            2 (volume.restrict (B0579.cell p.c)) := by
          have hfn : TailPeriodizeAux.qPeriodize p.c (fun y => Ψ y i) s =
              fun z => α (s - σ) * UnforcedLeray.Cyl.rotT φ z i := funext fun z => hqPer_Ψ s z i
          rw [hfn, ← show F8Ex.cellMeas p.c = volume.restrict (B0579.cell p.c) from rfl,
            cellMeas_eq_cellμ]
          exact Complex.ofRealCLM.comp_memLp'
            ((memLp_cellμ_of_test (hΦ_sol.cyl_test i)).const_mul (α (s - σ)))
        have hint_cell : IntegrableOn
            (fun z => b_win (s, z) i * (TailPeriodizeAux.qPeriodize p.c (fun y => Ψ y i) s z : ℂ))
            (B0579.cell p.c) := hm_b_c.integrable_mul hm_qp
        rw [← sc.integral_comp_comm hint_cell]
        have hstep : ∫ z in B0579.cell p.c,
            sc (b_win (s, z) i * (TailPeriodizeAux.qPeriodize p.c (fun y => Ψ y i) s z : ℂ)) =
            ∫ z in B0579.cell p.c,
              α r * ((b r : Plane → Vec2) z i * UnforcedLeray.Cyl.rotT φ z i) := by
          refine integral_congr_ae ?_
          filter_upwards [hb_ae] with z hz
          rw [hsc_mul_r, ← hL_coord, hs_eq, hz, hqPer_Ψ (σ + r) z i]
          have hsr : σ + r - σ = r := by ring
          rw [hsr]; ring
        rw [hstep, integral_const_mul]
      -- Assemble inner products on B0579.cell p.c
      have h_ip0 : ∀ f : L2v p.c,
          ⟪ψ₀, f⟫_ℝ =
            (∫ z in B0579.cell p.c, (f : Plane → Vec2) z 0 * UnforcedLeray.Cyl.rotT φ z 0) +
            (∫ z in B0579.cell p.c, (f : Plane → Vec2) z 1 * UnforcedLeray.Cyl.rotT φ z 1) := by
        intro f
        rw [inner_cylSmoothToL2_right]
        have hi0 : IntegrableOn (fun z => (f : Plane → Vec2) z 0 * UnforcedLeray.Cyl.rotT φ z 0)
            (B0579.cell p.c) := by
          rw [b0579_cell_eq_cyl_cell]
          exact (UnforcedLeray.Cyl.memLp_component f 0).integrable_mul
            (memLp_cellμ_of_test (hΦ_sol.cyl_test 0))
        have hi1 : IntegrableOn (fun z => (f : Plane → Vec2) z 1 * UnforcedLeray.Cyl.rotT φ z 1)
            (B0579.cell p.c) := by
          rw [b0579_cell_eq_cyl_cell]
          exact (UnforcedLeray.Cyl.memLp_component f 1).integrable_mul
            (memLp_cellμ_of_test (hΦ_sol.cyl_test 1))
        rw [← integral_add hi0 hi1]
        refine integral_congr_ae (Eventually.of_forall fun z => ?_)
        dsimp only
        rw [PiLp.inner_apply, Fin.sum_univ_two]
        simp only [RCLike.inner_apply, conj_trivial]
      have h_ip_dir : ∀ (j : Fin 2) (f : L2v p.c),
          ⟪cylSmoothToL2 (hΦ.dir (B0579.dir j)), f⟫_ℝ =
            (∫ z in B0579.cell p.c,
                (f : Plane → Vec2) z 0 * B0579.pd j (fun w => UnforcedLeray.Cyl.rotT φ w 0) z) +
            (∫ z in B0579.cell p.c,
                (f : Plane → Vec2) z 1 * B0579.pd j (fun w => UnforcedLeray.Cyl.rotT φ w 1) z) := by
        intro j f
        rw [inner_cylSmoothToL2_right]
        have hi0 : IntegrableOn
            (fun z => (f : Plane → Vec2) z 0 *
              B0579.pd j (fun w => UnforcedLeray.Cyl.rotT φ w 0) z)
            (B0579.cell p.c) := by
          rw [b0579_cell_eq_cyl_cell]
          exact (UnforcedLeray.Cyl.memLp_component f 0).integrable_mul
            (memLp_cellμ_of_test ((hΦ_sol.cyl_test 0).pd j))
        have hi1 : IntegrableOn
            (fun z => (f : Plane → Vec2) z 1 *
              B0579.pd j (fun w => UnforcedLeray.Cyl.rotT φ w 1) z)
            (B0579.cell p.c) := by
          rw [b0579_cell_eq_cyl_cell]
          exact (UnforcedLeray.Cyl.memLp_component f 1).integrable_mul
            (memLp_cellμ_of_test ((hΦ_sol.cyl_test 1).pd j))
        rw [← integral_add hi0 hi1]
        refine integral_congr_ae (Eventually.of_forall fun z => ?_)
        dsimp only
        rw [PiLp.inner_apply, Fin.sum_univ_two, pd_coord_cylSmooth hΦ j 0 z,
          pd_coord_cylSmooth hΦ j 1 z]
        simp only [RCLike.inner_apply, conj_trivial]
      simp only [map_add]
      rw [h_cell_m 0, h_cell_m 1, h_cell_b 0, h_cell_b 1]
      dsimp only [g_target, ψ₀, ψq, ψη]
      rw [h_ip0 (u₀ r), h_ip0 (b r), h_ip_dir 0 (uq r), h_ip_dir 1 (uη r)]
      ring
    -- Shift s = σ + r via setIntegral_eq_integral_of_forall_compl_eq_zero + integral_sub_right_eq_self
    have hs_compl : ∀ s ∉ Icc (σ + a₀) (σ + b₀), g_target (s - σ) = 0 := by
      intro s hs
      apply hg_van
      intro hr
      exact hs ⟨by linarith [hr.1], by linarith [hr.2]⟩
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero hs_compl,
      integral_sub_right_eq_self g_target σ] at hcongr_s
    exact hcongr_s
  -- Right-Lebesgue trace transfer
  have htrace_L : Tendsto (fun h : ℝ => h⁻¹ * ∫ r in Ioc 0 h, ‖u₀ r‖ ^ 2) (𝓝[>] 0) (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds htrace ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with h hh
      exact mul_nonneg (inv_nonneg.2 hh.le)
        (setIntegral_nonneg measurableSet_Ioc fun _ _ => sq_nonneg _)
    · have hmem : Ioo (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) :=
        Filter.inter_mem self_mem_nhdsWithin (nhdsWithin_le_nhds (Iio_mem_nhds zero_lt_one))
      filter_upwards [hmem] with h hh
      have hsub_r : Ioc 0 h ⊆ Ioo 0 1 := fun r hr =>
        ⟨hr.1, lt_of_le_of_lt hr.2 hh.2⟩
      have hG_Ioc : ∀ᵐ r ∂(volume.restrict (Ioc 0 h)), r ∈ G_set := by
        rw [ae_restrict_iff' measurableSet_Ioc]
        filter_upwards [(ae_restrict_iff' measurableSet_Ioo).1 hG_ae,
          (by simp [ae_iff, measure_singleton] : ∀ᵐ r : ℝ ∂volume, r ≠ h)] with r hr hrh hr_mem
        exact hr ⟨hr_mem.1, lt_trans (lt_of_le_of_ne hr_mem.2 hrh) hh.2⟩
      let N_δ : ℝ → ℝ := fun t => (F8U.cellL2 p.c (F8U.slice δ t)).toReal ^ 2
      have hN_meas : Measurable N_δ := by
        have hm : Measurable (fun t : ℝ =>
            (∫⁻ z, ‖δ (t, z)‖ₑ ^ (2 : ℝ) ∂(volume.restrict (B0579.cell p.c))) ^ (1 / (2 : ℝ))) :=
          ((hsm_δ.enorm.pow_const _).lintegral_prod_right').pow_const _
        have heq_N : (fun t : ℝ => F8U.cellL2 p.c (F8U.slice δ t)) =
            fun t => (∫⁻ z, ‖δ (t, z)‖ₑ ^ (2 : ℝ) ∂(volume.restrict (B0579.cell p.c))) ^ (1 / (2 : ℝ)) := by
          funext t
          unfold F8U.cellL2 F8U.slice
          rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
          rfl
        exact ((heq_N ▸ hm).ennreal_toReal).pow_const 2
      have hN_int_s : IntegrableOn N_δ (Ioc σ (σ + h)) := by
        have hconst : IntegrableOn (fun _ : ℝ => B ^ 2) (Ioc σ (σ + h)) := by simp
        refine hconst.mono' hN_meas.aestronglyMeasurable ?_
        rw [ae_restrict_iff' measurableSet_Ioc]
        filter_upwards [hslice_bdd] with t ht ht_mem
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        have ht_Ioo : t ∈ Ioo σ (σ + 1) := ⟨ht_mem.1, by linarith [ht_mem.2, hh.2]⟩
        have hle : F8U.cellL2 p.c (F8U.slice δ t) ≤ ENNReal.ofReal B :=
          (le_self_add.trans le_self_add).trans (ht ht_Ioo)
        exact pow_le_pow_left₀ ENNReal.toReal_nonneg (ENNReal.toReal_le_of_le_ofReal hB hle) 2
      have hshift_eq : ∫ r in Ioc 0 h, N_δ (σ + r) = ∫ t in Ioc σ (σ + h), N_δ t := by
        rw [← integral_indicator measurableSet_Ioc, ← integral_indicator measurableSet_Ioc]
        have hind : (Ioc 0 h).indicator (fun r => N_δ (σ + r)) =
            fun r => (Ioc σ (σ + h)).indicator N_δ (σ + r) := by
          funext r
          by_cases hr : r ∈ Ioc 0 h
          · have hsr : σ + r ∈ Ioc σ (σ + h) := ⟨by linarith [hr.1], by linarith [hr.2]⟩
            rw [indicator_of_mem hr, indicator_of_mem hsr]
          · have hsr : σ + r ∉ Ioc σ (σ + h) := fun hm => hr ⟨by linarith [hm.1], by linarith [hm.2]⟩
            rw [indicator_of_notMem hr, indicator_of_notMem hsr]
        rw [hind, integral_add_left_eq_self (fun t => (Ioc σ (σ + h)).indicator N_δ t) σ]
      have hN_int_r : IntegrableOn (fun r => N_δ (σ + r)) (Ioc 0 h) := by
        have hi_ind := (integrable_indicator_iff measurableSet_Ioc).2 hN_int_s
        have hi_sh : Integrable (fun r => (Ioc σ (σ + h)).indicator N_δ (σ + r)) :=
          hi_ind.comp_add_left σ
        refine (integrable_indicator_iff measurableSet_Ioc).1 (hi_sh.congr (Eventually.of_forall fun r => ?_))
        by_cases hr : r ∈ Ioc 0 h
        · have hsr : σ + r ∈ Ioc σ (σ + h) := ⟨by linarith [hr.1], by linarith [hr.2]⟩
          simp [hr, hsr]
        · have hsr : σ + r ∉ Ioc σ (σ + h) := fun hm => hr ⟨by linarith [hm.1], by linarith [hm.2]⟩
          simp [hr, hsr]
      have hu₀_int_r : IntegrableOn (fun r => ‖u₀ r‖ ^ 2) (Ioc 0 h) := by
        have hconst : IntegrableOn (fun _ : ℝ => B ^ 2) (Ioc 0 h) := by simp
        refine hconst.mono' (hu₀_sm.norm.pow 2).aestronglyMeasurable ?_
        filter_upwards [hG_Ioc] with r hrG
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (norm_nonneg _) (hG_props r hrG).2.2.2.1 2
      have hle_int : ∫ r in Ioc 0 h, ‖u₀ r‖ ^ 2 ≤ ∫ r in Ioc 0 h, N_δ (σ + r) := by
        refine integral_mono_ae hu₀_int_r hN_int_r ?_
        filter_upwards [hG_Ioc] with r ⟨_, _, hdat_r⟩
        have hm0 : MemLp (fun y => L (δ (σ + r, y))) 2 (cellμ p.c) := by
          rw [← cellMeas_eq_cellμ]; exact (hL_dat hdat_r).memL2.1
        have hu₀_eq : u₀ r = hm0.toLp _ := UnforcedLeray.BochnerTime.toPathLq_of_memLp hm0
        rw [hu₀_eq, Lp.norm_toLp]
        have hle_lp : eLpNorm (fun y => L (δ (σ + r, y))) 2 (cellμ p.c) ≤
            F8U.cellL2 p.c (F8U.slice δ (σ + r)) := by
          unfold F8U.cellL2
          rw [← cellMeas_eq_cellμ]
          exact eLpNorm_mono fun y => hL_norm _
        have hfin : F8U.cellL2 p.c (F8U.slice δ (σ + r)) ≠ ⊤ := hdat_r.memL2.1.eLpNorm_lt_top.ne
        exact pow_le_pow_left₀ ENNReal.toReal_nonneg
          ((ENNReal.toReal_le_toReal hm0.eLpNorm_lt_top.ne hfin).2 hle_lp) 2
      rw [← hshift_eq]
      exact mul_le_mul_of_nonneg_left hle_int (inv_nonneg.2 hh.1.le)
  -- Apply real_unit_weak_unique and transfer back to s ∈ Ioo σ (σ + 1)
  have hu₀_zero := real_unit_weak_unique hc hν hMV hB hu₀_sm huq_sm huη_sm hb_sm
    hG_sub hG_ae hG_props hwk_1d htrace_L
  have hu₀_unr : ∀ᵐ r ∂volume, r ∈ Ioo (0 : ℝ) 1 → u₀ r = 0 :=
    (ae_restrict_iff' measurableSet_Ioo).1 hu₀_zero
  have hu₀_sub : ∀ᵐ s ∂volume, s - σ ∈ Ioo (0 : ℝ) 1 → u₀ (s - σ) = 0 :=
    (measurePreserving_sub_right volume σ).quasiMeasurePreserving.ae hu₀_unr
  filter_upwards [hu₀_sub, hslice_dat] with s hs0 hdat hs_mem
  have hr_Ioo : s - σ ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hs_mem.1], by linarith [hs_mem.2]⟩
  have hs_eq : σ + (s - σ) = s := by ring
  have hm0 : MemLp (fun y => L (δ (σ + (s - σ), y))) 2 (cellμ p.c) := by
    rw [hs_eq, ← cellMeas_eq_cellμ]
    exact (hL_dat (hdat hs_mem)).memL2.1
  have hu₀_eq : u₀ (s - σ) = hm0.toLp _ := UnforcedLeray.BochnerTime.toPathLq_of_memLp hm0
  have htoLp_zero : hm0.toLp (fun y => L (δ (σ + (s - σ), y))) = 0 := hu₀_eq.symm.trans (hs0 hr_Ioo)
  have hzero_ae : (hm0.toLp (fun y => L (δ (σ + (s - σ), y))) : Plane → Vec2) =ᵐ[cellμ p.c] 0 := by
    rw [htoLp_zero]
    exact Lp.coeFn_zero Vec2 2 (cellμ p.c)
  filter_upwards [hm0.coeFn_toLp, hzero_ae] with y hy hy0
  rw [← hs_eq]
  exact hy.symm.trans hy0

end UnforcedLeray.Short.IIb.UnitWeakUniqueAux

namespace UnforcedLeray.Short.IIb

/-- **Proof of `CylUnitWeakHomogeneousUnique` (`PartII-b:F8/1/org/3/2`, SP 2301–2305).** -/
theorem cylUnitWeakHomogeneousUnique_proof : CylUnitWeakHomogeneousUnique := by
  intro dm dp p d hreg _hν_le σ hσ δ δq δη B hB
    hsm_δ hsm_δq hsm_δη hper_δ hper_δq hper_δη
    hslice_bdd hslice_dat _hwk_q _hwk_η _hsol heq htrace
  have hnorm_re : ∀ z : CMerid, ‖F8Ex.reMerid z‖ ≤ ‖z‖ := by
    intro z
    rw [← F8Ex.norm_ofRealMerid]
    have hsq : ‖F8Ex.ofRealMerid (F8Ex.reMerid z)‖ ^ 2 ≤ ‖z‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Fin.sum_univ_two, Fin.sum_univ_two]
      simp only [F8Ex.ofRealMerid_apply, F8Ex.reMerid_apply, Complex.norm_real, Real.norm_eq_abs,
        sq_abs]
      have h0 : (z 0).re ^ 2 ≤ ‖z 0‖ ^ 2 := pow_le_pow_left₀ (abs_nonneg _)
        (Complex.abs_re_le_norm (z 0)) 2 |>.trans' (by rw [sq_abs])
      have h1 : (z 1).re ^ 2 ≤ ‖z 1‖ ^ 2 := pow_le_pow_left₀ (abs_nonneg _)
        (Complex.abs_re_le_norm (z 1)) 2 |>.trans' (by rw [sq_abs])
      linarith
    exact nonneg_le_nonneg_of_sq_le_sq (norm_nonneg _) (by linarith)
  have hnorm_im : ∀ z : CMerid, ‖F8Ex.imMerid z‖ ≤ ‖z‖ := by
    intro z
    rw [← F8Ex.norm_ofImagMerid]
    have hsq : ‖F8Ex.ofImagMerid (F8Ex.imMerid z)‖ ^ 2 ≤ ‖z‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Fin.sum_univ_two, Fin.sum_univ_two]
      simp only [F8Ex.ofImagMerid_apply, F8Ex.imMerid_apply, norm_mul, Complex.norm_I, one_mul,
        Complex.norm_real, Real.norm_eq_abs, sq_abs]
      have h0 : (z 0).im ^ 2 ≤ ‖z 0‖ ^ 2 := pow_le_pow_left₀ (abs_nonneg _)
        (Complex.abs_im_le_norm (z 0)) 2 |>.trans' (by rw [sq_abs])
      have h1 : (z 1).im ^ 2 ≤ ‖z 1‖ ^ 2 := pow_le_pow_left₀ (abs_nonneg _)
        (Complex.abs_im_le_norm (z 1)) 2 |>.trans' (by rw [sq_abs])
      linarith
    exact nonneg_le_nonneg_of_sq_le_sq (norm_nonneg _) (by linarith)
  have hre_zero := UnitWeakUniqueAux.proj_slice_zero_ae hreg hσ hB
    hsm_δ hsm_δq hsm_δη hper_δ hper_δq hper_δη hslice_bdd hslice_dat heq htrace
    F8Ex.reMerid Complex.reCLM
    (fun z k => F8Ex.reMerid_apply z k)
    (fun w a => by simp [Complex.mul_re])
    (fun a w => by simp [Complex.mul_re])
    hnorm_re
    (fun hd => (F8Ex.split_cylH1Datum hd).1)
  have him_zero := UnitWeakUniqueAux.proj_slice_zero_ae hreg hσ hB
    hsm_δ hsm_δq hsm_δη hper_δ hper_δq hper_δη hslice_bdd hslice_dat heq htrace
    F8Ex.imMerid Complex.imCLM
    (fun z k => F8Ex.imMerid_apply z k)
    (fun w a => by simp [Complex.mul_im])
    (fun a w => by simp [Complex.mul_im])
    hnorm_im
    (fun hd => (F8Ex.split_cylH1Datum hd).2)
  have hcell_zero : ∀ᵐ s ∂volume, s ∈ Ioo σ (σ + 1) →
      (fun y => δ (s, y)) =ᵐ[volume.restrict (B0579.cell p.c)] (fun _ => 0) := by
    filter_upwards [hre_zero, him_zero] with s hre him hs
    have hre' : (fun y => F8Ex.reMerid (δ (s, y))) =ᵐ[volume.restrict (B0579.cell p.c)] 0 := by
      rw [UnitWeakUniqueAux.b0579_cell_eq_cyl_cell]; exact hre hs
    have him' : (fun y => F8Ex.imMerid (δ (s, y))) =ᵐ[volume.restrict (B0579.cell p.c)] 0 := by
      rw [UnitWeakUniqueAux.b0579_cell_eq_cyl_cell]; exact him hs
    filter_upwards [hre', him'] with y hy_re hy_im
    rw [← F8Ex.combineMerid_re_im (δ (s, y)), hy_re, hy_im]
    ext k; simp [F8Ex.combineMerid_apply]
  exact F8Duh.ae_vol_eq_on_Ioo_of_ae_cell_periodic p.c_pos hσ
    hsm_δ stronglyMeasurable_const hper_δ (Eventually.of_forall fun _ => rfl) hcell_zero

end UnforcedLeray.Short.IIb
