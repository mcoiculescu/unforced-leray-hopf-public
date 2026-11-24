import UnforcedLeray.Short.PartI.Sub.PartI_T22_1
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.RawJet.Leaves.VcJetSup.AgeJetLe

/-!
# `PartI:T22/2` Sub-module: Post-overlap higher age-derivative (`ℓ ≥ 1`) fluctuation decay

Source of record: `the November 2 reference manuscript`, lines 439-446, 523-526.

This module proves:
1. **Unconditional base case (`ℓ = 0`) of `TrainPostOverlapAgeDerivFromZero`**
   (`trainPostOverlapAgeDeriv_zero` and `trainPostOverlapVelPressOrderSup_zero`):
   combines `hVel0 : TrainPostOverlapVelZero` and `hSP0 : TrainPostOverlapStreamPressureZero` into
   the unified `ℓ = 0` post-overlap exponential bound for `(ψ_fluct, v_fluct, tr.p)`.
2. **Unconditional upgrade at any age order `r : ℕ` from unweighted `(v_fluct, tr.p)` bounds to full
   `(wCellL2 c 0 ∧ wSupNorm 0)` bounds for `(ψ_fluct, v_fluct, tr.p)`**
   (`trainPostOverlapFullOrder_of_velPressSup`):
   uses `PartI_T22.postOverlap_streamFluct_of_velFluct_sup` (for `ψ_fluct` from `v_fluct` at
   spatial order `j - 1`) and `PartI_T22.wCellL2_zero_and_wSupNorm_zero_of_wSupNorm_zero` (for
   `v_fluct` and `tr.p`) together with the weight-`4` polynomial tails `hTails.2.2`.
3. **Unconditional viscous and pressure-gradient step bounds at age order `ℓ`**
   (`PartI_T22.norm_ageJet_smul_vecLaplacian_le`, `PartI_T22.norm_ageJet_gradS_le`,
   `trainPostOverlapViscFluct_of_order`, `trainPostOverlapGradSPress_of_order`):
   proves that `ageJet ℓ j (ν • vecLaplacian v_fluct)` is bounded by `(2 * ν) * ageJet ℓ (j + 2) v_fluct`
   and `ageJet ℓ j (gradS tr.p)` is bounded by `2 * ageJet ℓ (j + 1) tr.p`, so both decay
   exponentially after overlap under `TrainPostOverlapVelPressOrderSup ℓ`.
4. **Strong induction in `ℓ` (`trainPostOverlapVelPressOrderSup_all`) and conditional assembly
   (`trainPostOverlapAgeDerivFromZero_of`)**:
   reduces `TrainPostOverlapAgeDerivFromZero` to the two inductive step leaves:
   * `TrainPostOverlapVelFluctHigherStep` (`PartI:T22/2/1`, velocity fluctuation `ageJet (ℓ + 1) j v_fluct`
     from orders `≤ ℓ` via the differentiated fluctuation momentum equation),
   * `TrainPostOverlapPressureHigherStep` (`PartI:T22/2/2`, pressure `ageJet (ℓ + 1) j tr.p` from
     velocity fluctuation orders `≤ ℓ + 1` and pressure orders `≤ ℓ` via the differentiated
     cylinder pressure equation).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec jet cellL2 wCellL2 jap)
open UnforcedLeray.Short.IIb (UU isOpen_UU mem_UU Dx eT eQ eE LapU Sm Dx_congr LapU_congr
  LapU_comm_t hasDerivAt_slice slice_lapD lapD vecLaplacian_eq_lapD norm_jet_lapD_le)

namespace PartI_T22

/-! ### 1. Viscous Laplacian and pressure gradient `ageJet` domination on `(0, ∞) × Plane` -/

/-- Iterated age directional derivative `(Dx eT)^[ℓ] F` on `ℝ × Plane`. -/
def DtU (ℓ : ℕ) (F : ℝ × Plane → Vec) : ℝ × Plane → Vec :=
  (Dx eT)^[ℓ] F

theorem sm_DtU {F : ℝ × Plane → Vec} (hF : Sm F) : ∀ ℓ : ℕ, Sm (DtU ℓ F)
  | 0 => hF
  | ℓ + 1 => by
    unfold DtU
    rw [Function.iterate_succ_apply']
    exact (sm_DtU hF ℓ).dx eT

theorem iteratedDeriv_slice_eq_DtU {F : ℝ × Plane → Vec} (hF : Sm F) :
    ∀ (ℓ : ℕ) {t : ℝ}, 0 < t → ∀ w : Plane,
      iteratedDeriv ℓ (fun r => F (r, w)) t = DtU ℓ F (t, w)
  | 0, _, _, _ => rfl
  | ℓ + 1, t, ht, w => by
    rw [iteratedDeriv_succ]
    have hev : iteratedDeriv ℓ (fun r => F (r, w)) =ᶠ[nhds t] fun r => DtU ℓ F (r, w) := by
      filter_upwards [Ioi_mem_nhds ht] with r hr using iteratedDeriv_slice_eq_DtU hF ℓ hr w
    rw [hev.deriv_eq, (hasDerivAt_slice (sm_DtU hF ℓ) ht w).deriv]
    unfold DtU
    rw [Function.iterate_succ_apply']

theorem DtU_comm_LapU {F : ℝ × Plane → Vec} (hF : Sm F) :
    ∀ ℓ : ℕ, EqOn (DtU ℓ (LapU F)) (LapU (DtU ℓ F)) UU
  | 0 => fun _ _ => rfl
  | ℓ + 1 => by
    intro x hx
    have hDt : ∀ G : ℝ × Plane → Vec, DtU (ℓ + 1) G = Dx eT (DtU ℓ G) :=
      fun G => Function.iterate_succ_apply' (Dx eT) ℓ G
    rw [hDt, hDt, Dx_congr (DtU_comm_LapU hF ℓ) eT hx]
    exact LapU_comm_t (sm_DtU hF ℓ) hx

theorem contDiff_slice_of_sm {F : ℝ → Plane → Vec}
    (hF : Sm (fun x : ℝ × Plane => F x.1 x.2)) {t : ℝ} (ht : 0 < t) :
    ContDiff ℝ ∞ (F t) := by
  rw [← contDiffOn_univ]
  exact hF.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ _ => mem_UU ht)

theorem vecLaplacian_slice_eq_LapU {F : ℝ → Plane → Vec}
    (hF : Sm (fun x : ℝ × Plane => F x.1 x.2)) {t : ℝ} (ht : 0 < t) (w : Plane) :
    Train.vecLaplacian (F t) w = LapU (fun x : ℝ × Plane => F x.1 x.2) (t, w) := by
  have hu : ContDiff ℝ ∞ (F t) := contDiff_slice_of_sm hF ht
  rw [vecLaplacian_eq_lapD hu]
  exact congrFun (slice_lapD hF ht) w

/-- Commutation of `iteratedDeriv ℓ` in age with `ν • Train.vecLaplacian` for jointly smooth `F`. -/
theorem iteratedDeriv_smul_vecLaplacian_eq {F : ℝ → Plane → Vec}
    (hF : Sm (fun x : ℝ × Plane => F x.1 x.2)) (ν : ℝ) (ℓ : ℕ) {s : ℝ} (hs : 0 < s) (w : Plane) :
    iteratedDeriv ℓ (fun r => ν • Train.vecLaplacian (F r) w) s =
      ν • lapD (fun x => iteratedDeriv ℓ (fun r => F r x) s) w := by
  let U : ℝ × Plane → Vec := fun x => F x.1 x.2
  have hev : (fun r => ν • Train.vecLaplacian (F r) w) =ᶠ[nhds s]
      fun r => ν • LapU U (r, w) := by
    filter_upwards [Ioi_mem_nhds hs] with r hr
    rw [vecLaplacian_slice_eq_LapU hF hr w]
  rw [hev.iteratedDeriv_eq ℓ]
  change iteratedDeriv ℓ (ν • fun r => LapU U (r, w)) s = _
  rw [iteratedDeriv_const_smul_field]
  congr 1
  rw [iteratedDeriv_slice_eq_DtU hF.lap ℓ hs w, DtU_comm_LapU hF ℓ (mem_UU hs)]
  rw [← congrFun (slice_lapD (sm_DtU hF ℓ) hs) w]
  congr 1
  funext x
  exact (iteratedDeriv_slice_eq_DtU hF ℓ hs x).symm

/-- Pointwise bound `‖ageJet ℓ j (fun r w => ν • Train.vecLaplacian (F r) w) s z‖ ≤ (2 * ν) * ‖ageJet ℓ (j + 2) F s z‖`
for jointly smooth `F` and `ν ≥ 0`, `s > 0`. -/
theorem norm_ageJet_smul_vecLaplacian_le {F : ℝ → Plane → Vec}
    (hF : Sm (fun x : ℝ × Plane => F x.1 x.2)) {ν : ℝ} (hν : 0 ≤ ν)
    (ℓ j : ℕ) {s : ℝ} (hs : 0 < s) (z : Plane) :
    ‖ageJet ℓ j (fun r w => ν • Train.vecLaplacian (F r) w) s z‖ ≤
      (2 * ν) * ‖ageJet ℓ (j + 2) F s z‖ := by
  have hslice : (fun w => iteratedDeriv ℓ (fun r => ν • Train.vecLaplacian (F r) w) s) =
      fun w => ν • lapD (fun x => iteratedDeriv ℓ (fun r => F r x) s) w :=
    funext fun w => iteratedDeriv_smul_vecLaplacian_eq hF ν ℓ hs w
  have hu : ContDiff ℝ ∞ (fun x : Plane => iteratedDeriv ℓ (fun r => F r x) s) :=
    contDiff_slice_iteratedDeriv hF ℓ hs
  have hlap : ContDiffAt ℝ j (lapD (fun x => iteratedDeriv ℓ (fun r => F r x) s)) z :=
    ((UnforcedLeray.Short.IIb.contDiff_lapD hu).of_le (by exact_mod_cast le_top)).contDiffAt
  have heq : ageJet ℓ j (fun r w => ν • Train.vecLaplacian (F r) w) s z =
      ν • iteratedFDeriv ℝ j (lapD (fun x => iteratedDeriv ℓ (fun r => F r x) s)) z := by
    unfold ageJet jet
    rw [hslice]
    exact iteratedFDeriv_const_smul_apply' hlap
  rw [heq, norm_smul, Real.norm_of_nonneg hν]
  have h1 := norm_jet_lapD_le hu j z
  unfold ageJet jet
  nlinarith

/-- The continuous linear map `T ↦ toVec (T (1, 0), T (0, 1))` representing `Train.gradS` on
the Fréchet derivative space `Plane →L[ℝ] ℝ`. -/
def gradSLam : (Plane →L[ℝ] ℝ) →L[ℝ] Vec :=
  (Train.toVecL : (ℝ × ℝ) →L[ℝ] Vec).comp
    ((ContinuousLinearMap.apply ℝ ℝ ((1 : ℝ), (0 : ℝ))).prod
      (ContinuousLinearMap.apply ℝ ℝ ((0 : ℝ), (1 : ℝ))))

theorem gradSLam_apply (T : Plane →L[ℝ] ℝ) :
    gradSLam T = Train.toVec (T (1, 0), T (0, 1)) := rfl

theorem norm_gradSLam_le : ‖gradSLam‖ ≤ 2 := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) (fun T => ?_)
  have h10 : ‖((1 : ℝ), (0 : ℝ))‖ ≤ 1 := by rw [Prod.norm_def]; simp
  have h01 : ‖((0 : ℝ), (1 : ℝ))‖ ≤ 1 := by rw [Prod.norm_def]; simp
  have ha : |T (1, 0)| ≤ ‖T‖ := by
    have h1 := T.le_opNorm ((1 : ℝ), (0 : ℝ))
    rw [Real.norm_eq_abs] at h1
    have h2 : ‖T‖ * ‖((1 : ℝ), (0 : ℝ))‖ ≤ ‖T‖ * 1 :=
      mul_le_mul_of_nonneg_left h10 (norm_nonneg _)
    linarith
  have hb : |T (0, 1)| ≤ ‖T‖ := by
    have h1 := T.le_opNorm ((0 : ℝ), (1 : ℝ))
    rw [Real.norm_eq_abs] at h1
    have h2 : ‖T‖ * ‖((0 : ℝ), (1 : ℝ))‖ ≤ ‖T‖ * 1 :=
      mul_le_mul_of_nonneg_left h01 (norm_nonneg _)
    linarith
  rw [gradSLam_apply, Train.norm_toVec]
  have hsq : (T (1, 0)) ^ 2 + (T (0, 1)) ^ 2 ≤ (2 * ‖T‖) ^ 2 := by
    have ha2 : (T (1, 0)) ^ 2 ≤ ‖T‖ ^ 2 :=
      sq_le_sq.mpr (by simpa [abs_of_nonneg (norm_nonneg T)] using ha)
    have hb2 : (T (0, 1)) ^ 2 ≤ ‖T‖ ^ 2 :=
      sq_le_sq.mpr (by simpa [abs_of_nonneg (norm_nonneg T)] using hb)
    have hT2 : 0 ≤ ‖T‖ ^ 2 := sq_nonneg ‖T‖
    nlinarith
  calc Real.sqrt ((T (1, 0)) ^ 2 + (T (0, 1)) ^ 2)
      ≤ Real.sqrt ((2 * ‖T‖) ^ 2) := Real.sqrt_le_sqrt hsq
    _ = 2 * ‖T‖ := Real.sqrt_sq (by positivity)

/-- Pointwise bound `‖jet k (Train.gradS u) z‖ ≤ 2 * ‖jet (k + 1) u z‖` for smooth `u : Plane → ℝ`. -/
theorem norm_jet_gradS_le (k : ℕ) {u : Plane → ℝ} (hu : ContDiff ℝ ∞ u) (z : Plane) :
    ‖jet k (Train.gradS u) z‖ ≤ 2 * ‖jet (k + 1) u z‖ := by
  have hdiff : Differentiable ℝ u := hu.differentiable (by simp)
  have hg : ContDiff ℝ ∞ (fderiv ℝ u) := (contDiff_infty_iff_fderiv.mp hu).2
  have hfun : Train.gradS u = fun w => gradSLam (fderiv ℝ u w) := by
    funext w
    unfold Train.gradS
    rw [Cyl.partialQ_eq_fderiv hdiff w, Cyl.partialEta_eq_fderiv hdiff w, gradSLam_apply]
  have hcomp : (gradSLam ∘ fderiv ℝ u) = Train.gradS u := by rw [hfun]; rfl
  have hiter : iteratedFDeriv ℝ k (Train.gradS u) z =
      gradSLam.compContinuousMultilinearMap (iteratedFDeriv ℝ k (fderiv ℝ u) z) := by
    rw [← hcomp]
    exact ContinuousLinearMap.iteratedFDeriv_comp_left gradSLam
      hg.contDiffAt (by exact_mod_cast le_top)
  unfold jet
  rw [hiter]
  have hnorm := ContinuousLinearMap.norm_compContinuousMultilinearMap_le gradSLam
    (iteratedFDeriv ℝ k (fderiv ℝ u) z)
  rw [norm_iteratedFDeriv_fderiv] at hnorm
  calc ‖gradSLam.compContinuousMultilinearMap (iteratedFDeriv ℝ k (fderiv ℝ u) z)‖
      ≤ ‖gradSLam‖ * ‖iteratedFDeriv ℝ (k + 1) u z‖ := hnorm
    _ ≤ 2 * ‖iteratedFDeriv ℝ (k + 1) u z‖ :=
        mul_le_mul_of_nonneg_right norm_gradSLam_le (norm_nonneg _)

/-- Directional derivative of a scalar field on `ℝ × Plane`. -/
def DxS (v : ℝ × Plane) (P : ℝ × Plane → ℝ) : ℝ × Plane → ℝ :=
  fun x => fderiv ℝ P x v

theorem contDiffOn_DxS {P : ℝ × Plane → ℝ} (hP : ContDiffOn ℝ ∞ P UU) (v : ℝ × Plane) :
    ContDiffOn ℝ ∞ (DxS v P) UU :=
  (hP.fderiv_of_isOpen isOpen_UU (by simp)).clm_apply contDiffOn_const

theorem DxS_symm {P : ℝ × Plane → ℝ} (hP : ContDiffOn ℝ ∞ P UU) {x : ℝ × Plane} (hx : x ∈ UU)
    (v w : ℝ × Plane) : DxS w (DxS v P) x = DxS v (DxS w P) x := by
  have hc : ContDiffAt ℝ ∞ P x := hP.contDiffAt (isOpen_UU.mem_nhds hx)
  have hc2 : ContDiffAt ℝ ((2 : ℕ) : WithTop ℕ∞) P x := hc.of_le (by simp)
  have hn : minSmoothness ℝ 2 ≤ ((2 : ℕ) : WithTop ℕ∞) := by
    rw [minSmoothness_of_isRCLikeNormedField]; simp
  have hs := ContDiffAt.isSymmSndFDerivAt hc2 hn
  have hd : DifferentiableAt ℝ (fderiv ℝ P) x :=
    ((hP.fderiv_of_isOpen (m := ∞) isOpen_UU (by simp)).differentiableOn (by simp)).differentiableAt
      (isOpen_UU.mem_nhds hx)
  have key : ∀ a b : ℝ × Plane, DxS a (DxS b P) x = fderiv ℝ (fderiv ℝ P) x a b := by
    intro a b
    show fderiv ℝ (fun y => fderiv ℝ P y b) x a = _
    rw [fderiv_clm_apply hd (differentiableAt_const b)]
    simp
  rw [key, key]
  exact hs w v

theorem DxS_congr {P P' : ℝ × Plane → ℝ} (h : EqOn P P' UU) (v : ℝ × Plane) :
    EqOn (DxS v P) (DxS v P') UU := by
  intro x hx
  have : P =ᶠ[nhds x] P' := h.eventuallyEq_of_mem (isOpen_UU.mem_nhds hx)
  show fderiv ℝ P x v = fderiv ℝ P' x v
  rw [this.fderiv_eq]

theorem hasDerivAt_sliceS {P : ℝ × Plane → ℝ} (hP : ContDiffOn ℝ ∞ P UU)
    {t : ℝ} (ht : 0 < t) (w : Plane) :
    HasDerivAt (fun r => P (r, w)) (DxS eT P (t, w)) t := by
  have h0 : HasDerivAt (fun r : ℝ => (r, w)) ((1 : ℝ), (0 : Plane)) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t w)
  have hd : DifferentiableAt ℝ P (t, w) :=
    (hP.differentiableOn (by simp)).differentiableAt (isOpen_UU.mem_nhds (mem_UU ht))
  exact hd.hasFDerivAt.comp_hasDerivAt t h0

/-- The `ℓ`-th age directional derivative `(DxS eT)^[ℓ] P` of a scalar field on `ℝ × Plane`. -/
def DtS (ℓ : ℕ) (P : ℝ × Plane → ℝ) : ℝ × Plane → ℝ :=
  (DxS eT)^[ℓ] P

theorem contDiffOn_DtS {P : ℝ × Plane → ℝ} (hP : ContDiffOn ℝ ∞ P UU) :
    ∀ ℓ : ℕ, ContDiffOn ℝ ∞ (DtS ℓ P) UU
  | 0 => hP
  | ℓ + 1 => by
    unfold DtS
    rw [Function.iterate_succ_apply']
    exact contDiffOn_DxS (contDiffOn_DtS hP ℓ) eT

theorem iteratedDeriv_slice_eq_DtS {P : ℝ × Plane → ℝ} (hP : ContDiffOn ℝ ∞ P UU) :
    ∀ (ℓ : ℕ) {t : ℝ}, 0 < t → ∀ w : Plane,
      iteratedDeriv ℓ (fun r => P (r, w)) t = DtS ℓ P (t, w)
  | 0, _, _, _ => rfl
  | ℓ + 1, t, ht, w => by
    rw [iteratedDeriv_succ]
    have hev : iteratedDeriv ℓ (fun r => P (r, w)) =ᶠ[nhds t] fun r => DtS ℓ P (r, w) := by
      filter_upwards [Ioi_mem_nhds ht] with r hr using iteratedDeriv_slice_eq_DtS hP ℓ hr w
    rw [hev.deriv_eq, (hasDerivAt_sliceS (contDiffOn_DtS hP ℓ) ht w).deriv]
    unfold DtS
    rw [Function.iterate_succ_apply']

theorem iteratedDeriv_slice_toVec_eq_DtS {G1 G2 : ℝ × Plane → ℝ}
    (hG1 : ContDiffOn ℝ ∞ G1 UU) (hG2 : ContDiffOn ℝ ∞ G2 UU) :
    ∀ (ℓ : ℕ) {t : ℝ}, 0 < t → ∀ w : Plane,
      iteratedDeriv ℓ (fun r => Train.toVec (G1 (r, w), G2 (r, w))) t =
        Train.toVec (DtS ℓ G1 (t, w), DtS ℓ G2 (t, w))
  | 0, _, _, _ => rfl
  | ℓ + 1, t, ht, w => by
    rw [iteratedDeriv_succ]
    have hev : iteratedDeriv ℓ (fun r => Train.toVec (G1 (r, w), G2 (r, w))) =ᶠ[nhds t]
        fun r => Train.toVec (DtS ℓ G1 (r, w), DtS ℓ G2 (r, w)) := by
      filter_upwards [Ioi_mem_nhds ht] with r hr using
        iteratedDeriv_slice_toVec_eq_DtS hG1 hG2 ℓ hr w
    rw [hev.deriv_eq]
    have hd12 : HasDerivAt (fun r => (DtS ℓ G1 (r, w), DtS ℓ G2 (r, w)))
        (DxS eT (DtS ℓ G1) (t, w), DxS eT (DtS ℓ G2) (t, w)) t :=
      (hasDerivAt_sliceS (contDiffOn_DtS hG1 ℓ) ht w).prodMk
        (hasDerivAt_sliceS (contDiffOn_DtS hG2 ℓ) ht w)
    have hd : HasDerivAt (fun r => Train.toVec (DtS ℓ G1 (r, w), DtS ℓ G2 (r, w)))
        (Train.toVec (DxS eT (DtS ℓ G1) (t, w), DxS eT (DtS ℓ G2) (t, w))) t :=
      (Train.toVecL : (ℝ × ℝ) →L[ℝ] Vec).hasFDerivAt.comp_hasDerivAt t hd12
    rw [hd.deriv]
    unfold DtS
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']

theorem DtS_comm_DxS {P : ℝ × Plane → ℝ} (hP : ContDiffOn ℝ ∞ P UU) (v : ℝ × Plane) :
    ∀ ℓ : ℕ, EqOn (DxS v (DtS ℓ P)) (DtS ℓ (DxS v P)) UU
  | 0 => fun _ _ => rfl
  | ℓ + 1 => by
    intro x hx
    unfold DtS
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    change DxS v (DxS eT (DtS ℓ P)) x = DxS eT (DtS ℓ (DxS v P)) x
    rw [DxS_symm (contDiffOn_DtS hP ℓ) hx eT v]
    exact DxS_congr (DtS_comm_DxS hP v ℓ) eT hx

theorem slice_DvS {P : ℝ × Plane → ℝ} (hP : ContDiffOn ℝ ∞ P UU)
    {t : ℝ} (ht : 0 < t) (e : Plane) (w : Plane) :
    fderiv ℝ (fun x : Plane => P (t, x)) w e = DxS (0, e) P (t, w) := by
  have h1 : HasFDerivAt (fun x : Plane => (t, x)) (ContinuousLinearMap.inr ℝ ℝ Plane) w :=
    hasFDerivAt_prodMk_right t w
  have hd : DifferentiableAt ℝ P (t, w) :=
    (hP.differentiableOn (by simp)).differentiableAt (isOpen_UU.mem_nhds (mem_UU ht))
  have h2 := hd.hasFDerivAt.comp w h1
  show fderiv ℝ (P ∘ fun x : Plane => (t, x)) w e = fderiv ℝ P (t, w) (0, e)
  rw [h2.fderiv]
  rfl

theorem gradS_slice_eq_DxS {P : ℝ × Plane → ℝ} (hP : ContDiffOn ℝ ∞ P UU)
    {t : ℝ} (ht : 0 < t) (w : Plane) :
    Train.gradS (fun x => P (t, x)) w = Train.toVec (DxS eQ P (t, w), DxS eE P (t, w)) := by
  have hu : ContDiff ℝ ∞ (fun x : Plane => P (t, x)) := by
    rw [← contDiffOn_univ]
    exact hP.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ _ => mem_UU ht)
  have hdu : Differentiable ℝ (fun x : Plane => P (t, x)) := hu.differentiable (by simp)
  unfold Train.gradS
  rw [Cyl.partialQ_eq_fderiv hdu w, Cyl.partialEta_eq_fderiv hdu w,
    slice_DvS hP ht ((1 : ℝ), (0 : ℝ)) w, slice_DvS hP ht ((0 : ℝ), (1 : ℝ)) w]
  rfl

/-- Commutation of `iteratedDeriv ℓ` in age with spatial `Train.gradS` for a jointly smooth
scalar field at `s > 0`. -/
theorem iteratedDeriv_gradS_eq {P : ℝ → Plane → ℝ}
    (hP : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => P x.1 x.2) (Ioi 0 ×ˢ univ))
    (ℓ : ℕ) {s : ℝ} (hs : 0 < s) (w : Plane) :
    iteratedDeriv ℓ (fun r => Train.gradS (P r) w) s =
      Train.gradS (fun x => iteratedDeriv ℓ (fun r => P r x) s) w := by
  let U : ℝ × Plane → ℝ := fun x => P x.1 x.2
  have hev : (fun r => Train.gradS (P r) w) =ᶠ[nhds s]
      fun r => Train.toVec (DxS eQ U (r, w), DxS eE U (r, w)) := by
    filter_upwards [Ioi_mem_nhds hs] with r hr using gradS_slice_eq_DxS hP hr w
  rw [hev.iteratedDeriv_eq]
  rw [iteratedDeriv_slice_toVec_eq_DtS (contDiffOn_DxS hP eQ) (contDiffOn_DxS hP eE) ℓ hs w]
  rw [← DtS_comm_DxS hP eQ ℓ (mem_UU hs), ← DtS_comm_DxS hP eE ℓ (mem_UU hs)]
  rw [← gradS_slice_eq_DxS (contDiffOn_DtS hP ℓ) hs w]
  congr 1
  funext x
  exact (iteratedDeriv_slice_eq_DtS hP ℓ hs x).symm

/-- Pointwise bound `‖ageJet ℓ j (fun r w => Train.gradS (P r) w) s z‖ ≤ 2 * ‖ageJet ℓ (j + 1) P s z‖`
for jointly smooth scalar fields `P` at `s > 0`. -/
theorem norm_ageJet_gradS_le {P : ℝ → Plane → ℝ}
    (hP : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => P x.1 x.2) (Ioi 0 ×ˢ univ))
    (ℓ j : ℕ) {s : ℝ} (hs : 0 < s) (z : Plane) :
    ‖ageJet ℓ j (fun r w => Train.gradS (P r) w) s z‖ ≤ 2 * ‖ageJet ℓ (j + 1) P s z‖ := by
  have hslice : (fun w => iteratedDeriv ℓ (fun r => Train.gradS (P r) w) s) =
      Train.gradS (fun x => iteratedDeriv ℓ (fun r => P r x) s) :=
    funext fun w => iteratedDeriv_gradS_eq hP ℓ hs w
  have hu : ContDiff ℝ ∞ (fun x : Plane => iteratedDeriv ℓ (fun r => P r x) s) :=
    contDiff_slice_iteratedDeriv hP ℓ hs
  unfold ageJet
  rw [hslice]
  exact norm_jet_gradS_le j hu z

/-- Monotonicity of `wSupNorm m` under a pointwise norm bound `‖f z‖ ≤ K * ‖g z‖`. -/
theorem wSupNorm_le_of_pointwise {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    (m : ℕ) {K : ℝ} (hK : 0 ≤ K) (f : Plane → E) (g : Plane → F)
    (hpt : ∀ z : Plane, ‖f z‖ ≤ K * ‖g z‖) :
    wSupNorm m f ≤ ENNReal.ofReal K * wSupNorm m g := by
  unfold wSupNorm
  rw [ENNReal.mul_iSup]
  refine iSup_mono fun z => ?_
  rw [← mul_assoc, mul_comm (ENNReal.ofReal K), mul_assoc]
  gcongr
  rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul hK]
  exact ENNReal.ofReal_le_ofReal (hpt z)

end PartI_T22

/-! ### 2. Base case (`ℓ = 0`) and age-order `r` inductive hierarchy -/

/-- **Unconditional `ℓ = 0` case of `TrainPostOverlapAgeDerivFromZero`:**
unifies `hVel0 : TrainPostOverlapVelZero` and `hSP0 : TrainPostOverlapStreamPressureZero` at
`ℓ = 0` for all spatial orders `j : ℕ`. -/
theorem trainPostOverlapAgeDeriv_zero
    (hVel0 : TrainPostOverlapVelZero)
    (hSP0 : TrainPostOverlapStreamPressureZero)
    (ρ : ℝ) (hρ : 1 / 2 < ρ) (j : ℕ) :
    ∃ C : ℝ, ∃ N : ℕ, ∃ lam ν₀ : ℝ,
      0 < C ∧ 0 < lam ∧ 0 < ν₀ ∧
      ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
        ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr →
          ∀ s : ℝ, 0 < s → B0146.overlapAge ν (trainPeriod ρ ν) ≤ s →
            let c := trainPeriod ρ ν
            let K : ℝ≥0∞ := ENNReal.ofReal (polyP C N ν c * Real.exp (-(lam * ν * s / c ^ 2)))
            (wCellL2 c 0 (ageJet 0 j (fun r z => tr.ψ r z - hmean c (tr.ψ r) z.2) s) ≤ K ∧
              wSupNorm 0 (ageJet 0 j (fun r z => tr.ψ r z - hmean c (tr.ψ r) z.2) s) ≤ K) ∧
            (wCellL2 c 0 (ageJet 0 j (fun r => hfluct c (tr.v r)) s) ≤ K ∧
              wSupNorm 0 (ageJet 0 j (fun r => hfluct c (tr.v r)) s) ≤ K) ∧
            (wCellL2 c 0 (ageJet 0 j tr.p s) ≤ K ∧
              wSupNorm 0 (ageJet 0 j tr.p s) ≤ K) := by
  obtain ⟨C₁, N₁, lam₁, ν₁, hC₁, hlam₁, hν₁, hv⟩ := hVel0 ρ hρ j
  obtain ⟨C₂, N₂, lam₂, ν₂, hC₂, hlam₂, hν₂, hsp⟩ := hSP0 ρ hρ j
  refine ⟨max C₁ C₂, max N₁ N₂, min lam₁ lam₂, min ν₁ ν₂,
    lt_max_of_lt_left hC₁, lt_min hlam₁ hlam₂, lt_min hν₁ hν₂, ?_⟩
  intro ν hν hν_le tr htr s hs hsc
  have hν₁_le : ν ≤ ν₁ := hν_le.trans (min_le_left _ _)
  have hν₂_le : ν ≤ ν₂ := hν_le.trans (min_le_right _ _)
  let c := trainPeriod ρ ν
  have hc0 : 0 ≤ c := Real.rpow_nonneg hν.le _
  have hν_inv : 0 ≤ ν⁻¹ := inv_nonneg.2 hν.le
  have h1X : 1 ≤ 1 + c + ν⁻¹ := by linarith
  obtain ⟨hv_L2, hv_Sup⟩ := hv ν hν hν₁_le tr htr s hs hsc
  obtain ⟨⟨hψ_L2, hψ_Sup⟩, ⟨hp_L2, hp_Sup⟩⟩ := hsp ν hν hν₂_le tr htr s hs hsc
  have hK₁ : polyP C₁ N₁ ν c * Real.exp (-(lam₁ * ν * s / c ^ 2)) ≤
      polyP (max C₁ C₂) (max N₁ N₂) ν c * Real.exp (-(min lam₁ lam₂ * ν * s / c ^ 2)) := by
    apply mul_le_mul
    · unfold polyP
      exact mul_le_mul (le_max_left _ _) (pow_le_pow_right₀ h1X (le_max_left _ _))
        (by positivity) (by positivity)
    · apply Real.exp_le_exp.2
      apply neg_le_neg
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (min_le_left _ _) hν.le) hs.le) (sq_nonneg c)
    · exact Real.exp_nonneg _
    · unfold polyP; positivity
  have hK₂ : polyP C₂ N₂ ν c * Real.exp (-(lam₂ * ν * s / c ^ 2)) ≤
      polyP (max C₁ C₂) (max N₁ N₂) ν c * Real.exp (-(min lam₁ lam₂ * ν * s / c ^ 2)) := by
    apply mul_le_mul
    · unfold polyP
      exact mul_le_mul (le_max_right _ _) (pow_le_pow_right₀ h1X (le_max_right _ _))
        (by positivity) (by positivity)
    · apply Real.exp_le_exp.2
      apply neg_le_neg
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (min_le_right _ _) hν.le) hs.le) (sq_nonneg c)
    · exact Real.exp_nonneg _
    · unfold polyP; positivity
  exact ⟨⟨hψ_L2.trans (ENNReal.ofReal_le_ofReal hK₂),
      hψ_Sup.trans (ENNReal.ofReal_le_ofReal hK₂)⟩,
    ⟨hv_L2.trans (ENNReal.ofReal_le_ofReal hK₁),
      hv_Sup.trans (ENNReal.ofReal_le_ofReal hK₁)⟩,
    ⟨hp_L2.trans (ENNReal.ofReal_le_ofReal hK₂),
      hp_Sup.trans (ENNReal.ofReal_le_ofReal hK₂)⟩⟩

/-- **Unweighted `wSupNorm 0` post-overlap exponential decay at age-derivative order `r : ℕ`**
for `(v_fluct, tr.p)` across all spatial derivative orders `j : ℕ`. -/
def TrainPostOverlapVelPressOrderSup (r : ℕ) : Prop :=
  ∀ ρ : ℝ, 1 / 2 < ρ → ∀ j : ℕ, ∃ C : ℝ, ∃ N : ℕ, ∃ lam ν₀ : ℝ,
    0 < C ∧ 0 < lam ∧ 0 < ν₀ ∧
    ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
      ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr →
        ∀ s : ℝ, 0 < s → B0146.overlapAge ν (trainPeriod ρ ν) ≤ s →
          let c := trainPeriod ρ ν
          let K := ENNReal.ofReal (polyP C N ν c * Real.exp (-(lam * ν * s / c ^ 2)))
          let v_fluct : ℝ → Plane → Vec := fun t => hfluct c (tr.v t)
          wSupNorm 0 (ageJet r j v_fluct s) ≤ K ∧
          wSupNorm 0 (ageJet r j tr.p s) ≤ K

/-- **Unconditional base case (`r = 0`) of `TrainPostOverlapVelPressOrderSup`:**
follows immediately from `hVel0 : TrainPostOverlapVelZero` and
`hSP0 : TrainPostOverlapStreamPressureZero`. -/
theorem trainPostOverlapVelPressOrderSup_zero
    (hVel0 : TrainPostOverlapVelZero)
    (hSP0 : TrainPostOverlapStreamPressureZero) :
    TrainPostOverlapVelPressOrderSup 0 := by
  intro ρ hρ j
  obtain ⟨C, N, lam, ν₀, hC, hlam, hν₀, h0⟩ := trainPostOverlapAgeDeriv_zero hVel0 hSP0 ρ hρ j
  refine ⟨C, N, lam, ν₀, hC, hlam, hν₀, ?_⟩
  intro ν hν hν_le tr htr s hs hsc
  obtain ⟨_, ⟨_, hv_Sup⟩, ⟨_, hp_Sup⟩⟩ := h0 ν hν hν_le tr htr s hs hsc
  exact ⟨hv_Sup, hp_Sup⟩

/-- **Unconditional viscous diffusion bound at age order `ℓ`:**
from `TrainPostOverlapVelPressOrderSup ℓ` (applied at spatial order `j + 2`),
`wSupNorm 0 (ageJet ℓ j (fun r z => ν • Train.vecLaplacian (hfluct c (tr.v r)) z) s)` decays
exponentially in `ν s / c²` on `s ≥ overlapAge ν c`. -/
theorem trainPostOverlapViscFluct_of_order (ℓ : ℕ)
    (hℓ : TrainPostOverlapVelPressOrderSup ℓ)
    (ρ : ℝ) (hρ : 1 / 2 < ρ) (j : ℕ) :
    ∃ C : ℝ, ∃ N : ℕ, ∃ lam ν₀ : ℝ,
      0 < C ∧ 0 < lam ∧ 0 < ν₀ ∧
      ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
        ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr →
          ∀ s : ℝ, 0 < s → B0146.overlapAge ν (trainPeriod ρ ν) ≤ s →
            let c := trainPeriod ρ ν
            let v_fluct : ℝ → Plane → Vec := fun r => hfluct c (tr.v r)
            wSupNorm 0 (ageJet ℓ j (fun r z => ν • Train.vecLaplacian (v_fluct r) z) s) ≤
              ENNReal.ofReal (polyP C N ν c * Real.exp (-(lam * ν * s / c ^ 2))) := by
  obtain ⟨C, N, lam, ν₀, hC, hlam, hν₀, hbd⟩ := hℓ ρ hρ (j + 2)
  refine ⟨2 * C, N, lam, min ν₀ 1, by positivity, hlam, lt_min hν₀ one_pos, ?_⟩
  intro ν hν hν_le tr htr s hs hsc
  have hν₀_le : ν ≤ ν₀ := hν_le.trans (min_le_left _ _)
  have hν1 : ν ≤ 1 := hν_le.trans (min_le_right _ _)
  let c := trainPeriod ρ ν
  have hc_pos : 0 < c := Real.rpow_pos_of_pos hν _
  let v_fluct : ℝ → Plane → Vec := fun r => hfluct c (tr.v r)
  have hsm : Sm (fun x : ℝ × Plane => v_fluct x.1 x.2) := PartI_T22.contDiffOn_hfluct_v hc_pos tr
  have hpt : ∀ z : Plane,
      ‖ageJet ℓ j (fun r w => ν • Train.vecLaplacian (v_fluct r) w) s z‖ ≤
        2 * ‖ageJet ℓ (j + 2) v_fluct s z‖ := by
    intro z
    calc ‖ageJet ℓ j (fun r w => ν • Train.vecLaplacian (v_fluct r) w) s z‖
        ≤ (2 * ν) * ‖ageJet ℓ (j + 2) v_fluct s z‖ :=
          PartI_T22.norm_ageJet_smul_vecLaplacian_le hsm hν.le ℓ j hs z
      _ ≤ 2 * ‖ageJet ℓ (j + 2) v_fluct s z‖ :=
          mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
  have hv_s := (hbd ν hν hν₀_le tr htr s hs hsc).1
  have h1 := PartI_T22.wSupNorm_le_of_pointwise 0 (K := 2) (by norm_num)
    (ageJet ℓ j (fun r w => ν • Train.vecLaplacian (v_fluct r) w) s)
    (ageJet ℓ (j + 2) v_fluct s) hpt
  have hpoly_eq : 2 * (polyP C N ν c * Real.exp (-(lam * ν * s / c ^ 2))) =
      polyP (2 * C) N ν c * Real.exp (-(lam * ν * s / c ^ 2)) := by
    unfold polyP; ring
  calc wSupNorm 0 (ageJet ℓ j (fun r z => ν • Train.vecLaplacian (v_fluct r) z) s)
      ≤ ENNReal.ofReal 2 * wSupNorm 0 (ageJet ℓ (j + 2) v_fluct s) := h1
    _ ≤ ENNReal.ofReal 2 * ENNReal.ofReal (polyP C N ν c * Real.exp (-(lam * ν * s / c ^ 2))) :=
        by gcongr
    _ = ENNReal.ofReal (polyP (2 * C) N ν c * Real.exp (-(lam * ν * s / c ^ 2))) := by
        rw [← ENNReal.ofReal_mul (by norm_num), hpoly_eq]

/-- **Unconditional pressure-gradient bound at age order `ℓ`:**
from `TrainPostOverlapVelPressOrderSup ℓ` (applied at spatial order `j + 1`),
`wSupNorm 0 (ageJet ℓ j (fun r z => Train.gradS (tr.p r) z) s)` decays exponentially in `ν s / c²`
on `s ≥ overlapAge ν c`. -/
theorem trainPostOverlapGradSPress_of_order (ℓ : ℕ)
    (hℓ : TrainPostOverlapVelPressOrderSup ℓ)
    (ρ : ℝ) (hρ : 1 / 2 < ρ) (j : ℕ) :
    ∃ C : ℝ, ∃ N : ℕ, ∃ lam ν₀ : ℝ,
      0 < C ∧ 0 < lam ∧ 0 < ν₀ ∧
      ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
        ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr →
          ∀ s : ℝ, 0 < s → B0146.overlapAge ν (trainPeriod ρ ν) ≤ s →
            let c := trainPeriod ρ ν
            wSupNorm 0 (ageJet ℓ j (fun r z => Train.gradS (tr.p r) z) s) ≤
              ENNReal.ofReal (polyP C N ν c * Real.exp (-(lam * ν * s / c ^ 2))) := by
  obtain ⟨C, N, lam, ν₀, hC, hlam, hν₀, hbd⟩ := hℓ ρ hρ (j + 1)
  refine ⟨2 * C, N, lam, ν₀, by positivity, hlam, hν₀, ?_⟩
  intro ν hν hν_le tr htr s hs hsc
  let c := trainPeriod ρ ν
  have hsm_p := PartI_T22.contDiffOn_p tr
  have hpt : ∀ z : Plane,
      ‖ageJet ℓ j (fun r w => Train.gradS (tr.p r) w) s z‖ ≤
        2 * ‖ageJet ℓ (j + 1) tr.p s z‖ :=
    fun z => PartI_T22.norm_ageJet_gradS_le hsm_p ℓ j hs z
  have hp_s := (hbd ν hν hν_le tr htr s hs hsc).2
  have h1 := PartI_T22.wSupNorm_le_of_pointwise 0 (K := 2) (by norm_num)
    (ageJet ℓ j (fun r w => Train.gradS (tr.p r) w) s)
    (ageJet ℓ (j + 1) tr.p s) hpt
  have hpoly_eq : 2 * (polyP C N ν c * Real.exp (-(lam * ν * s / c ^ 2))) =
      polyP (2 * C) N ν c * Real.exp (-(lam * ν * s / c ^ 2)) := by
    unfold polyP; ring
  calc wSupNorm 0 (ageJet ℓ j (fun r z => Train.gradS (tr.p r) z) s)
      ≤ ENNReal.ofReal 2 * wSupNorm 0 (ageJet ℓ (j + 1) tr.p s) := h1
    _ ≤ ENNReal.ofReal 2 * ENNReal.ofReal (polyP C N ν c * Real.exp (-(lam * ν * s / c ^ 2))) :=
        by gcongr
    _ = ENNReal.ofReal (polyP (2 * C) N ν c * Real.exp (-(lam * ν * s / c ^ 2))) := by
        rw [← ENNReal.ofReal_mul (by norm_num), hpoly_eq]

/-- **Unconditional upgrade from `TrainPostOverlapVelPressOrderSup r` to full `(wCellL2 c 0 ∧ wSupNorm 0)`
bounds at age order `r` for `(ψ_fluct, v_fluct, tr.p)`:**
combines `PartI_T22.postOverlap_streamFluct_of_velFluct_sup` and
`PartI_T22.wCellL2_zero_and_wSupNorm_zero_of_wSupNorm_zero` with `hTails.2.2`. -/
theorem trainPostOverlapFullOrder_of_velPressSup
    (hTails : TrainStreamVelocityPressureTails)
    (r : ℕ) (hr : TrainPostOverlapVelPressOrderSup r)
    (ρ : ℝ) (hρ : 1 / 2 < ρ) (j : ℕ) :
    ∃ C : ℝ, ∃ N : ℕ, ∃ lam ν₀ : ℝ,
      0 < C ∧ 0 < lam ∧ 0 < ν₀ ∧
      ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
        ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr →
          ∀ s : ℝ, 0 < s → B0146.overlapAge ν (trainPeriod ρ ν) ≤ s →
            let c := trainPeriod ρ ν
            let K := ENNReal.ofReal (polyP C N ν c * Real.exp (-(lam * ν * s / c ^ 2)))
            let ψ_fluct : ℝ → Plane → ℝ := fun t z => tr.ψ t z - hmean c (tr.ψ t) z.2
            let v_fluct : ℝ → Plane → Vec := fun t => hfluct c (tr.v t)
            (wCellL2 c 0 (ageJet r j ψ_fluct s) ≤ K ∧ wSupNorm 0 (ageJet r j ψ_fluct s) ≤ K) ∧
            (wCellL2 c 0 (ageJet r j v_fluct s) ≤ K ∧ wSupNorm 0 (ageJet r j v_fluct s) ≤ K) ∧
            (wCellL2 c 0 (ageJet r j tr.p s) ≤ K ∧ wSupNorm 0 (ageJet r j tr.p s) ≤ K) := by
  obtain ⟨C_v0, N_v0, lam_v0, ν_v0, hC_v0, hlam_v0, hν_v0, hVP_jm1⟩ := hr ρ hρ (j - 1)
  obtain ⟨C_ψ, N_ψ, lam_ψ, ν_ψ, hC_ψ, hlam_ψ, hν_ψ, hψ⟩ :=
    PartI_T22.postOverlap_streamFluct_of_velFluct_sup hTails ρ hρ r j hC_v0 hlam_v0 hν_v0
      fun ν hν hν_le tr htr s hs hsc => (hVP_jm1 ν hν hν_le tr htr s hs hsc).1
  obtain ⟨C₂, N₂, lam_vp, ν_vp, hC₂, hlam_vp, hν_vp, hVP_j⟩ := hr ρ hρ j
  obtain ⟨C₁, N₁, ν₁, hC₁, hν₁, hT4⟩ := hTails.2.2 ρ hρ 4 r j
  obtain ⟨νp, hνp, _hνp1, hp_asymp⟩ := trainPeriodAsymptotics_proof ρ hρ 1 one_pos
  let K_abs : ℝ := (N₁.factorial : ℝ) * ((lam_vp / 2) ^ N₁)⁻¹ * Real.exp (lam_vp / 2)
  let C₃ : ℝ := Real.sqrt (2 * C₁ * C₂ * K_abs)
  let C_vp := (PartI_T21.unitCellInvSqL2 + 1) * C₃
  let N_vp := 2 * N₁ + N₂ + 1
  have hfac_pos : (0 : ℝ) < N₁.factorial := by exact_mod_cast N₁.factorial_pos
  have hK_abs : 0 < K_abs := by dsimp [K_abs]; positivity
  have hC₃ : 0 < C₃ := by dsimp [C₃]; positivity
  have hW : 0 < PartI_T21.unitCellInvSqL2 := PartI_T21.unitCellInvSqL2_pos
  have hC_vp : 0 < C_vp := mul_pos (by linarith) hC₃
  let C_out := max C_ψ C_vp
  let N_out := max N_ψ N_vp
  let lam_out := min lam_ψ (lam_vp / 4)
  let ν_out := min ν_ψ (min ν₁ (min ν_vp νp))
  refine ⟨C_out, N_out, lam_out, ν_out, lt_max_of_lt_left hC_ψ,
    lt_min hlam_ψ (by positivity), lt_min hν_ψ (lt_min hν₁ (lt_min hν_vp hνp)), ?_⟩
  intro ν hν hν_le tr htr s hs hsc
  have hνψ_le : ν ≤ ν_ψ := hν_le.trans (min_le_left _ _)
  have hν₁_le : ν ≤ ν₁ := hν_le.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hνvp_le : ν ≤ ν_vp :=
    hν_le.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hνpa_le : ν ≤ νp :=
    hν_le.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  obtain ⟨hc1, _⟩ := hp_asymp ν hν hνpa_le
  let c := trainPeriod ρ ν
  have hc0 : 0 ≤ c := zero_le_one.trans hc1
  have hν_inv : 0 ≤ ν⁻¹ := inv_nonneg.2 hν.le
  have h1X : 1 ≤ 1 + c + ν⁻¹ := by linarith
  obtain ⟨hψ_L2, hψ_Sup⟩ := hψ ν hν hνψ_le tr htr s hs hsc
  have hT4_s := hT4 ν hν hν₁_le tr htr s hs
  have hv4 : wSupNorm 4 (ageJet r j (fun t => hfluct c (tr.v t)) s) ≤
      ENNReal.ofReal (polyPS C₁ N₁ ν c s) := hT4_s.2.1.2
  have hp4 : wSupNorm 4 (ageJet r j tr.p s) ≤
      ENNReal.ofReal (polyPS C₁ N₁ ν c s) := hT4_s.2.2.2.2.2
  obtain ⟨hv0_s, hp0_s⟩ := hVP_j ν hν hνvp_le tr htr s hs hsc
  obtain ⟨hv_L2, hv_Sup⟩ := PartI_T22.wCellL2_zero_and_wSupNorm_zero_of_wSupNorm_zero
    N₁ N₂ hC₁ hC₂ hlam_vp hν hc1 hs.le (ageJet r j (fun t => hfluct c (tr.v t)) s) hv4 hv0_s
  obtain ⟨hp_L2, hp_Sup⟩ := PartI_T22.wCellL2_zero_and_wSupNorm_zero_of_wSupNorm_zero
    N₁ N₂ hC₁ hC₂ hlam_vp hν hc1 hs.le (ageJet r j tr.p s) hp4 hp0_s
  have hK_ψ : polyP C_ψ N_ψ ν c * Real.exp (-(lam_ψ * ν * s / c ^ 2)) ≤
      polyP C_out N_out ν c * Real.exp (-(lam_out * ν * s / c ^ 2)) := by
    apply mul_le_mul
    · unfold polyP
      exact mul_le_mul (le_max_left _ _) (pow_le_pow_right₀ h1X (le_max_left _ _))
        (by positivity) (by positivity)
    · apply Real.exp_le_exp.2
      apply neg_le_neg
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (min_le_left _ _) hν.le) hs.le) (sq_nonneg c)
    · exact Real.exp_nonneg _
    · unfold polyP; positivity
  have hK_vp : polyP C_vp N_vp ν c * Real.exp (-((lam_vp / 4) * ν * s / c ^ 2)) ≤
      polyP C_out N_out ν c * Real.exp (-(lam_out * ν * s / c ^ 2)) := by
    apply mul_le_mul
    · unfold polyP
      exact mul_le_mul (le_max_right _ _) (pow_le_pow_right₀ h1X (le_max_right _ _))
        (by positivity) (by positivity)
    · apply Real.exp_le_exp.2
      apply neg_le_neg
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (min_le_right _ _) hν.le) hs.le) (sq_nonneg c)
    · exact Real.exp_nonneg _
    · unfold polyP; positivity
  exact ⟨⟨hψ_L2.trans (ENNReal.ofReal_le_ofReal hK_ψ),
      hψ_Sup.trans (ENNReal.ofReal_le_ofReal hK_ψ)⟩,
    ⟨hv_L2.trans (ENNReal.ofReal_le_ofReal hK_vp),
      hv_Sup.trans (ENNReal.ofReal_le_ofReal hK_vp)⟩,
    ⟨hp_L2.trans (ENNReal.ofReal_le_ofReal hK_vp),
      hp_Sup.trans (ENNReal.ofReal_le_ofReal hK_vp)⟩⟩

/-! ### 3. Inductive step leaves (`PartI:T22/2/1` and `PartI:T22/2/2`) and strong induction -/

/-- **Leaf 1 (`PartI:T22/2/1`, `TrainPostOverlapVelFluctHigherStep`):**
source lines 523-526 of `the November 2 reference manuscript`.
Given the inductive hypothesis `∀ r ≤ ℓ, TrainPostOverlapVelPressOrderSup r` (so `v_fluct` and
`tr.p` satisfy post-overlap `wSupNorm 0` exponential decay at all age orders `≤ ℓ` and all spatial
orders `j`), the differentiated fluctuation momentum equation
`∂_s v_fluct = ν Δ v_fluct - hfluct c (advection tr.v) - gradS tr.p` (where the viscous and
pressure-gradient terms are already bounded by `trainPostOverlapViscFluct_of_order` and
`trainPostOverlapGradSPress_of_order`, and every term in `hfluct c (advection tr.v)` has a
`v_fluct` factor of age order `≤ ℓ` and a `tr.v` factor bounded by `polyPS` from `hTails.2.2`,
absorbed via `PartI_T22.polyPS_mul_exp_absorb`) yields post-overlap `wSupNorm 0` exponential decay
for `ageJet (ℓ + 1) j v_fluct` across all spatial orders `j : ℕ`. -/
def TrainPostOverlapVelFluctHigherStep : Prop :=
  TrainStreamVelocityPressureTails → TrainPostOverlapVelZero →
    TrainPostOverlapStreamPressureZero → TrainOverlap →
    ∀ ℓ : ℕ, (∀ r : ℕ, r ≤ ℓ → TrainPostOverlapVelPressOrderSup r) →
      ∀ ρ : ℝ, 1 / 2 < ρ → ∀ j : ℕ, ∃ C : ℝ, ∃ N : ℕ, ∃ lam ν₀ : ℝ,
        0 < C ∧ 0 < lam ∧ 0 < ν₀ ∧
        ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
          ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr →
            ∀ s : ℝ, 0 < s → B0146.overlapAge ν (trainPeriod ρ ν) ≤ s →
              let c := trainPeriod ρ ν
              let v_fluct : ℝ → Plane → Vec := fun r => hfluct c (tr.v r)
              wSupNorm 0 (ageJet (ℓ + 1) j v_fluct s) ≤
                ENNReal.ofReal (polyP C N ν c * Real.exp (-(lam * ν * s / c ^ 2)))

/-- **Leaf 2 (`PartI:T22/2/2`, `TrainPostOverlapPressureHigherStep`):**
source lines 523-526 of `the November 2 reference manuscript`.
Given the inductive hypothesis `∀ r ≤ ℓ, TrainPostOverlapVelPressOrderSup r` AND the age-order
`ℓ + 1` velocity-fluctuation bound from `TrainPostOverlapVelFluctHigherStep` (so `v_fluct`
satisfies post-overlap `wSupNorm 0` exponential decay at all age orders `≤ ℓ + 1`), the
differentiated cylinder pressure equation `-Δ(∂_s^{ℓ+1} p) = ∂_s^{ℓ+1} ∂_i ∂_j (v_i v_j)` (with
`\bar p = -\overline{v₂²}`, where every term on the RHS retains a fluctuation factor `v_fluct` of
age order `≤ ℓ + 1` and a `tr.v` factor bounded by `polyPS` from `hTails.2.2`) yields post-overlap
`wSupNorm 0` exponential decay for `ageJet (ℓ + 1) j tr.p` across all spatial orders `j : ℕ`. -/
def TrainPostOverlapPressureHigherStep : Prop :=
  TrainStreamVelocityPressureTails → TrainPostOverlapVelZero →
    TrainPostOverlapStreamPressureZero → TrainOverlap →
    ∀ ℓ : ℕ, (∀ r : ℕ, r ≤ ℓ → TrainPostOverlapVelPressOrderSup r) →
      (∀ ρ : ℝ, 1 / 2 < ρ → ∀ j : ℕ, ∃ C : ℝ, ∃ N : ℕ, ∃ lam ν₀ : ℝ,
        0 < C ∧ 0 < lam ∧ 0 < ν₀ ∧
        ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
          ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr →
            ∀ s : ℝ, 0 < s → B0146.overlapAge ν (trainPeriod ρ ν) ≤ s →
              let c := trainPeriod ρ ν
              let v_fluct : ℝ → Plane → Vec := fun r => hfluct c (tr.v r)
              wSupNorm 0 (ageJet (ℓ + 1) j v_fluct s) ≤
                ENNReal.ofReal (polyP C N ν c * Real.exp (-(lam * ν * s / c ^ 2)))) →
      ∀ ρ : ℝ, 1 / 2 < ρ → ∀ j : ℕ, ∃ C : ℝ, ∃ N : ℕ, ∃ lam ν₀ : ℝ,
        0 < C ∧ 0 < lam ∧ 0 < ν₀ ∧
        ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
          ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr →
            ∀ s : ℝ, 0 < s → B0146.overlapAge ν (trainPeriod ρ ν) ≤ s →
              let c := trainPeriod ρ ν
              wSupNorm 0 (ageJet (ℓ + 1) j tr.p s) ≤
                ENNReal.ofReal (polyP C N ν c * Real.exp (-(lam * ν * s / c ^ 2)))

/-- **Inductive step `ℓ → ℓ + 1` for `TrainPostOverlapVelPressOrderSup`:**
combines `TrainPostOverlapVelFluctHigherStep` and `TrainPostOverlapPressureHigherStep`. -/
theorem trainPostOverlapVelPressOrderSup_succ
    (hVelStep : TrainPostOverlapVelFluctHigherStep)
    (hPressStep : TrainPostOverlapPressureHigherStep)
    (hTails : TrainStreamVelocityPressureTails)
    (hVel0 : TrainPostOverlapVelZero)
    (hSP0 : TrainPostOverlapStreamPressureZero)
    (hOv : TrainOverlap)
    (ℓ : ℕ) (hIH : ∀ r : ℕ, r ≤ ℓ → TrainPostOverlapVelPressOrderSup r) :
    TrainPostOverlapVelPressOrderSup (ℓ + 1) := by
  have hV_succ := hVelStep hTails hVel0 hSP0 hOv ℓ hIH
  have hP_succ := hPressStep hTails hVel0 hSP0 hOv ℓ hIH hV_succ
  intro ρ hρ j
  obtain ⟨C₁, N₁, lam₁, ν₁, hC₁, hlam₁, hν₁, hv⟩ := hV_succ ρ hρ j
  obtain ⟨C₂, N₂, lam₂, ν₂, hC₂, hlam₂, hν₂, hp⟩ := hP_succ ρ hρ j
  refine ⟨max C₁ C₂, max N₁ N₂, min lam₁ lam₂, min ν₁ ν₂,
    lt_max_of_lt_left hC₁, lt_min hlam₁ hlam₂, lt_min hν₁ hν₂, ?_⟩
  intro ν hν hν_le tr htr s hs hsc
  have hν₁_le : ν ≤ ν₁ := hν_le.trans (min_le_left _ _)
  have hν₂_le : ν ≤ ν₂ := hν_le.trans (min_le_right _ _)
  let c := trainPeriod ρ ν
  have hc0 : 0 ≤ c := Real.rpow_nonneg hν.le _
  have hν_inv : 0 ≤ ν⁻¹ := inv_nonneg.2 hν.le
  have h1X : 1 ≤ 1 + c + ν⁻¹ := by linarith
  have hv_s := hv ν hν hν₁_le tr htr s hs hsc
  have hp_s := hp ν hν hν₂_le tr htr s hs hsc
  have hK₁ : polyP C₁ N₁ ν c * Real.exp (-(lam₁ * ν * s / c ^ 2)) ≤
      polyP (max C₁ C₂) (max N₁ N₂) ν c * Real.exp (-(min lam₁ lam₂ * ν * s / c ^ 2)) := by
    apply mul_le_mul
    · unfold polyP
      exact mul_le_mul (le_max_left _ _) (pow_le_pow_right₀ h1X (le_max_left _ _))
        (by positivity) (by positivity)
    · apply Real.exp_le_exp.2
      apply neg_le_neg
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (min_le_left _ _) hν.le) hs.le) (sq_nonneg c)
    · exact Real.exp_nonneg _
    · unfold polyP; positivity
  have hK₂ : polyP C₂ N₂ ν c * Real.exp (-(lam₂ * ν * s / c ^ 2)) ≤
      polyP (max C₁ C₂) (max N₁ N₂) ν c * Real.exp (-(min lam₁ lam₂ * ν * s / c ^ 2)) := by
    apply mul_le_mul
    · unfold polyP
      exact mul_le_mul (le_max_right _ _) (pow_le_pow_right₀ h1X (le_max_right _ _))
        (by positivity) (by positivity)
    · apply Real.exp_le_exp.2
      apply neg_le_neg
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (min_le_right _ _) hν.le) hs.le) (sq_nonneg c)
    · exact Real.exp_nonneg _
    · unfold polyP; positivity
  exact ⟨hv_s.trans (ENNReal.ofReal_le_ofReal hK₁),
    hp_s.trans (ENNReal.ofReal_le_ofReal hK₂)⟩

/-- **Strong induction in `ℓ` for `TrainPostOverlapVelPressOrderSup`:**
establishes `TrainPostOverlapVelPressOrderSup ℓ` for all `ℓ : ℕ` from the unconditional base case
`r = 0` and the two step leaves. -/
theorem trainPostOverlapVelPressOrderSup_all
    (hVelStep : TrainPostOverlapVelFluctHigherStep)
    (hPressStep : TrainPostOverlapPressureHigherStep)
    (hTails : TrainStreamVelocityPressureTails)
    (hVel0 : TrainPostOverlapVelZero)
    (hSP0 : TrainPostOverlapStreamPressureZero)
    (hOv : TrainOverlap) :
    ∀ ℓ : ℕ, TrainPostOverlapVelPressOrderSup ℓ := by
  intro ℓ
  induction ℓ using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => exact trainPostOverlapVelPressOrderSup_zero hVel0 hSP0
    | succ m =>
      exact trainPostOverlapVelPressOrderSup_succ hVelStep hPressStep hTails hVel0 hSP0 hOv m
        (fun r hr => ih r (Nat.lt_succ_of_le hr))

/-- **Conditional assembly of `TrainPostOverlapAgeDerivFromZero` (`PartI:T22/2`):**
combines `trainPostOverlapVelPressOrderSup_all` and `trainPostOverlapFullOrder_of_velPressSup`
to prove `TrainPostOverlapAgeDerivFromZero` from `TrainPostOverlapVelFluctHigherStep`
(`PartI:T22/2/1`) and `TrainPostOverlapPressureHigherStep` (`PartI:T22/2/2`). -/
theorem trainPostOverlapAgeDerivFromZero_of
    (hVelStep : TrainPostOverlapVelFluctHigherStep)
    (hPressStep : TrainPostOverlapPressureHigherStep)
    (hTails : TrainStreamVelocityPressureTails) :
    TrainPostOverlapAgeDerivFromZero := by
  intro hVel0 hSP0 hOv ρ hρ ℓ j
  have hOrder := trainPostOverlapVelPressOrderSup_all hVelStep hPressStep hTails hVel0 hSP0 hOv ℓ
  exact trainPostOverlapFullOrder_of_velPressSup hTails ℓ hOrder ρ hρ j

end UnforcedLeray.Short.PartI

end
