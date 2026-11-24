import UnforcedLeray.Short.PartI.Sub.PartI_T25
import UnforcedLeray.Lib.Train.VortexBounds
import UnforcedLeray.Short.PartI.Sub.PartI_T25_1

/-!
# `PartI:T25/3` Sub-module: Fixed-band pressure-gradient age-jet bounds (`TrainFixedBandPressAgeJet`)

Source of record: `the November 2 reference manuscript`, lines 468–478, 543–551.

For `dp = Train.gradS (tr.p - pc)` on `0 < s ≤ Sg / ν`:
1. Proves that `Train.gradS` is a continuous linear functional `gradSLam` of `fderiv` with operator
   norm `≤ 2`, so `‖jet k (Train.gradS u) z‖ ≤ 2 * ‖jet (k + 1) u z‖` for smooth scalar fields `u`.
2. Proves commutation of `iteratedDeriv ℓ` in age with spatial `Train.gradS` for jointly smooth
   scalar fields `P : ℝ → Plane → ℝ` on `(0, ∞) × Plane`, yielding
   `‖ageJet ℓ j (fun r w => Train.gradS (P r) w) s z‖ ≤ 2 * ‖ageJet ℓ (j + 1) P s z‖`.
3. Proves the theta factorization `pc_theta_eq` and joint `C^∞` smoothness `smS_pc` of the
   periodized Gaussian pressure `pc ν c` on `(0, ∞) × Plane` (`0 < ν`, `0 < c`), unconditionally
   establishing `Continuous (ageJet ℓ j dp s)`, the exact age-jet linearity
   `ageJet ℓ j dp s z = ageJet ℓ j (gradS tr.p) s z - ageJet ℓ j (gradS pc) s z`, and the reduction
   `wCellL2_dp_le_add_pc` of the `pc` gradient contribution to `ageJet ℓ (j + 1) (pc ν c) s`.
4. Proves `gradS_pc_eq` (`∇pc = div Qc - Vc · ∇Vc`) from `Train.Vc_hasDerivAt` and `Train.Vc_heat`.
5. Combines `hTails.2.2` at spatial order `j + 1` (converted via
   `PartI_T25.polyPS_le_polyP_of_le_div_nu`) with `PartI_T25.wCellL2_le_of_pointwise` to prove
   the weight-`2m` polynomial bound `trainFixedBandPressAgeJet_tr_p_two_mul_m` for
   `ageJet ℓ j (fun r w => Train.gradS (tr.p r) w) s`, and `trainFixedBandPressAgeJet_two_mul_m_of_pc`
   for `ageJet ℓ j dp s` from `TrainFixedBandPcAgeJetTwoMulM`.
6. States the two leaf propositions `TrainFixedBandPcAgeJetTwoMulM` (`PartI:T25/3/1`) and
   `TrainFixedBandPressAgeJetUnweighted` (`PartI:T25/3/2`, carrying the consumer hypotheses
   `TrainStreamVelocityPressureTails`, `TrainFluctuationDecay`, `TrainFixedBandVelAgeJet`), and
   proves the conditional assembly `trainFixedBandPressAgeJet_of_leaves`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartI.VelAgeJetAux
open UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec Vc pc Qc width jap jet cellL2 wCellL2)
open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Short.IIb (UU isOpen_UU mem_UU eT eQ eE)

/-! ### 1. Continuous linear map representation of `Train.gradS` and jet domination -/

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
  have h10 : ‖((1 : ℝ), (0 : ℝ))‖ ≤ 1 := by
    rw [Prod.norm_def]; simp
  have h01 : ‖((0 : ℝ), (1 : ℝ))‖ ≤ 1 := by
    rw [Prod.norm_def]; simp
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
    have ha2 : (T (1, 0)) ^ 2 ≤ ‖T‖ ^ 2 := sq_le_sq.mpr (by simpa [abs_of_nonneg (norm_nonneg T)] using ha)
    have hb2 : (T (0, 1)) ^ 2 ≤ ‖T‖ ^ 2 := sq_le_sq.mpr (by simpa [abs_of_nonneg (norm_nonneg T)] using hb)
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
  have hcomp : (gradSLam ∘ fderiv ℝ u) = Train.gradS u := by
    rw [hfun]; rfl
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

/-! ### 2. Scalar jointly smooth fields on `(0, ∞) × Plane` and `gradS` age-jet commutation -/

/-- Jointly smooth scalar fields on `UU = Ioi 0 ×ˢ univ`. -/
def SmS (P : ℝ × Plane → ℝ) : Prop := ContDiffOn ℝ ∞ P UU

/-- Directional derivative of a scalar field on `ℝ × Plane`. -/
def DxS (v : ℝ × Plane) (P : ℝ × Plane → ℝ) : ℝ × Plane → ℝ :=
  fun x => fderiv ℝ P x v

theorem SmS.dx {P : ℝ × Plane → ℝ} (hP : SmS P) (v : ℝ × Plane) : SmS (DxS v P) :=
  (hP.fderiv_of_isOpen isOpen_UU (by simp)).clm_apply contDiffOn_const

theorem SmS.sub {P Q : ℝ × Plane → ℝ} (hP : SmS P) (hQ : SmS Q) : SmS (fun x => P x - Q x) :=
  ContDiffOn.sub hP hQ

theorem SmS.diffAt {P : ℝ × Plane → ℝ} (hP : SmS P) {x : ℝ × Plane} (hx : x ∈ UU) :
    DifferentiableAt ℝ P x :=
  (hP.differentiableOn (by simp)).differentiableAt (isOpen_UU.mem_nhds hx)

theorem SmS.symm {P : ℝ × Plane → ℝ} (hP : SmS P) {x : ℝ × Plane} (hx : x ∈ UU)
    (v w : ℝ × Plane) : DxS w (DxS v P) x = DxS v (DxS w P) x := by
  have hc : ContDiffAt ℝ ∞ P x := hP.contDiffAt (isOpen_UU.mem_nhds hx)
  have hc2 : ContDiffAt ℝ ((2 : ℕ) : WithTop ℕ∞) P x := hc.of_le (by simp)
  have hn : minSmoothness ℝ 2 ≤ ((2 : ℕ) : WithTop ℕ∞) := by
    rw [minSmoothness_of_isRCLikeNormedField]
    simp
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

theorem hasDerivAt_sliceS {P : ℝ × Plane → ℝ} (hP : SmS P) {t : ℝ} (ht : 0 < t) (w : Plane) :
    HasDerivAt (fun r => P (r, w)) (DxS eT P (t, w)) t := by
  have h0 : HasDerivAt (fun r : ℝ => (r, w)) ((1 : ℝ), (0 : Plane)) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t w)
  exact (hP.diffAt (mem_UU ht)).hasFDerivAt.comp_hasDerivAt t h0

/-- The `ℓ`-th age directional derivative `(DxS eT)^[ℓ] P` of a scalar field on `ℝ × Plane`. -/
def DtS (ℓ : ℕ) (P : ℝ × Plane → ℝ) : ℝ × Plane → ℝ :=
  (DxS eT)^[ℓ] P

theorem SmS_DtS {P : ℝ × Plane → ℝ} (hP : SmS P) : ∀ ℓ : ℕ, SmS (DtS ℓ P)
  | 0 => hP
  | ℓ + 1 => by
    unfold DtS
    rw [Function.iterate_succ_apply']
    exact (SmS_DtS hP ℓ).dx eT

theorem iteratedDeriv_slice_eq_DtS {P : ℝ × Plane → ℝ} (hP : SmS P) :
    ∀ (ℓ : ℕ) {t : ℝ}, 0 < t → ∀ w : Plane,
      iteratedDeriv ℓ (fun r => P (r, w)) t = DtS ℓ P (t, w)
  | 0, _, _, _ => rfl
  | ℓ + 1, t, ht, w => by
    rw [iteratedDeriv_succ]
    have hev : iteratedDeriv ℓ (fun r => P (r, w)) =ᶠ[nhds t] fun r => DtS ℓ P (r, w) := by
      filter_upwards [Ioi_mem_nhds ht] with r hr using iteratedDeriv_slice_eq_DtS hP ℓ hr w
    rw [hev.deriv_eq, (hasDerivAt_sliceS (SmS_DtS hP ℓ) ht w).deriv]
    unfold DtS
    rw [Function.iterate_succ_apply']

theorem iteratedDeriv_slice_toVec_eq_DtS {G1 G2 : ℝ × Plane → ℝ} (hG1 : SmS G1) (hG2 : SmS G2) :
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
      (hasDerivAt_sliceS (SmS_DtS hG1 ℓ) ht w).prodMk (hasDerivAt_sliceS (SmS_DtS hG2 ℓ) ht w)
    have hd : HasDerivAt (fun r => Train.toVec (DtS ℓ G1 (r, w), DtS ℓ G2 (r, w)))
        (Train.toVec (DxS eT (DtS ℓ G1) (t, w), DxS eT (DtS ℓ G2) (t, w))) t :=
      (Train.toVecL : (ℝ × ℝ) →L[ℝ] Vec).hasFDerivAt.comp_hasDerivAt t hd12
    rw [hd.deriv]
    unfold DtS
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']

theorem DtS_comm_DxS {P : ℝ × Plane → ℝ} (hP : SmS P) (v : ℝ × Plane) :
    ∀ ℓ : ℕ, EqOn (DxS v (DtS ℓ P)) (DtS ℓ (DxS v P)) UU
  | 0 => fun _ _ => rfl
  | ℓ + 1 => by
    intro x hx
    unfold DtS
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    change DxS v (DxS eT (DtS ℓ P)) x = DxS eT (DtS ℓ (DxS v P)) x
    rw [(SmS_DtS hP ℓ).symm hx eT v]
    exact DxS_congr (DtS_comm_DxS hP v ℓ) eT hx

theorem slice_DvS {P : ℝ × Plane → ℝ} (hP : SmS P) {t : ℝ} (ht : 0 < t) (e : Plane) (w : Plane) :
    fderiv ℝ (fun x : Plane => P (t, x)) w e = DxS (0, e) P (t, w) := by
  have h1 : HasFDerivAt (fun x : Plane => (t, x)) (ContinuousLinearMap.inr ℝ ℝ Plane) w :=
    hasFDerivAt_prodMk_right t w
  have h2 := (hP.diffAt (mem_UU ht)).hasFDerivAt.comp w h1
  show fderiv ℝ (P ∘ fun x : Plane => (t, x)) w e = fderiv ℝ P (t, w) (0, e)
  rw [h2.fderiv]
  rfl

theorem gradS_slice_eq_DxS {P : ℝ × Plane → ℝ} (hP : SmS P) {t : ℝ} (ht : 0 < t) (w : Plane) :
    Train.gradS (fun x => P (t, x)) w = Train.toVec (DxS eQ P (t, w), DxS eE P (t, w)) := by
  have hu : ContDiff ℝ ∞ (fun x : Plane => P (t, x)) := by
    rw [← contDiffOn_univ]
    exact hP.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun x _ => mem_UU ht)
  have hdu : Differentiable ℝ (fun x : Plane => P (t, x)) := hu.differentiable (by simp)
  unfold Train.gradS
  rw [Cyl.partialQ_eq_fderiv hdu w, Cyl.partialEta_eq_fderiv hdu w,
    slice_DvS hP ht ((1 : ℝ), (0 : ℝ)) w, slice_DvS hP ht ((0 : ℝ), (1 : ℝ)) w]
  rfl

theorem contDiffOn_gradS_of_smS {P : ℝ → Plane → ℝ}
    (hP : SmS (fun x : ℝ × Plane => P x.1 x.2)) :
    ContDiffOn ℝ ∞ (fun x : ℝ × Plane => Train.gradS (P x.1) x.2) (Ioi 0 ×ˢ univ) := by
  have heq : EqOn (fun x : ℝ × Plane => Train.gradS (P x.1) x.2)
      (fun x : ℝ × Plane => Train.toVec (DxS eQ (fun y => P y.1 y.2) x,
        DxS eE (fun y => P y.1 y.2) x)) UU :=
    fun ⟨r, w⟩ hr => gradS_slice_eq_DxS hP hr.1 w
  exact ((Train.toVecL : (ℝ × ℝ) →L[ℝ] Vec).contDiff.comp_contDiffOn
    ((hP.dx eQ).prodMk (hP.dx eE))).congr heq

/-- Commutation of `iteratedDeriv ℓ` in age with spatial `Train.gradS` for a jointly smooth
scalar field at `s > 0`. -/
theorem iteratedDeriv_gradS_eq {P : ℝ → Plane → ℝ}
    (hP : SmS (fun x : ℝ × Plane => P x.1 x.2)) (ℓ : ℕ) {s : ℝ} (hs : 0 < s) (w : Plane) :
    iteratedDeriv ℓ (fun r => Train.gradS (P r) w) s =
      Train.gradS (fun x => iteratedDeriv ℓ (fun r => P r x) s) w := by
  let U : ℝ × Plane → ℝ := fun x => P x.1 x.2
  have hev : (fun r => Train.gradS (P r) w) =ᶠ[nhds s]
      fun r => Train.toVec (DxS eQ U (r, w), DxS eE U (r, w)) := by
    filter_upwards [Ioi_mem_nhds hs] with r hr using gradS_slice_eq_DxS hP hr w
  rw [hev.iteratedDeriv_eq]
  rw [iteratedDeriv_slice_toVec_eq_DtS (hP.dx eQ) (hP.dx eE) ℓ hs w]
  rw [← DtS_comm_DxS hP eQ ℓ (mem_UU hs), ← DtS_comm_DxS hP eE ℓ (mem_UU hs)]
  rw [← gradS_slice_eq_DxS (SmS_DtS hP ℓ) hs w]
  congr 1
  funext x
  exact (iteratedDeriv_slice_eq_DtS hP ℓ hs x).symm

theorem contDiff_slice_iteratedDerivS {P : ℝ → Plane → ℝ}
    (hP : SmS (fun x : ℝ × Plane => P x.1 x.2)) (ℓ : ℕ) {s : ℝ} (hs : 0 < s) :
    ContDiff ℝ ∞ (fun x : Plane => iteratedDeriv ℓ (fun r => P r x) s) := by
  have heq : (fun x : Plane => iteratedDeriv ℓ (fun r => P r x) s) =
      fun x : Plane => DtS ℓ (fun y : ℝ × Plane => P y.1 y.2) (s, x) :=
    funext fun x => iteratedDeriv_slice_eq_DtS hP ℓ hs x
  rw [heq, ← contDiffOn_univ]
  exact (SmS_DtS hP ℓ).comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun x _ => mem_UU hs)

/-- Pointwise bound `‖ageJet ℓ j (fun r w => Train.gradS (P r) w) s z‖ ≤ 2 * ‖ageJet ℓ (j + 1) P s z‖`
for jointly smooth scalar fields `P` at `s > 0`. -/
theorem norm_ageJet_gradS_le {P : ℝ → Plane → ℝ}
    (hP : SmS (fun x : ℝ × Plane => P x.1 x.2)) (ℓ j : ℕ) {s : ℝ} (hs : 0 < s) (z : Plane) :
    ‖ageJet ℓ j (fun r w => Train.gradS (P r) w) s z‖ ≤ 2 * ‖ageJet ℓ (j + 1) P s z‖ := by
  have hslice : (fun w => iteratedDeriv ℓ (fun r => Train.gradS (P r) w) s) =
      Train.gradS (fun x => iteratedDeriv ℓ (fun r => P r x) s) :=
    funext fun w => iteratedDeriv_gradS_eq hP ℓ hs w
  have hu : ContDiff ℝ ∞ (fun x : Plane => iteratedDeriv ℓ (fun r => P r x) s) :=
    contDiff_slice_iteratedDerivS hP ℓ hs
  unfold ageJet
  rw [hslice]
  exact norm_jet_gradS_le j hu z

/-! ### 3. Theta factorization, joint smoothness of `pc`, and linearity of `ageJet` on `dp` -/

namespace PartI_T25_3

/-- Theta factorization of the summed Gaussian pressure `pc ν c s`:
`pc ν c s z = -(1 + ν s)⁻³ e^{-η² / (2 (1 + ν s))} · tt c 0 ((2 (1 + ν s))⁻¹, q)`. -/
theorem pc_theta_eq {ν c s : ℝ} (hν : 0 < ν) (_hc : 0 < c) (hs : 0 ≤ s) (z : Plane) :
    pc ν c s z =
      (-((1 + ν * s) ^ 3)⁻¹ * Real.exp (-z.2 ^ 2 / (2 * (1 + ν * s)))) *
        UnforcedLeray.Short.IIb.tt c 0 ((2 * (1 + ν * s))⁻¹, z.1) := by
  have ha : 0 < 1 + ν * s := by nlinarith [mul_nonneg hν.le hs]
  have hterm : ∀ n : ℤ,
      UnforcedLeray.Train.isoP ν s (z.1 - n * c, z.2) =
        (-((1 + ν * s) ^ 3)⁻¹ * Real.exp (-z.2 ^ 2 / (2 * (1 + ν * s)))) *
          UnforcedLeray.Short.IIb.ttTerm c 0 n ((2 * (1 + ν * s))⁻¹, z.1) := by
    intro n
    unfold UnforcedLeray.Train.isoP UnforcedLeray.B0146.isoPressure
      UnforcedLeray.Short.IIb.ttTerm
    simp only [UnforcedLeray.B0113.pExp, UnforcedLeray.B0113.gw,
      UnforcedLeray.B0113.heatWidth, UnforcedLeray.GaussianVortex.radiusSq, pow_zero, one_mul]
    rw [← Real.exp_add, inv_pow]
    have key : -((1 + ν * s)⁻¹ * ((z.1 - n * c) ^ 2 + z.2 ^ 2) / 4) +
        -((1 + ν * s)⁻¹ * ((z.1 - n * c) ^ 2 + z.2 ^ 2) / 4) =
        -(2 * (1 + ν * s))⁻¹ * (z.1 - n * c) ^ 2 + -z.2 ^ 2 / (2 * (1 + ν * s)) := by
      field_simp
      ring
    rw [key, Real.exp_add]
    ring
  unfold UnforcedLeray.Train.pc UnforcedLeray.Gaussian.periodize
    UnforcedLeray.Short.IIb.tt
  rw [tsum_congr hterm, tsum_mul_left]

/-- Joint `C^∞` smoothness of `(s, z) ↦ pc ν c s z` on `UU = Ioi 0 ×ˢ univ` for `0 < ν`, `0 < c`. -/
theorem smS_pc {ν c : ℝ} (hν : 0 < ν) (hc : 0 < c) :
    SmS (fun x : ℝ × Plane => pc ν c x.1 x.2) := by
  have hpos : ∀ x : ℝ × Plane, x ∈ (Ioi (0 : ℝ) ×ˢ (univ : Set Plane)) → 0 < 1 + ν * x.1 := by
    intro x hx
    have := mul_pos hν hx.1
    linarith
  have hc1 : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => 1 + ν * x.1) (Ioi 0 ×ˢ univ) := by
    fun_prop
  have hc3 : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => ((1 + ν * x.1) ^ 3)⁻¹) (Ioi 0 ×ˢ univ) :=
    (hc1.pow 3).inv fun x hx => pow_ne_zero _ (hpos x hx).ne'
  have hexp : ContDiffOn ℝ ∞
      (fun x : ℝ × Plane => Real.exp (-x.2.2 ^ 2 / (2 * (1 + ν * x.1)))) (Ioi 0 ×ˢ univ) := by
    refine ContDiffOn.exp ?_
    refine ContDiffOn.div ?_ ?_ fun x hx => ?_
    · fun_prop
    · exact contDiffOn_const.mul hc1
    · exact (mul_pos two_pos (hpos x hx)).ne'
  have henv : ContDiffOn ℝ ∞
      (fun x : ℝ × Plane => -((1 + ν * x.1) ^ 3)⁻¹ * Real.exp (-x.2.2 ^ 2 / (2 * (1 + ν * x.1))))
      (Ioi 0 ×ˢ univ) :=
    hc3.neg.mul hexp
  have hm : ContDiffOn ℝ ∞
      (fun x : ℝ × Plane => ((2 * (1 + ν * x.1))⁻¹, x.2.1)) (Ioi 0 ×ˢ univ) := by
    refine ContDiffOn.prodMk ?_ (by fun_prop)
    exact (contDiffOn_const.mul hc1).inv fun x hx => (mul_pos two_pos (hpos x hx)).ne'
  have hmaps : MapsTo (fun x : ℝ × Plane => ((2 * (1 + ν * x.1))⁻¹, x.2.1))
      (Ioi 0 ×ˢ univ) {x : ℝ × ℝ | 0 < x.1} := by
    intro x hx
    show 0 < (2 * (1 + ν * x.1))⁻¹
    exact inv_pos.2 (mul_pos two_pos (hpos x hx))
  have htt : ContDiffOn ℝ ∞
      (fun x : ℝ × Plane => UnforcedLeray.Short.IIb.tt c 0 ((2 * (1 + ν * x.1))⁻¹, x.2.1))
      (Ioi 0 ×ˢ univ) :=
    (UnforcedLeray.Short.IIb.contDiffOn_tt_infty hc.ne' 0).comp hm hmaps
  exact (henv.mul htt).congr fun x hx => pc_theta_eq hν hc hx.1.le x.2

/-- Exact formula `∇pc = div Qc - Vc · ∇Vc` from `Train.Vc_hasDerivAt` and `Train.Vc_heat`. -/
theorem gradS_pc_eq {ν c s : ℝ} (hν : 0 < ν) (hc : c ≠ 0) (hs : 0 ≤ s) (w : Plane) :
    Train.gradS (pc ν c s) w = Train.matDiv (Train.Qc ν c s) w - Train.advection (Vc ν c s) w := by
  have h1 := UnforcedLeray.Train.Vc_hasDerivAt hν hc hs w
  have h2 := UnforcedLeray.Train.Vc_heat hν hc hs w
  have heq := h1.unique h2
  ext k
  have hk := congrArg (fun v : Vec => v k) heq
  simp only [PiLp.add_apply, PiLp.sub_apply] at hk ⊢
  linarith

/-- For `r > 0`, `Train.gradS (fun w => tr.p r w - pc ν c r w) z = Train.gradS (tr.p r) z - Train.gradS (pc ν c r) z`. -/
theorem dp_eq_sub_gradS {ν c : ℝ} (tr : B0140.TrainSol ν c)
    (hν : 0 < ν) (hc : 0 < c) {r : ℝ} (hr : 0 < r) (z : Plane) :
    Train.gradS (fun w => tr.p r w - pc ν c r w) z =
      Train.gradS (tr.p r) z - Train.gradS (pc ν c r) z :=
  TrainErrorEquation.gradS_sub_eq
    (TrainErrorEquation.G1_of_contDiff
      (TrainErrorEquation.contDiff_slice (f := tr.p) tr.isTrain.smooth_p hr.le))
    (TrainErrorEquation.G1_pc hν hc.ne' hr.le) z

/-- Exact linearity of `ageJet ℓ j` on `dp = Train.gradS (tr.p - pc)` for `s > 0`. -/
theorem ageJet_dp_eq_sub {ν c : ℝ} (tr : B0140.TrainSol ν c)
    (hν : 0 < ν) (hc : 0 < c) (ℓ j : ℕ) {s : ℝ} (hs : 0 < s) (z : Plane) :
    ageJet ℓ j (fun r w => Train.gradS (fun u => tr.p r u - pc ν c r u) w) s z =
      ageJet ℓ j (fun r w => Train.gradS (tr.p r) w) s z -
        ageJet ℓ j (fun r w => Train.gradS (pc ν c r) w) s z := by
  have hsm_p : SmS (fun x : ℝ × Plane => tr.p x.1 x.2) :=
    tr.isTrain.smooth_p.mono (Set.prod_mono Set.Ioi_subset_Ici_self Subset.rfl)
  have hsm_pc : SmS (fun x : ℝ × Plane => pc ν c x.1 x.2) := smS_pc hν hc
  have hsm_gp := contDiffOn_gradS_of_smS hsm_p
  have hsm_gpc := contDiffOn_gradS_of_smS hsm_pc
  have hcongr : ageJet ℓ j (fun r w => Train.gradS (fun u => tr.p r u - pc ν c r u) w) s z =
      ageJet ℓ j (fun r w => Train.gradS (tr.p r) w - Train.gradS (pc ν c r) w) s z := by
    unfold ageJet
    congr 1
    funext w
    have hev : (fun r => Train.gradS (fun u => tr.p r u - pc ν c r u) w) =ᶠ[nhds s]
        fun r => Train.gradS (tr.p r) w - Train.gradS (pc ν c r) w := by
      filter_upwards [Ioi_mem_nhds hs] with r hr using dp_eq_sub_gradS tr hν hc hr w
    exact hev.iteratedDeriv_eq ℓ
  exact hcongr.trans (UnforcedLeray.Short.IIb.vb_ageJet_sub
    (fun r w => Train.gradS (tr.p r) w) (fun r w => Train.gradS (pc ν c r) w)
    hsm_gp hsm_gpc hs ℓ j z)

/-- Triangle-inequality bound for `wCellL2 c (2 * m) (ageJet ℓ j dp s)`. -/
theorem wCellL2_dp_le_add_gradS_pc {ν c : ℝ} (tr : B0140.TrainSol ν c)
    (hν : 0 < ν) (hc : 0 < c) (m ℓ j : ℕ) {s : ℝ} (hs : 0 < s) :
    wCellL2 c (2 * m)
      (ageJet ℓ j (fun r z => Train.gradS (fun w => tr.p r w - pc ν c r w) z) s) ≤
      wCellL2 c (2 * m) (ageJet ℓ j (fun r w => Train.gradS (tr.p r) w) s) +
        wCellL2 c (2 * m) (ageJet ℓ j (fun r w => Train.gradS (pc ν c r) w) s) := by
  have hsm_p : SmS (fun x : ℝ × Plane => tr.p x.1 x.2) :=
    tr.isTrain.smooth_p.mono (Set.prod_mono Set.Ioi_subset_Ici_self Subset.rfl)
  have hsm_pc : SmS (fun x : ℝ × Plane => pc ν c x.1 x.2) := smS_pc hν hc
  have hcont_gp : Continuous (ageJet ℓ j (fun r w => Train.gradS (tr.p r) w) s) :=
    continuous_ageJet_of_contDiffOn (fun r w => Train.gradS (tr.p r) w)
      (contDiffOn_gradS_of_smS hsm_p) ℓ j hs
  have hcont_gpc : Continuous (ageJet ℓ j (fun r w => Train.gradS (pc ν c r) w) s) :=
    continuous_ageJet_of_contDiffOn (fun r w => Train.gradS (pc ν c r) w)
      (contDiffOn_gradS_of_smS hsm_pc) ℓ j hs
  have hsub : ageJet ℓ j (fun r z => Train.gradS (fun w => tr.p r w - pc ν c r w) z) s =
      fun z => ageJet ℓ j (fun r w => Train.gradS (tr.p r) w) s z -
        ageJet ℓ j (fun r w => Train.gradS (pc ν c r) w) s z :=
    funext (ageJet_dp_eq_sub tr hν hc ℓ j hs)
  have hsub_L2 :
      wCellL2 c (2 * m)
        (ageJet ℓ j (fun r z => Train.gradS (fun w => tr.p r w - pc ν c r w) z) s) =
      wCellL2 c (2 * m) (fun z => ageJet ℓ j (fun r w => Train.gradS (tr.p r) w) s z -
        ageJet ℓ j (fun r w => Train.gradS (pc ν c r) w) s z) :=
    congrArg (wCellL2 c (2 * m)) hsub
  exact hsub_L2.le.trans (wCellL2_sub_le_of_continuous c (2 * m) hcont_gp hcont_gpc)

/-- Gradient domination for `wCellL2 c (2 * m) (ageJet ℓ j (gradS pc) s)`. -/
theorem wCellL2_gradS_pc_le {ν c : ℝ}
    (hν : 0 < ν) (hc : 0 < c) (m ℓ j : ℕ) {s : ℝ} (hs : 0 < s) :
    wCellL2 c (2 * m) (ageJet ℓ j (fun r w => Train.gradS (pc ν c r) w) s) ≤
      ENNReal.ofReal 2 * wCellL2 c (2 * m) (ageJet ℓ (j + 1) (pc ν c) s) :=
  PartI_T25.wCellL2_le_of_pointwise c (2 * m) (K := 2) (by norm_num)
    (ageJet ℓ j (fun r w => Train.gradS (pc ν c r) w) s) (ageJet ℓ (j + 1) (pc ν c) s)
    (fun z => norm_ageJet_gradS_le (smS_pc hν hc) ℓ j hs z)

/-- Triangle-inequality and gradient-domination bound for `wCellL2 c (2 * m) (ageJet ℓ j dp s)`. -/
theorem wCellL2_dp_le_add_pc {ν c : ℝ} (tr : B0140.TrainSol ν c)
    (hν : 0 < ν) (hc : 0 < c) (m ℓ j : ℕ) {s : ℝ} (hs : 0 < s) :
    wCellL2 c (2 * m)
      (ageJet ℓ j (fun r z => Train.gradS (fun w => tr.p r w - pc ν c r w) z) s) ≤
      wCellL2 c (2 * m) (ageJet ℓ j (fun r w => Train.gradS (tr.p r) w) s) +
        ENNReal.ofReal 2 * wCellL2 c (2 * m) (ageJet ℓ (j + 1) (pc ν c) s) :=
  le_trans (wCellL2_dp_le_add_gradS_pc tr hν hc m ℓ j hs)
    (add_le_add le_rfl (wCellL2_gradS_pc_le hν hc m ℓ j hs))

end PartI_T25_3

/-! ### 4. Weight-`2m` polynomial bound for `ageJet ℓ j (fun r w => Train.gradS (tr.p r) w) s` -/

/-- On the fixed band `0 < s ≤ Sg / ν`, `wCellL2 c (2 * m) (ageJet ℓ j (fun r w => Train.gradS (tr.p r) w) s)`
is bounded by `ENNReal.ofReal (polyP C N ν c)` using `hTails.2.2` at spatial order `j + 1`. -/
theorem trainFixedBandPressAgeJet_tr_p_two_mul_m
    (hTails : TrainStreamVelocityPressureTails)
    (ρ : ℝ) (hρ : 1 / 2 < ρ) (Sg : ℝ) (hSg : 0 < Sg) (m ℓ j : ℕ) :
    ∃ C : ℝ, ∃ N : ℕ, ∃ ν₀ : ℝ, 0 < C ∧ 0 < ν₀ ∧
      ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
        ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr →
          ∀ s : ℝ, 0 < s → s ≤ Sg / ν →
            let c := trainPeriod ρ ν
            wCellL2 c (2 * m) (ageJet ℓ j (fun r z => Train.gradS (tr.p r) z) s) ≤
              ENNReal.ofReal (polyP C N ν c) := by
  obtain ⟨C₁, N₁, ν₁, hC₁, hν₁, hT⟩ := hTails.2.2 ρ hρ (2 * m) ℓ (j + 1)
  refine ⟨2 * (C₁ * (1 + Sg) ^ N₁), 2 * N₁, ν₁, by positivity, hν₁, ?_⟩
  intro ν hν hν_le tr htr s hs hs_le
  let c := trainPeriod ρ ν
  have hc_pos : 0 < c := by
    dsimp [c]
    unfold trainPeriod
    exact Real.rpow_pos_of_pos hν _
  have hsm_p : SmS (fun x : ℝ × Plane => tr.p x.1 x.2) :=
    tr.isTrain.smooth_p.mono (Set.prod_mono Set.Ioi_subset_Ici_self Subset.rfl)
  have hpt : ∀ z : Plane,
      ‖ageJet ℓ j (fun r w => Train.gradS (tr.p r) w) s z‖ ≤ 2 * ‖ageJet ℓ (j + 1) tr.p s z‖ :=
    fun z => norm_ageJet_gradS_le hsm_p ℓ j hs z
  have h1 := PartI_T25.wCellL2_le_of_pointwise c (2 * m) (K := 2) (by norm_num)
    (ageJet ℓ j (fun r w => Train.gradS (tr.p r) w) s) (ageJet ℓ (j + 1) tr.p s) hpt
  have hp_tail : wCellL2 c (2 * m) (ageJet ℓ (j + 1) tr.p s) ≤
      ENNReal.ofReal (polyPS C₁ N₁ ν c s) :=
    ((hT ν hν hν_le tr htr s hs).2.2.2.2).1
  have hpoly_le :=
    PartI_T25.polyPS_le_polyP_of_le_div_nu N₁ hC₁.le hSg.le hν hc_pos.le hs.le hs_le
  have hpoly_eq : 2 * polyP (C₁ * (1 + Sg) ^ N₁) (2 * N₁) ν c =
      polyP (2 * (C₁ * (1 + Sg) ^ N₁)) (2 * N₁) ν c := by
    unfold polyP; ring
  calc wCellL2 c (2 * m) (ageJet ℓ j (fun r z => Train.gradS (tr.p r) z) s)
      ≤ ENNReal.ofReal 2 * wCellL2 c (2 * m) (ageJet ℓ (j + 1) tr.p s) := h1
    _ ≤ ENNReal.ofReal 2 * ENNReal.ofReal (polyPS C₁ N₁ ν c s) := by gcongr
    _ ≤ ENNReal.ofReal 2 * ENNReal.ofReal (polyP (C₁ * (1 + Sg) ^ N₁) (2 * N₁) ν c) := by
        gcongr
    _ = ENNReal.ofReal (polyP (2 * (C₁ * (1 + Sg) ^ N₁)) (2 * N₁) ν c) := by
        rw [← ENNReal.ofReal_mul (by norm_num), hpoly_eq]

/-! ### 5. Leaf propositions and conditional assembly for `PartI:T25/3` -/

/-- **Leaf 1 for `PartI:T25/3` (`PartI:T25/3/1`, `TrainFixedBandPcAgeJetTwoMulM`)**:
source lines 468–478, 543–551 of `the November 2 reference manuscript`.
Weight-`2m` polynomial bound on `0 < s ≤ Sg / ν` (`0 < ν ≤ 1`, `0 < c`, `1 + Sg ≤ c ^ 2`) for
`ageJet ℓ k (pc ν c) s` of the periodized Gaussian pressure `pc ν c`. -/
def TrainFixedBandPcAgeJetTwoMulM : Prop :=
  ∀ Sg : ℝ, 0 < Sg → ∀ m ℓ k : ℕ,
    ∃ C : ℝ, ∃ N : ℕ, 0 < C ∧
      ∀ ν c s : ℝ, 0 < ν → ν ≤ 1 → 0 < c → 1 + Sg ≤ c ^ 2 → 0 < s → s ≤ Sg / ν →
        wCellL2 c (2 * m) (ageJet ℓ k (pc ν c) s) ≤ ENNReal.ofReal (polyP C N ν c)

/-- **Leaf 2 for `PartI:T25/3` (`PartI:T25/3/2`, `TrainFixedBandPressAgeJetUnweighted`)**:
source lines 468–478, 543–551 of `the November 2 reference manuscript`.
Given `TrainStreamVelocityPressureTails`, `TrainFluctuationDecay`, and `TrainFixedBandVelAgeJet`,
on `0 < s ≤ Sg / ν`, `ageJet ℓ j dp s` for `dp = Train.gradS (tr.p - pc)` satisfies the unweighted
(`m = 0`) exponential fixed-band bound in `wCellL2 c 0` and `wSupNorm 0`. -/
def TrainFixedBandPressAgeJetUnweighted : Prop :=
  TrainStreamVelocityPressureTails →
    TrainFluctuationDecay →
      TrainFixedBandVelAgeJet →
        ∀ ρ : ℝ, 1 / 2 < ρ → ∀ Sg : ℝ, 0 < Sg → ∀ ℓ j : ℕ,
          ∃ C : ℝ, ∃ N : ℕ, ∃ CS bS ν₀ : ℝ, 0 < C ∧ 0 < bS ∧ 0 < ν₀ ∧
            ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
              ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr →
                ∀ s : ℝ, 0 < s → s ≤ Sg / ν →
                  let c := trainPeriod ρ ν
                  let dp : ℝ → Plane → Vec := fun r z =>
                    Train.gradS (fun w => tr.p r w - pc ν c r w) z
                  wCellL2 c 0 (ageJet ℓ j dp s) ≤
                    ENNReal.ofReal (polyP C N ν c * Real.exp (CS / ν - bS * c ^ 2)) ∧
                  wSupNorm 0 (ageJet ℓ j dp s) ≤
                    ENNReal.ofReal (polyP C N ν c * Real.exp (CS / ν - bS * c ^ 2))

/-- Weight-`2m` polynomial bound for `ageJet ℓ j dp s` on `0 < s ≤ Sg / ν` derived from
`TrainStreamVelocityPressureTails` and `TrainFixedBandPcAgeJetTwoMulM`. -/
theorem trainFixedBandPressAgeJet_two_mul_m_of_pc
    (hTails : TrainStreamVelocityPressureTails)
    (hPc : TrainFixedBandPcAgeJetTwoMulM)
    (ρ : ℝ) (hρ : 1 / 2 < ρ) (Sg : ℝ) (hSg : 0 < Sg) (m ℓ j : ℕ) :
    ∃ C : ℝ, ∃ N : ℕ, ∃ ν₀ : ℝ, 0 < C ∧ 0 < ν₀ ∧
      ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
        ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr →
          ∀ s : ℝ, 0 < s → s ≤ Sg / ν →
            let c := trainPeriod ρ ν
            let dp : ℝ → Plane → Vec := fun r z =>
              Train.gradS (fun w => tr.p r w - pc ν c r w) z
            wCellL2 c (2 * m) (ageJet ℓ j dp s) ≤ ENNReal.ofReal (polyP C N ν c) := by
  obtain ⟨C₁, N₁, ν₁, hC₁, hν₁, hp2m⟩ :=
    trainFixedBandPressAgeJet_tr_p_two_mul_m hTails ρ hρ Sg hSg m ℓ j
  obtain ⟨C₂, N₂, hC₂, hpc⟩ := hPc Sg hSg m ℓ (j + 1)
  obtain ⟨νp, hνp, hνp1, hp⟩ := trainPeriodAsymptotics_proof ρ hρ (1 + Sg) (by positivity)
  let C_out := C₁ + 2 * C₂
  let N_out := max N₁ N₂
  refine ⟨C_out, N_out, min ν₁ νp, by dsimp [C_out]; positivity, lt_min hν₁ hνp, ?_⟩
  intro ν hν hν_le tr htr s hs hs_le
  have hν₁_le : ν ≤ ν₁ := hν_le.trans (min_le_left _ _)
  have hνp_le : ν ≤ νp := hν_le.trans (min_le_right _ _)
  have hν1 : ν ≤ 1 := hνp_le.trans hνp1
  obtain ⟨hc1, hνc2⟩ := hp ν hν hνp_le
  let c := trainPeriod ρ ν
  have hc_pos : 0 < c := zero_lt_one.trans_le hc1
  have hSg_c2 : 1 + Sg ≤ c ^ 2 := by
    calc 1 + Sg ≤ ν * c ^ 2 := hνc2
      _ ≤ 1 * c ^ 2 := mul_le_mul_of_nonneg_right hν1 (sq_nonneg c)
      _ = c ^ 2 := one_mul _
  have hX1 : 1 ≤ 1 + c + ν⁻¹ := by
    have : 0 ≤ ν⁻¹ := inv_nonneg.2 hν.le
    linarith
  have hgp_bd := hp2m ν hν hν₁_le tr htr s hs hs_le
  have hpc_bd := hpc ν c s hν hν1 hc_pos hSg_c2 hs hs_le
  have htri := PartI_T25_3.wCellL2_dp_le_add_pc tr hν hc_pos m ℓ j hs
  have hP₁ : polyP C₁ N₁ ν c ≤ polyP C₁ N_out ν c := by
    unfold polyP
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hX1 (le_max_left _ _)) hC₁.le
  have hP₂ : 2 * polyP C₂ N₂ ν c ≤ polyP (2 * C₂) N_out ν c := by
    unfold polyP
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hX1 (le_max_right _ _)) (by positivity)
  let dp : ℝ → Plane → Vec := fun r z => Train.gradS (fun w => tr.p r w - pc ν c r w) z
  calc wCellL2 c (2 * m) (ageJet ℓ j dp s)
      ≤ wCellL2 c (2 * m) (ageJet ℓ j (fun r w => Train.gradS (tr.p r) w) s) +
          ENNReal.ofReal 2 * wCellL2 c (2 * m) (ageJet ℓ (j + 1) (pc ν c) s) := htri
    _ ≤ ENNReal.ofReal (polyP C₁ N₁ ν c) +
          ENNReal.ofReal 2 * ENNReal.ofReal (polyP C₂ N₂ ν c) := by gcongr
    _ = ENNReal.ofReal (polyP C₁ N₁ ν c) + ENNReal.ofReal (2 * polyP C₂ N₂ ν c) := by
        rw [← ENNReal.ofReal_mul (by norm_num)]
    _ ≤ ENNReal.ofReal (polyP C₁ N_out ν c) + ENNReal.ofReal (polyP (2 * C₂) N_out ν c) :=
        add_le_add (ENNReal.ofReal_le_ofReal hP₁) (ENNReal.ofReal_le_ofReal hP₂)
    _ = ENNReal.ofReal (polyP C_out N_out ν c) := by
        rw [← ENNReal.ofReal_add (by unfold polyP; positivity) (by unfold polyP; positivity)]
        congr 1
        unfold polyP
        dsimp [C_out]
        ring

/-- **Conditional assembly of `TrainFixedBandPressAgeJet` (`PartI:T25/3`)** from
`TrainFixedBandPcAgeJetTwoMulM` (`PartI:T25/3/1`) and `TrainFixedBandPressAgeJetUnweighted`
(`PartI:T25/3/2`). -/
theorem trainFixedBandPressAgeJet_of_leaves
    (hPc2m : TrainFixedBandPcAgeJetTwoMulM)
    (hUnw : TrainFixedBandPressAgeJetUnweighted)
    (hTails : TrainStreamVelocityPressureTails)
    (hFD : TrainFluctuationDecay)
    (hVel : TrainFixedBandVelAgeJet) :
    TrainFixedBandPressAgeJet := by
  intro ρ hρ Sg hSg m ℓ j
  obtain ⟨C₁, N₁, ν₁, hC₁, hν₁, h2m⟩ :=
    trainFixedBandPressAgeJet_two_mul_m_of_pc hTails hPc2m ρ hρ Sg hSg m ℓ j
  obtain ⟨C₂, N₂, CS, bS, ν₂, hC₂, hbS, hν₂, h0⟩ := hUnw hTails hFD hVel ρ hρ Sg hSg ℓ j
  refine ⟨max C₁ C₂, max N₁ N₂, CS, bS, min ν₁ ν₂,
    lt_max_of_lt_left hC₁, hbS, lt_min hν₁ hν₂, ?_⟩
  intro ν hν hν_le tr htr s hs hs_le
  have hν₁_le : ν ≤ ν₁ := hν_le.trans (min_le_left _ _)
  have hν₂_le : ν ≤ ν₂ := hν_le.trans (min_le_right _ _)
  let c := trainPeriod ρ ν
  have hc0 : 0 ≤ c := by
    dsimp [c]
    unfold trainPeriod
    exact Real.rpow_nonneg hν.le _
  have hX1 : 1 ≤ 1 + c + ν⁻¹ := by
    have : 0 ≤ ν⁻¹ := inv_nonneg.2 hν.le
    linarith
  have hdp_2m := h2m ν hν hν₁_le tr htr s hs hs_le
  obtain ⟨hL2_0, hSup_0⟩ := h0 ν hν hν₂_le tr htr s hs hs_le
  have hP₁ : polyP C₁ N₁ ν c ≤ polyP (max C₁ C₂) (max N₁ N₂) ν c := by
    unfold polyP
    exact mul_le_mul (le_max_left _ _) (pow_le_pow_right₀ hX1 (le_max_left _ _))
      (by positivity) (by positivity)
  have hP₂ : polyP C₂ N₂ ν c * Real.exp (CS / ν - bS * c ^ 2) ≤
      polyP (max C₁ C₂) (max N₁ N₂) ν c * Real.exp (CS / ν - bS * c ^ 2) := by
    apply mul_le_mul _ le_rfl (Real.exp_pos _).le (by unfold polyP; positivity)
    unfold polyP
    exact mul_le_mul (le_max_right _ _) (pow_le_pow_right₀ hX1 (le_max_right _ _))
      (by positivity) (by positivity)
  exact ⟨hdp_2m.trans (ENNReal.ofReal_le_ofReal hP₁),
    hL2_0.trans (ENNReal.ofReal_le_ofReal hP₂),
    hSup_0.trans (ENNReal.ofReal_le_ofReal hP₂)⟩

/-! ### 6. Reductions of `TrainFixedBandPressAgeJetUnweighted` (`PartI:T25/3/2`) to `PartI:T25/1` leaves -/

open UnforcedLeray.Short.IIb (Dx Sm hasDerivAt_slice vcSmooth_proof)

/-- `TrainFixedBandVelAgeJet` implies `TrainFixedBandVelOrderUnweighted r` for every `r : ℕ`
by taking `m = 0` and projecting to the unweighted `wCellL2 c 0` and `wSupNorm 0` bounds. -/
theorem trainFixedBandVelOrderUnweighted_of_velAgeJet
    (hVel : TrainFixedBandVelAgeJet) (r : ℕ) :
    TrainFixedBandVelOrderUnweighted r := by
  intro ρ hρ Sg hSg j
  obtain ⟨C, N, CS, bS, ν₀, hC, hbS, hν₀, h⟩ := hVel ρ hρ Sg hSg 0 r j
  refine ⟨C, N, CS, bS, ν₀, hC, hbS, hν₀, ?_⟩
  intro ν hν hν_le tr htr s hs hs_le
  exact (h ν hν hν_le tr htr s hs hs_le).2

/-- Direct derivation of `TrainFixedBandPressAgeJetUnweighted` (`PartI:T25/3/2`) from
`TrainFixedBandPressStep` (`PartI:T25/1/3`). -/
theorem trainFixedBandPressAgeJetUnweighted_of_pressStep
    (hPress : TrainFixedBandPressStep) :
    TrainFixedBandPressAgeJetUnweighted := by
  intro _hTails _hFD hVel ρ hρ Sg hSg ℓ j
  exact hPress ℓ (fun r _ => trainFixedBandVelOrderUnweighted_of_velAgeJet hVel r) ρ hρ Sg hSg j

namespace PartI_T25_3

/-- Pointwise expression for `dp = Train.gradS (tr.p - pc)` on `r > 0` from
`TrainErrorEquation.train_error_equation`. -/
theorem dp_eq_error_rhs {ν c : ℝ} (tr : B0140.TrainSol ν c)
    (hν : 0 < ν) (hc : c ≠ 0) {r : ℝ} (hr : 0 < r) (z : Plane) :
    Train.gradS (fun w => tr.p r w - pc ν c r w) z =
      ν • Train.vecLaplacian (fun w => tr.v r w - Vc ν c r w) z
      - deriv (fun t => tr.v t z - Vc ν c t z) r
      - (Train.advection (tr.v r) z - Train.advection (Vc ν c r) z)
      - Train.matDiv (Train.Qc ν c r) z := by
  have h := PartI_T25_1.deriv_dv_eq_error_rhs tr hν hc hr z
  ext k
  have hk := congrArg (fun v : Vec => v k) h
  simp only [PiLp.sub_apply] at hk ⊢
  linarith

/-- Iterated age derivative of `dp = Train.gradS (tr.p - pc)` on `s > 0` via the error equation. -/
theorem iteratedDeriv_dp_eq {ν c : ℝ} (tr : B0140.TrainSol ν c)
    (hν : 0 < ν) (hc : c ≠ 0) (ℓ : ℕ) {s : ℝ} (hs : 0 < s) (z : Plane) :
    iteratedDeriv ℓ (fun r => Train.gradS (fun w => tr.p r w - pc ν c r w) z) s =
      iteratedDeriv ℓ (fun r =>
        ν • Train.vecLaplacian (fun w => tr.v r w - Vc ν c r w) z
        - deriv (fun t => tr.v t z - Vc ν c t z) r
        - (Train.advection (tr.v r) z - Train.advection (Vc ν c r) z)
        - Train.matDiv (Train.Qc ν c r) z) s := by
  have hev : (fun r => Train.gradS (fun w => tr.p r w - pc ν c r w) z) =ᶠ[nhds s]
      fun r =>
        ν • Train.vecLaplacian (fun w => tr.v r w - Vc ν c r w) z
        - deriv (fun t => tr.v t z - Vc ν c t z) r
        - (Train.advection (tr.v r) z - Train.advection (Vc ν c r) z)
        - Train.matDiv (Train.Qc ν c r) z := by
    filter_upwards [Ioi_mem_nhds hs] with r hr using dp_eq_error_rhs tr hν hc hr z
  exact hev.iteratedDeriv_eq ℓ

/-- `ageJet ℓ j dp s` equals `ageJet ℓ j` of the four-term error-equation decomposition. -/
theorem ageJet_dp_eq_error_rhs {ν c : ℝ} (tr : B0140.TrainSol ν c)
    (hν : 0 < ν) (hc : c ≠ 0) (ℓ j : ℕ) {s : ℝ} (hs : 0 < s) :
    ageJet ℓ j (fun r z => Train.gradS (fun w => tr.p r w - pc ν c r w) z) s =
      ageJet ℓ j (fun r z =>
        ν • Train.vecLaplacian (fun w => tr.v r w - Vc ν c r w) z
        - deriv (fun t => tr.v t z - Vc ν c t z) r
        - (Train.advection (tr.v r) z - Train.advection (Vc ν c r) z)
        - Train.matDiv (Train.Qc ν c r) z) s := by
  unfold ageJet
  congr 1
  funext z
  exact iteratedDeriv_dp_eq tr hν hc ℓ hs z

/-- Joint smoothness on `UU = Ioi 0 ×ˢ univ` of the age derivative `(r, z) ↦ deriv (fun t => F t z) r`
of a jointly smooth vector field `F`. -/
theorem sm_deriv_slice {F : ℝ → Plane → Vec}
    (hF : Sm (fun x : ℝ × Plane => F x.1 x.2)) :
    Sm (fun x : ℝ × Plane => deriv (fun t => F t x.2) x.1) := by
  have hdx : Sm (Dx eT (fun x : ℝ × Plane => F x.1 x.2)) := hF.dx eT
  refine hdx.congr fun ⟨r, z⟩ hx => ?_
  exact (hasDerivAt_slice hF hx.1 z).deriv

/-- `ageJet ℓ j` of the first age derivative `(r, z) ↦ deriv (fun t => F t z) r` equals
`ageJet (ℓ + 1) j F s`. -/
theorem ageJet_deriv_eq_ageJet_succ (F : ℝ → Plane → Vec) (ℓ j : ℕ) (s : ℝ) :
    ageJet ℓ j (fun r z => deriv (fun t => F t z) r) s = ageJet (ℓ + 1) j F s := by
  unfold ageJet
  congr 1
  funext z
  rw [← iteratedDeriv_succ']

theorem polyP_exp_mono {C C' : ℝ} {N N' : ℕ} {CS CS' bS bS' ν c : ℝ}
    (hC : C ≤ C') (hC' : 0 ≤ C') (hN : N ≤ N') (hCS : CS ≤ CS') (hbS : bS' ≤ bS)
    (hν : 0 < ν) (hc : 0 ≤ c) :
    polyP C N ν c * Real.exp (CS / ν - bS * c ^ 2) ≤
      polyP C' N' ν c * Real.exp (CS' / ν - bS' * c ^ 2) := by
  have hX1 : 1 ≤ 1 + c + ν⁻¹ := by
    have : 0 ≤ ν⁻¹ := inv_nonneg.2 hν.le
    linarith
  apply mul_le_mul
  · unfold polyP
    exact mul_le_mul hC (pow_le_pow_right₀ hX1 hN) (by positivity) hC'
  · apply Real.exp_le_exp.2
    have hCS_div : CS / ν ≤ CS' / ν := div_le_div_of_nonneg_right hCS hν.le
    have hb_mul : bS' * c ^ 2 ≤ bS * c ^ 2 := mul_le_mul_of_nonneg_right hbS (sq_nonneg c)
    linarith
  · exact (Real.exp_pos _).le
  · unfold polyP; positivity

theorem add_four_ofReal_polyP_exp {C₁ C₂ C₃ C₄ : ℝ} {N : ℕ} {CS bS ν c : ℝ}
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hC₃ : 0 ≤ C₃) (hC₄ : 0 ≤ C₄) (hν : 0 < ν) (hc : 0 ≤ c) :
    ENNReal.ofReal (polyP C₁ N ν c * Real.exp (CS / ν - bS * c ^ 2)) +
      ENNReal.ofReal (polyP C₂ N ν c * Real.exp (CS / ν - bS * c ^ 2)) +
      ENNReal.ofReal (polyP C₃ N ν c * Real.exp (CS / ν - bS * c ^ 2)) +
      ENNReal.ofReal (polyP C₄ N ν c * Real.exp (CS / ν - bS * c ^ 2)) =
    ENNReal.ofReal (polyP (C₁ + C₂ + C₃ + C₄) N ν c * Real.exp (CS / ν - bS * c ^ 2)) := by
  have hX : 0 ≤ 1 + c + ν⁻¹ := by
    have : 0 ≤ ν⁻¹ := inv_nonneg.2 hν.le
    linarith
  have h1 : 0 ≤ polyP C₁ N ν c * Real.exp (CS / ν - bS * c ^ 2) := by unfold polyP; positivity
  have h2 : 0 ≤ polyP C₂ N ν c * Real.exp (CS / ν - bS * c ^ 2) := by unfold polyP; positivity
  have h3 : 0 ≤ polyP C₃ N ν c * Real.exp (CS / ν - bS * c ^ 2) := by unfold polyP; positivity
  have h4 : 0 ≤ polyP C₄ N ν c * Real.exp (CS / ν - bS * c ^ 2) := by unfold polyP; positivity
  rw [← ENNReal.ofReal_add h1 h2, ← ENNReal.ofReal_add (add_nonneg h1 h2) h3,
    ← ENNReal.ofReal_add (add_nonneg (add_nonneg h1 h2) h3) h4]
  congr 1
  unfold polyP
  ring

end PartI_T25_3

/-- Derivation of `TrainFixedBandPressAgeJetUnweighted` (`PartI:T25/3/2`) from
`TrainFixedBandQcDivAgeJet` (`PartI:T25/1/1`) and `TrainFixedBandAdvDiffStep` (`PartI:T25/1/2`)
via the Navier–Stokes error equation for `dp = gradS (tr.p - pc)`. -/
theorem trainFixedBandPressAgeJetUnweighted_of_qc_adv
    (hQc : TrainFixedBandQcDivAgeJet)
    (hAdv : TrainFixedBandAdvDiffStep) :
    TrainFixedBandPressAgeJetUnweighted := by
  intro _hTails _hFD hVel ρ hρ Sg hSg ℓ j
  have hIH : ∀ r : ℕ, r ≤ ℓ → TrainFixedBandVelOrderUnweighted r :=
    fun r _ => trainFixedBandVelOrderUnweighted_of_velAgeJet hVel r
  obtain ⟨C₁, N₁, CS₁, b₁, ν₁, hC₁, hb₁, hν₁, hVisc⟩ :=
    trainFixedBandViscStep_of_order ℓ (trainFixedBandVelOrderUnweighted_of_velAgeJet hVel ℓ)
      ρ hρ Sg hSg j
  obtain ⟨C₂, N₂, CS₂, b₂, ν₂, hC₂, hb₂, hν₂, hDt_bd⟩ :=
    trainFixedBandVelOrderUnweighted_of_velAgeJet hVel (ℓ + 1) ρ hρ Sg hSg j
  obtain ⟨C₃, N₃, CS₃, b₃, ν₃, hC₃, hb₃, hν₃, hAdv_bd⟩ := hAdv ℓ hIH ρ hρ Sg hSg j
  obtain ⟨C₄, N₄, CS₄, b₄, ν₄, hC₄, hb₄, hν₄, hQc_bd⟩ := hQc.2 ρ hρ Sg hSg ℓ j
  let C_out := C₁ + C₂ + C₃ + C₄
  let N_out := max (max N₁ N₂) (max N₃ N₄)
  let CS_out := max (max CS₁ CS₂) (max CS₃ CS₄)
  let b_out := min (min b₁ b₂) (min b₃ b₄)
  let ν_out := min (min ν₁ ν₂) (min ν₃ ν₄)
  refine ⟨C_out, N_out, CS_out, b_out, ν_out,
    by dsimp [C_out]; positivity,
    lt_min (lt_min hb₁ hb₂) (lt_min hb₃ hb₄),
    lt_min (lt_min hν₁ hν₂) (lt_min hν₃ hν₄), ?_⟩
  intro ν hν hν_le tr htr s hs hs_le
  have hν₁_le : ν ≤ ν₁ := hν_le.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hν₂_le : ν ≤ ν₂ := hν_le.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hν₃_le : ν ≤ ν₃ := hν_le.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hν₄_le : ν ≤ ν₄ := hν_le.trans ((min_le_right _ _).trans (min_le_right _ _))
  let c := trainPeriod ρ ν
  have hc_pos : 0 < c := by
    dsimp [c]
    unfold trainPeriod
    exact Real.rpow_pos_of_pos hν _
  let dv : ℝ → Plane → Vec := fun r z => tr.v r z - Vc ν c r z
  let F₁ : ℝ → Plane → Vec := fun r z => ν • Train.vecLaplacian (dv r) z
  let F₂ : ℝ → Plane → Vec := fun r z => deriv (fun t => dv t z) r
  let F₃ : ℝ → Plane → Vec := fun r z => Train.advection (tr.v r) z - Train.advection (Vc ν c r) z
  let F₄ : ℝ → Plane → Vec := fun r z => Train.matDiv (Train.Qc ν c r) z
  let dp : ℝ → Plane → Vec := fun r z => Train.gradS (fun w => tr.p r w - pc ν c r w) z
  have hsm_v : Sm (fun x : ℝ × Plane => tr.v x.1 x.2) :=
    tr.isTrain.smooth_v.mono (Set.prod_mono Set.Ioi_subset_Ici_self Subset.rfl)
  have hsm_Vc : Sm (fun x : ℝ × Plane => Vc ν c x.1 x.2) := vcSmooth_proof ν c hν hc_pos
  have hsm_dv : Sm (fun x : ℝ × Plane => dv x.1 x.2) := hsm_v.sub hsm_Vc
  have hsm₁ : Sm (fun x : ℝ × Plane => F₁ x.1 x.2) := PartI_T25_1.sm_smul_vecLaplacian hsm_dv ν
  have hsm₂ : Sm (fun x : ℝ × Plane => F₂ x.1 x.2) := PartI_T25_3.sm_deriv_slice hsm_dv
  have hsm₃ : Sm (fun x : ℝ × Plane => F₃ x.1 x.2) :=
    (PartI_T25_1.sm_advection hsm_v).sub (PartI_T25_1.sm_advection hsm_Vc)
  have hsm₄ : Sm (fun x : ℝ × Plane => F₄ x.1 x.2) := hQc.1 ν c hν hc_pos
  have hsm₁₂ : Sm (fun x : ℝ × Plane => F₁ x.1 x.2 - F₂ x.1 x.2) := hsm₁.sub hsm₂
  have hsm₁₂₃ : Sm (fun x : ℝ × Plane => F₁ x.1 x.2 - F₂ x.1 x.2 - F₃ x.1 x.2) := hsm₁₂.sub hsm₃
  have hjet_eq : ageJet ℓ j dp s =
      fun z => ageJet ℓ j F₁ s z - ageJet ℓ j F₂ s z - ageJet ℓ j F₃ s z - ageJet ℓ j F₄ s z := by
    rw [PartI_T25_3.ageJet_dp_eq_error_rhs tr hν hc_pos.ne' ℓ j hs]
    funext z
    have hsub3 := UnforcedLeray.Short.IIb.vb_ageJet_sub
      (fun r w => F₁ r w - F₂ r w - F₃ r w) F₄ hsm₁₂₃ hsm₄ hs ℓ j z
    have hsub2 := UnforcedLeray.Short.IIb.vb_ageJet_sub
      (fun r w => F₁ r w - F₂ r w) F₃ hsm₁₂ hsm₃ hs ℓ j z
    have hsub1 := UnforcedLeray.Short.IIb.vb_ageJet_sub F₁ F₂ hsm₁ hsm₂ hs ℓ j z
    dsimp only [F₁, F₂, F₃, F₄, dv] at hsub3 hsub2 hsub1 ⊢
    rw [hsub3, hsub2, hsub1]
  have hcont₁ := continuous_ageJet_of_contDiffOn F₁ hsm₁ ℓ j hs
  have hcont₂ := continuous_ageJet_of_contDiffOn F₂ hsm₂ ℓ j hs
  have hcont₃ := continuous_ageJet_of_contDiffOn F₃ hsm₃ ℓ j hs
  have hcont₄ := continuous_ageJet_of_contDiffOn F₄ hsm₄ ℓ j hs
  have htri_L2 : wCellL2 c 0 (ageJet ℓ j dp s) ≤
      wCellL2 c 0 (ageJet ℓ j F₁ s) + wCellL2 c 0 (ageJet ℓ j F₂ s) +
        wCellL2 c 0 (ageJet ℓ j F₃ s) + wCellL2 c 0 (ageJet ℓ j F₄ s) := by
    rw [hjet_eq]
    exact wCellL2_sub4_le_of_continuous c 0 hcont₁ hcont₂ hcont₃ hcont₄
  have htri_Sup : wSupNorm 0 (ageJet ℓ j dp s) ≤
      wSupNorm 0 (ageJet ℓ j F₁ s) + wSupNorm 0 (ageJet ℓ j F₂ s) +
        wSupNorm 0 (ageJet ℓ j F₃ s) + wSupNorm 0 (ageJet ℓ j F₄ s) := by
    rw [hjet_eq]
    exact wSupNorm_sub4_le 0 (ageJet ℓ j F₁ s) (ageJet ℓ j F₂ s) (ageJet ℓ j F₃ s) (ageJet ℓ j F₄ s)
  obtain ⟨hL2_1, hSup_1⟩ := hVisc ν hν hν₁_le tr htr s hs hs_le
  obtain ⟨hL2_2', hSup_2'⟩ := hDt_bd ν hν hν₂_le tr htr s hs hs_le
  have hF₂_eq : ageJet ℓ j F₂ s = ageJet (ℓ + 1) j dv s :=
    PartI_T25_3.ageJet_deriv_eq_ageJet_succ dv ℓ j s
  have hL2_2 : wCellL2 c 0 (ageJet ℓ j F₂ s) ≤
      ENNReal.ofReal (polyP C₂ N₂ ν c * Real.exp (CS₂ / ν - b₂ * c ^ 2)) := by
    rw [hF₂_eq]; exact hL2_2'
  have hSup_2 : wSupNorm 0 (ageJet ℓ j F₂ s) ≤
      ENNReal.ofReal (polyP C₂ N₂ ν c * Real.exp (CS₂ / ν - b₂ * c ^ 2)) := by
    rw [hF₂_eq]; exact hSup_2'
  obtain ⟨hL2_3, hSup_3⟩ := hAdv_bd ν hν hν₃_le tr htr s hs hs_le
  obtain ⟨hL2_4, hSup_4⟩ := hQc_bd ν hν hν₄_le s hs hs_le
  have hm₁ := ENNReal.ofReal_le_ofReal (PartI_T25_3.polyP_exp_mono
    (N' := N_out) (CS' := CS_out) (bS' := b_out) le_rfl hC₁.le
    ((le_max_left N₁ N₂).trans (le_max_left _ _))
    ((le_max_left CS₁ CS₂).trans (le_max_left _ _))
    ((min_le_left _ _).trans (min_le_left _ _)) hν hc_pos.le)
  have hm₂ := ENNReal.ofReal_le_ofReal (PartI_T25_3.polyP_exp_mono
    (N' := N_out) (CS' := CS_out) (bS' := b_out) le_rfl hC₂.le
    ((le_max_right N₁ N₂).trans (le_max_left _ _))
    ((le_max_right CS₁ CS₂).trans (le_max_left _ _))
    ((min_le_left _ _).trans (min_le_right _ _)) hν hc_pos.le)
  have hm₃ := ENNReal.ofReal_le_ofReal (PartI_T25_3.polyP_exp_mono
    (N' := N_out) (CS' := CS_out) (bS' := b_out) le_rfl hC₃.le
    ((le_max_left N₃ N₄).trans (le_max_right _ _))
    ((le_max_left CS₃ CS₄).trans (le_max_right _ _))
    ((min_le_right _ _).trans (min_le_left _ _)) hν hc_pos.le)
  have hm₄ := ENNReal.ofReal_le_ofReal (PartI_T25_3.polyP_exp_mono
    (N' := N_out) (CS' := CS_out) (bS' := b_out) le_rfl hC₄.le
    ((le_max_right N₃ N₄).trans (le_max_right _ _))
    ((le_max_right CS₃ CS₄).trans (le_max_right _ _))
    ((min_le_right _ _).trans (min_le_right _ _)) hν hc_pos.le)
  have hsum_eq := PartI_T25_3.add_four_ofReal_polyP_exp
    (N := N_out) (CS := CS_out) (bS := b_out) hC₁.le hC₂.le hC₃.le hC₄.le hν hc_pos.le
  dsimp only
  refine ⟨?_, ?_⟩
  · calc wCellL2 c 0 (ageJet ℓ j dp s)
        ≤ wCellL2 c 0 (ageJet ℓ j F₁ s) + wCellL2 c 0 (ageJet ℓ j F₂ s) +
            wCellL2 c 0 (ageJet ℓ j F₃ s) + wCellL2 c 0 (ageJet ℓ j F₄ s) := htri_L2
      _ ≤ _ := add_le_add (add_le_add (add_le_add (hL2_1.trans hm₁) (hL2_2.trans hm₂))
            (hL2_3.trans hm₃)) (hL2_4.trans hm₄)
      _ = ENNReal.ofReal (polyP C_out N_out ν c * Real.exp (CS_out / ν - b_out * c ^ 2)) := hsum_eq
  · calc wSupNorm 0 (ageJet ℓ j dp s)
        ≤ wSupNorm 0 (ageJet ℓ j F₁ s) + wSupNorm 0 (ageJet ℓ j F₂ s) +
            wSupNorm 0 (ageJet ℓ j F₃ s) + wSupNorm 0 (ageJet ℓ j F₄ s) := htri_Sup
      _ ≤ _ := add_le_add (add_le_add (add_le_add (hSup_1.trans hm₁) (hSup_2.trans hm₂))
            (hSup_3.trans hm₃)) (hSup_4.trans hm₄)
      _ = ENNReal.ofReal (polyP C_out N_out ν c * Real.exp (CS_out / ν - b_out * c ^ 2)) := hsum_eq

/-- Conditional assembly of `TrainFixedBandPressAgeJet` from `TrainFixedBandPcAgeJetTwoMulM`
(`PartI:T25/3/1`) and `TrainFixedBandPressStep` (`PartI:T25/1/3`). -/
theorem trainFixedBandPressAgeJet_of_pc_and_pressStep
    (hPc2m : TrainFixedBandPcAgeJetTwoMulM)
    (hPress : TrainFixedBandPressStep)
    (hTails : TrainStreamVelocityPressureTails)
    (hFD : TrainFluctuationDecay)
    (hVel : TrainFixedBandVelAgeJet) :
    TrainFixedBandPressAgeJet :=
  trainFixedBandPressAgeJet_of_leaves hPc2m
    (trainFixedBandPressAgeJetUnweighted_of_pressStep hPress) hTails hFD hVel

/-- Conditional assembly of `TrainFixedBandPressAgeJet` from `TrainFixedBandPcAgeJetTwoMulM`
(`PartI:T25/3/1`), `TrainFixedBandQcDivAgeJet` (`PartI:T25/1/1`), and `TrainFixedBandAdvDiffStep`
(`PartI:T25/1/2`). -/
theorem trainFixedBandPressAgeJet_of_pc_qc_adv
    (hPc2m : TrainFixedBandPcAgeJetTwoMulM)
    (hQc : TrainFixedBandQcDivAgeJet)
    (hAdv : TrainFixedBandAdvDiffStep)
    (hTails : TrainStreamVelocityPressureTails)
    (hFD : TrainFluctuationDecay)
    (hVel : TrainFixedBandVelAgeJet) :
    TrainFixedBandPressAgeJet :=
  trainFixedBandPressAgeJet_of_leaves hPc2m
    (trainFixedBandPressAgeJetUnweighted_of_qc_adv hQc hAdv) hTails hFD hVel

end UnforcedLeray.Short.PartI.VelAgeJetAux

end
