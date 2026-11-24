import Mathlib.Analysis.Calculus.ContDiff.Bounds
import UnforcedLeray.Short.PartI.Sub.PartI_T20
import UnforcedLeray.Short.PartI.Sub.PartI_T25_1
import UnforcedLeray.Short.PartI.Tasks.TrainFixedBandProof.VortAgeJet
import UnforcedLeray.Short.PartI.Tasks.VorticityFirstMoment.LocalVorticityEquation.Layer

/-!
# `PartI:T20/1`: Age derivatives of the vorticity Gaussian transverse tail (`AgeDeriv.lean`)

Source of record: `the November 2 reference manuscript`, lines 483-497 and 523-526
("The equations now give the age derivatives by finite induction").

This module proves:
1. **Jointly smooth scalar calculus on `UU = Ioi 0 ×ˢ univ`** (`SmR`, `DxR`, `DtR`, `LapR`):
   commutation of `iteratedDeriv ℓ` in age `s > 0` with `Cyl.partialQ`, `Cyl.partialEta`, and
   `Train.lapS`; linearity of `ageJet ℓ j` on sums and differences of jointly smooth scalar and
   vector families; and joint smoothness on `UU` of `Cyl.curl (tr.v r)`,
   `ν * Train.lapS (Cyl.curl (tr.v r))`, and the vorticity advection terms
   `tr.v r w 0 * Cyl.partialQ (Cyl.curl (tr.v r)) w` and
   `tr.v r w 1 * Cyl.partialEta (Cyl.curl (tr.v r)) w`.
2. **Spacetime Leibniz product rule for `ageJet ℓ j`** (`PartI_T20.norm_ageJet_mul_le`):
   by induction on the age derivative order `ℓ : ℕ` using the product rule for `DtR` and
   `norm_iteratedFDerivWithin_mul_le` on `Plane` at `ℓ = 0`, any product of two jointly smooth
   scalar families `A, B : ℝ → Plane → ℝ` satisfies
   `‖ageJet ℓ j (fun r w => A r w * B r w) s z‖ ≤ 2 ^ (ℓ + j) * M_A * M_B`
   whenever `‖ageJet r i A s z‖ ≤ M_A` and `‖ageJet r i B s z‖ ≤ M_B` for all `r ≤ ℓ` and `i ≤ j`.
3. **Iterated age-derivative vorticity equation (`PartI_T20.ageJet_succ_curl_eq`)**:
   from `localVorticityEquation` (`∂_s ω = ν Δω - v_0 ∂_q ω - v_1 ∂_η ω`), expresses
   `ageJet (ℓ + 1) j (fun r w => Cyl.curl (tr.v r) w) s z` as the combination of the viscous term
   and the two vorticity advection terms at age order `ℓ`.
4. **Inductive step and strong induction on age order `ℓ` for the vorticity Gaussian tail**:
   * `trainVorticityGaussianTailAt_zero`: base case `ℓ = 0` for all `j : ℕ` from
     `hSpatial : TrainVorticitySpatialJetTail`;
   * `trainVelocityAgeJetSupBoundAt_zero`: unconditional `ℓ = 0` velocity jet sup bound from
     `PartI_T20.train_v_jet_sup_bound`;
   * `trainVorticityGaussianTailAt_succ`: inductive step `ℓ → ℓ + 1` combining the viscous step
     (`norm_ageJet_mul_lapS_le`), the advection steps (`norm_ageJet_mul_le`), and Gaussian tail
     parameter merging (`exp_gaussian_tail_mono`);
   * `trainVorticityGaussianTailAt_one`: unconditional `ℓ = 1` vorticity Gaussian tail for all
     spatial orders `j : ℕ` from `hOv : TrainOverlap` and `hSpatial : TrainVorticitySpatialJetTail`;
   * `trainVorticityGaussianTailAt_all` and `trainVorticityAgeDerivFromZero_of`: full all-order
     induction from `TrainVelocityHigherAgeJetSupBound` (and reduction of the latter via the
     differentiated momentum equation `∂_s v = ν Δv - (v · ∇)v - ∇p` to the pressure-gradient
     sup bound `TrainPressureGradAgeJetSupBound`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec toVec jet cellL2 wCellL2 jap Vc pc width)
open UnforcedLeray.Short.IIb (UU isOpen_UU mem_UU Dx eT eQ eE LapU Sm Dx_congr Dx_add LapU_comm_t
  hasDerivAt_slice slice_Dv slice_lapD lapD vecLaplacian_eq_lapD norm_jet_lapD_le
  Dv contDiff_Dv Dv_proj scalar_lap_eq
  vb_slice_iteratedDeriv_eq vb_slice_contDiffAt vb_slice_smooth_at vb_ageJet_sub)

namespace PartI_T20

/-! ### 1. Jointly smooth scalar calculus on `UU = Ioi 0 ×ˢ univ` -/

/-- Jointly `C^∞` scalar field on `UU = Ioi 0 ×ˢ univ`. -/
abbrev SmR (F : ℝ × Plane → ℝ) : Prop := ContDiffOn ℝ ∞ F UU

/-- Directional derivative of a scalar field on `ℝ × Plane`. -/
noncomputable def DxR (v : ℝ × Plane) (F : ℝ × Plane → ℝ) : ℝ × Plane → ℝ :=
  fun x => fderiv ℝ F x v

/-- Iterated age directional derivative `(DxR eT)^[ℓ] F` of a scalar field on `ℝ × Plane`. -/
noncomputable def DtR (ℓ : ℕ) (F : ℝ × Plane → ℝ) : ℝ × Plane → ℝ :=
  (DxR eT)^[ℓ] F

/-- Spatial Laplacian `∂_q² + ∂_η²` of a scalar field on `ℝ × Plane`. -/
noncomputable def LapR (F : ℝ × Plane → ℝ) : ℝ × Plane → ℝ :=
  fun x => DxR eQ (DxR eQ F) x + DxR eE (DxR eE F) x

theorem SmR.dx {F : ℝ × Plane → ℝ} (hF : SmR F) (v : ℝ × Plane) : SmR (DxR v F) :=
  (hF.fderiv_of_isOpen isOpen_UU (by simp)).clm_apply contDiffOn_const

theorem SmR.lap {F : ℝ × Plane → ℝ} (hF : SmR F) : SmR (LapR F) :=
  ((hF.dx _).dx _).add ((hF.dx _).dx _)

theorem SmR.diffAt {F : ℝ × Plane → ℝ} (hF : SmR F) {x : ℝ × Plane} (hx : x ∈ UU) :
    DifferentiableAt ℝ F x :=
  (hF.differentiableOn (by simp)).differentiableAt (isOpen_UU.mem_nhds hx)

theorem SmR.symm {F : ℝ × Plane → ℝ} (hF : SmR F) {x : ℝ × Plane} (hx : x ∈ UU)
    (v w : ℝ × Plane) : DxR w (DxR v F) x = DxR v (DxR w F) x := by
  have hc : ContDiffAt ℝ ∞ F x := hF.contDiffAt (isOpen_UU.mem_nhds hx)
  have hc2 : ContDiffAt ℝ ((2 : ℕ) : WithTop ℕ∞) F x := hc.of_le (by simp)
  have hn : minSmoothness ℝ 2 ≤ ((2 : ℕ) : WithTop ℕ∞) := by
    rw [minSmoothness_of_isRCLikeNormedField]
    simp
  have hs := ContDiffAt.isSymmSndFDerivAt hc2 hn
  have hd : DifferentiableAt ℝ (fderiv ℝ F) x :=
    ((hF.fderiv_of_isOpen (m := ∞) isOpen_UU (by simp)).differentiableOn (by simp)).differentiableAt
      (isOpen_UU.mem_nhds hx)
  have key : ∀ a b : ℝ × Plane, DxR a (DxR b F) x = fderiv ℝ (fderiv ℝ F) x a b := by
    intro a b
    show fderiv ℝ (fun y => fderiv ℝ F y b) x a = _
    rw [fderiv_clm_apply hd (differentiableAt_const b)]
    simp
  rw [key, key]
  exact hs w v

theorem DxR_congr {F F' : ℝ × Plane → ℝ} (h : EqOn F F' UU) (v : ℝ × Plane) :
    EqOn (DxR v F) (DxR v F') UU := by
  intro x hx
  have : F =ᶠ[nhds x] F' := h.eventuallyEq_of_mem (isOpen_UU.mem_nhds hx)
  show fderiv ℝ F x v = fderiv ℝ F' x v
  rw [this.fderiv_eq]

theorem DxR_add {A B : ℝ × Plane → ℝ} (hA : SmR A) (hB : SmR B) (v : ℝ × Plane) :
    EqOn (DxR v (fun y => A y + B y)) (fun y => DxR v A y + DxR v B y) UU := by
  intro x hx
  show fderiv ℝ (fun y => A y + B y) x v = fderiv ℝ A x v + fderiv ℝ B x v
  have h : HasFDerivAt (fun y => A y + B y) (fderiv ℝ A x + fderiv ℝ B x) x :=
    (hA.diffAt hx).hasFDerivAt.add (hB.diffAt hx).hasFDerivAt
  rw [h.fderiv]
  rfl

theorem DxR_comm_sq {F : ℝ × Plane → ℝ} (hF : SmR F) (e : ℝ × Plane) {x : ℝ × Plane}
    (hx : x ∈ UU) : DxR eT (DxR e (DxR e F)) x = DxR e (DxR e (DxR eT F)) x := by
  have hG : SmR (DxR e F) := hF.dx e
  have h1 : DxR eT (DxR e (DxR e F)) x = DxR e (DxR eT (DxR e F)) x := hG.symm hx e eT
  have h2 : EqOn (DxR eT (DxR e F)) (DxR e (DxR eT F)) UU := fun y hy => hF.symm hy e eT
  rw [h1]
  exact DxR_congr h2 e hx

theorem LapR_comm_t {F : ℝ × Plane → ℝ} (hF : SmR F) :
    EqOn (DxR eT (LapR F)) (LapR (DxR eT F)) UU := by
  intro x hx
  have hQ : SmR (DxR eQ (DxR eQ F)) := (hF.dx _).dx _
  have hE : SmR (DxR eE (DxR eE F)) := (hF.dx _).dx _
  have := DxR_add hQ hE eT hx
  show DxR eT (fun y => DxR eQ (DxR eQ F) y + DxR eE (DxR eE F) y) x = _
  rw [this]
  show DxR eT (DxR eQ (DxR eQ F)) x + DxR eT (DxR eE (DxR eE F)) x = _
  rw [DxR_comm_sq hF eQ hx, DxR_comm_sq hF eE hx]
  rfl

theorem smR_DtR {F : ℝ × Plane → ℝ} (hF : SmR F) : ∀ ℓ : ℕ, SmR (DtR ℓ F)
  | 0 => hF
  | ℓ + 1 => by
    unfold DtR
    rw [Function.iterate_succ_apply']
    exact (smR_DtR hF ℓ).dx eT

theorem hasDerivAt_sliceR {F : ℝ × Plane → ℝ} (hF : SmR F) {t : ℝ} (ht : 0 < t) (w : Plane) :
    HasDerivAt (fun r => F (r, w)) (DxR eT F (t, w)) t := by
  have h0 : HasDerivAt (fun r : ℝ => (r, w)) ((1 : ℝ), (0 : Plane)) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t w)
  exact (hF.diffAt (mem_UU ht)).hasFDerivAt.comp_hasDerivAt t h0

theorem iteratedDeriv_slice_eq_DtR {F : ℝ × Plane → ℝ} (hF : SmR F) :
    ∀ (ℓ : ℕ) {t : ℝ}, 0 < t → ∀ w : Plane,
      iteratedDeriv ℓ (fun r => F (r, w)) t = DtR ℓ F (t, w)
  | 0, _, _, _ => rfl
  | ℓ + 1, t, ht, w => by
    rw [iteratedDeriv_succ]
    have hev : iteratedDeriv ℓ (fun r => F (r, w)) =ᶠ[nhds t] fun r => DtR ℓ F (r, w) := by
      filter_upwards [Ioi_mem_nhds ht] with r hr using iteratedDeriv_slice_eq_DtR hF ℓ hr w
    rw [hev.deriv_eq, (hasDerivAt_sliceR (smR_DtR hF ℓ) ht w).deriv]
    unfold DtR
    rw [Function.iterate_succ_apply']

theorem DtR_comm_DxR {F : ℝ × Plane → ℝ} (hF : SmR F) (v : ℝ × Plane) :
    ∀ ℓ : ℕ, EqOn (DxR v (DtR ℓ F)) (DtR ℓ (DxR v F)) UU
  | 0 => fun _ _ => rfl
  | ℓ + 1 => by
    intro x hx
    unfold DtR
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    change DxR v (DxR eT (DtR ℓ F)) x = DxR eT (DtR ℓ (DxR v F)) x
    rw [(smR_DtR hF ℓ).symm hx eT v]
    exact DxR_congr (DtR_comm_DxR hF v ℓ) eT hx

theorem DtR_comm_LapR {F : ℝ × Plane → ℝ} (hF : SmR F) :
    ∀ ℓ : ℕ, EqOn (DtR ℓ (LapR F)) (LapR (DtR ℓ F)) UU
  | 0 => fun _ _ => rfl
  | ℓ + 1 => by
    intro x hx
    have hDt : ∀ G : ℝ × Plane → ℝ, DtR (ℓ + 1) G = DxR eT (DtR ℓ G) :=
      fun G => Function.iterate_succ_apply' (DxR eT) ℓ G
    rw [hDt, hDt, DxR_congr (DtR_comm_LapR hF ℓ) eT hx]
    exact LapR_comm_t (smR_DtR hF ℓ) hx

theorem contDiff_slice_of_smR {F : ℝ → Plane → ℝ}
    (hF : SmR (fun x : ℝ × Plane => F x.1 x.2)) {t : ℝ} (ht : 0 < t) :
    ContDiff ℝ ∞ (F t) := by
  rw [← contDiffOn_univ]
  exact hF.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun x _ => mem_UU ht)

theorem slice_DvR {F : ℝ × Plane → ℝ} (hF : SmR F) {t : ℝ} (ht : 0 < t) (e : Plane) :
    Dv e (fun w => F (t, w)) = fun w => DxR (0, e) F (t, w) := by
  funext w
  have h1 : HasFDerivAt (fun w : Plane => (t, w)) (ContinuousLinearMap.inr ℝ ℝ Plane) w :=
    hasFDerivAt_prodMk_right t w
  have h2 := (hF.diffAt (mem_UU ht)).hasFDerivAt.comp w h1
  show fderiv ℝ (F ∘ fun w : Plane => (t, w)) w e = fderiv ℝ F (t, w) (0, e)
  rw [h2.fderiv]
  rfl

theorem partialQ_slice_eq_DxR {F : ℝ → Plane → ℝ}
    (hF : SmR (fun x : ℝ × Plane => F x.1 x.2)) {t : ℝ} (ht : 0 < t) (w : Plane) :
    Cyl.partialQ (F t) w = DxR eQ (fun x : ℝ × Plane => F x.1 x.2) (t, w) := by
  have hu : ContDiff ℝ ∞ (F t) := contDiff_slice_of_smR hF ht
  rw [Cyl.partialQ_eq_fderiv (hu.differentiable (by simp)) w]
  exact congrFun (slice_DvR hF ht ((1 : ℝ), (0 : ℝ))) w

theorem partialEta_slice_eq_DxR {F : ℝ → Plane → ℝ}
    (hF : SmR (fun x : ℝ × Plane => F x.1 x.2)) {t : ℝ} (ht : 0 < t) (w : Plane) :
    Cyl.partialEta (F t) w = DxR eE (fun x : ℝ × Plane => F x.1 x.2) (t, w) := by
  have hu : ContDiff ℝ ∞ (F t) := contDiff_slice_of_smR hF ht
  rw [Cyl.partialEta_eq_fderiv (hu.differentiable (by simp)) w]
  exact congrFun (slice_DvR hF ht ((0 : ℝ), (1 : ℝ))) w

theorem lapS_slice_eq_LapR {F : ℝ → Plane → ℝ}
    (hF : SmR (fun x : ℝ × Plane => F x.1 x.2)) {t : ℝ} (ht : 0 < t) (w : Plane) :
    Train.lapS (F t) w = LapR (fun x : ℝ × Plane => F x.1 x.2) (t, w) := by
  let U : ℝ × Plane → ℝ := fun x => F x.1 x.2
  have hu : ContDiff ℝ ∞ (F t) := contDiff_slice_of_smR hF ht
  rw [scalar_lap_eq hu w]
  have a1 : Dv ((1 : ℝ), (0 : ℝ)) (F t) = fun w => DxR eQ U (t, w) := slice_DvR hF ht _
  have a2 : Dv ((0 : ℝ), (1 : ℝ)) (F t) = fun w => DxR eE U (t, w) := slice_DvR hF ht _
  have b1 : Dv ((1 : ℝ), (0 : ℝ)) (fun w => DxR eQ U (t, w)) =
      fun w => DxR eQ (DxR eQ U) (t, w) := slice_DvR (hF.dx eQ) ht _
  have b2 : Dv ((0 : ℝ), (1 : ℝ)) (fun w => DxR eE U (t, w)) =
      fun w => DxR eE (DxR eE U) (t, w) := slice_DvR (hF.dx eE) ht _
  rw [a1, a2, b1, b2]
  rfl

theorem smR_partialQ {F : ℝ → Plane → ℝ}
    (hF : SmR (fun x : ℝ × Plane => F x.1 x.2)) :
    SmR (fun x : ℝ × Plane => Cyl.partialQ (F x.1) x.2) :=
  (hF.dx eQ).congr fun ⟨_t, w⟩ hx => partialQ_slice_eq_DxR hF hx.1 w

theorem smR_partialEta {F : ℝ → Plane → ℝ}
    (hF : SmR (fun x : ℝ × Plane => F x.1 x.2)) :
    SmR (fun x : ℝ × Plane => Cyl.partialEta (F x.1) x.2) :=
  (hF.dx eE).congr fun ⟨_t, w⟩ hx => partialEta_slice_eq_DxR hF hx.1 w

theorem smR_mul_lapS {F : ℝ → Plane → ℝ}
    (hF : SmR (fun x : ℝ × Plane => F x.1 x.2)) (ν : ℝ) :
    SmR (fun x : ℝ × Plane => ν * Train.lapS (F x.1) x.2) := by
  have hLap : SmR (fun x : ℝ × Plane => ν * LapR (fun y : ℝ × Plane => F y.1 y.2) x) :=
    contDiffOn_const.mul hF.lap
  refine hLap.congr fun ⟨_t, w⟩ hx => ?_
  dsimp only
  rw [lapS_slice_eq_LapR hF hx.1 w]

theorem smR_curl {V : ℝ → Plane → Vec}
    (hV : Sm (fun x : ℝ × Plane => V x.1 x.2)) :
    SmR (fun x : ℝ × Plane => Cyl.curl (V x.1) x.2) := by
  let U : ℝ × Plane → Vec := fun x => V x.1 x.2
  have h1 : SmR (fun x : ℝ × Plane => Dx eQ U x 1) :=
    (EuclideanSpace.proj (1 : Fin 2) : Vec →L[ℝ] ℝ).contDiff.comp_contDiffOn (hV.dx eQ)
  have h0 : SmR (fun x : ℝ × Plane => Dx eE U x 0) :=
    (EuclideanSpace.proj (0 : Fin 2) : Vec →L[ℝ] ℝ).contDiff.comp_contDiffOn (hV.dx eE)
  exact (h1.sub h0).congr fun ⟨t, w⟩ hx => curl_slice_eq_Dx hV hx.1 w

/-! ### 2. Linearity of `ageJet` and commutation with `partialQ`, `partialEta`, `lapS` -/

theorem ageJet_add {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F G : ℝ → Plane → E)
    (hF : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => F x.1 x.2) UU)
    (hG : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => G x.1 x.2) UU)
    {s : ℝ} (hs : 0 < s) (ℓ j : ℕ) (w : Plane) :
    ageJet ℓ j (fun r v => F r v + G r v) s w =
      ageJet ℓ j F s w + ageJet ℓ j G s w := by
  have hadd : ∀ v : Plane, iteratedDeriv ℓ (fun r => F r v + G r v) s =
      iteratedDeriv ℓ (fun r => F r v) s + iteratedDeriv ℓ (fun r => G r v) s := by
    intro v
    exact iteratedDeriv_add (vb_slice_smooth_at F hF hs v ℓ) (vb_slice_smooth_at G hG hs v ℓ)
  have hjet : (fun v : Plane => iteratedDeriv ℓ (fun r => F r v + G r v) s) =
      (fun v : Plane => iteratedDeriv ℓ (fun r => F r v) s) +
        (fun v : Plane => iteratedDeriv ℓ (fun r => G r v) s) :=
    funext hadd
  have hA : ContDiffAt ℝ j (fun v : Plane => iteratedDeriv ℓ (fun r => F r v) s) w :=
    vb_slice_contDiffAt (fun x : ℝ × Plane => F x.1 x.2) hF ℓ j hs w
  have hB : ContDiffAt ℝ j (fun v : Plane => iteratedDeriv ℓ (fun r => G r v) s) w :=
    vb_slice_contDiffAt (fun x : ℝ × Plane => G x.1 x.2) hG ℓ j hs w
  unfold ageJet jet
  rw [hjet, iteratedFDeriv_add_apply hA hB]

theorem ageJet_sub {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F G : ℝ → Plane → E)
    (hF : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => F x.1 x.2) UU)
    (hG : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => G x.1 x.2) UU)
    {s : ℝ} (hs : 0 < s) (ℓ j : ℕ) (w : Plane) :
    ageJet ℓ j (fun r v => F r v - G r v) s w =
      ageJet ℓ j F s w - ageJet ℓ j G s w := by
  have hsub : ∀ v : Plane, iteratedDeriv ℓ (fun r => F r v - G r v) s =
      iteratedDeriv ℓ (fun r => F r v) s - iteratedDeriv ℓ (fun r => G r v) s := by
    intro v
    exact iteratedDeriv_sub (vb_slice_smooth_at F hF hs v ℓ) (vb_slice_smooth_at G hG hs v ℓ)
  have hjet : (fun v : Plane => iteratedDeriv ℓ (fun r => F r v - G r v) s) =
      (fun v : Plane => iteratedDeriv ℓ (fun r => F r v) s) -
        (fun v : Plane => iteratedDeriv ℓ (fun r => G r v) s) :=
    funext hsub
  have hA : ContDiffAt ℝ j (fun v : Plane => iteratedDeriv ℓ (fun r => F r v) s) w :=
    vb_slice_contDiffAt (fun x : ℝ × Plane => F x.1 x.2) hF ℓ j hs w
  have hB : ContDiffAt ℝ j (fun v : Plane => iteratedDeriv ℓ (fun r => G r v) s) w :=
    vb_slice_contDiffAt (fun x : ℝ × Plane => G x.1 x.2) hG ℓ j hs w
  unfold ageJet jet
  rw [hjet, iteratedFDeriv_sub_apply hA hB]

theorem iteratedDeriv_partialQ_eq {F : ℝ → Plane → ℝ}
    (hF : SmR (fun x : ℝ × Plane => F x.1 x.2)) (ℓ : ℕ) {s : ℝ} (hs : 0 < s) (w : Plane) :
    iteratedDeriv ℓ (fun r => Cyl.partialQ (F r) w) s =
      Cyl.partialQ (fun x => iteratedDeriv ℓ (fun r => F r x) s) w := by
  let U : ℝ × Plane → ℝ := fun x => F x.1 x.2
  have hev : (fun r => Cyl.partialQ (F r) w) =ᶠ[nhds s] fun r => DxR eQ U (r, w) := by
    filter_upwards [Ioi_mem_nhds hs] with r hr using partialQ_slice_eq_DxR hF hr w
  rw [hev.iteratedDeriv_eq ℓ, iteratedDeriv_slice_eq_DtR (hF.dx eQ) ℓ hs w,
    ← DtR_comm_DxR hF eQ ℓ (mem_UU hs)]
  have hsl := partialQ_slice_eq_DxR (F := fun r x => DtR ℓ U (r, x)) (smR_DtR hF ℓ) hs w
  rw [← hsl]
  congr 1
  funext x
  exact (iteratedDeriv_slice_eq_DtR hF ℓ hs x).symm

theorem iteratedDeriv_partialEta_eq {F : ℝ → Plane → ℝ}
    (hF : SmR (fun x : ℝ × Plane => F x.1 x.2)) (ℓ : ℕ) {s : ℝ} (hs : 0 < s) (w : Plane) :
    iteratedDeriv ℓ (fun r => Cyl.partialEta (F r) w) s =
      Cyl.partialEta (fun x => iteratedDeriv ℓ (fun r => F r x) s) w := by
  let U : ℝ × Plane → ℝ := fun x => F x.1 x.2
  have hev : (fun r => Cyl.partialEta (F r) w) =ᶠ[nhds s] fun r => DxR eE U (r, w) := by
    filter_upwards [Ioi_mem_nhds hs] with r hr using partialEta_slice_eq_DxR hF hr w
  rw [hev.iteratedDeriv_eq ℓ, iteratedDeriv_slice_eq_DtR (hF.dx eE) ℓ hs w,
    ← DtR_comm_DxR hF eE ℓ (mem_UU hs)]
  have hsl := partialEta_slice_eq_DxR (F := fun r x => DtR ℓ U (r, x)) (smR_DtR hF ℓ) hs w
  rw [← hsl]
  congr 1
  funext x
  exact (iteratedDeriv_slice_eq_DtR hF ℓ hs x).symm

theorem iteratedDeriv_mul_lapS_eq {F : ℝ → Plane → ℝ}
    (hF : SmR (fun x : ℝ × Plane => F x.1 x.2)) (ν : ℝ) (ℓ : ℕ) {s : ℝ} (hs : 0 < s) (w : Plane) :
    iteratedDeriv ℓ (fun r => ν * Train.lapS (F r) w) s =
      ν * Train.lapS (fun x => iteratedDeriv ℓ (fun r => F r x) s) w := by
  let U : ℝ × Plane → ℝ := fun x => F x.1 x.2
  have hev : (fun r => ν * Train.lapS (F r) w) =ᶠ[nhds s] fun r => ν * LapR U (r, w) := by
    filter_upwards [Ioi_mem_nhds hs] with r hr
    rw [lapS_slice_eq_LapR hF hr w]
  rw [hev.iteratedDeriv_eq ℓ]
  change iteratedDeriv ℓ (ν • fun r => LapR U (r, w)) s = _
  rw [iteratedDeriv_const_smul_field, smul_eq_mul]
  congr 1
  rw [iteratedDeriv_slice_eq_DtR hF.lap ℓ hs w, DtR_comm_LapR hF ℓ (mem_UU hs)]
  have hsl := lapS_slice_eq_LapR (F := fun r x => DtR ℓ U (r, x)) (smR_DtR hF ℓ) hs w
  rw [← hsl]
  congr 1
  funext x
  exact (iteratedDeriv_slice_eq_DtR hF ℓ hs x).symm

/-! ### 3. Spatial jet bounds for `Dv`, `partialQ`, `partialEta`, `lapS`, and projections -/

theorem norm_jet_Dv_scalar_le {u : Plane → ℝ} (hu : ContDiff ℝ ∞ u) (v : Plane) (j : ℕ) (z : Plane) :
    ‖iteratedFDeriv ℝ j (Dv v u) z‖ ≤ ‖v‖ * ‖iteratedFDeriv ℝ (j + 1) u z‖ := by
  have hfd : ContDiff ℝ ∞ (fderiv ℝ u) := (contDiff_infty_iff_fderiv.1 hu).2
  have e : Dv v u = (ContinuousLinearMap.apply ℝ ℝ v) ∘ (fderiv ℝ u) := rfl
  rw [e, ← norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := u) (x := z) (n := j)]
  refine ((ContinuousLinearMap.apply ℝ ℝ v).norm_iteratedFDeriv_comp_left
    (hfd.contDiffAt) (by exact_mod_cast le_top)).trans ?_
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (fun f => ?_)
  simpa [mul_comm] using f.le_opNorm v

theorem norm_jet_lapS_le {u : Plane → ℝ} (hu : ContDiff ℝ ∞ u) (j : ℕ) (z : Plane) :
    ‖iteratedFDeriv ℝ j (Train.lapS u) z‖ ≤ 2 * ‖iteratedFDeriv ℝ (j + 2) u z‖ := by
  have hA : ContDiff ℝ ∞ (Dv ((1 : ℝ), (0 : ℝ)) (Dv ((1 : ℝ), (0 : ℝ)) u)) :=
    contDiff_Dv (contDiff_Dv hu _) _
  have hB : ContDiff ℝ ∞ (Dv ((0 : ℝ), (1 : ℝ)) (Dv ((0 : ℝ), (1 : ℝ)) u)) :=
    contDiff_Dv (contDiff_Dv hu _) _
  have cA : ContDiffAt ℝ j (Dv ((1 : ℝ), (0 : ℝ)) (Dv ((1 : ℝ), (0 : ℝ)) u)) z :=
    (hA.of_le (by exact_mod_cast le_top)).contDiffAt
  have cB : ContDiffAt ℝ j (Dv ((0 : ℝ), (1 : ℝ)) (Dv ((0 : ℝ), (1 : ℝ)) u)) z :=
    (hB.of_le (by exact_mod_cast le_top)).contDiffAt
  have e : Train.lapS u = Dv ((1 : ℝ), (0 : ℝ)) (Dv ((1 : ℝ), (0 : ℝ)) u) +
      Dv ((0 : ℝ), (1 : ℝ)) (Dv ((0 : ℝ), (1 : ℝ)) u) := funext (scalar_lap_eq hu)
  have n1 : ‖((1 : ℝ), (0 : ℝ))‖ = 1 := by simp [Prod.norm_def]
  have n2 : ‖((0 : ℝ), (1 : ℝ))‖ = 1 := by simp [Prod.norm_def]
  have b1 := norm_jet_Dv_scalar_le (contDiff_Dv hu ((1 : ℝ), (0 : ℝ))) ((1 : ℝ), (0 : ℝ)) j z
  have b2 := norm_jet_Dv_scalar_le hu ((1 : ℝ), (0 : ℝ)) (j + 1) z
  have b3 := norm_jet_Dv_scalar_le (contDiff_Dv hu ((0 : ℝ), (1 : ℝ))) ((0 : ℝ), (1 : ℝ)) j z
  have b4 := norm_jet_Dv_scalar_le hu ((0 : ℝ), (1 : ℝ)) (j + 1) z
  rw [n1] at b1 b2
  rw [n2] at b3 b4
  rw [e, iteratedFDeriv_add_apply cA cB]
  refine (norm_add_le _ _).trans ?_
  have : j + 1 + 1 = j + 2 := rfl
  rw [this] at b2 b4
  linarith

theorem norm_ageJet_mul_lapS_le {F : ℝ → Plane → ℝ}
    (hF : SmR (fun x : ℝ × Plane => F x.1 x.2)) {ν : ℝ} (hν : 0 ≤ ν)
    (ℓ j : ℕ) {s : ℝ} (hs : 0 < s) (z : Plane) :
    ‖ageJet ℓ j (fun r w => ν * Train.lapS (F r) w) s z‖ ≤
      (2 * ν) * ‖ageJet ℓ (j + 2) F s z‖ := by
  have hslice : (fun w => iteratedDeriv ℓ (fun r => ν * Train.lapS (F r) w) s) =
      fun w => ν • Train.lapS (fun x => iteratedDeriv ℓ (fun r => F r x) s) w :=
    funext fun w => iteratedDeriv_mul_lapS_eq hF ν ℓ hs w
  have hu : ContDiff ℝ ∞ (fun x : Plane => iteratedDeriv ℓ (fun r => F r x) s) :=
    contDiff_slice_iteratedDeriv_of_contDiffOn F hF ℓ hs
  have hlap_sm : ContDiff ℝ ∞ (Train.lapS (fun x => iteratedDeriv ℓ (fun r => F r x) s)) := by
    have e : Train.lapS (fun x => iteratedDeriv ℓ (fun r => F r x) s) =
        Dv ((1 : ℝ), (0 : ℝ)) (Dv ((1 : ℝ), (0 : ℝ)) (fun x => iteratedDeriv ℓ (fun r => F r x) s)) +
          Dv ((0 : ℝ), (1 : ℝ)) (Dv ((0 : ℝ), (1 : ℝ)) (fun x => iteratedDeriv ℓ (fun r => F r x) s)) :=
      funext (scalar_lap_eq hu)
    rw [e]
    exact (contDiff_Dv (contDiff_Dv hu _) _).add (contDiff_Dv (contDiff_Dv hu _) _)
  have hlap : ContDiffAt ℝ j (Train.lapS (fun x => iteratedDeriv ℓ (fun r => F r x) s)) z :=
    (hlap_sm.of_le (by exact_mod_cast le_top)).contDiffAt
  have heq : ageJet ℓ j (fun r w => ν * Train.lapS (F r) w) s z =
      ν • iteratedFDeriv ℝ j (Train.lapS (fun x => iteratedDeriv ℓ (fun r => F r x) s)) z := by
    unfold ageJet jet
    rw [hslice]
    exact iteratedFDeriv_const_smul_apply' hlap
  rw [heq, norm_smul, Real.norm_of_nonneg hν]
  have h1 := norm_jet_lapS_le hu j z
  unfold ageJet jet
  nlinarith

theorem norm_ageJet_partialQ_le {F : ℝ → Plane → ℝ}
    (hF : SmR (fun x : ℝ × Plane => F x.1 x.2))
    (ℓ j : ℕ) {s : ℝ} (hs : 0 < s) (z : Plane) :
    ‖ageJet ℓ j (fun r w => Cyl.partialQ (F r) w) s z‖ ≤
      ‖ageJet ℓ (j + 1) F s z‖ := by
  have hslice : (fun w => iteratedDeriv ℓ (fun r => Cyl.partialQ (F r) w) s) =
      Cyl.partialQ (fun x => iteratedDeriv ℓ (fun r => F r x) s) :=
    funext fun w => iteratedDeriv_partialQ_eq hF ℓ hs w
  have hu : ContDiff ℝ ∞ (fun x : Plane => iteratedDeriv ℓ (fun r => F r x) s) :=
    contDiff_slice_iteratedDeriv_of_contDiffOn F hF ℓ hs
  have hQ : Cyl.partialQ (fun x => iteratedDeriv ℓ (fun r => F r x) s) =
      Dv ((1 : ℝ), (0 : ℝ)) (fun x => iteratedDeriv ℓ (fun r => F r x) s) :=
    funext (Cyl.partialQ_eq_fderiv (hu.differentiable (by simp)))
  have n1 : ‖((1 : ℝ), (0 : ℝ))‖ = 1 := by simp [Prod.norm_def]
  have hb := norm_jet_Dv_scalar_le hu ((1 : ℝ), (0 : ℝ)) j z
  rw [n1, one_mul] at hb
  unfold ageJet jet
  rw [hslice, hQ]
  exact hb

theorem norm_ageJet_partialEta_le {F : ℝ → Plane → ℝ}
    (hF : SmR (fun x : ℝ × Plane => F x.1 x.2))
    (ℓ j : ℕ) {s : ℝ} (hs : 0 < s) (z : Plane) :
    ‖ageJet ℓ j (fun r w => Cyl.partialEta (F r) w) s z‖ ≤
      ‖ageJet ℓ (j + 1) F s z‖ := by
  have hslice : (fun w => iteratedDeriv ℓ (fun r => Cyl.partialEta (F r) w) s) =
      Cyl.partialEta (fun x => iteratedDeriv ℓ (fun r => F r x) s) :=
    funext fun w => iteratedDeriv_partialEta_eq hF ℓ hs w
  have hu : ContDiff ℝ ∞ (fun x : Plane => iteratedDeriv ℓ (fun r => F r x) s) :=
    contDiff_slice_iteratedDeriv_of_contDiffOn F hF ℓ hs
  have hE : Cyl.partialEta (fun x => iteratedDeriv ℓ (fun r => F r x) s) =
      Dv ((0 : ℝ), (1 : ℝ)) (fun x => iteratedDeriv ℓ (fun r => F r x) s) :=
    funext (Cyl.partialEta_eq_fderiv (hu.differentiable (by simp)))
  have n2 : ‖((0 : ℝ), (1 : ℝ))‖ = 1 := by simp [Prod.norm_def]
  have hb := norm_jet_Dv_scalar_le hu ((0 : ℝ), (1 : ℝ)) j z
  rw [n2, one_mul] at hb
  unfold ageJet jet
  rw [hslice, hE]
  exact hb

theorem iteratedDeriv_vec_proj_eq {V : ℝ → Plane → Vec}
    (hV : Sm (fun x : ℝ × Plane => V x.1 x.2)) (k : Fin 2) :
    ∀ (ℓ : ℕ) {t : ℝ}, 0 < t → ∀ w : Plane,
      iteratedDeriv ℓ (fun r => V r w k) t = (iteratedDeriv ℓ (fun r => V r w) t) k
  | 0, _, _, _ => rfl
  | ℓ + 1, t, ht, w => by
    rw [iteratedDeriv_succ, iteratedDeriv_succ]
    have hev : iteratedDeriv ℓ (fun r => V r w k) =ᶠ[nhds t]
        fun r => (Dt ℓ (fun x => V x.1 x.2) (r, w)) k := by
      filter_upwards [Ioi_mem_nhds ht] with r hr
      rw [iteratedDeriv_vec_proj_eq hV k ℓ hr w, iteratedDeriv_slice_eq_Dt hV ℓ hr w]
    have hevV : iteratedDeriv ℓ (fun r => V r w) =ᶠ[nhds t]
        fun r => Dt ℓ (fun x => V x.1 x.2) (r, w) := by
      filter_upwards [Ioi_mem_nhds ht] with r hr using iteratedDeriv_slice_eq_Dt hV ℓ hr w
    rw [hev.deriv_eq, hevV.deriv_eq]
    have hd : HasDerivAt (fun r => (Dt ℓ (fun x => V x.1 x.2) (r, w)) k)
        ((Dx eT (Dt ℓ (fun x => V x.1 x.2)) (t, w)) k) t :=
      (EuclideanSpace.proj k : Vec →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt t
        (hasDerivAt_slice (Sm_Dt hV ℓ) ht w)
    rw [hd.deriv, (hasDerivAt_slice (Sm_Dt hV ℓ) ht w).deriv]

theorem norm_ageJet_vec_proj_le {V : ℝ → Plane → Vec}
    (hV : Sm (fun x : ℝ × Plane => V x.1 x.2)) (k : Fin 2)
    (ℓ j : ℕ) {s : ℝ} (hs : 0 < s) (z : Plane) :
    ‖ageJet ℓ j (fun r w => V r w k) s z‖ ≤ ‖ageJet ℓ j V s z‖ := by
  have hslice : (fun w => iteratedDeriv ℓ (fun r => V r w k) s) =
      ((EuclideanSpace.proj k : Vec →L[ℝ] ℝ) ∘ fun w => iteratedDeriv ℓ (fun r => V r w) s) :=
    funext fun w => iteratedDeriv_vec_proj_eq hV k ℓ hs w
  have hu : ContDiff ℝ ∞ (fun w : Plane => iteratedDeriv ℓ (fun r => V r w) s) :=
    contDiff_slice_iteratedDeriv_of_contDiffOn V hV ℓ hs
  unfold ageJet jet
  rw [hslice]
  refine ((EuclideanSpace.proj k : Vec →L[ℝ] ℝ).norm_iteratedFDeriv_comp_left
    hu.contDiffAt (by exact_mod_cast le_top)).trans ?_
  have hproj : ‖(EuclideanSpace.proj k : Vec →L[ℝ] ℝ)‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => ?_
    simpa [one_mul] using PiLp.norm_apply_le v k
  exact (mul_le_mul_of_nonneg_right hproj (norm_nonneg _)).trans (by linarith)

/-! ### 4. Spacetime Leibniz product rule for `ageJet ℓ j` -/

/-- Auxiliary shifted product `(DtR m₁ A) * (DtR m₂ B)` on `ℝ → Plane → ℝ`. -/
noncomputable def prodDt (m₁ m₂ : ℕ) (A B : ℝ → Plane → ℝ) : ℝ → Plane → ℝ :=
  fun r w =>
    DtR m₁ (fun x : ℝ × Plane => A x.1 x.2) (r, w) *
      DtR m₂ (fun x : ℝ × Plane => B x.1 x.2) (r, w)

theorem smR_prodDt {A B : ℝ → Plane → ℝ}
    (hA : SmR (fun x : ℝ × Plane => A x.1 x.2))
    (hB : SmR (fun x : ℝ × Plane => B x.1 x.2)) (m₁ m₂ : ℕ) :
    SmR (fun x : ℝ × Plane => prodDt m₁ m₂ A B x.1 x.2) :=
  (smR_DtR hA m₁).mul (smR_DtR hB m₂)

theorem deriv_prodDt_eq {A B : ℝ → Plane → ℝ}
    (hA : SmR (fun x : ℝ × Plane => A x.1 x.2))
    (hB : SmR (fun x : ℝ × Plane => B x.1 x.2))
    (m₁ m₂ : ℕ) {t : ℝ} (ht : 0 < t) (w : Plane) :
    deriv (fun r => prodDt m₁ m₂ A B r w) t =
      prodDt (m₁ + 1) m₂ A B t w + prodDt m₁ (m₂ + 1) A B t w := by
  have hdA := hasDerivAt_sliceR (smR_DtR hA m₁) ht w
  have hdB := hasDerivAt_sliceR (smR_DtR hB m₂) ht w
  have hmul := hdA.mul hdB
  have hderiv : deriv (fun r => prodDt m₁ m₂ A B r w) t =
      DxR eT (DtR m₁ fun x => A x.1 x.2) (t, w) * DtR m₂ (fun x => B x.1 x.2) (t, w) +
        DtR m₁ (fun x => A x.1 x.2) (t, w) * DxR eT (DtR m₂ fun x => B x.1 x.2) (t, w) :=
    hmul.deriv
  rw [hderiv]
  unfold prodDt DtR
  rw [Function.iterate_succ_apply', Function.iterate_succ_apply']

theorem ageJet_succ_prodDt_eq {A B : ℝ → Plane → ℝ}
    (hA : SmR (fun x : ℝ × Plane => A x.1 x.2))
    (hB : SmR (fun x : ℝ × Plane => B x.1 x.2))
    (m₁ m₂ ℓ j : ℕ) {s : ℝ} (hs : 0 < s) (z : Plane) :
    ageJet (ℓ + 1) j (prodDt m₁ m₂ A B) s z =
      ageJet ℓ j (prodDt (m₁ + 1) m₂ A B) s z + ageJet ℓ j (prodDt m₁ (m₂ + 1) A B) s z := by
  have hstep : ageJet (ℓ + 1) j (prodDt m₁ m₂ A B) s =
      ageJet ℓ j (fun r w => prodDt (m₁ + 1) m₂ A B r w + prodDt m₁ (m₂ + 1) A B r w) s := by
    unfold ageJet
    congr 1
    funext w
    rw [iteratedDeriv_succ']
    have hev : deriv (fun r => prodDt m₁ m₂ A B r w) =ᶠ[nhds s]
        fun r => prodDt (m₁ + 1) m₂ A B r w + prodDt m₁ (m₂ + 1) A B r w := by
      filter_upwards [Ioi_mem_nhds hs] with r hr using deriv_prodDt_eq hA hB m₁ m₂ hr w
    exact hev.iteratedDeriv_eq ℓ
  rw [hstep]
  exact ageJet_add (prodDt (m₁ + 1) m₂ A B) (prodDt m₁ (m₂ + 1) A B)
    (smR_prodDt hA hB (m₁ + 1) m₂) (smR_prodDt hA hB m₁ (m₂ + 1)) hs ℓ j z

theorem norm_ageJet_zero_prodDt_le {A B : ℝ → Plane → ℝ}
    (hA : SmR (fun x : ℝ × Plane => A x.1 x.2))
    (hB : SmR (fun x : ℝ × Plane => B x.1 x.2))
    (m₁ m₂ j : ℕ) {s M_A M_B : ℝ} (hs : 0 < s) (hMA : 0 ≤ M_A) (_hMB : 0 ≤ M_B) (z : Plane)
    (hA_bd : ∀ i ≤ j, ‖ageJet m₁ i A s z‖ ≤ M_A)
    (hB_bd : ∀ i ≤ j, ‖ageJet m₂ i B s z‖ ≤ M_B) :
    ‖ageJet 0 j (prodDt m₁ m₂ A B) s z‖ ≤ (2 : ℝ) ^ j * M_A * M_B := by
  let f : Plane → ℝ := fun w => iteratedDeriv m₁ (fun r => A r w) s
  let g : Plane → ℝ := fun w => iteratedDeriv m₂ (fun r => B r w) s
  have hprod_eq : prodDt m₁ m₂ A B s = fun w => f w * g w := by
    funext w
    unfold prodDt f g
    rw [iteratedDeriv_slice_eq_DtR hA m₁ hs w, iteratedDeriv_slice_eq_DtR hB m₂ hs w]
  have hf_sm : ContDiff ℝ ∞ f := contDiff_slice_iteratedDeriv_of_contDiffOn A hA m₁ hs
  have hg_sm : ContDiff ℝ ∞ g := contDiff_slice_iteratedDeriv_of_contDiffOn B hB m₂ hs
  have hmul := norm_iteratedFDerivWithin_mul_le (𝕜 := ℝ) (f := f) (g := g)
    hf_sm.contDiffOn hg_sm.contDiffOn uniqueDiffOn_univ (mem_univ z) (n := j) (by exact_mod_cast le_top)
  simp only [iteratedFDerivWithin_univ] at hmul
  have hsum : ∑ i ∈ Finset.range (j + 1),
      (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i f z‖ * ‖iteratedFDeriv ℝ (j - i) g z‖ ≤
      ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * (M_A * M_B) := by
    refine Finset.sum_le_sum fun i hi => ?_
    have hij : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hji : j - i ≤ j := Nat.sub_le j i
    have hAi : ‖iteratedFDeriv ℝ i f z‖ ≤ M_A := hA_bd i hij
    have hBi : ‖iteratedFDeriv ℝ (j - i) g z‖ ≤ M_B := hB_bd (j - i) hji
    have hch : (0 : ℝ) ≤ (j.choose i : ℝ) := by positivity
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul hAi hBi (norm_nonneg _) hMA) hch
  have hchoose : (∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ)) = (2 : ℝ) ^ j := by
    exact_mod_cast Nat.sum_range_choose j
  unfold ageJet jet
  simp only [iteratedDeriv_zero]
  rw [hprod_eq]
  calc ‖iteratedFDeriv ℝ j (fun w => f w * g w) z‖
      ≤ ∑ i ∈ Finset.range (j + 1),
          (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i f z‖ * ‖iteratedFDeriv ℝ (j - i) g z‖ := hmul
    _ ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * (M_A * M_B) := hsum
    _ = (∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ)) * (M_A * M_B) :=
        (Finset.sum_mul _ _ _).symm
    _ = (2 : ℝ) ^ j * M_A * M_B := by rw [hchoose]; ring

theorem norm_ageJet_prodDt_le {A B : ℝ → Plane → ℝ}
    (hA : SmR (fun x : ℝ × Plane => A x.1 x.2))
    (hB : SmR (fun x : ℝ × Plane => B x.1 x.2)) :
    ∀ (ℓ m₁ m₂ j : ℕ) {s M_A M_B : ℝ}, 0 < s → 0 ≤ M_A → 0 ≤ M_B → ∀ z : Plane,
      (∀ r ≤ m₁ + ℓ, ∀ i ≤ j, ‖ageJet r i A s z‖ ≤ M_A) →
      (∀ r ≤ m₂ + ℓ, ∀ i ≤ j, ‖ageJet r i B s z‖ ≤ M_B) →
      ‖ageJet ℓ j (prodDt m₁ m₂ A B) s z‖ ≤ (2 : ℝ) ^ (ℓ + j) * M_A * M_B
  | 0, m₁, m₂, j, s, M_A, M_B, hs, hMA, hMB, z, hA_bd, hB_bd => by
    rw [zero_add]
    exact norm_ageJet_zero_prodDt_le hA hB m₁ m₂ j hs hMA hMB z
      (fun i hi => hA_bd m₁ (by omega) i hi)
      (fun i hi => hB_bd m₂ (by omega) i hi)
  | ℓ + 1, m₁, m₂, j, s, M_A, M_B, hs, hMA, hMB, z, hA_bd, hB_bd => by
    rw [ageJet_succ_prodDt_eq hA hB m₁ m₂ ℓ j hs z]
    have h1 := norm_ageJet_prodDt_le hA hB ℓ (m₁ + 1) m₂ j hs hMA hMB z
      (fun r hr i hi => hA_bd r (by omega) i hi)
      (fun r hr i hi => hB_bd r (by omega) i hi)
    have h2 := norm_ageJet_prodDt_le hA hB ℓ m₁ (m₂ + 1) j hs hMA hMB z
      (fun r hr i hi => hA_bd r (by omega) i hi)
      (fun r hr i hi => hB_bd r (by omega) i hi)
    calc ‖ageJet ℓ j (prodDt (m₁ + 1) m₂ A B) s z + ageJet ℓ j (prodDt m₁ (m₂ + 1) A B) s z‖
        ≤ ‖ageJet ℓ j (prodDt (m₁ + 1) m₂ A B) s z‖ + ‖ageJet ℓ j (prodDt m₁ (m₂ + 1) A B) s z‖ :=
          norm_add_le _ _
      _ ≤ (2 : ℝ) ^ (ℓ + j) * M_A * M_B + (2 : ℝ) ^ (ℓ + j) * M_A * M_B := add_le_add h1 h2
      _ = (2 : ℝ) ^ (ℓ + 1 + j) * M_A * M_B := by
          rw [add_right_comm ℓ 1 j, pow_succ']
          ring

/-- **Spacetime Leibniz product bound for `ageJet ℓ j`:**
if `A, B : ℝ → Plane → ℝ` are jointly smooth on `(0, ∞) × Plane` and have mixed jets up to order
`(ℓ, j)` at `(s, z)` bounded by `M_A` and `M_B`, then `ageJet ℓ j (A * B) s z` is bounded by
`2 ^ (ℓ + j) * M_A * M_B`. -/
theorem norm_ageJet_mul_le {A B : ℝ → Plane → ℝ}
    (hA : SmR (fun x : ℝ × Plane => A x.1 x.2))
    (hB : SmR (fun x : ℝ × Plane => B x.1 x.2))
    (ℓ j : ℕ) {s M_A M_B : ℝ} (hs : 0 < s) (hMA : 0 ≤ M_A) (hMB : 0 ≤ M_B) (z : Plane)
    (hA_bd : ∀ r ≤ ℓ, ∀ i ≤ j, ‖ageJet r i A s z‖ ≤ M_A)
    (hB_bd : ∀ r ≤ ℓ, ∀ i ≤ j, ‖ageJet r i B s z‖ ≤ M_B) :
    ‖ageJet ℓ j (fun r w => A r w * B r w) s z‖ ≤ (2 : ℝ) ^ (ℓ + j) * M_A * M_B := by
  have h := norm_ageJet_prodDt_le hA hB ℓ 0 0 j hs hMA hMB z
    (fun r hr i hi => hA_bd r (by omega) i hi)
    (fun r hr i hi => hB_bd r (by omega) i hi)
  exact h

/-! ### 5. Iterated age derivative of the vorticity equation (`localVorticityEquation`) -/

/-- Pointwise age-derivative vorticity equation on `s > 0`:
`∂_s ω = ν Δω - v_0 ∂_q ω - v_1 ∂_η ω`. -/
theorem deriv_curl_eq_vorticity_rhs {ν c : ℝ} (tr : B0140.TrainSol ν c)
    {s : ℝ} (hs : 0 < s) (z : Plane) :
    deriv (fun r => Cyl.curl (tr.v r) z) s =
      ν * Train.lapS (Cyl.curl (tr.v s)) z
      - tr.v s z 0 * Cyl.partialQ (Cyl.curl (tr.v s)) z
      - tr.v s z 1 * Cyl.partialEta (Cyl.curl (tr.v s)) z := by
  have h := B0238.vorticityResidual_eq_zero tr.isTrain.smooth_v tr.isTrain.smooth_p
    (fun r hr => tr.isTrain.solenoidal r hr.le) tr.isTrain.momentum hs z
  unfold B0238.vorticityResidual at h
  linarith

/-- Iterated age derivative of `ω = Cyl.curl (tr.v r)` at order `ℓ + 1` on `s > 0`. -/
theorem iteratedDeriv_succ_curl_eq {ν c : ℝ} (tr : B0140.TrainSol ν c)
    (ℓ : ℕ) {s : ℝ} (hs : 0 < s) (z : Plane) :
    iteratedDeriv (ℓ + 1) (fun r => Cyl.curl (tr.v r) z) s =
      iteratedDeriv ℓ (fun r =>
        ν * Train.lapS (Cyl.curl (tr.v r)) z
        - tr.v r z 0 * Cyl.partialQ (Cyl.curl (tr.v r)) z
        - tr.v r z 1 * Cyl.partialEta (Cyl.curl (tr.v r)) z) s := by
  rw [iteratedDeriv_succ']
  have hev : deriv (fun r => Cyl.curl (tr.v r) z) =ᶠ[nhds s]
      fun r =>
        ν * Train.lapS (Cyl.curl (tr.v r)) z
        - tr.v r z 0 * Cyl.partialQ (Cyl.curl (tr.v r)) z
        - tr.v r z 1 * Cyl.partialEta (Cyl.curl (tr.v r)) z := by
    filter_upwards [Ioi_mem_nhds hs] with r hr using deriv_curl_eq_vorticity_rhs tr hr z
  exact hev.iteratedDeriv_eq ℓ

/-- `ageJet (ℓ + 1) j` of `ω = Cyl.curl (tr.v r)` decomposes into the viscous term and the two
advection terms at age order `ℓ`. -/
theorem ageJet_succ_curl_eq {ν c : ℝ} (tr : B0140.TrainSol ν c)
    (ℓ j : ℕ) {s : ℝ} (hs : 0 < s) (z : Plane) :
    ageJet (ℓ + 1) j (fun r w => Cyl.curl (tr.v r) w) s z =
      ageJet ℓ j (fun r w => ν * Train.lapS (Cyl.curl (tr.v r)) w) s z
      - ageJet ℓ j (fun r w => tr.v r w 0 * Cyl.partialQ (Cyl.curl (tr.v r)) w) s z
      - ageJet ℓ j (fun r w => tr.v r w 1 * Cyl.partialEta (Cyl.curl (tr.v r)) w) s z := by
  have hstep : ageJet (ℓ + 1) j (fun r w => Cyl.curl (tr.v r) w) s =
      ageJet ℓ j (fun r w =>
        ν * Train.lapS (Cyl.curl (tr.v r)) w
        - tr.v r w 0 * Cyl.partialQ (Cyl.curl (tr.v r)) w
        - tr.v r w 1 * Cyl.partialEta (Cyl.curl (tr.v r)) w) s := by
    unfold ageJet
    congr 1
    funext w
    exact iteratedDeriv_succ_curl_eq tr ℓ hs w
  let F₁ : ℝ → Plane → ℝ := fun r w => ν * Train.lapS (Cyl.curl (tr.v r)) w
  let F₂ : ℝ → Plane → ℝ := fun r w => tr.v r w 0 * Cyl.partialQ (Cyl.curl (tr.v r)) w
  let F₃ : ℝ → Plane → ℝ := fun r w => tr.v r w 1 * Cyl.partialEta (Cyl.curl (tr.v r)) w
  have hsm_v : Sm (fun x : ℝ × Plane => tr.v x.1 x.2) :=
    tr.isTrain.smooth_v.mono (Set.prod_mono Set.Ioi_subset_Ici_self Subset.rfl)
  have hsm_ω : SmR (fun x : ℝ × Plane => Cyl.curl (tr.v x.1) x.2) := smR_curl hsm_v
  have hsm_v0 : SmR (fun x : ℝ × Plane => tr.v x.1 x.2 0) :=
    (EuclideanSpace.proj (0 : Fin 2) : Vec →L[ℝ] ℝ).contDiff.comp_contDiffOn hsm_v
  have hsm_v1 : SmR (fun x : ℝ × Plane => tr.v x.1 x.2 1) :=
    (EuclideanSpace.proj (1 : Fin 2) : Vec →L[ℝ] ℝ).contDiff.comp_contDiffOn hsm_v
  have hsm₁ : SmR (fun x : ℝ × Plane => F₁ x.1 x.2) :=
    smR_mul_lapS (F := fun r w => Cyl.curl (tr.v r) w) hsm_ω ν
  have hsm₂ : SmR (fun x : ℝ × Plane => F₂ x.1 x.2) :=
    hsm_v0.mul (smR_partialQ (F := fun r w => Cyl.curl (tr.v r) w) hsm_ω)
  have hsm₃ : SmR (fun x : ℝ × Plane => F₃ x.1 x.2) :=
    hsm_v1.mul (smR_partialEta (F := fun r w => Cyl.curl (tr.v r) w) hsm_ω)
  have hsub2 := ageJet_sub (fun r w => F₁ r w - F₂ r w) F₃ (hsm₁.sub hsm₂) hsm₃ hs ℓ j z
  have hsub1 := ageJet_sub F₁ F₂ hsm₁ hsm₂ hs ℓ j z
  rw [hstep]
  exact hsub2.trans (by rw [hsub1])

theorem norm_ageJet_succ_curl_le {ν c : ℝ} (tr : B0140.TrainSol ν c)
    (ℓ j : ℕ) {s : ℝ} (hs : 0 < s) (z : Plane) :
    ‖ageJet (ℓ + 1) j (fun r w => Cyl.curl (tr.v r) w) s z‖ ≤
      ‖ageJet ℓ j (fun r w => ν * Train.lapS (Cyl.curl (tr.v r)) w) s z‖
      + ‖ageJet ℓ j (fun r w => tr.v r w 0 * Cyl.partialQ (Cyl.curl (tr.v r)) w) s z‖
      + ‖ageJet ℓ j (fun r w => tr.v r w 1 * Cyl.partialEta (Cyl.curl (tr.v r)) w) s z‖ := by
  rw [ageJet_succ_curl_eq tr ℓ j hs z]
  have h1 := norm_sub_le
    (ageJet ℓ j (fun r w => ν * Train.lapS (Cyl.curl (tr.v r)) w) s z -
      ageJet ℓ j (fun r w => tr.v r w 0 * Cyl.partialQ (Cyl.curl (tr.v r)) w) s z)
    (ageJet ℓ j (fun r w => tr.v r w 1 * Cyl.partialEta (Cyl.curl (tr.v r)) w) s z)
  have h2 := norm_sub_le
    (ageJet ℓ j (fun r w => ν * Train.lapS (Cyl.curl (tr.v r)) w) s z)
    (ageJet ℓ j (fun r w => tr.v r w 0 * Cyl.partialQ (Cyl.curl (tr.v r)) w) s z)
  linarith

/-! ### 6. Gaussian tail monotonicity and finite-order uniform parameter merging -/

/-- Monotonicity of the Gaussian transverse tail `exp(-b d² / (C₀ + ν s))` under
`b₂ ≤ b₁`, `C₀₁ ≤ C₀₂`, and `C'₁ ≤ C'₂`. -/
theorem exp_gaussian_tail_mono {b₁ b₂ C₀₁ C₀₂ C'₁ C'₂ ν s : ℝ} (z : Plane)
    (hb₂ : 0 < b₂) (hb : b₂ ≤ b₁)
    (hC₀₁ : 0 < C₀₁) (hC₀ : C₀₁ ≤ C₀₂)
    (hC' : C'₁ ≤ C'₂) (hν : 0 < ν) (hs : 0 ≤ s) :
    Real.exp (-(b₁ * (max (|z.2| - C'₁ / ν) 0) ^ 2 / (C₀₁ + ν * s))) ≤
      Real.exp (-(b₂ * (max (|z.2| - C'₂ / ν) 0) ^ 2 / (C₀₂ + ν * s))) := by
  apply Real.exp_le_exp.2
  apply neg_le_neg
  set d₁ := max (|z.2| - C'₁ / ν) 0
  set d₂ := max (|z.2| - C'₂ / ν) 0
  have hd₂_nn : 0 ≤ d₂ := le_max_right _ _
  have hd_le : d₂ ≤ d₁ := by
    dsimp only [d₁, d₂]
    refine max_le_max ?_ le_rfl
    have hdiv : C'₁ / ν ≤ C'₂ / ν := div_le_div_of_nonneg_right hC' hν.le
    linarith
  have hd_sq : d₂ ^ 2 ≤ d₁ ^ 2 := pow_le_pow_left₀ hd₂_nn hd_le 2
  have hnum : b₂ * d₂ ^ 2 ≤ b₁ * d₁ ^ 2 :=
    mul_le_mul hb hd_sq (sq_nonneg d₂) (hb₂.le.trans hb)
  have hden₁ : 0 < C₀₁ + ν * s := by positivity
  have hden : C₀₁ + ν * s ≤ C₀₂ + ν * s := by linarith
  exact div_le_div₀ (mul_nonneg (hb₂.le.trans hb) (sq_nonneg d₁)) hnum hden₁ hden

theorem polyP_mono {C₁ C₂ : ℝ} {N₁ N₂ : ℕ} {ν c : ℝ}
    (hC₁ : 0 ≤ C₁) (hC : C₁ ≤ C₂) (hN : N₁ ≤ N₂) (hν : 0 < ν) (hc : 0 ≤ c) :
    polyP C₁ N₁ ν c ≤ polyP C₂ N₂ ν c := by
  unfold polyP
  have hX1 : 1 ≤ 1 + c + ν⁻¹ := by
    have : 0 ≤ ν⁻¹ := inv_nonneg.2 hν.le
    linarith
  exact mul_le_mul hC (pow_le_pow_right₀ hX1 hN) (by positivity) (hC₁.trans hC)

end PartI_T20

/-! ### 7. Inductive hierarchy on age derivative order `ℓ` -/

/-- Vorticity Gaussian transverse tail at a fixed age-derivative order `ℓ : ℕ` and all spatial
orders `j : ℕ`. -/
def TrainVorticityGaussianTailAt (ℓ : ℕ) : Prop :=
  ∀ ρ : ℝ, 1 / 2 < ρ → ∀ j : ℕ, ∃ b C₀ C' : ℝ, 0 < b ∧ 0 < C₀ ∧ 0 < C' ∧
    ∃ C : ℝ, ∃ N : ℕ, ∃ ν₀ : ℝ, 0 < C ∧ 0 < ν₀ ∧
      ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
        ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr →
          ∀ s : ℝ, 0 < s → ∀ z : Plane,
            let c := trainPeriod ρ ν
            let d := max (|z.2| - C' / ν) 0
            ‖ageJet ℓ j (fun r w => Cyl.curl (tr.v r) w) s z‖ ≤
              polyP C N ν c * Real.exp (-(b * d ^ 2 / (C₀ + ν * s)))

/-- Global polynomial-in-`(c, ν⁻¹)` sup bound on the velocity age-jet `ageJet ℓ k tr.v s z` at a
fixed age-derivative order `ℓ : ℕ` and all spatial orders `k : ℕ`. -/
def TrainVelocityAgeJetSupBoundAt (ℓ : ℕ) : Prop :=
  ∀ ρ : ℝ, 1 / 2 < ρ → ∀ k : ℕ,
    ∃ C_v : ℝ, ∃ N_v : ℕ, ∃ ν₀ : ℝ, 0 < C_v ∧ 0 < ν₀ ∧
      ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
        ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr →
          ∀ s : ℝ, 0 < s → ∀ z : Plane,
            ‖ageJet ℓ k tr.v s z‖ ≤ polyP C_v N_v ν (trainPeriod ρ ν)

/-- Global polynomial-in-`(c, ν⁻¹)` sup bound on higher age derivatives `ageJet (m + 1) k tr.v s z`
of the train velocity (`m ≥ 0`). -/
def TrainVelocityHigherAgeJetSupBound : Prop :=
  ∀ m : ℕ, TrainVelocityAgeJetSupBoundAt (m + 1)

/-- **Base case `ℓ = 0` for vorticity:** `TrainVorticityGaussianTailAt 0` is `TrainVorticitySpatialJetTail`. -/
theorem trainVorticityGaussianTailAt_zero (hSpatial : TrainVorticitySpatialJetTail) :
    TrainVorticityGaussianTailAt 0 :=
  hSpatial

/-- **Base case `ℓ = 0` for velocity:** proved unconditionally from `PartI_T20.train_v_jet_sup_bound`. -/
theorem trainVelocityAgeJetSupBoundAt_zero (_hOv : TrainOverlap) :
    TrainVelocityAgeJetSupBoundAt 0 := by
  intro ρ hρ k
  obtain ⟨C_v, ν_v, hC_v, hν_v, hbd⟩ := PartI_T20.train_v_jet_sup_bound ρ hρ k
  refine ⟨C_v, 1, ν_v, hC_v, hν_v, ?_⟩
  intro ν hν hν_le tr htr s hs z
  simpa [ageJet, iteratedDeriv_zero] using hbd ν hν hν_le tr htr s hs z

namespace PartI_T20

/-- Uniform velocity age-jet sup bound across all `i ≤ K` at a fixed age order `r`. -/
theorem uniform_velocity_sup_spatial {ρ : ℝ} (hρ : 1 / 2 < ρ) {r : ℕ}
    (hr : TrainVelocityAgeJetSupBoundAt r) :
    ∀ K : ℕ, ∃ C_v : ℝ, ∃ N_v : ℕ, ∃ ν₀ : ℝ, 0 < C_v ∧ 0 < ν₀ ∧
      ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
        ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr →
          ∀ s : ℝ, 0 < s → ∀ z : Plane, ∀ i ≤ K,
            ‖ageJet r i tr.v s z‖ ≤ polyP C_v N_v ν (trainPeriod ρ ν)
  | 0 => by
    obtain ⟨C_v, N_v, ν₀, hC_v, hν₀, h0⟩ := hr ρ hρ 0
    refine ⟨C_v, N_v, ν₀, hC_v, hν₀, fun ν hν hν_le tr htr s hs z i hi => ?_⟩
    have hi0 : i = 0 := Nat.le_zero.mp hi
    subst hi0
    exact h0 ν hν hν_le tr htr s hs z
  | K + 1 => by
    obtain ⟨C₁, N₁, ν₁, hC₁, hν₁, hIH⟩ := uniform_velocity_sup_spatial hρ hr K
    obtain ⟨C₂, N₂, ν₂, hC₂, hν₂, hK1⟩ := hr ρ hρ (K + 1)
    refine ⟨max C₁ C₂, max N₁ N₂, min ν₁ ν₂, lt_max_of_lt_left hC₁, lt_min hν₁ hν₂, ?_⟩
    intro ν hν hν_le tr htr s hs z i hi
    have hc0 : 0 ≤ trainPeriod ρ ν := Real.rpow_nonneg hν.le _
    rcases Nat.of_le_succ hi with hiK | rfl
    · exact (hIH ν hν (hν_le.trans (min_le_left _ _)) tr htr s hs z i hiK).trans
        (polyP_mono hC₁.le (le_max_left _ _) (le_max_left _ _) hν hc0)
    · exact (hK1 ν hν (hν_le.trans (min_le_right _ _)) tr htr s hs z).trans
        (polyP_mono hC₂.le (le_max_right _ _) (le_max_right _ _) hν hc0)

/-- Uniform velocity age-jet sup bound across all `r ≤ L` and `i ≤ K`. -/
theorem uniform_velocity_sup_rect {ρ : ℝ} (hρ : 1 / 2 < ρ) (K : ℕ) :
    ∀ (L : ℕ), (∀ r ≤ L, TrainVelocityAgeJetSupBoundAt r) →
      ∃ C_v : ℝ, ∃ N_v : ℕ, ∃ ν₀ : ℝ, 0 < C_v ∧ 0 < ν₀ ∧
        ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
          ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr →
            ∀ s : ℝ, 0 < s → ∀ z : Plane, ∀ r ≤ L, ∀ i ≤ K,
              ‖ageJet r i tr.v s z‖ ≤ polyP C_v N_v ν (trainPeriod ρ ν)
  | 0, hVel => by
    obtain ⟨C_v, N_v, ν₀, hC_v, hν₀, h0⟩ := uniform_velocity_sup_spatial hρ (hVel 0 le_rfl) K
    refine ⟨C_v, N_v, ν₀, hC_v, hν₀, fun ν hν hν_le tr htr s hs z r hr i hi => ?_⟩
    have hr0 : r = 0 := Nat.le_zero.mp hr
    subst hr0
    exact h0 ν hν hν_le tr htr s hs z i hi
  | L + 1, hVel => by
    obtain ⟨C₁, N₁, ν₁, hC₁, hν₁, hIH⟩ :=
      uniform_velocity_sup_rect hρ K L (fun r hr => hVel r (Nat.le_succ_of_le hr))
    obtain ⟨C₂, N₂, ν₂, hC₂, hν₂, hL1⟩ :=
      uniform_velocity_sup_spatial hρ (hVel (L + 1) le_rfl) K
    refine ⟨max C₁ C₂, max N₁ N₂, min ν₁ ν₂, lt_max_of_lt_left hC₁, lt_min hν₁ hν₂, ?_⟩
    intro ν hν hν_le tr htr s hs z r hr i hi
    have hc0 : 0 ≤ trainPeriod ρ ν := Real.rpow_nonneg hν.le _
    rcases Nat.of_le_succ hr with hrL | rfl
    · exact (hIH ν hν (hν_le.trans (min_le_left _ _)) tr htr s hs z r hrL i hi).trans
        (polyP_mono hC₁.le (le_max_left _ _) (le_max_left _ _) hν hc0)
    · exact (hL1 ν hν (hν_le.trans (min_le_right _ _)) tr htr s hs z i hi).trans
        (polyP_mono hC₂.le (le_max_right _ _) (le_max_right _ _) hν hc0)

/-- Uniform vorticity Gaussian tail bound across all `i ≤ K` at a fixed age order `r`. -/
theorem uniform_vorticity_tail_spatial {ρ : ℝ} (hρ : 1 / 2 < ρ) {r : ℕ}
    (hr : TrainVorticityGaussianTailAt r) :
    ∀ K : ℕ, ∃ b C₀ C' : ℝ, 0 < b ∧ 0 < C₀ ∧ 0 < C' ∧
      ∃ C : ℝ, ∃ N : ℕ, ∃ ν₀ : ℝ, 0 < C ∧ 0 < ν₀ ∧
        ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
          ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr →
            ∀ s : ℝ, 0 < s → ∀ z : Plane, ∀ i ≤ K,
              let c := trainPeriod ρ ν
              let d := max (|z.2| - C' / ν) 0
              ‖ageJet r i (fun t w => Cyl.curl (tr.v t) w) s z‖ ≤
                polyP C N ν c * Real.exp (-(b * d ^ 2 / (C₀ + ν * s)))
  | 0 => by
    obtain ⟨b, C₀, C', hb, hC₀, hC', C, N, ν₀, hC, hν₀, h0⟩ := hr ρ hρ 0
    refine ⟨b, C₀, C', hb, hC₀, hC', C, N, ν₀, hC, hν₀,
      fun ν hν hν_le tr htr s hs z i hi => ?_⟩
    have hi0 : i = 0 := Nat.le_zero.mp hi
    subst hi0
    exact h0 ν hν hν_le tr htr s hs z
  | K + 1 => by
    obtain ⟨b₁, C₀₁, C'₁, hb₁, hC₀₁, hC'₁, C₁, N₁, ν₁, hC₁, hν₁, hIH⟩ :=
      uniform_vorticity_tail_spatial hρ hr K
    obtain ⟨b₂, C₀₂, C'₂, hb₂, hC₀₂, hC'₂, C₂, N₂, ν₂, hC₂, hν₂, hK1⟩ := hr ρ hρ (K + 1)
    refine ⟨min b₁ b₂, max C₀₁ C₀₂, max C'₁ C'₂, lt_min hb₁ hb₂,
      lt_max_of_lt_left hC₀₁, lt_max_of_lt_left hC'₁,
      max C₁ C₂, max N₁ N₂, min ν₁ ν₂, lt_max_of_lt_left hC₁, lt_min hν₁ hν₂, ?_⟩
    intro ν hν hν_le tr htr s hs z i hi
    have hc0 : 0 ≤ trainPeriod ρ ν := Real.rpow_nonneg hν.le _
    rcases Nat.of_le_succ hi with hiK | rfl
    · have h1 := hIH ν hν (hν_le.trans (min_le_left _ _)) tr htr s hs z i hiK
      refine h1.trans (mul_le_mul
        (polyP_mono hC₁.le (le_max_left _ _) (le_max_left _ _) hν hc0)
        (exp_gaussian_tail_mono z (lt_min hb₁ hb₂) (min_le_left _ _) hC₀₁ (le_max_left _ _)
          (le_max_left _ _) hν hs.le)
        (Real.exp_nonneg _) (by unfold polyP; positivity))
    · have h2 := hK1 ν hν (hν_le.trans (min_le_right _ _)) tr htr s hs z
      refine h2.trans (mul_le_mul
        (polyP_mono hC₂.le (le_max_right _ _) (le_max_right _ _) hν hc0)
        (exp_gaussian_tail_mono z (lt_min hb₁ hb₂) (min_le_right _ _) hC₀₂ (le_max_right _ _)
          (le_max_right _ _) hν hs.le)
        (Real.exp_nonneg _) (by unfold polyP; positivity))

/-- Uniform vorticity Gaussian tail bound across all `r ≤ L` and `i ≤ K`. -/
theorem uniform_vorticity_tail_rect {ρ : ℝ} (hρ : 1 / 2 < ρ) (K : ℕ) :
    ∀ (L : ℕ), (∀ r ≤ L, TrainVorticityGaussianTailAt r) →
      ∃ b C₀ C' : ℝ, 0 < b ∧ 0 < C₀ ∧ 0 < C' ∧
        ∃ C : ℝ, ∃ N : ℕ, ∃ ν₀ : ℝ, 0 < C ∧ 0 < ν₀ ∧
          ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
            ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr →
              ∀ s : ℝ, 0 < s → ∀ z : Plane, ∀ r ≤ L, ∀ i ≤ K,
                let c := trainPeriod ρ ν
                let d := max (|z.2| - C' / ν) 0
                ‖ageJet r i (fun t w => Cyl.curl (tr.v t) w) s z‖ ≤
                  polyP C N ν c * Real.exp (-(b * d ^ 2 / (C₀ + ν * s)))
  | 0, hVort => by
    obtain ⟨b, C₀, C', hb, hC₀, hC', C, N, ν₀, hC, hν₀, h0⟩ :=
      uniform_vorticity_tail_spatial hρ (hVort 0 le_rfl) K
    refine ⟨b, C₀, C', hb, hC₀, hC', C, N, ν₀, hC, hν₀,
      fun ν hν hν_le tr htr s hs z r hr i hi => ?_⟩
    have hr0 : r = 0 := Nat.le_zero.mp hr
    subst hr0
    exact h0 ν hν hν_le tr htr s hs z i hi
  | L + 1, hVort => by
    obtain ⟨b₁, C₀₁, C'₁, hb₁, hC₀₁, hC'₁, C₁, N₁, ν₁, hC₁, hν₁, hIH⟩ :=
      uniform_vorticity_tail_rect hρ K L (fun r hr => hVort r (Nat.le_succ_of_le hr))
    obtain ⟨b₂, C₀₂, C'₂, hb₂, hC₀₂, hC'₂, C₂, N₂, ν₂, hC₂, hν₂, hL1⟩ :=
      uniform_vorticity_tail_spatial hρ (hVort (L + 1) le_rfl) K
    refine ⟨min b₁ b₂, max C₀₁ C₀₂, max C'₁ C'₂, lt_min hb₁ hb₂,
      lt_max_of_lt_left hC₀₁, lt_max_of_lt_left hC'₁,
      max C₁ C₂, max N₁ N₂, min ν₁ ν₂, lt_max_of_lt_left hC₁, lt_min hν₁ hν₂, ?_⟩
    intro ν hν hν_le tr htr s hs z r hr i hi
    have hc0 : 0 ≤ trainPeriod ρ ν := Real.rpow_nonneg hν.le _
    rcases Nat.of_le_succ hr with hrL | rfl
    · have h1 := hIH ν hν (hν_le.trans (min_le_left _ _)) tr htr s hs z r hrL i hi
      refine h1.trans (mul_le_mul
        (polyP_mono hC₁.le (le_max_left _ _) (le_max_left _ _) hν hc0)
        (exp_gaussian_tail_mono z (lt_min hb₁ hb₂) (min_le_left _ _) hC₀₁ (le_max_left _ _)
          (le_max_left _ _) hν hs.le)
        (Real.exp_nonneg _) (by unfold polyP; positivity))
    · have h2 := hL1 ν hν (hν_le.trans (min_le_right _ _)) tr htr s hs z i hi
      refine h2.trans (mul_le_mul
        (polyP_mono hC₂.le (le_max_right _ _) (le_max_right _ _) hν hc0)
        (exp_gaussian_tail_mono z (lt_min hb₁ hb₂) (min_le_right _ _) hC₀₂ (le_max_right _ _)
          (le_max_right _ _) hν hs.le)
        (Real.exp_nonneg _) (by unfold polyP; positivity))

end PartI_T20

/-- **Inductive step (`ℓ → ℓ + 1`) for `TrainVorticityGaussianTailAt`:**
given the vorticity Gaussian tail bounds up to age order `ℓ` and the velocity age-jet sup bounds
up to age order `ℓ`, differentiating `∂_s ω = ν Δω - v_0 ∂_q ω - v_1 ∂_η ω` proves
`TrainVorticityGaussianTailAt (ℓ + 1)`. -/
theorem trainVorticityGaussianTailAt_succ (ℓ : ℕ)
    (hVort : ∀ r ≤ ℓ, TrainVorticityGaussianTailAt r)
    (hVel : ∀ r ≤ ℓ, TrainVelocityAgeJetSupBoundAt r) :
    TrainVorticityGaussianTailAt (ℓ + 1) := by
  intro ρ hρ j
  obtain ⟨b, C₀, C', hb, hC₀, hC', C_W, N_W, ν_W, hC_W, hν_W, hW_bd⟩ :=
    PartI_T20.uniform_vorticity_tail_rect hρ (j + 2) ℓ hVort
  obtain ⟨C_V, N_V, ν_V, hC_V, hν_V, hV_bd⟩ :=
    PartI_T20.uniform_velocity_sup_rect hρ j ℓ hVel
  let C_out : ℝ := 2 * C_W + 2 * (2 : ℝ) ^ (ℓ + j) * C_V * C_W
  let N_out : ℕ := N_V + N_W
  let ν_out : ℝ := min (min ν_W ν_V) 1
  refine ⟨b, C₀, C', hb, hC₀, hC', C_out, N_out, ν_out,
    by dsimp [C_out]; positivity,
    lt_min (lt_min hν_W hν_V) one_pos, ?_⟩
  intro ν hν hν_le tr htr s hs z
  have hν_W_le : ν ≤ ν_W := hν_le.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hν_V_le : ν ≤ ν_V := hν_le.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hν1 : ν ≤ 1 := hν_le.trans (min_le_right _ _)
  let c := trainPeriod ρ ν
  have hc0 : 0 ≤ c := Real.rpow_nonneg hν.le _
  let d := max (|z.2| - C' / ν) 0
  let G := Real.exp (-(b * d ^ 2 / (C₀ + ν * s)))
  let M_V := polyP C_V N_V ν c
  let M_W := polyP C_W N_W ν c * G
  have hMV_nn : 0 ≤ M_V := by dsimp [M_V, polyP]; positivity
  have hMW_nn : 0 ≤ M_W := by dsimp [M_W, G, polyP]; positivity
  have hsm_v : Sm (fun x : ℝ × Plane => tr.v x.1 x.2) :=
    tr.isTrain.smooth_v.mono (Set.prod_mono Set.Ioi_subset_Ici_self Subset.rfl)
  have hsm_ω : PartI_T20.SmR (fun x : ℝ × Plane => Cyl.curl (tr.v x.1) x.2) :=
    PartI_T20.smR_curl hsm_v
  have hsm_v0 : PartI_T20.SmR (fun x : ℝ × Plane => tr.v x.1 x.2 0) :=
    (EuclideanSpace.proj (0 : Fin 2) : Vec →L[ℝ] ℝ).contDiff.comp_contDiffOn hsm_v
  have hsm_v1 : PartI_T20.SmR (fun x : ℝ × Plane => tr.v x.1 x.2 1) :=
    (EuclideanSpace.proj (1 : Fin 2) : Vec →L[ℝ] ℝ).contDiff.comp_contDiffOn hsm_v
  have hsm_Qω : PartI_T20.SmR (fun x : ℝ × Plane => Cyl.partialQ (Cyl.curl (tr.v x.1)) x.2) :=
    PartI_T20.smR_partialQ (F := fun r w => Cyl.curl (tr.v r) w) hsm_ω
  have hsm_Eω : PartI_T20.SmR (fun x : ℝ × Plane => Cyl.partialEta (Cyl.curl (tr.v x.1)) x.2) :=
    PartI_T20.smR_partialEta (F := fun r w => Cyl.curl (tr.v r) w) hsm_ω
  -- 1. Viscous term bound
  have hvisc :
      ‖ageJet ℓ j (fun r w => ν * Train.lapS (Cyl.curl (tr.v r)) w) s z‖ ≤
        2 * M_W := by
    calc ‖ageJet ℓ j (fun r w => ν * Train.lapS (Cyl.curl (tr.v r)) w) s z‖
        ≤ (2 * ν) * ‖ageJet ℓ (j + 2) (fun r w => Cyl.curl (tr.v r) w) s z‖ :=
          PartI_T20.norm_ageJet_mul_lapS_le (F := fun r w => Cyl.curl (tr.v r) w) hsm_ω hν.le ℓ j hs z
      _ ≤ 2 * ‖ageJet ℓ (j + 2) (fun r w => Cyl.curl (tr.v r) w) s z‖ :=
          mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
      _ ≤ 2 * M_W :=
          mul_le_mul_of_nonneg_left (hW_bd ν hν hν_W_le tr htr s hs z ℓ le_rfl (j + 2) le_rfl)
            (by norm_num)
  -- 2. Advection term 0 (`v_0 * ∂_q ω`) bound
  have hadv0 :
      ‖ageJet ℓ j (fun r w => tr.v r w 0 * Cyl.partialQ (Cyl.curl (tr.v r)) w) s z‖ ≤
        (2 : ℝ) ^ (ℓ + j) * M_V * M_W := by
    refine PartI_T20.norm_ageJet_mul_le
      (A := fun r w => tr.v r w 0) (B := fun r w => Cyl.partialQ (Cyl.curl (tr.v r)) w)
      hsm_v0 hsm_Qω ℓ j hs hMV_nn hMW_nn z
      (fun r hr i hi => ?_) (fun r hr i hi => ?_)
    · exact (PartI_T20.norm_ageJet_vec_proj_le hsm_v 0 r i hs z).trans
        (hV_bd ν hν hν_V_le tr htr s hs z r hr i hi)
    · exact (PartI_T20.norm_ageJet_partialQ_le (F := fun r w => Cyl.curl (tr.v r) w) hsm_ω r i hs z).trans
        (hW_bd ν hν hν_W_le tr htr s hs z r hr (i + 1) (by omega))
  -- 3. Advection term 1 (`v_1 * ∂_η ω`) bound
  have hadv1 :
      ‖ageJet ℓ j (fun r w => tr.v r w 1 * Cyl.partialEta (Cyl.curl (tr.v r)) w) s z‖ ≤
        (2 : ℝ) ^ (ℓ + j) * M_V * M_W := by
    refine PartI_T20.norm_ageJet_mul_le
      (A := fun r w => tr.v r w 1) (B := fun r w => Cyl.partialEta (Cyl.curl (tr.v r)) w)
      hsm_v1 hsm_Eω ℓ j hs hMV_nn hMW_nn z
      (fun r hr i hi => ?_) (fun r hr i hi => ?_)
    · exact (PartI_T20.norm_ageJet_vec_proj_le hsm_v 1 r i hs z).trans
        (hV_bd ν hν hν_V_le tr htr s hs z r hr i hi)
    · exact (PartI_T20.norm_ageJet_partialEta_le (F := fun r w => Cyl.curl (tr.v r) w) hsm_ω r i hs z).trans
        (hW_bd ν hν hν_W_le tr htr s hs z r hr (i + 1) (by omega))
  -- 4. Combine the three terms
  have htri := PartI_T20.norm_ageJet_succ_curl_le tr ℓ j hs z
  have hX1 : 1 ≤ 1 + c + ν⁻¹ := by
    have : 0 ≤ ν⁻¹ := inv_nonneg.2 hν.le
    linarith
  have hpow_W : (1 + c + ν⁻¹) ^ N_W ≤ (1 + c + ν⁻¹) ^ N_out :=
    pow_le_pow_right₀ hX1 (Nat.le_add_left N_W N_V)
  have hcomb : 2 * M_W + (2 : ℝ) ^ (ℓ + j) * M_V * M_W + (2 : ℝ) ^ (ℓ + j) * M_V * M_W ≤
      polyP C_out N_out ν c * G := by
    dsimp [M_V, M_W, C_out, N_out, polyP]
    have hmul_pow : (1 + c + ν⁻¹) ^ N_V * (1 + c + ν⁻¹) ^ N_W = (1 + c + ν⁻¹) ^ (N_V + N_W) :=
      (pow_add _ N_V N_W).symm
    have hG_nn : 0 ≤ G := Real.exp_nonneg _
    calc 2 * (C_W * (1 + c + ν⁻¹) ^ N_W * G) +
          (2 : ℝ) ^ (ℓ + j) * (C_V * (1 + c + ν⁻¹) ^ N_V) * (C_W * (1 + c + ν⁻¹) ^ N_W * G) +
          (2 : ℝ) ^ (ℓ + j) * (C_V * (1 + c + ν⁻¹) ^ N_V) * (C_W * (1 + c + ν⁻¹) ^ N_W * G)
        = (2 * C_W * (1 + c + ν⁻¹) ^ N_W +
            2 * (2 : ℝ) ^ (ℓ + j) * C_V * C_W *
              ((1 + c + ν⁻¹) ^ N_V * (1 + c + ν⁻¹) ^ N_W)) * G := by ring
      _ = (2 * C_W * (1 + c + ν⁻¹) ^ N_W +
            2 * (2 : ℝ) ^ (ℓ + j) * C_V * C_W * (1 + c + ν⁻¹) ^ (N_V + N_W)) * G := by
          rw [hmul_pow]
      _ ≤ (2 * C_W * (1 + c + ν⁻¹) ^ (N_V + N_W) +
            2 * (2 : ℝ) ^ (ℓ + j) * C_V * C_W * (1 + c + ν⁻¹) ^ (N_V + N_W)) * G := by
          apply mul_le_mul_of_nonneg_right _ hG_nn
          linarith [mul_le_mul_of_nonneg_left hpow_W (by positivity : 0 ≤ 2 * C_W)]
      _ = (2 * C_W + 2 * (2 : ℝ) ^ (ℓ + j) * C_V * C_W) * (1 + c + ν⁻¹) ^ (N_V + N_W) * G := by
          ring
  exact htri.trans ((add_le_add (add_le_add hvisc hadv0) hadv1).trans hcomb)

/-- **Unconditional `ℓ = 1` vorticity Gaussian tail (`trainVorticityGaussianTailAt_one`)** for all
spatial orders `j : ℕ`, proved from `hOv : TrainOverlap` and `hSpatial : TrainVorticitySpatialJetTail`. -/
theorem trainVorticityGaussianTailAt_one
    (hOv : TrainOverlap) (hSpatial : TrainVorticitySpatialJetTail) :
    TrainVorticityGaussianTailAt 1 := by
  refine trainVorticityGaussianTailAt_succ 0
    (fun r hr => ?_) (fun r hr => ?_)
  · have hr0 : r = 0 := Nat.le_zero.mp hr
    subst hr0
    exact trainVorticityGaussianTailAt_zero hSpatial
  · have hr0 : r = 0 := Nat.le_zero.mp hr
    subst hr0
    exact trainVelocityAgeJetSupBoundAt_zero hOv

/-- All-order velocity age-jet sup bound from `TrainOverlap` (`ℓ = 0`) and
`TrainVelocityHigherAgeJetSupBound` (`ℓ ≥ 1`). -/
theorem trainVelocityAgeJetSupBoundAt_all
    (hOv : TrainOverlap) (hVelHigher : TrainVelocityHigherAgeJetSupBound) :
    ∀ ℓ : ℕ, TrainVelocityAgeJetSupBoundAt ℓ
  | 0 => trainVelocityAgeJetSupBoundAt_zero hOv
  | m + 1 => hVelHigher m

/-- **All-order vorticity Gaussian tail (`trainVorticityGaussianTailAt_all`)** proved by strong
induction on `ℓ : ℕ` from `trainVorticityGaussianTailAt_zero` and `trainVorticityGaussianTailAt_succ`. -/
theorem trainVorticityGaussianTailAt_all
    (hOv : TrainOverlap)
    (hSpatial : TrainVorticitySpatialJetTail)
    (hVelHigher : TrainVelocityHigherAgeJetSupBound) :
    ∀ ℓ : ℕ, TrainVorticityGaussianTailAt ℓ := by
  intro ℓ
  induction ℓ using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => exact trainVorticityGaussianTailAt_zero hSpatial
    | succ m =>
      exact trainVorticityGaussianTailAt_succ m
        (fun r hr => ih r (Nat.lt_succ_of_le hr))
        (fun r _ => trainVelocityAgeJetSupBoundAt_all hOv hVelHigher r)

/-- **Conditional assembly of `TrainVorticityAgeDerivFromZero` (`PartI:T20/1`)** from
`TrainVelocityHigherAgeJetSupBound`. -/
theorem trainVorticityAgeDerivFromZero_of
    (hVelHigher : TrainVelocityHigherAgeJetSupBound) :
    TrainVorticityAgeDerivFromZero := by
  intro hOv hSpatial ρ hρ ℓ j
  exact trainVorticityGaussianTailAt_all hOv hSpatial hVelHigher ℓ ρ hρ j

end UnforcedLeray.Short.PartI

end
