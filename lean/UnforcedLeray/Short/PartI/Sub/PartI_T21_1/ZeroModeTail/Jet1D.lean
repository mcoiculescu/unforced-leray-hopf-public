import UnforcedLeray.Short.PartI.Sub.PartI_T21_1.ZeroModeTail.MeanVorticityFTC
import UnforcedLeray.Short.PartI.Tasks.TrainVorticityTail.AgeDeriv
import UnforcedLeray.Lib.Kernels.ParamIntegral

/-!
# `PartI:T21/1/2` Helper: 1D spatial jet reduction and horizontal-average vorticity jet bounds

Source of record: `the November 2 reference manuscript`, lines 504-513.

Provides:
1. Exact `ageJet` subtraction identities (`ageJet_train_ψ_sub_fluct_eq`, `ageJet_train_v_sub_fluct_eq`).
2. Reduction `‖ageJet ℓ j (hmean c tr.v) s z‖ ≤ ‖ageJet ℓ j meanVel1 s z‖`
   (`norm_ageJet_hmean_v_le_meanVel1`).
3. Spatial jet step `‖ageJet ℓ (k + 1) (fun r w => g r w.2) s z‖ ≤ ‖ageJet ℓ k (fun r w => g' r w.2) s z‖`
   for any 1D family `g` with `∂_η g = g'` (`norm_ageJet_succ_snd_le`), specialized to
   `meanStream` (`norm_ageJet_meanStream_succ_le`) and `meanVel1` (`norm_ageJet_meanVel1_succ_le`).
4. Pointwise bound `‖ageJet ℓ m (fun r w => hmean c (f r) w.2) s z‖ ≤ B` from
   `∀ q ∈ Ioc (-c/2) (c/2), ‖ageJet ℓ m f s (q, z.2)‖ ≤ B` (`norm_ageJet_hmean_scalar_le`).
5. Evenness / oddness symmetry at `j = 0`:
   `‖ageJet ℓ 0 (fun r w => meanStream tr r w.2) s z‖ = |iteratedDeriv ℓ (fun r => meanStream tr r |z.2|) s|`
   and
   `‖ageJet ℓ 0 (fun r w => meanVel1 tr r w.2) s z‖ = |iteratedDeriv ℓ (fun r => meanVel1 tr r |z.2|) s|`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec toVec toVec_zero toVec_one jet)

namespace PartI_T21

/-! ### 1. Joint smoothness of 1D lifts and exact `ageJet` subtraction -/

/-- Lifting a `C^∞` function on `(0, ∞) × ℝ` to `(0, ∞) × Plane` via `(r, w) ↦ g r w.2`. -/
theorem contDiffOn_snd_lift {g : ℝ → ℝ → ℝ}
    (hg : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => g x.1 x.2) (Ioi 0 ×ˢ univ)) :
    ContDiffOn ℝ ∞ (fun x : ℝ × Plane => g x.1 x.2.2) (Ioi 0 ×ˢ univ) := by
  have hproj : ContDiff ℝ ∞ (fun x : ℝ × Plane => ((x.1, x.2.2) : ℝ × ℝ)) := by fun_prop
  exact hg.comp hproj.contDiffOn (fun _ hx => ⟨hx.1, mem_univ _⟩)

/-- Joint `C^∞` smoothness of `(r, η) ↦ meanVel1 tr r η` on `(0, ∞) × ℝ`. -/
theorem contDiffOn_meanVel1 {ν c : ℝ} (hc : 0 < c) (tr : B0140.TrainSol ν c) :
    ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => meanVel1 tr x.1 x.2) (Ioi 0 ×ˢ univ) := by
  have hv_joint : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => tr.v x.1 x.2) (Ioi 0 ×ˢ univ) :=
    tr.isTrain.smooth_v.mono (prod_mono Ioi_subset_Ici_self Subset.rfl)
  have hv0 : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => tr.v x.1 x.2 0) (Ioi 0 ×ˢ univ) :=
    (EuclideanSpace.proj (0 : Fin 2) : Vec →L[ℝ] ℝ).contDiff.comp_contDiffOn hv_joint
  exact hmeanContDiff c hc (fun r z => tr.v r z 0) hv0

/-- Joint `C^∞` smoothness of `(r, η) ↦ hmean c (Cyl.curl (tr.v r)) η` on `(0, ∞) × ℝ`. -/
theorem contDiffOn_hmean_curl {ν c : ℝ} (hc : 0 < c) (tr : B0140.TrainSol ν c) :
    ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => hmean c (Cyl.curl (tr.v x.1)) x.2) (Ioi 0 ×ˢ univ) := by
  have hv_joint : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => tr.v x.1 x.2) (Ioi 0 ×ˢ univ) :=
    tr.isTrain.smooth_v.mono (prod_mono Ioi_subset_Ici_self Subset.rfl)
  exact hmeanContDiff c hc (fun r z => Cyl.curl (tr.v r) z) (PartI_T20.smR_curl hv_joint)

/-- Joint `C^∞` smoothness of `(r, w) ↦ hmean c (tr.v r) w.2` on `(0, ∞) × Plane`. -/
theorem contDiffOn_hmean_v {ν c : ℝ} (hc : 0 < c) (tr : B0140.TrainSol ν c) :
    ContDiffOn ℝ ∞ (fun x : ℝ × Plane => hmean c (tr.v x.1) x.2.2) (Ioi 0 ×ˢ univ) := by
  have hv_joint : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => tr.v x.1 x.2) (Ioi 0 ×ˢ univ) :=
    tr.isTrain.smooth_v.mono (prod_mono Ioi_subset_Ici_self Subset.rfl)
  have hv_fluct := PartI_T22.contDiffOn_hfluct_v hc tr
  have hsub := hv_joint.sub hv_fluct
  refine hsub.congr fun ⟨r, w⟩ _ => ?_
  dsimp [hfluct]
  abel

/-- `ageJet ℓ j tr.ψ s z - ageJet ℓ j ψ_fluct s z = ageJet ℓ j (fun r w => meanStream tr r w.2) s z`. -/
theorem ageJet_train_ψ_sub_fluct_eq {ν c : ℝ} (hν : 0 < ν) (hc : 0 < c)
    (tr : B0140.TrainSol ν c) (htr : IsBUCTrain tr) {s : ℝ} (hs : 0 < s)
    (ℓ j : ℕ) (z : Plane) :
    ageJet ℓ j tr.ψ s z -
        ageJet ℓ j (fun r w => tr.ψ r w - meanStream tr r w.2) s z =
      ageJet ℓ j (fun r w => meanStream tr r w.2) s z := by
  have hψ : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => tr.ψ x.1 x.2) (Ioi 0 ×ˢ univ) :=
    trainStreamSmooth ν c hν hc tr htr
  have hS : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => meanStream tr x.1 x.2.2) (Ioi 0 ×ˢ univ) :=
    contDiffOn_snd_lift (bucMeanStreamSmooth ν c hν hc tr htr)
  rw [PartI_T22.ageJet_sub tr.ψ (fun r w => meanStream tr r w.2) hψ hS hs ℓ j z]
  abel

/-- `ageJet ℓ j tr.v s z - ageJet ℓ j (hfluct c tr.v) s z = ageJet ℓ j (fun r w => hmean c (tr.v r) w.2) s z`. -/
theorem ageJet_train_v_sub_fluct_eq {ν c : ℝ} (hc : 0 < c)
    (tr : B0140.TrainSol ν c) {s : ℝ} (hs : 0 < s) (ℓ j : ℕ) (z : Plane) :
    ageJet ℓ j tr.v s z - ageJet ℓ j (fun r => hfluct c (tr.v r)) s z =
      ageJet ℓ j (fun r w => hmean c (tr.v r) w.2) s z := by
  have hv : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => tr.v x.1 x.2) (Ioi 0 ×ˢ univ) :=
    tr.isTrain.smooth_v.mono (prod_mono Ioi_subset_Ici_self Subset.rfl)
  have hm : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => hmean c (tr.v x.1) x.2.2) (Ioi 0 ×ˢ univ) :=
    contDiffOn_hmean_v hc tr
  change ageJet ℓ j tr.v s z - ageJet ℓ j (fun r w => tr.v r w - hmean c (tr.v r) w.2) s z = _
  rw [PartI_T22.ageJet_sub tr.v (fun r w => hmean c (tr.v r) w.2) hv hm hs ℓ j z]
  abel

/-! ### 2. Continuous linear embedding `u ↦ toVec (u, 0)` for `hmean c (tr.v r)` -/

/-- Continuous linear map `u ↦ toVec (u, 0)` from `ℝ` to `Vec`, of norm `≤ 1`. -/
def fstVecMap : ℝ →L[ℝ] Vec :=
  (Train.toVecL : (ℝ × ℝ) →L[ℝ] Vec).comp
    ((ContinuousLinearMap.id ℝ ℝ).prod (0 : ℝ →L[ℝ] ℝ))

theorem fstVecMap_apply (u : ℝ) : fstVecMap u = toVec (u, 0) := rfl

theorem norm_fstVecMap_le_one : ‖fstVecMap‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun u => ?_
  rw [fstVecMap_apply, Train.norm_toVec, Real.norm_eq_abs, one_mul]
  simp [Real.sqrt_sq_eq_abs]

/-- For `r > 0`, `hmean c (tr.v r) η = fstVecMap (meanVel1 tr r η)`. -/
theorem hmean_v_eq_fstVecMap {ν c : ℝ} (hν : 0 < ν) (hc : 0 < c)
    (tr : B0140.TrainSol ν c) {r : ℝ} (hr : 0 < r) (η : ℝ) :
    hmean c (tr.v r) η = fstVecMap (meanVel1 tr r η) := by
  have hvc : Continuous (tr.v r) := (bucVel_vslice_contDiff tr hr.le).continuous
  have hm0 := PartI_T22.hmean_apply_vec' c hvc η 0
  have hm1 := PartI_T22.hmean_apply_vec' c hvc η 1
  have hv2 := trainMeanV2 ν c hν hc tr r hr η
  ext i
  fin_cases i
  · change (hmean c (tr.v r) η).ofLp 0 = (fstVecMap (meanVel1 tr r η)).ofLp 0
    rw [hm0, fstVecMap_apply, toVec_zero]
    rfl
  · change (hmean c (tr.v r) η).ofLp 1 = (fstVecMap (meanVel1 tr r η)).ofLp 1
    rw [hm1, hv2, fstVecMap_apply, toVec_one]

/-- `‖ageJet ℓ j (fun r w => hmean c (tr.v r) w.2) s z‖ ≤ ‖ageJet ℓ j (fun r w => meanVel1 tr r w.2) s z‖`. -/
theorem norm_ageJet_hmean_v_le_meanVel1 {ν c : ℝ} (hν : 0 < ν) (hc : 0 < c)
    (tr : B0140.TrainSol ν c) (ℓ j : ℕ) {s : ℝ} (hs : 0 < s) (z : Plane) :
    ‖ageJet ℓ j (fun r w => hmean c (tr.v r) w.2) s z‖ ≤
      ‖ageJet ℓ j (fun r w => meanVel1 tr r w.2) s z‖ := by
  let U : ℝ → Plane → ℝ := fun r w => meanVel1 tr r w.2
  have hU : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => U x.1 x.2) (Ioi 0 ×ˢ univ) :=
    contDiffOn_snd_lift (contDiffOn_meanVel1 hc tr)
  have hslice_eq : (fun w : Plane => iteratedDeriv ℓ (fun r => hmean c (tr.v r) w.2) s) =
      fstVecMap ∘ (fun w : Plane => iteratedDeriv ℓ (fun r => U r w) s) := by
    funext w
    have hev : (fun r => hmean c (tr.v r) w.2) =ᶠ[𝓝 s] fun r => fstVecMap (U r w) := by
      filter_upwards [Ioi_mem_nhds hs] with r hr using hmean_v_eq_fstVecMap hν hc tr hr w.2
    rw [hev.iteratedDeriv_eq ℓ, Function.comp_apply]
    have hAt : ContDiffAt ℝ ℓ (fun r => U r w) s :=
      PartI_T22.contDiffAt_age_slice hU hs w ℓ
    rw [iteratedDeriv_eq_iteratedFDeriv, iteratedDeriv_eq_iteratedFDeriv]
    have hcomp := fstVecMap.iteratedFDeriv_comp_left hAt le_rfl
    change (iteratedFDeriv ℝ ℓ (fstVecMap ∘ fun r => U r w) s) (fun _ => 1) = _
    rw [hcomp]
    rfl
  have hG_sm : ContDiffAt ℝ j (fun w : Plane => iteratedDeriv ℓ (fun r => U r w) s) z :=
    ((PartI_T22.contDiff_slice_iteratedDeriv hU ℓ hs).contDiffAt).of_le (by exact_mod_cast le_top)
  unfold ageJet jet
  change ‖iteratedFDeriv ℝ j (fun w : Plane => iteratedDeriv ℓ (fun r => hmean c (tr.v r) w.2) s) z‖ ≤ _
  rw [hslice_eq, fstVecMap.iteratedFDeriv_comp_left hG_sm le_rfl]
  calc ‖fstVecMap.compContinuousMultilinearMap
          (iteratedFDeriv ℝ j (fun w : Plane => iteratedDeriv ℓ (fun r => U r w) s) z)‖
      ≤ ‖fstVecMap‖ *
          ‖iteratedFDeriv ℝ j (fun w : Plane => iteratedDeriv ℓ (fun r => U r w) s) z‖ :=
        ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _
    _ ≤ 1 * ‖iteratedFDeriv ℝ j (fun w : Plane => iteratedDeriv ℓ (fun r => U r w) s) z‖ :=
        mul_le_mul_of_nonneg_right norm_fstVecMap_le_one (norm_nonneg _)
    _ = ‖iteratedFDeriv ℝ j (fun w : Plane => iteratedDeriv ℓ (fun r => U r w) s) z‖ := one_mul _

/-! ### 3. Spatial jet step for 1D lifts `(r, w) ↦ g r w.2` -/

/-- Continuous linear map `a ↦ a • snd` from `ℝ` to `Plane →L[ℝ] ℝ`, of norm `≤ 1`. -/
def sndGradMap : ℝ →L[ℝ] (Plane →L[ℝ] ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun a => a • ContinuousLinearMap.snd ℝ ℝ ℝ
      map_add' := fun a b => add_smul a b _
      map_smul' := fun c a => mul_smul c a _ }

theorem sndGradMap_apply (a : ℝ) (h : Plane) : sndGradMap a h = a * h.2 := by
  simp [sndGradMap]

theorem norm_sndGradMap_le_one : ‖sndGradMap‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun a => ?_
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun h => ?_
  rw [sndGradMap_apply, Real.norm_eq_abs, Real.norm_eq_abs, one_mul, abs_mul]
  have hh2 : |h.2| ≤ ‖h‖ := by simpa [Real.norm_eq_abs] using norm_snd_le h
  exact mul_le_mul_of_nonneg_left hh2 (abs_nonneg a)

/-- If `g, g' : ℝ → ℝ → ℝ` are jointly `C^∞` on `(0, ∞) × ℝ` and `HasDerivAt (g r) (g' r η) η`
for all `r > 0` and `η : ℝ`, then for all `ℓ, k : ℕ`, `s > 0`, and `z : Plane`,
`‖ageJet ℓ (k + 1) (fun r w => g r w.2) s z‖ ≤ ‖ageJet ℓ k (fun r w => g' r w.2) s z‖`. -/
theorem norm_ageJet_succ_snd_le {g g' : ℝ → ℝ → ℝ}
    (hg : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => g x.1 x.2) (Ioi 0 ×ˢ univ))
    (hg' : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => g' x.1 x.2) (Ioi 0 ×ˢ univ))
    (hd : ∀ r : ℝ, 0 < r → ∀ η : ℝ, HasDerivAt (g r) (g' r η) η)
    (ℓ k : ℕ) {s : ℝ} (hs : 0 < s) (z : Plane) :
    ‖ageJet ℓ (k + 1) (fun (r : ℝ) (w : Plane) => g r w.2) s z‖ ≤
      ‖ageJet ℓ k (fun (r : ℝ) (w : Plane) => g' r w.2) s z‖ := by
  let F : ℝ → Plane → ℝ := fun r w => g r w.2
  let F' : ℝ → Plane → ℝ := fun r w => g' r w.2
  have hF : PartI_T20.SmR (fun x : ℝ × Plane => F x.1 x.2) := contDiffOn_snd_lift hg
  have hF' : PartI_T20.SmR (fun x : ℝ × Plane => F' x.1 x.2) := contDiffOn_snd_lift hg'
  set G : Plane → ℝ := fun w => iteratedDeriv ℓ (fun r => F r w) s
  set G' : Plane → ℝ := fun w => iteratedDeriv ℓ (fun r => F' r w) s
  have hG_cd : ContDiff ℝ ∞ G := PartI_T22.contDiff_slice_iteratedDeriv hF ℓ hs
  have hG'_cd : ContDiff ℝ ∞ G' := PartI_T22.contDiff_slice_iteratedDeriv hF' ℓ hs
  have hG_diff : Differentiable ℝ G := hG_cd.differentiable (by simp)
  have hQ_F : ∀ r : ℝ, 0 < r → ∀ w : Plane, Cyl.partialQ (F r) w = 0 := by
    intro r _ w
    change deriv (fun q => g r w.2) w.1 = 0
    exact deriv_const w.1 (g r w.2)
  have hE_F : ∀ r : ℝ, 0 < r → ∀ w : Plane, Cyl.partialEta (F r) w = F' r w := by
    intro r hr w
    change deriv (g r) w.2 = g' r w.2
    exact (hd r hr w.2).deriv
  have hQ_G : ∀ w : Plane, Cyl.partialQ G w = 0 := by
    intro w
    rw [← PartI_T20.iteratedDeriv_partialQ_eq hF ℓ hs w]
    have hev : (fun r => Cyl.partialQ (F r) w) =ᶠ[𝓝 s] fun _ => (0 : ℝ) := by
      filter_upwards [Ioi_mem_nhds hs] with r hr using hQ_F r hr w
    rw [hev.iteratedDeriv_eq ℓ, iteratedDeriv_const]
    split_ifs <;> rfl
  have hE_G : ∀ w : Plane, Cyl.partialEta G w = G' w := by
    intro w
    rw [← PartI_T20.iteratedDeriv_partialEta_eq hF ℓ hs w]
    have hev : (fun r => Cyl.partialEta (F r) w) =ᶠ[𝓝 s] fun r => F' r w := by
      filter_upwards [Ioi_mem_nhds hs] with r hr using hE_F r hr w
    exact hev.iteratedDeriv_eq ℓ
  have hfd : fderiv ℝ G = sndGradMap ∘ G' := by
    funext w
    refine ContinuousLinearMap.ext fun h => ?_
    have hdec : h = h.1 • ((1 : ℝ), (0 : ℝ)) + h.2 • ((0 : ℝ), (1 : ℝ)) := by ext <;> simp
    have step : fderiv ℝ G w h =
        h.1 * Cyl.partialQ G w + h.2 * Cyl.partialEta G w := by
      rw [Cyl.partialQ_eq_fderiv hG_diff w, Cyl.partialEta_eq_fderiv hG_diff w]
      conv_lhs => rw [hdec]
      rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    rw [step, hQ_G w, hE_G w, Function.comp_apply, sndGradMap_apply]
    ring
  have hG'_at : ContDiffAt ℝ k G' z := (hG'_cd.contDiffAt).of_le (by exact_mod_cast le_top)
  show ‖iteratedFDeriv ℝ (k + 1) G z‖ ≤ ‖iteratedFDeriv ℝ k G' z‖
  calc ‖iteratedFDeriv ℝ (k + 1) G z‖
      = ‖iteratedFDeriv ℝ k (fderiv ℝ G) z‖ := (norm_iteratedFDeriv_fderiv).symm
    _ = ‖sndGradMap.compContinuousMultilinearMap (iteratedFDeriv ℝ k G' z)‖ := by
        rw [hfd, sndGradMap.iteratedFDeriv_comp_left hG'_at le_rfl]
    _ ≤ ‖sndGradMap‖ * ‖iteratedFDeriv ℝ k G' z‖ :=
        ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _
    _ ≤ 1 * ‖iteratedFDeriv ℝ k G' z‖ :=
        mul_le_mul_of_nonneg_right norm_sndGradMap_le_one (norm_nonneg _)
    _ = ‖iteratedFDeriv ℝ k G' z‖ := one_mul _

/-- Norm of `ageJet ℓ j (-F)` equals norm of `ageJet ℓ j F` for jointly smooth `F`. -/
theorem norm_ageJet_neg_eq (F : ℝ → Plane → ℝ)
    (hF : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => F x.1 x.2) (Ioi 0 ×ˢ univ))
    (ℓ j : ℕ) {s : ℝ} (hs : 0 < s) (z : Plane) :
    ‖ageJet ℓ j (fun r w => -F r w) s z‖ = ‖ageJet ℓ j F s z‖ := by
  have h0 : ContDiffOn ℝ ∞ (fun _ : ℝ × Plane => (0 : ℝ)) (Ioi 0 ×ˢ univ) := contDiffOn_const
  have hsub := PartI_T22.ageJet_sub (fun _ _ => (0 : ℝ)) F h0 hF hs ℓ j z
  have hzero : ageJet ℓ j (fun (_ : ℝ) (_ : Plane) => (0 : ℝ)) s z = 0 := by
    unfold ageJet jet
    have h1 : (fun _ : Plane => iteratedDeriv ℓ (fun _ : ℝ => (0 : ℝ)) s) = fun _ => 0 := by
      funext _
      rw [iteratedDeriv_const]
      split_ifs <;> rfl
    rw [h1, iteratedFDeriv_fun_zero]
    rfl
  rw [hzero, zero_sub] at hsub
  have heq : (fun r w => -F r w) = fun r w => (0 : ℝ) - F r w := by
    funext r w; ring
  rw [heq, hsub, norm_neg]

/-- `‖ageJet ℓ (k + 1) (fun r w => meanStream tr r w.2) s z‖ ≤ ‖ageJet ℓ k (fun r w => meanVel1 tr r w.2) s z‖`. -/
theorem norm_ageJet_meanStream_succ_le {ν c : ℝ} (hν : 0 < ν) (hc : 0 < c)
    (tr : B0140.TrainSol ν c) (htr : IsBUCTrain tr) (ℓ k : ℕ) {s : ℝ} (hs : 0 < s) (z : Plane) :
    ‖ageJet ℓ (k + 1) (fun r w => meanStream tr r w.2) s z‖ ≤
      ‖ageJet ℓ k (fun r w => meanVel1 tr r w.2) s z‖ := by
  have hS := bucMeanStreamSmooth ν c hν hc tr htr
  have hU := contDiffOn_meanVel1 hc tr
  have h1 := norm_ageJet_succ_snd_le hS hU.neg
    (fun r hr η => bucVel_S_deriv tr hr.le η) ℓ k hs z
  exact (norm_ageJet_neg_eq (fun r w => meanVel1 tr r w.2) (contDiffOn_snd_lift hU) ℓ k hs z) ▸ h1

/-- `‖ageJet ℓ (k + 1) (fun r w => meanVel1 tr r w.2) s z‖ ≤ ‖ageJet ℓ k (fun r w => hmean c (Cyl.curl (tr.v r)) w.2) s z‖`. -/
theorem norm_ageJet_meanVel1_succ_le {ν c : ℝ} (hc : 0 < c)
    (tr : B0140.TrainSol ν c) (ℓ k : ℕ) {s : ℝ} (hs : 0 < s) (z : Plane) :
    ‖ageJet ℓ (k + 1) (fun r w => meanVel1 tr r w.2) s z‖ ≤
      ‖ageJet ℓ k (fun r w => hmean c (Cyl.curl (tr.v r)) w.2) s z‖ := by
  have hU := contDiffOn_meanVel1 hc tr
  have hW := contDiffOn_hmean_curl hc tr
  have h1 := norm_ageJet_succ_snd_le hU hW.neg
    (fun r hr η => hasDerivAt_meanVel1_curl hc tr hr.le η) ℓ k hs z
  exact (norm_ageJet_neg_eq (fun r w => hmean c (Cyl.curl (tr.v r)) w.2)
    (contDiffOn_snd_lift (g := fun r η => hmean c (Cyl.curl (tr.v r)) η) hW) ℓ k hs z) ▸ h1

/-! ### 4. Horizontal-average jet bound `‖ageJet ℓ m (fun r w => hmean c (f r) w.2) s z‖ ≤ B` -/

private def sndPlane1D : Plane →L[ℝ] Plane :=
  (0 : Plane →L[ℝ] ℝ).prod (ContinuousLinearMap.snd ℝ ℝ ℝ)

private theorem sndPlane1D_apply (w : Plane) : sndPlane1D w = (0, w.2) := rfl

private theorem norm_sndPlane1D_le_one : ‖sndPlane1D‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun w => ?_
  rw [one_mul, sndPlane1D_apply, Prod.norm_def, Prod.norm_def, norm_zero]
  exact max_le ((norm_nonneg w.1).trans (le_max_left _ _)) (le_max_right _ _)

private theorem slice_snd1D_iteratedFDeriv {G : Plane → ℝ} (hG : ContDiff ℝ ∞ G)
    (q : ℝ) (n : ℕ) (w : Plane) :
    iteratedFDeriv ℝ n (fun w' : Plane => G (q, w'.2)) w =
      (iteratedFDeriv ℝ n G (q, w.2)).compContinuousLinearMap
        (fun _ : Fin n => sndPlane1D) := by
  have hsmooth : ContDiff ℝ ∞ (fun z : Plane => G (z + (q, 0))) :=
    hG.comp (contDiff_id.add contDiff_const)
  have hfun : (fun w' : Plane => G (q, w'.2)) =
      (fun z : Plane => G (z + (q, 0))) ∘ sndPlane1D := by
    funext w'
    simp [sndPlane1D_apply]
  rw [hfun, ContinuousLinearMap.iteratedFDeriv_comp_right (i := n)
    sndPlane1D hsmooth w (by exact_mod_cast le_top),
    iteratedFDeriv_comp_add_right]
  have hw : sndPlane1D w + (q, 0) = (q, w.2) := by ext <;> simp [sndPlane1D_apply]
  rw [hw]

private theorem norm_slice_snd1D_iteratedFDeriv_le {G : Plane → ℝ} (hG : ContDiff ℝ ∞ G)
    (q : ℝ) (n : ℕ) (w : Plane) :
    ‖iteratedFDeriv ℝ n (fun w' : Plane => G (q, w'.2)) w‖ ≤
      ‖iteratedFDeriv ℝ n G (q, w.2)‖ := by
  rw [slice_snd1D_iteratedFDeriv hG q n w]
  have hprod : ∏ _i : Fin n, ‖sndPlane1D‖ ≤ 1 := by
    calc ∏ _i : Fin n, ‖sndPlane1D‖
        ≤ ∏ _i : Fin n, (1 : ℝ) :=
          Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun _ _ => norm_sndPlane1D_le_one)
      _ = 1 := Finset.prod_const_one
  calc ‖(iteratedFDeriv ℝ n G (q, w.2)).compContinuousLinearMap (fun _ => sndPlane1D)‖
      ≤ ‖iteratedFDeriv ℝ n G (q, w.2)‖ * ∏ _i : Fin n, ‖sndPlane1D‖ :=
        ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ ‖iteratedFDeriv ℝ n G (q, w.2)‖ * 1 :=
        mul_le_mul_of_nonneg_left hprod (norm_nonneg _)
    _ = ‖iteratedFDeriv ℝ n G (q, w.2)‖ := mul_one _

private theorem slice_snd1D_continuous {G : Plane → ℝ} (hG : ContDiff ℝ ∞ G)
    (n : ℕ) (w : Plane) :
    Continuous (fun q : ℝ => iteratedFDeriv ℝ n (fun w' : Plane => G (q, w'.2)) w) := by
  have hcont : Continuous (fun q : ℝ => iteratedFDeriv ℝ n G (q, w.2)) :=
    (hG.continuous_iteratedFDeriv (m := n) (by exact_mod_cast le_top)).comp
      (continuous_id.prodMk continuous_const)
  have hT : Continuous (fun A : ContinuousMultilinearMap ℝ (fun _ : Fin n => Plane) ℝ =>
      A.compContinuousLinearMap (fun _ : Fin n => sndPlane1D)) :=
    (ContinuousMultilinearMap.compContinuousLinearMapL
      (fun _ : Fin n => sndPlane1D)).continuous
  refine (hT.comp hcont).congr fun q => ?_
  exact (slice_snd1D_iteratedFDeriv hG q n w).symm

private theorem slice_snd1D_locDominated {G : Plane → ℝ} (hG : ContDiff ℝ ∞ G) (c : ℝ) :
    UnforcedLeray.Kernels.LocDominated (volume.restrict (Ioc (-c / 2) (c / 2)))
      (fun (q : ℝ) (w : Plane) => G (q, w.2)) univ := by
  intro n x _
  have hK : IsCompact (Icc (-c / 2) (c / 2) ×ˢ Metric.closedBall x 1) :=
    isCompact_Icc.prod (isCompact_closedBall x 1)
  have hcont : ContinuousOn (fun p : ℝ × Plane => iteratedFDeriv ℝ n G (p.1, p.2.2))
      (Icc (-c / 2) (c / 2) ×ˢ Metric.closedBall x 1) :=
    ((hG.continuous_iteratedFDeriv (m := n) (by exact_mod_cast le_top)).comp
      (continuous_fst.prodMk (continuous_snd.comp continuous_snd))).continuousOn
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont
  refine ⟨Metric.closedBall x 1, Metric.closedBall_mem_nhds x one_pos,
    fun _ => C, integrable_const _, ?_⟩
  filter_upwards [ae_restrict_mem (measurableSet_Ioc : MeasurableSet (Ioc (-c / 2) (c / 2)))]
    with q hq y hy
  exact (norm_slice_snd1D_iteratedFDeriv_le hG q n y).trans
    (hC (q, y) ⟨Ioc_subset_Icc_self hq, hy⟩)

/-- Iterated age derivative commutes with `hmean c` for jointly `C^∞` scalar families. -/
theorem iteratedDeriv_hmean_scalar_eq {c : ℝ} (hc : 0 < c) {f : ℝ → Plane → ℝ}
    (hf : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => f x.1 x.2) (Ioi 0 ×ˢ univ)) :
    ∀ (ℓ : ℕ) {s : ℝ}, 0 < s → ∀ η : ℝ,
      iteratedDeriv ℓ (fun r => hmean c (f r) η) s =
        hmean c (fun w => iteratedDeriv ℓ (fun r => f r w) s) η
  | 0, _, _, _ => rfl
  | ℓ + 1, s, hs, η => by
    rw [iteratedDeriv_succ]
    have hev : iteratedDeriv ℓ (fun r => hmean c (f r) η) =ᶠ[𝓝 s]
        fun r => hmean c (fun w => iteratedDeriv ℓ (fun r' => f r' w) r) η := by
      filter_upwards [Ioi_mem_nhds hs] with r hr using iteratedDeriv_hmean_scalar_eq hc hf ℓ hr η
    rw [hev.deriv_eq, hmeanDerivS c hc (fun r w => iteratedDeriv ℓ (fun r' => f r' w) r)
      (PartI_T22.contDiffOn_iteratedDeriv_age hf ℓ) s hs η]
    simp only [iteratedDeriv_succ]

/-- If `‖ageJet ℓ m f s (q, z.2)‖ ≤ B` for all `q ∈ Ioc (-c/2) (c/2)` (`B ≥ 0`), then
`‖ageJet ℓ m (fun r w => hmean c (f r) w.2) s z‖ ≤ B`. -/
theorem norm_ageJet_hmean_scalar_le {c B : ℝ} (hc : 0 < c) (_hB : 0 ≤ B)
    {f : ℝ → Plane → ℝ}
    (hf : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => f x.1 x.2) (Ioi 0 ×ˢ univ))
    (ℓ m : ℕ) {s : ℝ} (hs : 0 < s) (z : Plane)
    (hpt : ∀ q ∈ Ioc (-c / 2) (c / 2), ‖ageJet ℓ m f s (q, z.2)‖ ≤ B) :
    ‖ageJet ℓ m (fun r w => hmean c (f r) w.2) s z‖ ≤ B := by
  let G : Plane → ℝ := fun w => iteratedDeriv ℓ (fun r => f r w) s
  have hG : ContDiff ℝ ∞ G := PartI_T22.contDiff_slice_iteratedDeriv hf ℓ hs
  have hhm_eq : ageJet ℓ m (fun r w => hmean c (f r) w.2) s z =
      jet m (fun w : Plane => hmean c G w.2) z := by
    unfold ageJet jet
    congr 1
    funext w
    exact iteratedDeriv_hmean_scalar_eq hc hf ℓ hs w.2
  rw [hhm_eq]
  let μ : Measure ℝ := volume.restrict (Ioc (-c / 2) (c / 2))
  let S : ℝ →L[ℝ] ℝ := c⁻¹ • ContinuousLinearMap.id ℝ ℝ
  let I : Plane → ℝ := fun w => ∫ q, G (q, w.2) ∂μ
  have hsmooth : ∀ q : ℝ, ContDiff ℝ ∞ (fun w : Plane => G (q, w.2)) :=
    fun _ => hG.comp (contDiff_const.prodMk contDiff_snd)
  have hmeas : ∀ (n : ℕ) (w : Plane),
      AEStronglyMeasurable (fun q => iteratedFDeriv ℝ n (fun w' : Plane => G (q, w'.2)) w) μ :=
    fun n w => (slice_snd1D_continuous hG n w).aestronglyMeasurable
  have hdom := slice_snd1D_locDominated hG c
  have hI_cd : ContDiffOn ℝ ∞ I univ :=
    UnforcedLeray.Kernels.contDiffOn_integral isOpen_univ (ae_of_all _ hsmooth) hmeas hdom
  have hI_at : ContDiffAt ℝ m I z :=
    (hI_cd.contDiffAt (isOpen_univ.mem_nhds (mem_univ z))).of_le (by exact_mod_cast le_top)
  have hfun : (fun w : Plane => hmean c G w.2) = S ∘ I := rfl
  unfold jet
  rw [hfun, S.iteratedFDeriv_comp_left hI_at le_rfl]
  have hS_norm : ‖S‖ ≤ c⁻¹ := by
    refine ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.2 hc.le) fun x => ?_
    simp [S, Real.norm_of_nonneg (inv_nonneg.2 hc.le)]
  have hint_le := UnforcedLeray.Kernels.norm_iteratedFDeriv_integral_le isOpen_univ
    (ae_of_all _ hsmooth) hmeas hdom m (mem_univ z)
  have hslice_le : ∀ q ∈ Ioc (-c / 2) (c / 2),
      ‖iteratedFDeriv ℝ m (fun w : Plane => G (q, w.2)) z‖ ≤ B := by
    intro q hq
    exact (norm_slice_snd1D_iteratedFDeriv_le hG q m z).trans (hpt q hq)
  have hint_bound : ∫ q in Ioc (-c / 2) (c / 2),
      ‖iteratedFDeriv ℝ m (fun w : Plane => G (q, w.2)) z‖ ≤ B * c := by
    have h0 := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ioc (-c / 2) (c / 2))
      (f := fun q => ‖iteratedFDeriv ℝ m (fun w : Plane => G (q, w.2)) z‖)
      (C := B) measure_Ioc_lt_top (fun q hq => by
        rw [Real.norm_of_nonneg (norm_nonneg _)]
        exact hslice_le q hq)
    rw [Real.volume_real_Ioc_of_le (by linarith), show c / 2 - -c / 2 = c by ring] at h0
    exact (le_abs_self _).trans h0
  calc ‖S.compContinuousMultilinearMap (iteratedFDeriv ℝ m I z)‖
      ≤ ‖S‖ * ‖iteratedFDeriv ℝ m I z‖ :=
        ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _
    _ ≤ c⁻¹ * (∫ q, ‖iteratedFDeriv ℝ m (fun w : Plane => G (q, w.2)) z‖ ∂μ) :=
        mul_le_mul hS_norm hint_le (norm_nonneg _) (inv_nonneg.2 hc.le)
    _ ≤ c⁻¹ * (B * c) := mul_le_mul_of_nonneg_left hint_bound (inv_nonneg.2 hc.le)
    _ = B := by field_simp [hc.ne']

/-! ### 5. Evenness / oddness symmetry at spatial order `j = 0` -/

/-- `meanVel1 tr r (-η) = -meanVel1 tr r η` for `r ≥ 0`. -/
theorem meanVel1_odd {ν c : ℝ} (hc : 0 < c) (tr : B0140.TrainSol ν c) {r : ℝ} (hr : 0 ≤ r) (η : ℝ) :
    meanVel1 tr r (-η) = -meanVel1 tr r η := by
  have hd1 : HasDerivAt (meanStream tr r) (-meanVel1 tr r η) η :=
    bucVel_S_deriv tr hr η
  have hd_neg : HasDerivAt (fun y : ℝ => meanStream tr r (-y))
      (-meanVel1 tr r (-η) * -1) η :=
    (bucVel_S_deriv tr hr (-η)).comp η (hasDerivAt_id η).neg
  have heven : (fun y : ℝ => meanStream tr r (-y)) = meanStream tr r :=
    funext fun y => train_meanStream_even hc tr r hr y
  rw [heven] at hd_neg
  have hu := hd1.unique hd_neg
  linarith

/-- `‖ageJet ℓ 0 (fun r w => meanStream tr r w.2) s z‖ = |iteratedDeriv ℓ (fun r => meanStream tr r |z.2|) s|`. -/
theorem norm_ageJet_zero_meanStream_eq_abs {ν c : ℝ} (hc : 0 < c) (tr : B0140.TrainSol ν c)
    (ℓ : ℕ) {s : ℝ} (hs : 0 < s) (z : Plane) :
    ‖ageJet ℓ 0 (fun r w => meanStream tr r w.2) s z‖ =
      |iteratedDeriv ℓ (fun r => meanStream tr r |z.2|) s| := by
  unfold ageJet jet
  rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]
  rcases le_or_gt 0 z.2 with hz | hz
  · rw [abs_of_nonneg hz]
  · rw [abs_of_neg hz]
    have hev : (fun r => meanStream tr r (-z.2)) =ᶠ[𝓝 s] (fun r => meanStream tr r z.2) := by
      filter_upwards [Ioi_mem_nhds hs] with r hr using train_meanStream_even hc tr r hr.le z.2
    rw [hev.iteratedDeriv_eq ℓ]

/-- `‖ageJet ℓ 0 (fun r w => meanVel1 tr r w.2) s z‖ = |iteratedDeriv ℓ (fun r => meanVel1 tr r |z.2|) s|`. -/
theorem norm_ageJet_zero_meanVel1_eq_abs {ν c : ℝ} (hc : 0 < c) (tr : B0140.TrainSol ν c)
    (ℓ : ℕ) {s : ℝ} (hs : 0 < s) (z : Plane) :
    ‖ageJet ℓ 0 (fun r w => meanVel1 tr r w.2) s z‖ =
      |iteratedDeriv ℓ (fun r => meanVel1 tr r |z.2|) s| := by
  unfold ageJet jet
  rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]
  rcases le_or_gt 0 z.2 with hz | hz
  · rw [abs_of_nonneg hz]
  · rw [abs_of_neg hz]
    have hev : (fun r => meanVel1 tr r (-z.2)) =ᶠ[𝓝 s] -(fun r => meanVel1 tr r z.2) := by
      filter_upwards [Ioi_mem_nhds hs] with r hr using meanVel1_odd hc tr hr.le z.2
    rw [hev.iteratedDeriv_eq ℓ, iteratedDeriv_neg, abs_neg]

end PartI_T21

end UnforcedLeray.Short.PartI
