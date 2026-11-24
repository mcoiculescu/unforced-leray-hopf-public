import UnforcedLeray.Short.PartI.Sub.PartI_T25
import UnforcedLeray.Short.PartI.Tasks.TrainGlobalExistence.APLevel3.Energy.Limit.CurlBound
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.RawJet.Leaves.VcJetSup.AgeJetLe

/-!
# Part I, Task `PartI:T25/2`: Fixed-band vorticity age-jet bounds (`TrainFixedBandVortAgeJet`)

Source of record: `the November 2 reference manuscript`, lines 468–478, 541–551.

Proves `TrainFixedBandVortAgeJet` for `dω = curl tr.v - curl Vc` on `0 < s ≤ Sg / ν` from
`TrainFixedBandVelAgeJet` at spatial order `j + 1`:
1. Since `tr.v` and `Vc` are jointly smooth on `(0, ∞) × Plane`, age differentiation `∂_s^ℓ`
   commutes with spatial `Cyl.curl` for `s > 0`, so
   `ageJet ℓ j dω s = jet j (Cyl.curl (fun w => iteratedDeriv ℓ (fun r => dv r w) s))`.
2. By `cbCurlLam` / `norm_cbCurlLam_le`, `‖ageJet ℓ j dω s z‖ ≤ 2 * ‖ageJet ℓ (j + 1) dv s z‖`.
3. `PartI_T25.wCellL2_le_of_pointwise` and `PartI_T25.wSupNorm_le_of_pointwise` lift the velocity
   bounds at `j + 1` to `wCellL2 c (2 * m)`, `wCellL2 c 0`, and `wSupNorm 0` for `dω`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec Vc pc Qc width jap jet cellL2 wCellL2)
open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Short.IIb (UU isOpen_UU mem_UU Dx eT eQ eE Sm Dx_congr hasDerivAt_slice
  Dv Dv_proj slice_Dv vcSmooth_proof)

/-! ### 1. Iterated age derivatives of jointly smooth fields on `(0, ∞) × Plane` -/

/-- The `ℓ`-th age directional derivative `(Dx eT)^[ℓ] F` on `ℝ × Plane`. -/
def Dt (ℓ : ℕ) (F : ℝ × Plane → Vec) : ℝ × Plane → Vec :=
  (Dx eT)^[ℓ] F

theorem Sm_Dt {F : ℝ × Plane → Vec} (hF : Sm F) : ∀ ℓ : ℕ, Sm (Dt ℓ F)
  | 0 => hF
  | ℓ + 1 => by
    unfold Dt
    rw [Function.iterate_succ_apply']
    exact (Sm_Dt hF ℓ).dx eT

theorem iteratedDeriv_slice_eq_Dt {F : ℝ × Plane → Vec} (hF : Sm F) :
    ∀ (ℓ : ℕ) {t : ℝ}, 0 < t → ∀ w : Plane,
      iteratedDeriv ℓ (fun r => F (r, w)) t = Dt ℓ F (t, w)
  | 0, _, _, _ => rfl
  | ℓ + 1, t, ht, w => by
    rw [iteratedDeriv_succ]
    have hev : iteratedDeriv ℓ (fun r => F (r, w)) =ᶠ[nhds t] fun r => Dt ℓ F (r, w) := by
      filter_upwards [Ioi_mem_nhds ht] with r hr using iteratedDeriv_slice_eq_Dt hF ℓ hr w
    rw [hev.deriv_eq, (hasDerivAt_slice (Sm_Dt hF ℓ) ht w).deriv]
    unfold Dt
    rw [Function.iterate_succ_apply']

theorem iteratedDeriv_slice_sub_proj_eq_Dt {G1 G2 : ℝ × Plane → Vec}
    (hG1 : Sm G1) (hG2 : Sm G2) (i1 i2 : Fin 2) :
    ∀ (ℓ : ℕ) {t : ℝ}, 0 < t → ∀ w : Plane,
      iteratedDeriv ℓ (fun r => G1 (r, w) i1 - G2 (r, w) i2) t =
        Dt ℓ G1 (t, w) i1 - Dt ℓ G2 (t, w) i2
  | 0, _, _, _ => rfl
  | ℓ + 1, t, ht, w => by
    rw [iteratedDeriv_succ]
    have hev : iteratedDeriv ℓ (fun r => G1 (r, w) i1 - G2 (r, w) i2) =ᶠ[nhds t]
        fun r => Dt ℓ G1 (r, w) i1 - Dt ℓ G2 (r, w) i2 := by
      filter_upwards [Ioi_mem_nhds ht] with r hr using
        iteratedDeriv_slice_sub_proj_eq_Dt hG1 hG2 i1 i2 ℓ hr w
    rw [hev.deriv_eq]
    have hd1 : HasDerivAt (fun r => Dt ℓ G1 (r, w) i1) ((Dx eT (Dt ℓ G1) (t, w)) i1) t :=
      (EuclideanSpace.proj i1 : Vec →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt t
        (hasDerivAt_slice (Sm_Dt hG1 ℓ) ht w)
    have hd2 : HasDerivAt (fun r => Dt ℓ G2 (r, w) i2) ((Dx eT (Dt ℓ G2) (t, w)) i2) t :=
      (EuclideanSpace.proj i2 : Vec →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt t
        (hasDerivAt_slice (Sm_Dt hG2 ℓ) ht w)
    have hd : HasDerivAt (fun r => Dt ℓ G1 (r, w) i1 - Dt ℓ G2 (r, w) i2)
        ((Dx eT (Dt ℓ G1) (t, w)) i1 - (Dx eT (Dt ℓ G2) (t, w)) i2) t := hd1.sub hd2
    rw [hd.deriv]
    unfold Dt
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']

theorem Dt_comm_Dx {F : ℝ × Plane → Vec} (hF : Sm F) (v : ℝ × Plane) :
    ∀ ℓ : ℕ, EqOn (Dx v (Dt ℓ F)) (Dt ℓ (Dx v F)) UU
  | 0 => fun _ _ => rfl
  | ℓ + 1 => by
    intro x hx
    unfold Dt
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    change Dx v (Dx eT (Dt ℓ F)) x = Dx eT (Dt ℓ (Dx v F)) x
    rw [(Sm_Dt hF ℓ).symm hx eT v]
    exact Dx_congr (Dt_comm_Dx hF v ℓ) eT hx

theorem Dx_sub {F1 F2 : ℝ × Plane → Vec} (hF1 : Sm F1) (hF2 : Sm F2) (v : ℝ × Plane)
    {x : ℝ × Plane} (hx : x ∈ UU) :
    Dx v (fun y => F1 y - F2 y) x = Dx v F1 x - Dx v F2 x := by
  have h : HasFDerivAt (fun y => F1 y - F2 y) (fderiv ℝ F1 x - fderiv ℝ F2 x) x :=
    (hF1.diffAt hx).hasFDerivAt.sub (hF2.diffAt hx).hasFDerivAt
  show fderiv ℝ (fun y => F1 y - F2 y) x v = fderiv ℝ F1 x v - fderiv ℝ F2 x v
  rw [h.fderiv]
  rfl

/-- Spatial curl of a time slice of a jointly smooth field `F` at `t > 0`. -/
theorem curl_slice_eq_Dx {F : ℝ × Plane → Vec} (hF : Sm F) {t : ℝ} (ht : 0 < t) (w : Plane) :
    Cyl.curl (fun x => F (t, x)) w = Dx eQ F (t, w) 1 - Dx eE F (t, w) 0 := by
  have hu : ContDiff ℝ ∞ (fun x : Plane => F (t, x)) := by
    rw [← contDiffOn_univ]
    exact hF.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun x _ => mem_UU ht)
  have hdu : Differentiable ℝ (fun x : Plane => F (t, x)) := hu.differentiable (by simp)
  have hd1 : Differentiable ℝ (fun x : Plane => F (t, x) 1) :=
    (EuclideanSpace.proj (1 : Fin 2) : Vec →L[ℝ] ℝ).differentiable.comp hdu
  have hd0 : Differentiable ℝ (fun x : Plane => F (t, x) 0) :=
    (EuclideanSpace.proj (0 : Fin 2) : Vec →L[ℝ] ℝ).differentiable.comp hdu
  have e1 : Cyl.partialQ (fun x => F (t, x) 1) w = Dx eQ F (t, w) 1 := by
    rw [Cyl.partialQ_eq_fderiv hd1 w]
    change Dv ((1 : ℝ), (0 : ℝ)) (fun x => F (t, x) 1) w = _
    rw [Dv_proj hdu _ 1, slice_Dv hF ht]
    rfl
  have e2 : Cyl.partialEta (fun x => F (t, x) 0) w = Dx eE F (t, w) 0 := by
    rw [Cyl.partialEta_eq_fderiv hd0 w]
    change Dv ((0 : ℝ), (1 : ℝ)) (fun x => F (t, x) 0) w = _
    rw [Dv_proj hdu _ 0, slice_Dv hF ht]
    rfl
  unfold Cyl.curl
  rw [e1, e2]

/-- Commutation of `iteratedDeriv ℓ` in age with spatial `Cyl.curl` for a difference of jointly
smooth velocity fields at `s > 0`. -/
theorem iteratedDeriv_curl_sub_eq {F1 F2 : ℝ → Plane → Vec}
    (hF1 : Sm (fun x : ℝ × Plane => F1 x.1 x.2))
    (hF2 : Sm (fun x : ℝ × Plane => F2 x.1 x.2))
    (ℓ : ℕ) {s : ℝ} (hs : 0 < s) (w : Plane) :
    iteratedDeriv ℓ (fun r => Cyl.curl (F1 r) w - Cyl.curl (F2 r) w) s =
      Cyl.curl (fun x => iteratedDeriv ℓ (fun r => F1 r x - F2 r x) s) w := by
  let U1 : ℝ × Plane → Vec := fun x => F1 x.1 x.2
  let U2 : ℝ × Plane → Vec := fun x => F2 x.1 x.2
  let U : ℝ × Plane → Vec := fun x => U1 x - U2 x
  have hU : Sm U := hF1.sub hF2
  have hev : (fun r => Cyl.curl (F1 r) w - Cyl.curl (F2 r) w) =ᶠ[nhds s]
      fun r => Dx eQ U (r, w) 1 - Dx eE U (r, w) 0 := by
    filter_upwards [Ioi_mem_nhds hs] with r hr
    rw [curl_slice_eq_Dx hF1 hr w, curl_slice_eq_Dx hF2 hr w]
    rw [Dx_sub hF1 hF2 eQ (mem_UU hr), Dx_sub hF1 hF2 eE (mem_UU hr)]
    simp [PiLp.sub_apply, sub_sub_sub_comm]
  rw [hev.iteratedDeriv_eq]
  rw [iteratedDeriv_slice_sub_proj_eq_Dt (hU.dx eQ) (hU.dx eE) 1 0 ℓ hs w]
  rw [← Dt_comm_Dx hU eQ ℓ (mem_UU hs), ← Dt_comm_Dx hU eE ℓ (mem_UU hs)]
  rw [← curl_slice_eq_Dx (Sm_Dt hU ℓ) hs w]
  congr 1
  funext x
  exact (iteratedDeriv_slice_eq_Dt hU ℓ hs x).symm

/-- Spatial smoothness of the `ℓ`-th age derivative slice at `s > 0`. -/
theorem contDiff_slice_iteratedDeriv {F : ℝ → Plane → Vec}
    (hF : Sm (fun x : ℝ × Plane => F x.1 x.2)) (ℓ : ℕ) {s : ℝ} (hs : 0 < s) :
    ContDiff ℝ ∞ (fun x : Plane => iteratedDeriv ℓ (fun r => F r x) s) := by
  have heq : (fun x : Plane => iteratedDeriv ℓ (fun r => F r x) s) =
      fun x : Plane => Dt ℓ (fun y : ℝ × Plane => F y.1 y.2) (s, x) :=
    funext fun x => iteratedDeriv_slice_eq_Dt hF ℓ hs x
  rw [heq]
  rw [← contDiffOn_univ]
  exact (Sm_Dt hF ℓ).comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun x _ => mem_UU hs)

/-! ### 2. Pointwise curl age-jet domination -/

/-- Pointwise bound `‖jet k (Cyl.curl u) z‖ ≤ 2 * ‖jet (k + 1) u z‖` for smooth `u : Plane → Vec`. -/
theorem norm_jet_curl_le (k : ℕ) {u : Plane → Vec} (hu : ContDiff ℝ ∞ u) (z : Plane) :
    ‖jet k (Cyl.curl u) z‖ ≤ 2 * ‖jet (k + 1) u z‖ := by
  have hdiff : Differentiable ℝ u := hu.differentiable (by simp)
  have hg : ContDiff ℝ ∞ (fderiv ℝ u) := (contDiff_infty_iff_fderiv.mp hu).2
  have hd1 : Differentiable ℝ (fun x : Plane => u x 1) :=
    (EuclideanSpace.proj (1 : Fin 2) : Vec →L[ℝ] ℝ).differentiable.comp hdiff
  have hd0 : Differentiable ℝ (fun x : Plane => u x 0) :=
    (EuclideanSpace.proj (0 : Fin 2) : Vec →L[ℝ] ℝ).differentiable.comp hdiff
  have hfun : Cyl.curl u = fun w => cbCurlLam (fderiv ℝ u w) := by
    funext w
    have e1 : Cyl.partialQ (fun x => u x 1) w = fderiv ℝ u w (1, 0) 1 := by
      rw [Cyl.partialQ_eq_fderiv hd1 w]
      exact congrFun (Dv_proj hdiff (1, 0) 1) w
    have e2 : Cyl.partialEta (fun x => u x 0) w = fderiv ℝ u w (0, 1) 0 := by
      rw [Cyl.partialEta_eq_fderiv hd0 w]
      exact congrFun (Dv_proj hdiff (0, 1) 0) w
    unfold Cyl.curl
    rw [e1, e2, cbCurlLam_apply]
  have hcomp : (cbCurlLam ∘ fderiv ℝ u) = Cyl.curl u := by
    rw [hfun]; rfl
  have hiter : iteratedFDeriv ℝ k (Cyl.curl u) z =
      cbCurlLam.compContinuousMultilinearMap (iteratedFDeriv ℝ k (fderiv ℝ u) z) := by
    rw [← hcomp]
    exact ContinuousLinearMap.iteratedFDeriv_comp_left cbCurlLam
      hg.contDiffAt (by exact_mod_cast le_top)
  unfold jet
  rw [hiter]
  have hnorm := ContinuousLinearMap.norm_compContinuousMultilinearMap_le cbCurlLam
    (iteratedFDeriv ℝ k (fderiv ℝ u) z)
  rw [norm_iteratedFDeriv_fderiv] at hnorm
  calc ‖cbCurlLam.compContinuousMultilinearMap (iteratedFDeriv ℝ k (fderiv ℝ u) z)‖
      ≤ ‖cbCurlLam‖ * ‖iteratedFDeriv ℝ (k + 1) u z‖ := hnorm
    _ ≤ 2 * ‖iteratedFDeriv ℝ (k + 1) u z‖ :=
        mul_le_mul_of_nonneg_right norm_cbCurlLam_le (norm_nonneg _)

/-- Pointwise bound `‖ageJet ℓ j dω s z‖ ≤ 2 * ‖ageJet ℓ (j + 1) dv s z‖` for `s > 0`. -/
theorem norm_ageJet_curl_sub_le {F1 F2 : ℝ → Plane → Vec}
    (hF1 : Sm (fun x : ℝ × Plane => F1 x.1 x.2))
    (hF2 : Sm (fun x : ℝ × Plane => F2 x.1 x.2))
    (ℓ j : ℕ) {s : ℝ} (hs : 0 < s) (z : Plane) :
    ‖ageJet ℓ j (fun r w => Cyl.curl (F1 r) w - Cyl.curl (F2 r) w) s z‖ ≤
      2 * ‖ageJet ℓ (j + 1) (fun r w => F1 r w - F2 r w) s z‖ := by
  have hslice : (fun w => iteratedDeriv ℓ (fun r => Cyl.curl (F1 r) w - Cyl.curl (F2 r) w) s) =
      Cyl.curl (fun x => iteratedDeriv ℓ (fun r => F1 r x - F2 r x) s) :=
    funext fun w => iteratedDeriv_curl_sub_eq hF1 hF2 ℓ hs w
  have hu : ContDiff ℝ ∞ (fun x : Plane => iteratedDeriv ℓ (fun r => F1 r x - F2 r x) s) :=
    contDiff_slice_iteratedDeriv (F := fun r x => F1 r x - F2 r x) (hF1.sub hF2) ℓ hs
  unfold ageJet
  rw [hslice]
  exact norm_jet_curl_le j hu z

/-! ### 3. Main theorem: `trainFixedBandVortAgeJet_of` -/

/-- **Fixed-band vorticity age-jet bounds (`TrainFixedBandVortAgeJet`)** from velocity age-jet
bounds at spatial order `j + 1`. -/
theorem trainFixedBandVortAgeJet_of
    (_hTails : TrainStreamVelocityPressureTails)
    (_hFD : TrainFluctuationDecay)
    (hVel : TrainFixedBandVelAgeJet) :
    TrainFixedBandVortAgeJet := by
  intro ρ hρ Sg hSg m ℓ j
  obtain ⟨C, N, CS, bS, ν₀, hC_pos, hbS_pos, hν₀_pos, hVel_bd⟩ := hVel ρ hρ Sg hSg m ℓ (j + 1)
  refine ⟨2 * C, N, CS, bS, ν₀, by positivity, hbS_pos, hν₀_pos, ?_⟩
  intro ν hν hν_le tr htr s hs hs_le
  let c := trainPeriod ρ ν
  have hc : 0 < c := by
    dsimp [c]
    unfold trainPeriod
    exact Real.rpow_pos_of_pos hν _
  have hsm_v : Sm (fun x : ℝ × Plane => tr.v x.1 x.2) :=
    tr.isTrain.smooth_v.mono (Set.prod_mono Set.Ioi_subset_Ici_self Subset.rfl)
  have hsm_Vc : Sm (fun x : ℝ × Plane => Vc ν c x.1 x.2) := vcSmooth_proof ν c hν hc
  let dv : ℝ → Plane → Vec := fun r z => tr.v r z - Vc ν c r z
  let dω : ℝ → Plane → ℝ := fun r z => Cyl.curl (tr.v r) z - Cyl.curl (Vc ν c r) z
  have hpt : ∀ z : Plane, ‖ageJet ℓ j dω s z‖ ≤ 2 * ‖ageJet ℓ (j + 1) dv s z‖ :=
    fun z => norm_ageJet_curl_sub_le hsm_v hsm_Vc ℓ j hs z
  obtain ⟨hL2_2m, hL2_0, hSup_0⟩ := hVel_bd ν hν hν_le tr htr s hs hs_le
  have hpoly_eq : 2 * polyP C N ν c = polyP (2 * C) N ν c := by
    unfold polyP; ring
  refine ⟨?_, ?_, ?_⟩
  · have h1 := PartI_T25.wCellL2_le_of_pointwise c (2 * m) (K := 2) (by norm_num)
      (ageJet ℓ j dω s) (ageJet ℓ (j + 1) dv s) hpt
    calc wCellL2 c (2 * m) (ageJet ℓ j dω s)
        ≤ ENNReal.ofReal 2 * wCellL2 c (2 * m) (ageJet ℓ (j + 1) dv s) := h1
      _ ≤ ENNReal.ofReal 2 * ENNReal.ofReal (polyP C N ν c) := by gcongr
      _ = ENNReal.ofReal (2 * polyP C N ν c) := by
          rw [← ENNReal.ofReal_mul (by norm_num)]
      _ = ENNReal.ofReal (polyP (2 * C) N ν c) := by
          rw [hpoly_eq]
  · have h2 := PartI_T25.wCellL2_le_of_pointwise c 0 (K := 2) (by norm_num)
      (ageJet ℓ j dω s) (ageJet ℓ (j + 1) dv s) hpt
    calc wCellL2 c 0 (ageJet ℓ j dω s)
        ≤ ENNReal.ofReal 2 * wCellL2 c 0 (ageJet ℓ (j + 1) dv s) := h2
      _ ≤ ENNReal.ofReal 2 * ENNReal.ofReal (polyP C N ν c * Real.exp (CS / ν - bS * c ^ 2)) := by
          gcongr
      _ = ENNReal.ofReal (polyP (2 * C) N ν c * Real.exp (CS / ν - bS * c ^ 2)) := by
          rw [← ENNReal.ofReal_mul (by norm_num), ← mul_assoc, hpoly_eq]
  · have h3 := PartI_T25.wSupNorm_le_of_pointwise 0 (K := 2) (by norm_num)
      (ageJet ℓ j dω s) (ageJet ℓ (j + 1) dv s) hpt
    calc wSupNorm 0 (ageJet ℓ j dω s)
        ≤ ENNReal.ofReal 2 * wSupNorm 0 (ageJet ℓ (j + 1) dv s) := h3
      _ ≤ ENNReal.ofReal 2 * ENNReal.ofReal (polyP C N ν c * Real.exp (CS / ν - bS * c ^ 2)) := by
          gcongr
      _ = ENNReal.ofReal (polyP (2 * C) N ν c * Real.exp (CS / ν - bS * c ^ 2)) := by
          rw [← ENNReal.ofReal_mul (by norm_num), ← mul_assoc, hpoly_eq]

end UnforcedLeray.Short.PartI

end
