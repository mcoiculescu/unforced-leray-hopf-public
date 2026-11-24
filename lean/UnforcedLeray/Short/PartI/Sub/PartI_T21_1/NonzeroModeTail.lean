import UnforcedLeray.Short.PartI.Sub.PartI_T21_1
import UnforcedLeray.Short.PartI.Sub.PartI_T21_1.NonzeroModeTail.LocalMP
import UnforcedLeray.Short.PartI.Sub.PartI_T21_1.ZeroModeTail.Jet1D
import UnforcedLeray.Short.PartI.Sub.PartI_T20_1.PressureStep

/-!
# `PartI:T21/1/1` (`Sub/PartI_T21_1/NonzeroModeTail.lean`): nonzero-mode stream and velocity transverse tails

Source of record: `the November 2 reference manuscript`, lines 499-503
(old 493-498), in the proof of Lemma `sct:heat`.

Proves `trainNonzeroModeStreamVelTail_proof : TrainNonzeroModeStreamVelTail` from
`hOv : TrainOverlap` and `hVort : TrainVorticityGaussianTail`:
1. **Unconditional global velocity age-jet sup bounds**:
   `PartI_T20_1.trainVorticityAndVelocityAgeJet_all` applied to `trainPressureAgeJetSupStep_proof`
   and `train_vorticity_spatial_jet_tail hOv` yields `TrainVelocityAgeJetSupBoundAt ℓ` for every
   `ℓ : ℕ`, giving a global bound `‖ageJet ℓ j tr.v s w‖ ≤ polyP C_V N_V ν c` on `Plane`.
2. **Localized nonzero-mode velocity jet bound (`trainNonzeroModeVelTail`)**:
   For each coordinate component `k : Fin 2` and word `w` of length `j` on the velocity age-slice
   `u_k(y) = iteratedDeriv ℓ (fun r => tr.v r y k) s`, the horizontal oscillation
   `vhaOsc c u_k` commutes with `B0151.derivWord w`, and `q_w = B0151.derivWord w u_k` satisfies
   `|Train.lapS q_w y| ≤ ‖ageJet ℓ (j + 1) (Cyl.curl ∘ tr.v) s y‖`. Applying
   `PartI_T21.cylPoisOscPartLocalBound_of_modeBdd` at cutoff radius `R = l / 2` on
   `|z.2| ≥ C'_ω / ν + 2 + l` bounds `‖ageJet ℓ j (fun r => hfluct c (tr.v r)) s z‖` by
   `polyPS C N ν c S_ * (exp(-(b * l / c)) + exp(-(b * l^2 / (C₀ + ν * S_))))`.
3. **Nonzero-mode stream jet bound**:
   * For `j = 0`: at fixed `s > 0` and `z : Plane`, `q ↦ iteratedDeriv ℓ (fun r => ψ̃ r (q, z.2)) s`
     is `c`-periodic with zero horizontal mean and `q`-derivative `(∂_s^ℓ ṽ)(s, (q, z.2))_1`, so
     `PartI_T22.abs_le_period_mul_of_periodic_mean_zero` bounds `‖ageJet ℓ 0 ψ̃ s z‖` by `c` times
     the `j = 0` fluctuation velocity bound along `(·, z.2)`.
   * For `j = k + 1`: `PartI_T22.norm_ageJet_streamFluct_succ_le` bounds
     `‖ageJet ℓ (k + 1) ψ̃ s z‖ ≤ 2 * ‖ageJet ℓ k (fun r => hfluct c (tr.v r)) s z‖`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Real
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec toVec toVec_zero toVec_one jet lapS)
open UnforcedLeray.Short.IIb (IsStreamPair)

namespace PartI_T21

/-! ### 1. Word-derivative commutation with `osc c` and Laplacian bound for velocity age-slices -/

/-- Horizontal oscillation operator `osc c q z = q z - hmean c q z.2` on scalar fields. -/
def osc (c : ℝ) (q : Plane → ℝ) : Plane → ℝ :=
  fun z => q z - hmean c q z.2

theorem partialX_osc {c : ℝ} (hc : 0 < c) {q : Plane → ℝ}
    (hq : ContDiff ℝ ∞ q) (hqp : UnforcedLeray.B0151.IsPeriodicQ c q) :
    UnforcedLeray.GaussianVortex.partialX (osc c q) =
      osc c (UnforcedLeray.GaussianVortex.partialX q) := by
  funext z
  have h1 : UnforcedLeray.GaussianVortex.partialX (osc c q) z =
      UnforcedLeray.GaussianVortex.partialX q z := by
    show deriv (fun x : ℝ => q (x, z.2) - hmean c q z.2) z.1 =
      deriv (fun x : ℝ => q (x, z.2)) z.1
    exact deriv_sub_const (hmean c q z.2)
  have hC2 := Cyl.C2.of_contDiff (hq.of_le (by norm_num))
  have hqp' : Cyl.IsPeriodic c q := fun w => hqp w.1 w.2
  have hint0 : ∫ x in Ioc (-c / 2) (c / 2), Cyl.partialQ q (x, z.2) = 0 :=
    cpHL_integral_partialQ_zero hc (hq.differentiable (by simp)) hC2.contQ hqp' z.2
  have hm0 : hmean c (UnforcedLeray.GaussianVortex.partialX q) z.2 = 0 := by
    unfold hmean
    change c⁻¹ • ∫ x in Ioc (-c / 2) (c / 2), Cyl.partialQ q (x, z.2) = 0
    rw [hint0, smul_zero]
  change UnforcedLeray.GaussianVortex.partialX (osc c q) z =
    UnforcedLeray.GaussianVortex.partialX q z - hmean c (UnforcedLeray.GaussianVortex.partialX q) z.2
  rw [h1, hm0, sub_zero]

theorem partialY_osc (c : ℝ) {q : Plane → ℝ} (hq : ContDiff ℝ ∞ q) :
    UnforcedLeray.GaussianVortex.partialY (osc c q) =
      osc c (UnforcedLeray.GaussianVortex.partialY q) := by
  funext z
  have hqd : Differentiable ℝ q := hq.differentiable (by simp)
  have hpath : HasDerivAt (fun y : ℝ => ((z.1, y) : Plane)) ((0 : ℝ), (1 : ℝ)) z.2 :=
    (hasDerivAt_const z.2 z.1).prodMk (hasDerivAt_id z.2)
  have hd_q : HasDerivAt (fun y : ℝ => q (z.1, y))
      (UnforcedLeray.GaussianVortex.partialY q z) z.2 :=
    ((hqd z).comp z.2 hpath.differentiableAt).hasDerivAt
  have hd_m : HasDerivAt (hmean c q)
      (hmean c (UnforcedLeray.GaussianVortex.partialY q) z.2) z.2 :=
    cpH2_hasDerivAt_hmean (hq.of_le (by norm_num)) z.2
  exact (hd_q.sub hd_m).deriv

/-- Coordinate word derivatives commute with `osc c` on smooth `c`-periodic fields. -/
theorem derivWord_osc {c : ℝ} (hc : 0 < c) {q : Plane → ℝ}
    (hq : ContDiff ℝ ∞ q) (hqp : UnforcedLeray.B0151.IsPeriodicQ c q) :
    ∀ w : List Bool,
      UnforcedLeray.B0151.derivWord w (osc c q) =
        osc c (UnforcedLeray.B0151.derivWord w q)
  | [] => rfl
  | true :: w => by
    show UnforcedLeray.GaussianVortex.partialX (UnforcedLeray.B0151.derivWord w (osc c q)) =
      osc c (UnforcedLeray.GaussianVortex.partialX (UnforcedLeray.B0151.derivWord w q))
    rw [derivWord_osc hc hq hqp w]
    exact partialX_osc hc (UnforcedLeray.B0151.contDiff_derivWord hq w)
      (UnforcedLeray.B0151.periodic_derivWord hqp w)
  | false :: w => by
    show UnforcedLeray.GaussianVortex.partialY (UnforcedLeray.B0151.derivWord w (osc c q)) =
      osc c (UnforcedLeray.GaussianVortex.partialY (UnforcedLeray.B0151.derivWord w q))
    rw [derivWord_osc hc hq hqp w]
    exact partialY_osc c (UnforcedLeray.B0151.contDiff_derivWord hq w)

/-- Pointwise identity `iteratedDeriv ℓ (fun r => (hfluct c (tr.v r) z) k) s = osc c u_k z`
for `u_k(w) = iteratedDeriv ℓ (fun r => tr.v r w k) s`. -/
theorem iteratedDeriv_hfluct_v_comp_eq {ν c : ℝ} (hc : 0 < c)
    (tr : B0140.TrainSol ν c) (k : Fin 2) (ℓ : ℕ) {s : ℝ} (hs : 0 < s) (z : Plane) :
    iteratedDeriv ℓ (fun r => (hfluct c (tr.v r) z) k) s =
      osc c (fun w => iteratedDeriv ℓ (fun r => tr.v r w k) s) z := by
  have hv_joint : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => tr.v x.1 x.2) (Ioi 0 ×ˢ univ) :=
    tr.isTrain.smooth_v.mono (prod_mono Ioi_subset_Ici_self Subset.rfl)
  have hvk_sm : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => tr.v x.1 x.2 k) (Ioi 0 ×ˢ univ) :=
    (EuclideanSpace.proj k : Vec →L[ℝ] ℝ).contDiff.comp_contDiffOn hv_joint
  have hmk_sm : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => hmean c (fun w => tr.v x.1 w k) x.2.2)
      (Ioi 0 ×ˢ univ) :=
    contDiffOn_snd_lift (g := fun r η => hmean c (fun w => tr.v r w k) η)
      (hmeanContDiff c hc (fun r w => tr.v r w k) hvk_sm)
  have hev : (fun r => (hfluct c (tr.v r) z) k) =ᶠ[𝓝 s]
      fun r => tr.v r z k - hmean c (fun w => tr.v r w k) z.2 := by
    filter_upwards [Ioi_mem_nhds hs] with r hr
    have hvc : Continuous (tr.v r) := (bucVel_vslice_contDiff tr hr.le).continuous
    change (tr.v r z - hmean c (tr.v r) z.2) k = _
    rw [PiLp.sub_apply, PartI_T22.hmean_apply_vec' c hvc z.2 k]
  have hsub := iteratedDeriv_sub
    (PartI_T22.contDiffAt_age_slice (F := fun r w => tr.v r w k) hvk_sm hs z ℓ)
    (PartI_T22.contDiffAt_age_slice (F := fun r w => hmean c (fun y => tr.v r y k) w.2) hmk_sm hs z ℓ)
  rw [hev.iteratedDeriv_eq ℓ]
  exact hsub.trans (by rw [iteratedDeriv_hmean_scalar_eq hc hvk_sm ℓ hs z.2]; rfl)

/-- Pointwise Laplacian bound `|Train.lapS (B0151.derivWord w u_k) z| ≤ ‖ageJet ℓ (j + 1) (Cyl.curl ∘ tr.v) s z‖`
for any coordinate word `w` of length `j` on the velocity age-slice `u_k`. -/
theorem norm_lapS_derivWord_velSlice_le {ν c : ℝ} (tr : B0140.TrainSol ν c)
    (k : Fin 2) (ℓ j : ℕ) {s : ℝ} (hs : 0 < s) {w : List Bool} (hw : w.length = j) (z : Plane) :
    |Train.lapS (UnforcedLeray.B0151.derivWord w (fun y => iteratedDeriv ℓ (fun r => tr.v r y k) s)) z| ≤
      ‖ageJet ℓ (j + 1) (fun r y => Cyl.curl (tr.v r) y) s z‖ := by
  let u0 : Plane → ℝ := fun y => iteratedDeriv ℓ (fun r => tr.v r y 0) s
  let u1 : Plane → ℝ := fun y => iteratedDeriv ℓ (fun r => tr.v r y 1) s
  let vom : Plane → ℝ := fun y => iteratedDeriv ℓ (fun r => Cyl.curl (tr.v r) y) s
  have hv_joint : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => tr.v x.1 x.2) (Ioi 0 ×ˢ univ) :=
    tr.isTrain.smooth_v.mono (prod_mono Ioi_subset_Ici_self Subset.rfl)
  have hv0_sm : PartI_T20.SmR (fun x : ℝ × Plane => tr.v x.1 x.2 0) :=
    (EuclideanSpace.proj (0 : Fin 2) : Vec →L[ℝ] ℝ).contDiff.comp_contDiffOn hv_joint
  have hv1_sm : PartI_T20.SmR (fun x : ℝ × Plane => tr.v x.1 x.2 1) :=
    (EuclideanSpace.proj (1 : Fin 2) : Vec →L[ℝ] ℝ).contDiff.comp_contDiffOn hv_joint
  have hvom_sm : PartI_T20.SmR (fun x : ℝ × Plane => Cyl.curl (tr.v x.1) x.2) :=
    PartI_T20.smR_curl hv_joint
  have hu0 : ContDiff ℝ ∞ u0 := PartI_T22.contDiff_slice_iteratedDeriv hv0_sm ℓ hs
  have hu1 : ContDiff ℝ ∞ u1 := PartI_T22.contDiff_slice_iteratedDeriv hv1_sm ℓ hs
  have hvoms : ContDiff ℝ ∞ vom := PartI_T22.contDiff_slice_iteratedDeriv hvom_sm ℓ hs
  have hQ1 : PartI_T20.SmR (fun x : ℝ × Plane => Cyl.partialQ (fun y => tr.v x.1 y 1) x.2) :=
    PartI_T20.smR_partialQ (F := fun r y => tr.v r y 1) hv1_sm
  have hE0 : PartI_T20.SmR (fun x : ℝ × Plane => Cyl.partialEta (fun y => tr.v x.1 y 0) x.2) :=
    PartI_T20.smR_partialEta (F := fun r y => tr.v r y 0) hv0_sm
  have hQ0 : PartI_T20.SmR (fun x : ℝ × Plane => Cyl.partialQ (fun y => tr.v x.1 y 0) x.2) :=
    PartI_T20.smR_partialQ (F := fun r y => tr.v r y 0) hv0_sm
  have hE1 : PartI_T20.SmR (fun x : ℝ × Plane => Cyl.partialEta (fun y => tr.v x.1 y 1) x.2) :=
    PartI_T20.smR_partialEta (F := fun r y => tr.v r y 1) hv1_sm
  have hvom_eq : vom = fun y => UnforcedLeray.B0151.derivWord [true] u1 y -
      UnforcedLeray.B0151.derivWord [false] u0 y := by
    funext y
    have hsub := iteratedDeriv_sub
      (PartI_T22.contDiffAt_age_slice (F := fun r w => Cyl.partialQ (fun x => tr.v r x 1) w) hQ1 hs y ℓ)
      (PartI_T22.contDiffAt_age_slice (F := fun r w => Cyl.partialEta (fun x => tr.v r x 0) w) hE0 hs y ℓ)
    change iteratedDeriv ℓ (fun r => Cyl.partialQ (fun x => tr.v r x 1) y -
      Cyl.partialEta (fun x => tr.v r x 0) y) s =
      Cyl.partialQ u1 y - Cyl.partialEta u0 y
    exact hsub.trans (by
      rw [PartI_T20.iteratedDeriv_partialQ_eq (F := fun r x => tr.v r x 1) hv1_sm ℓ hs y,
        PartI_T20.iteratedDeriv_partialEta_eq (F := fun r x => tr.v r x 0) hv0_sm ℓ hs y])
  have hdiv : ∀ y, UnforcedLeray.B0151.derivWord [true] u0 y +
      UnforcedLeray.B0151.derivWord [false] u1 y = 0 := by
    intro y
    have hadd := iteratedDeriv_add
      (PartI_T22.contDiffAt_age_slice (F := fun r w => Cyl.partialQ (fun x => tr.v r x 0) w) hQ0 hs y ℓ)
      (PartI_T22.contDiffAt_age_slice (F := fun r w => Cyl.partialEta (fun x => tr.v r x 1) w) hE1 hs y ℓ)
    change Cyl.partialQ u0 y + Cyl.partialEta u1 y = 0
    rw [← PartI_T20.iteratedDeriv_partialQ_eq (F := fun r x => tr.v r x 0) hv0_sm ℓ hs y,
      ← PartI_T20.iteratedDeriv_partialEta_eq (F := fun r x => tr.v r x 1) hv1_sm ℓ hs y,
      ← hadd]
    have hev : ((fun r => Cyl.partialQ (fun x => tr.v r x 0) y) +
        fun r => Cyl.partialEta (fun x => tr.v r x 1) y) =ᶠ[𝓝 s] fun _ => (0 : ℝ) := by
      filter_upwards [Ioi_mem_nhds hs] with r hr using tr.isTrain.solenoidal r hr.le y
    rw [hev.iteratedDeriv_eq ℓ, iteratedDeriv_const]
    split_ifs <;> rfl
  obtain ⟨hL0, hL1⟩ := vwl_lap_pair u0 u1 vom hu0 hu1 hvom_eq hdiv
  fin_cases k
  · have hcomm : Train.lapS (UnforcedLeray.B0151.derivWord w u0) =
        UnforcedLeray.B0151.derivWord w (Train.lapS u0) :=
      (derivWordLapComm_proof u0 hu0 w).symm
    have hcons : UnforcedLeray.B0151.derivWord (false :: w) vom =
        UnforcedLeray.B0151.derivWord w (UnforcedLeray.B0151.derivWord [false] vom) :=
      vwl_cons_false vom hvoms w
    have hlap_w : Train.lapS (UnforcedLeray.B0151.derivWord w u0) z =
        -UnforcedLeray.B0151.derivWord (false :: w) vom z := by
      rw [hcomm, hL0, vwl_derivWord_neg, hcons]
    change |Train.lapS (UnforcedLeray.B0151.derivWord w u0) z| ≤ ‖iteratedFDeriv ℝ (j + 1) vom z‖
    rw [hlap_w, abs_neg]
    exact (cylJetWord_proof vom hvoms (j + 1) z).1 (false :: w) (by simp [hw])
  · have hcomm : Train.lapS (UnforcedLeray.B0151.derivWord w u1) =
        UnforcedLeray.B0151.derivWord w (Train.lapS u1) :=
      (derivWordLapComm_proof u1 hu1 w).symm
    have hcons : UnforcedLeray.B0151.derivWord (true :: w) vom =
        UnforcedLeray.B0151.derivWord w (UnforcedLeray.B0151.derivWord [true] vom) :=
      vwl_cons_true vom hvoms w
    have hlap_w : Train.lapS (UnforcedLeray.B0151.derivWord w u1) z =
        UnforcedLeray.B0151.derivWord (true :: w) vom z := by
      rw [hcomm, hL1, hcons]
    change |Train.lapS (UnforcedLeray.B0151.derivWord w u1) z| ≤ ‖iteratedFDeriv ℝ (j + 1) vom z‖
    rw [hlap_w]
    exact (cylJetWord_proof vom hvoms (j + 1) z).1 (true :: w) (by simp [hw])

/-! ### 2. Localized bound on `‖ageJet ℓ j (fun r => hfluct c (tr.v r)) s z‖` -/

/-- Pointwise localized bound on `‖ageJet ℓ j (fun r => hfluct c (tr.v r)) s z‖` at cutoff radius
`R ≥ 0` from global vorticity jet bound `G_all`, local vorticity jet bound `G_far` on
`|w.2 - z.2| ≤ R`, and global velocity jet bound `M_v`. -/
theorem norm_ageJet_hfluct_v_local_le
    {ν c R G_all G_far M_v : ℝ} (hc : 0 < c) (hR : 0 ≤ R)
    (hG_all : 0 ≤ G_all) (hG_far : 0 ≤ G_far) (_hM_v : 0 ≤ M_v)
    (tr : B0140.TrainSol ν c) (ℓ j : ℕ) {s : ℝ} (hs : 0 < s) (z : Plane)
    (hω_all : ∀ w : Plane, ‖ageJet ℓ (j + 1) (fun r y => Cyl.curl (tr.v r) y) s w‖ ≤ G_all)
    (hω_far : ∀ w : Plane, |w.2 - z.2| ≤ R →
      ‖ageJet ℓ (j + 1) (fun r y => Cyl.curl (tr.v r) y) s w‖ ≤ G_far)
    (hVel_bdd : ∀ w : Plane, ‖ageJet ℓ j tr.v s w‖ ≤ M_v) :
    let B_loc : ℝ :=
      ((G_far + 2 * G_all * Real.exp (-(2 * Real.pi * R / c))) * c ^ 2 / (2 * Real.pi ^ 2)) *
        (∑' n : ℤ, 1 / (n : ℝ) ^ 2)
    ‖ageJet ℓ j (fun r => hfluct c (tr.v r)) s z‖ ≤ 2 * (2 : ℝ) ^ j * B_loc := by
  intro B_loc
  have hv_fl_sm : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => hfluct c (tr.v x.1) x.2) (Ioi 0 ×ˢ univ) :=
    PartI_T22.contDiffOn_hfluct_v hc tr
  have hv_joint : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => tr.v x.1 x.2) (Ioi 0 ×ˢ univ) :=
    tr.isTrain.smooth_v.mono (prod_mono Ioi_subset_Ici_self Subset.rfl)
  have hcomp_le : ∀ k : Fin 2,
      ‖ageJet ℓ j (fun r w => (hfluct c (tr.v r) w) k) s z‖ ≤
        (2 : ℝ) ^ j * B_loc := by
    intro k
    let u_k : Plane → ℝ := fun w => iteratedDeriv ℓ (fun r => tr.v r w k) s
    let u_fl_k : Plane → ℝ := fun w => iteratedDeriv ℓ (fun r => (hfluct c (tr.v r) w) k) s
    have hvk_sm : PartI_T20.SmR (fun x : ℝ × Plane => tr.v x.1 x.2 k) :=
      (EuclideanSpace.proj k : Vec →L[ℝ] ℝ).contDiff.comp_contDiffOn hv_joint
    have hvflk_sm : PartI_T20.SmR (fun x : ℝ × Plane => (hfluct c (tr.v x.1) x.2) k) :=
      (EuclideanSpace.proj k : Vec →L[ℝ] ℝ).contDiff.comp_contDiffOn hv_fl_sm
    have hu_k : ContDiff ℝ ∞ u_k := PartI_T22.contDiff_slice_iteratedDeriv hvk_sm ℓ hs
    have hu_fl_k : ContDiff ℝ ∞ u_fl_k := PartI_T22.contDiff_slice_iteratedDeriv hvflk_sm ℓ hs
    have hu_k_per : UnforcedLeray.B0151.IsPeriodicQ c u_k := by
      intro q η
      have hev : (fun r => tr.v r (q + c, η) k) =ᶠ[𝓝 s] (fun r => tr.v r (q, η) k) := by
        filter_upwards [Ioi_mem_nhds hs] with r hr
        exact congrArg (fun u : Vec => u k) (tr.isTrain.periodic_v r hr.le (q, η))
      exact hev.iteratedDeriv_eq ℓ
    have hu_fl_eq : u_fl_k = osc c u_k :=
      funext fun w => iteratedDeriv_hfluct_v_comp_eq hc tr k ℓ hs w
    refine UnforcedLeray.Short.Spine.norm_iteratedFDeriv_le_of_derivWord hu_fl_k j z (fun w hw => ?_)
    rw [hu_fl_eq, derivWord_osc hc hu_k hu_k_per w]
    let q_w : Plane → ℝ := UnforcedLeray.B0151.derivWord w u_k
    have hq_w_cd : ContDiff ℝ ∞ q_w := UnforcedLeray.B0151.contDiff_derivWord hu_k w
    have hq_w_perQ : UnforcedLeray.B0151.IsPeriodicQ c q_w :=
      UnforcedLeray.B0151.periodic_derivWord hu_k_per w
    have hq_w_per : Cyl.IsPeriodic c q_w := fun y => hq_w_perQ y.1 y.2
    have hLap_all : ∀ y : Plane, |Train.lapS q_w y| ≤ G_all :=
      fun y => (norm_lapS_derivWord_velSlice_le tr k ℓ j hs hw y).trans (hω_all y)
    have hLap_far : ∀ y : Plane, |y.2 - z.2| ≤ R → |Train.lapS q_w y| ≤ G_far :=
      fun y hy => (norm_lapS_derivWord_velSlice_le tr k ℓ j hs hw y).trans (hω_far y hy)
    have hBdd_qw : ∀ (n : ℤ), n ≠ 0 →
        ∃ B : ℝ, ∀ η : ℝ, ‖Cyl.qMode c hc n (fun y : Plane => ((q_w y : ℝ) : ℂ)) η‖ ≤ B := by
      intro n _hn
      refine ⟨M_v, fun η => ?_⟩
      refine (cylPoisQModeEstimates c hc n (fun y : Plane => ((q_w y : ℝ) : ℂ))).1 M_v
        (fun y => ?_) η
      rw [Complex.norm_real, Real.norm_eq_abs]
      have h1 : |q_w y| ≤ ‖iteratedFDeriv ℝ j u_k y‖ :=
        (cylJetWord_proof u_k hu_k j y).1 w hw
      have h2 : ‖iteratedFDeriv ℝ j u_k y‖ ≤ ‖ageJet ℓ j tr.v s y‖ :=
        PartI_T20.norm_ageJet_vec_proj_le hv_joint k ℓ j hs y
      exact (h1.trans h2).trans (hVel_bdd y)
    exact cylPoisOscPartLocalBound_of_modeBdd hc hR hG_all hG_far
      (hq_w_cd.of_le (by norm_num)) hq_w_per z hLap_all hLap_far hBdd_qw
  have hvec := PartI_T20_1.norm_ageJet_vec_le_add_proj
    (V := fun r w => hfluct c (tr.v r) w) hv_fl_sm ℓ j hs z
  have h0 := hcomp_le 0
  have h1 := hcomp_le 1
  linarith

/-- Gaussian tail comparison on the local ball `|w.2 - z.2| ≤ l / 2` when `|z.2| ≥ C'_ω / ν + 2 + l`. -/
theorem vort_local_ball_tail_le
    {b_ω b C₀_ω C'_ω ν l s S_ : ℝ}
    (hb_ω : 0 < b_ω) (_hb : 0 < b) (hb_le : b ≤ b_ω / 4)
    (hC₀_ω : 0 < C₀_ω) (_hC'_ω : 0 < C'_ω) (hν : 0 < ν) (hl : 0 ≤ l)
    (hs : 0 < s) (hsS : s ≤ S_) {z w : Plane}
    (hz : C'_ω / ν + 2 + l ≤ |z.2|) (hw : |w.2 - z.2| ≤ l / 2) :
    Real.exp (-(b_ω * (max (|w.2| - C'_ω / ν) 0) ^ 2 / (C₀_ω + ν * s))) ≤
      Real.exp (-(b * l ^ 2 / (C₀_ω + ν * S_))) := by
  have hw_abs : |z.2| - |w.2 - z.2| ≤ |w.2| := by
    have h1 : w.2 - (w.2 - z.2) = z.2 := by ring
    have h2 : |w.2 - (w.2 - z.2)| ≤ |w.2| + |w.2 - z.2| := abs_sub w.2 (w.2 - z.2)
    rw [h1] at h2
    linarith
  have hw_ge : l / 2 ≤ |w.2| - C'_ω / ν := by linarith
  have hd_ge : l / 2 ≤ max (|w.2| - C'_ω / ν) 0 := hw_ge.trans (le_max_left _ _)
  have hsq : (l / 2) ^ 2 ≤ (max (|w.2| - C'_ω / ν) 0) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hd_ge 2
  have hnum : b * l ^ 2 ≤ b_ω * (max (|w.2| - C'_ω / ν) 0) ^ 2 := by
    calc b * l ^ 2
        ≤ (b_ω / 4) * l ^ 2 := mul_le_mul_of_nonneg_right hb_le (sq_nonneg l)
      _ = b_ω * (l / 2) ^ 2 := by ring
      _ ≤ b_ω * (max (|w.2| - C'_ω / ν) 0) ^ 2 := mul_le_mul_of_nonneg_left hsq hb_ω.le
  have hden_pos : 0 < C₀_ω + ν * s := by positivity
  have hden_le : C₀_ω + ν * s ≤ C₀_ω + ν * S_ :=
    add_le_add le_rfl (mul_le_mul_of_nonneg_left hsS hν.le)
  apply Real.exp_le_exp.2
  apply neg_le_neg
  exact div_le_div₀ (by positivity) hnum hden_pos hden_le

/-- Algebraic envelope bound assembling the localized Poisson bound into `polyPS C_out N_out ν c S_ * E`. -/
theorem fluct_vel_envelope_le
    {C_ω S_zeta b l c ν S_ E_lin E_gauss : ℝ} {N_ω j : ℕ}
    (hC_ω : 0 < C_ω) (hS_nn : 0 ≤ S_zeta)
    (hb_pi : b ≤ Real.pi) (hl : 0 ≤ l) (hc : 0 < c) (hν : 0 < ν) (hS_ : 0 ≤ S_)
    (hE_lin_nn : 0 ≤ E_lin) (hE_gauss_nn : 0 ≤ E_gauss)
    (hE_lin_ge : E_lin = Real.exp (-(b * l / c))) :
    let E : ℝ := E_lin + E_gauss
    let G_all : ℝ := polyP C_ω N_ω ν c
    let G_far : ℝ := G_all * E_gauss
    let B_loc : ℝ :=
      ((G_far + 2 * G_all * Real.exp (-(2 * Real.pi * (l / 2) / c))) * c ^ 2 / (2 * Real.pi ^ 2)) *
        S_zeta
    let C_out : ℝ := 2 * (2 : ℝ) ^ j * (C_ω / Real.pi ^ 2) * S_zeta + 1
    let N_out : ℕ := N_ω + 2
    2 * (2 : ℝ) ^ j * B_loc ≤ polyPS C_out N_out ν c S_ * E := by
  intro E G_all G_far B_loc C_out N_out
  have hE_nn : 0 ≤ E := add_nonneg hE_lin_nn hE_gauss_nn
  have hG_all_nn : 0 ≤ G_all := by dsimp [G_all]; unfold polyP; positivity
  have hexp_le : Real.exp (-(2 * Real.pi * (l / 2) / c)) ≤ E_lin := by
    rw [hE_lin_ge]
    apply Real.exp_le_exp.2
    apply neg_le_neg
    have h1 : b * l ≤ 2 * Real.pi * (l / 2) := by
      calc b * l ≤ Real.pi * l := mul_le_mul_of_nonneg_right hb_pi hl
        _ = 2 * Real.pi * (l / 2) := by ring
    exact div_le_div_of_nonneg_right h1 hc.le
  have hsum_G : G_far + 2 * G_all * Real.exp (-(2 * Real.pi * (l / 2) / c)) ≤
      2 * G_all * E := by
    have h1 : 2 * G_all * Real.exp (-(2 * Real.pi * (l / 2) / c)) ≤ 2 * G_all * E_lin :=
      mul_le_mul_of_nonneg_left hexp_le (by positivity)
    have h2 : G_far ≤ 2 * G_all * E_gauss := by
      dsimp [G_far]
      have : 1 * (G_all * E_gauss) ≤ 2 * (G_all * E_gauss) :=
        mul_le_mul_of_nonneg_right (by norm_num) (mul_nonneg hG_all_nn hE_gauss_nn)
      linarith
    calc G_far + 2 * G_all * Real.exp (-(2 * Real.pi * (l / 2) / c))
        ≤ 2 * G_all * E_gauss + 2 * G_all * E_lin := add_le_add h2 h1
      _ = 2 * G_all * E := by dsimp [E]; ring
  have hB_loc_le : B_loc ≤ (S_zeta / Real.pi ^ 2) * (c ^ 2 * G_all) * E := by
    dsimp [B_loc]
    calc ((G_far + 2 * G_all * Real.exp (-(2 * Real.pi * (l / 2) / c))) * c ^ 2 /
            (2 * Real.pi ^ 2)) * S_zeta
        ≤ ((2 * G_all * E) * c ^ 2 / (2 * Real.pi ^ 2)) * S_zeta := by
          apply mul_le_mul_of_nonneg_right _ hS_nn
          apply div_le_div_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_right hsum_G (sq_nonneg c)
      _ = (S_zeta / Real.pi ^ 2) * (c ^ 2 * G_all) * E := by ring
  let X : ℝ := 1 + c + ν⁻¹
  let Y : ℝ := X * (1 + S_)
  have h1X : 1 ≤ X := by
    dsimp [X]
    have : 0 ≤ ν⁻¹ := inv_nonneg.2 hν.le
    linarith
  have h1S : 1 ≤ 1 + S_ := by linarith
  have h1Y : 1 ≤ Y := one_le_mul_of_one_le_of_one_le h1X h1S
  have hXY : X ≤ Y := by
    dsimp [Y]
    exact le_mul_of_one_le_right (by linarith) h1S
  have hcY : c ≤ Y := by
    have hcX : c ≤ X := by
      dsimp [X]
      have : 0 ≤ ν⁻¹ := inv_nonneg.2 hν.le
      linarith
    exact hcX.trans hXY
  have hc2 : c ^ 2 ≤ Y ^ 2 := pow_le_pow_left₀ hc.le hcY 2
  have hpow_ω : X ^ N_ω ≤ Y ^ N_ω := pow_le_pow_left₀ (by linarith) hXY N_ω
  have hc2_G : c ^ 2 * G_all ≤ C_ω * Y ^ N_out := by
    dsimp [G_all, N_out]
    unfold polyP
    change c ^ 2 * (C_ω * X ^ N_ω) ≤ C_ω * Y ^ (N_ω + 2)
    calc c ^ 2 * (C_ω * X ^ N_ω)
        = C_ω * (c ^ 2 * X ^ N_ω) := by ring
      _ ≤ C_ω * (Y ^ 2 * Y ^ N_ω) := by
          apply mul_le_mul_of_nonneg_left _ hC_ω.le
          exact mul_le_mul hc2 hpow_ω (by positivity) (by positivity)
      _ = C_ω * Y ^ (N_ω + 2) := by rw [pow_add]; ring
  calc 2 * (2 : ℝ) ^ j * B_loc
      ≤ 2 * (2 : ℝ) ^ j * ((S_zeta / Real.pi ^ 2) * (c ^ 2 * G_all) * E) :=
        mul_le_mul_of_nonneg_left hB_loc_le (by positivity)
    _ = (2 * (2 : ℝ) ^ j * (S_zeta / Real.pi ^ 2)) * (c ^ 2 * G_all) * E := by ring
    _ ≤ (2 * (2 : ℝ) ^ j * (S_zeta / Real.pi ^ 2)) * (C_ω * Y ^ N_out) * E := by
        apply mul_le_mul_of_nonneg_right _ hE_nn
        exact mul_le_mul_of_nonneg_left hc2_G (by positivity)
    _ = (2 * (2 : ℝ) ^ j * (C_ω / Real.pi ^ 2) * S_zeta) * Y ^ N_out * E := by ring
    _ ≤ C_out * Y ^ N_out * E := by
        apply mul_le_mul_of_nonneg_right _ hE_nn
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        dsimp [C_out]
        linarith
    _ = polyPS C_out N_out ν c S_ * E := rfl

/-- **Nonzero-mode velocity transverse tail (`trainNonzeroModeVelTail`)**:
for every `ρ > 1/2` and `ℓ, j : ℕ`, `‖ageJet ℓ j (fun r => hfluct c (tr.v r)) s z‖` satisfies
the combined `exp(-(b * l / c)) + exp(-(b * l^2 / (C₀ + ν * S_)))` tail bound on
`|z.2| ≥ C' / ν + 2 + l`. -/
theorem trainNonzeroModeVelTail
    (hOv : TrainOverlap)
    (hVort : TrainVorticityGaussianTail)
    (ρ : ℝ) (hρ : 1 / 2 < ρ) (ℓ j : ℕ) :
    ∃ b C₀ C' : ℝ, 0 < b ∧ 0 < C₀ ∧ 0 < C' ∧
      ∃ C : ℝ, ∃ N : ℕ, ∃ ν₀ : ℝ, 0 < C ∧ 0 < ν₀ ∧
        ∀ S_ : ℝ, 0 ≤ S_ →
          ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
            ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr →
              ∀ l : ℝ, 0 ≤ l →
                ∀ s : ℝ, 0 < s → s ≤ S_ →
                  ∀ z : Plane, C' / ν + 2 + l ≤ |z.2| →
                    let c := trainPeriod ρ ν
                    let E := Real.exp (-(b * l / c)) + Real.exp (-(b * l ^ 2 / (C₀ + ν * S_)))
                    ‖ageJet ℓ j (fun r => hfluct c (tr.v r)) s z‖ ≤
                      polyPS C N ν c S_ * E := by
  obtain ⟨b_ω, C₀_ω, C'_ω, hb_ω, hC₀_ω, hC'_ω, C_ω, N_ω, ν_ω, hC_ω, hν_ω, hW⟩ :=
    hVort ρ hρ ℓ (j + 1)
  have hAll := PartI_T20_1.trainVorticityAndVelocityAgeJet_all
    trainPressureAgeJetSupStep_proof hOv (train_vorticity_spatial_jet_tail hOv)
  obtain ⟨C_V, N_V, ν_V, _hC_V, hν_V, hVel⟩ := (hAll ℓ).2 ρ hρ j
  let b : ℝ := min (b_ω / 4) Real.pi
  let C₀ : ℝ := C₀_ω
  let C' : ℝ := C'_ω
  have hb : 0 < b := lt_min (by positivity) Real.pi_pos
  let S_zeta : ℝ := ∑' n : ℤ, 1 / (n : ℝ) ^ 2
  have hS_nn : 0 ≤ S_zeta := tsum_nonneg fun n => by positivity
  let C_out : ℝ := 2 * (2 : ℝ) ^ j * (C_ω / Real.pi ^ 2) * S_zeta + 1
  let N_out : ℕ := N_ω + 2
  let ν₀ : ℝ := min ν_ω ν_V
  have hC_out : 0 < C_out := by dsimp [C_out]; positivity
  refine ⟨b, C₀, C', hb, hC₀_ω, hC'_ω, C_out, N_out, ν₀, hC_out, lt_min hν_ω hν_V, ?_⟩
  intro S_ hS_ ν hν hν_le tr htr l hl s hs hsS z hz
  have hν_ω_le : ν ≤ ν_ω := hν_le.trans (min_le_left _ _)
  have hν_V_le : ν ≤ ν_V := hν_le.trans (min_le_right _ _)
  let c : ℝ := trainPeriod ρ ν
  have hc : 0 < c := Real.rpow_pos_of_pos hν _
  let E_lin : ℝ := Real.exp (-(b * l / c))
  let E_gauss : ℝ := Real.exp (-(b * l ^ 2 / (C₀ + ν * S_)))
  let E : ℝ := E_lin + E_gauss
  let G_all : ℝ := polyP C_ω N_ω ν c
  let G_far : ℝ := G_all * E_gauss
  let M_v : ℝ := polyP C_V N_V ν c
  have hG_all_nn : 0 ≤ G_all := by dsimp [G_all]; unfold polyP; positivity
  have hG_far_nn : 0 ≤ G_far := mul_nonneg hG_all_nn (Real.exp_nonneg _)
  have hM_v_nn : 0 ≤ M_v := by dsimp [M_v]; unfold polyP; positivity
  have hω_all : ∀ w : Plane, ‖ageJet ℓ (j + 1) (fun r y => Cyl.curl (tr.v r) y) s w‖ ≤ G_all := by
    intro w
    have hw := hW ν hν hν_ω_le tr htr s hs w
    have hexp1 : Real.exp (-(b_ω * (max (|w.2| - C'_ω / ν) 0) ^ 2 / (C₀_ω + ν * s))) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have h1 : 0 ≤ b_ω * (max (|w.2| - C'_ω / ν) 0) ^ 2 / (C₀_ω + ν * s) :=
        div_nonneg (mul_nonneg hb_ω.le (sq_nonneg _)) (by positivity)
      linarith
    exact hw.trans (mul_le_of_le_one_right hG_all_nn hexp1)
  have hω_far : ∀ w : Plane, |w.2 - z.2| ≤ l / 2 →
      ‖ageJet ℓ (j + 1) (fun r y => Cyl.curl (tr.v r) y) s w‖ ≤ G_far := by
    intro w hw_dist
    have hw := hW ν hν hν_ω_le tr htr s hs w
    have htail := vort_local_ball_tail_le hb_ω hb (min_le_left _ _) hC₀_ω hC'_ω hν hl hs hsS hz hw_dist
    exact hw.trans (mul_le_mul_of_nonneg_left htail hG_all_nn)
  have hVel_bdd : ∀ w : Plane, ‖ageJet ℓ j tr.v s w‖ ≤ M_v :=
    fun w => hVel ν hν hν_V_le tr htr s hs w
  have hloc := norm_ageJet_hfluct_v_local_le hc (by positivity : 0 ≤ l / 2)
    hG_all_nn hG_far_nn hM_v_nn tr ℓ j hs z hω_all hω_far hVel_bdd
  have henv := fluct_vel_envelope_le (b := b) (E_lin := E_lin) (E_gauss := E_gauss)
    (N_ω := N_ω) (j := j) hC_ω hS_nn
    (min_le_right _ _) hl hc hν hS_ (Real.exp_nonneg _) (Real.exp_nonneg _) rfl
  exact hloc.trans henv

/-! ### 3. Pointwise `j = 0` stream fluctuation bound along a horizontal line -/

/-- For `j = 0` and any `ℓ : ℕ`, `s > 0`, `z : Plane`, if
`∀ q : ℝ, ‖ageJet ℓ 0 (fun r => hfluct c (tr.v r)) s (q, z.2)‖ ≤ B` (`B ≥ 0`), then
`‖ageJet ℓ 0 (fun r w => tr.ψ r w - meanStream tr r w.2) s z‖ ≤ c * B`. -/
theorem norm_ageJet_streamFluct_zero_le {ν c B : ℝ}
    (hν : 0 < ν) (hc : 0 < c) (hB : 0 ≤ B)
    (tr : B0140.TrainSol ν c) (ℓ : ℕ) {s : ℝ} (hs : 0 < s) (z : Plane)
    (hV_line : ∀ q : ℝ, ‖ageJet ℓ 0 (fun r => hfluct c (tr.v r)) s (q, z.2)‖ ≤ B) :
    ‖ageJet ℓ 0 (fun r w => tr.ψ r w - meanStream tr r w.2) s z‖ ≤ c * B := by
  let ψ_fluct : ℝ → Plane → ℝ := fun r w => tr.ψ r w - hmean c (tr.ψ r) w.2
  let v_fluct : ℝ → Plane → Vec := fun r => hfluct c (tr.v r)
  have hsp : IsStreamPair ψ_fluct v_fluct := PartI_T22.isStreamPair_ψ_fluct_v_fluct hν hc tr
  unfold ageJet jet
  rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]
  let g : ℝ → ℝ := fun q => iteratedDeriv ℓ (fun r => ψ_fluct r (q, z.2)) s
  let g' : ℝ → ℝ := fun q => iteratedDeriv ℓ (fun r => v_fluct r (q, z.2)) s 1
  have hper : Function.Periodic g c := by
    intro q
    have hev : (fun r => ψ_fluct r (q + c, z.2)) =ᶠ[𝓝 s] (fun r => ψ_fluct r (q, z.2)) := by
      filter_upwards [Ioi_mem_nhds hs] with r hr
      dsimp [ψ_fluct]
      rw [PartI_T22.stream_periodic_q tr hr q z.2]
    exact hev.iteratedDeriv_eq ℓ
  have hmean0 : hmean c (fun w : Plane => g w.1) 0 = 0 :=
    PartI_T22.hmean_iteratedDeriv_eq_zero hc hsp.1
      (fun r hr η => PartI_T22.hmean_ψ_fluct_eq_zero hc tr hr η) ℓ hs z.2
  have hderiv : ∀ q : ℝ, HasDerivAt g (g' q) q :=
    fun q => _root_.psiQSwap_proof ψ_fluct v_fluct hsp ℓ s hs q z.2
  have hcont_V : Continuous (fun w : Plane => iteratedDeriv ℓ (fun r => v_fluct r w) s) :=
    (PartI_T22.contDiff_slice_iteratedDeriv hsp.2.1 ℓ hs).continuous
  have hcont' : Continuous g' :=
    ((PiLp.continuous_apply _ _ 1).comp hcont_V).comp (continuous_id.prodMk continuous_const)
  have hbound : ∀ q : ℝ, |g' q| ≤ B := by
    intro q
    have h1 : |g' q| ≤ ‖iteratedDeriv ℓ (fun r => v_fluct r (q, z.2)) s‖ := by
      simpa [Real.norm_eq_abs] using
        PiLp.norm_apply_le (iteratedDeriv ℓ (fun r => v_fluct r (q, z.2)) s) 1
    have h2 : ‖iteratedDeriv ℓ (fun r => v_fluct r (q, z.2)) s‖ =
        ‖ageJet ℓ 0 v_fluct s (q, z.2)‖ := by
      unfold ageJet jet
      rw [norm_iteratedFDeriv_zero]
    exact h1.trans (h2.symm ▸ hV_line q)
  exact PartI_T22.abs_le_period_mul_of_periodic_mean_zero hc hB hper hmean0 hderiv hcont' hbound z.1

end PartI_T21

open PartI_T21 in
/-- **Target theorem (`PartI:T21/1/1`)**: nonzero-mode stream and velocity transverse tails
`TrainNonzeroModeStreamVelTail` from `hOv : TrainOverlap` and `hVort : TrainVorticityGaussianTail`. -/
theorem trainNonzeroModeStreamVelTail_proof
    (hOv : TrainOverlap)
    (hVort : TrainVorticityGaussianTail) :
    TrainNonzeroModeStreamVelTail := by
  intro ρ hρ ℓ j
  cases j with
  | zero =>
    obtain ⟨b, C₀, C', hb, hC₀, hC', C_v, N_v, ν₀, hC_v, hν₀, hB0⟩ :=
      trainNonzeroModeVelTail hOv hVort ρ hρ ℓ 0
    refine ⟨b, C₀, C', hb, hC₀, hC', C_v, N_v + 1, ν₀, hC_v, hν₀, ?_⟩
    intro S_ hS_ ν hν hν_le tr htr l hl s hs hsS z hz
    let c : ℝ := trainPeriod ρ ν
    have hc : 0 < c := Real.rpow_pos_of_pos hν _
    let E : ℝ := Real.exp (-(b * l / c)) + Real.exp (-(b * l ^ 2 / (C₀ + ν * S_)))
    have hE_nn : 0 ≤ E := add_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _)
    have hPv_nn : 0 ≤ polyPS C_v N_v ν c S_ := by unfold polyPS; positivity
    have hB_nn : 0 ≤ polyPS C_v N_v ν c S_ * E := mul_nonneg hPv_nn hE_nn
    have hV_line : ∀ q : ℝ,
        ‖ageJet ℓ 0 (fun r => hfluct c (tr.v r)) s (q, z.2)‖ ≤ polyPS C_v N_v ν c S_ * E := by
      intro q
      exact hB0 S_ hS_ ν hν hν_le tr htr l hl s hs hsS (q, z.2) hz
    have hψ_raw : ‖ageJet ℓ 0 (fun r w => tr.ψ r w - meanStream tr r w.2) s z‖ ≤
        c * (polyPS C_v N_v ν c S_ * E) :=
      norm_ageJet_streamFluct_zero_le hν hc hB_nn tr ℓ hs z hV_line
    have hc_poly : c * polyPS C_v N_v ν c S_ ≤ polyPS C_v (N_v + 1) ν c S_ := by
      unfold polyPS
      have hν_inv : 0 ≤ ν⁻¹ := inv_nonneg.2 hν.le
      have hcX : c ≤ 1 + c + ν⁻¹ := by linarith
      have h1S : 1 ≤ 1 + S_ := by linarith
      have hcY : c ≤ (1 + c + ν⁻¹) * (1 + S_) :=
        hcX.trans (le_mul_of_one_le_right (by linarith) h1S)
      calc c * (C_v * ((1 + c + ν⁻¹) * (1 + S_)) ^ N_v)
          = C_v * (c * ((1 + c + ν⁻¹) * (1 + S_)) ^ N_v) := by ring
        _ ≤ C_v * (((1 + c + ν⁻¹) * (1 + S_)) * ((1 + c + ν⁻¹) * (1 + S_)) ^ N_v) := by
            apply mul_le_mul_of_nonneg_left _ hC_v.le
            exact mul_le_mul_of_nonneg_right hcY (by positivity)
        _ = C_v * ((1 + c + ν⁻¹) * (1 + S_)) ^ (N_v + 1) := by rw [pow_succ']
    have hmono : polyPS C_v N_v ν c S_ ≤ polyPS C_v (N_v + 1) ν c S_ :=
      polyPS_mono hC_v.le le_rfl (Nat.le_succ N_v) hν hc.le hS_
    refine ⟨?_, ?_⟩
    · calc ‖ageJet ℓ 0 (fun r w => tr.ψ r w - meanStream tr r w.2) s z‖
          ≤ c * (polyPS C_v N_v ν c S_ * E) := hψ_raw
        _ = (c * polyPS C_v N_v ν c S_) * E := by ring
        _ ≤ polyPS C_v (N_v + 1) ν c S_ * E := mul_le_mul_of_nonneg_right hc_poly hE_nn
    · exact (hV_line z.1).trans (mul_le_mul_of_nonneg_right hmono hE_nn)
  | succ k =>
    obtain ⟨b₁, C₀₁, C'₁, hb₁, hC₀₁, hC'₁, C₁, N₁, ν₁, hC₁, hν₁, hB_succ⟩ :=
      trainNonzeroModeVelTail hOv hVort ρ hρ ℓ (k + 1)
    obtain ⟨b₂, C₀₂, C'₂, hb₂, hC₀₂, _hC'₂, C₂, N₂, ν₂, _hC₂, hν₂, hB_k⟩ :=
      trainNonzeroModeVelTail hOv hVort ρ hρ ℓ k
    let b : ℝ := min b₁ b₂
    let C₀ : ℝ := max C₀₁ C₀₂
    let C' : ℝ := max C'₁ C'₂
    let C : ℝ := max C₁ (2 * C₂)
    let N : ℕ := max N₁ N₂
    let ν₀ : ℝ := min ν₁ ν₂
    have hb : 0 < b := lt_min hb₁ hb₂
    have hC₀ : 0 < C₀ := lt_max_of_lt_left hC₀₁
    have hC' : 0 < C' := lt_max_of_lt_left hC'₁
    have hC : 0 < C := lt_max_of_lt_left hC₁
    refine ⟨b, C₀, C', hb, hC₀, hC', C, N, ν₀, hC, lt_min hν₁ hν₂, ?_⟩
    intro S_ hS_ ν hν hν_le tr htr l hl s hs hsS z hz
    have hν₁_le : ν ≤ ν₁ := hν_le.trans (min_le_left _ _)
    have hν₂_le : ν ≤ ν₂ := hν_le.trans (min_le_right _ _)
    let c : ℝ := trainPeriod ρ ν
    have hc : 0 < c := Real.rpow_pos_of_pos hν _
    let E : ℝ := Real.exp (-(b * l / c)) + Real.exp (-(b * l ^ 2 / (C₀ + ν * S_)))
    let E₁ : ℝ := Real.exp (-(b₁ * l / c)) + Real.exp (-(b₁ * l ^ 2 / (C₀₁ + ν * S_)))
    let E₂ : ℝ := Real.exp (-(b₂ * l / c)) + Real.exp (-(b₂ * l ^ 2 / (C₀₂ + ν * S_)))
    have hz₁ : C'₁ / ν + 2 + l ≤ |z.2| := by
      have hle : C'₁ / ν ≤ C' / ν := div_le_div_of_nonneg_right (le_max_left _ _) hν.le
      linarith
    have hz₂ : C'₂ / ν + 2 + l ≤ |z.2| := by
      have hle : C'₂ / ν ≤ C' / ν := div_le_div_of_nonneg_right (le_max_right _ _) hν.le
      linarith
    have hE₁_le : E₁ ≤ E :=
      tail_kernel_mono hb (min_le_left _ _) hC₀₁ (le_max_left _ _) hc hν hS_ hl
    have hE₂_le : E₂ ≤ E :=
      tail_kernel_mono hb (min_le_right _ _) hC₀₂ (le_max_right _ _) hc hν hS_ hl
    have hP₁_le : polyPS C₁ N₁ ν c S_ ≤ polyPS C N ν c S_ :=
      polyPS_mono hC₁.le (le_max_left _ _) (le_max_left _ _) hν hc.le hS_
    have hP₂_le : polyPS (2 * C₂) N₂ ν c S_ ≤ polyPS C N ν c S_ :=
      polyPS_mono (by positivity) (le_max_right _ _) (le_max_right _ _) hν hc.le hS_
    have hv_succ := hB_succ S_ hS_ ν hν hν₁_le tr htr l hl s hs hsS z hz₁
    have hv_k := hB_k S_ hS_ ν hν hν₂_le tr htr l hl s hs hsS z hz₂
    have hψ_step : ‖ageJet ℓ (k + 1) (fun r w => tr.ψ r w - meanStream tr r w.2) s z‖ ≤
        2 * ‖ageJet ℓ k (fun r => hfluct c (tr.v r)) s z‖ :=
      PartI_T22.norm_ageJet_streamFluct_succ_le hν hc tr ℓ k hs z
    refine ⟨?_, ?_⟩
    · calc ‖ageJet ℓ (k + 1) (fun r w => tr.ψ r w - meanStream tr r w.2) s z‖
          ≤ 2 * ‖ageJet ℓ k (fun r => hfluct c (tr.v r)) s z‖ := hψ_step
        _ ≤ 2 * (polyPS C₂ N₂ ν c S_ * E₂) :=
            mul_le_mul_of_nonneg_left hv_k (by norm_num)
        _ = polyPS (2 * C₂) N₂ ν c S_ * E₂ := by unfold polyPS; ring
        _ ≤ polyPS C N ν c S_ * E :=
            mul_le_mul hP₂_le hE₂_le (add_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _))
              (by unfold polyPS; positivity)
    · exact hv_succ.trans (mul_le_mul hP₁_le hE₁_le
        (add_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _)) (by unfold polyPS; positivity))

end UnforcedLeray.Short.PartI

end
