import UnforcedLeray.Short.PartI.Sub.PartI_HF_1
import UnforcedLeray.Lib.Kernels.ParamIntegral
import UnforcedLeray.Short.PartI.Sub.PartI_T22_1
import UnforcedLeray.Short.PartI.Tasks.LerayPressureGauge.PressureBounded
import UnforcedLeray.Short.PartI.Tasks.LerayPressureGauge.PressureMeanIdentity
import UnforcedLeray.Short.PartI.Tasks.ClassicalOdd.SlicePoisson
import UnforcedLeray.Short.PartI.Tasks.ClassicalOdd.VelocityDecayOfEnergy
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.ViscousIBP

/-!
# Part I, task `PartI:HF/1/1`: Pressure Age-Step at Fixed Parameters (`TrainVelAgeStepPressFixed`)

Source of record: `the November 2 reference manuscript`, lines 318–322,
326–359, 427–435 (see also lines 276–288 and 447 for the cylinder pressure decomposition).

Proves `trainVelAgeStepPressFixed : TrainVelAgeStepPressFixed`:
at fixed `0 < ν` and `1 < c`, if a `BUC` train `tr : B0140.TrainSol ν c` satisfies
`∀ r ≤ ℓ, VelOrderBoundedFixed tr r`, then for every spatial order `j : ℕ`, the pressure-gradient
age-jet `ageJet ℓ j (fun r w => Train.gradS (tr.p r) w)` is bounded uniformly on `s > 0` × `Plane`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec toVec)
open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Short.IIb (UU isOpen_UU mem_UU Dx eT eQ eE Sm Dv hasDerivAt_slice
  vb_slice_contDiffAt vb_slice_smooth_at vb_ageJet_sub norm_jet_vec_le)
open PartI_T25_1 PartI_T25_3

namespace PressStepFixed

/-! ### 1. Word derivatives: commutation with partials, horizontal averages, and age derivatives -/

theorem periodic_derivWord_cyl {c : ℝ} {g : Plane → ℝ} (hper : Cyl.IsPeriodic c g)
    (w : List Bool) : Cyl.IsPeriodic c (B0151.derivWord w g) :=
  fun z => B0151.periodic_derivWord (fun x y => hper (x, y)) w z.1 z.2

theorem derivWord_neg (g : Plane → ℝ) :
    ∀ (w : List Bool) (z : Plane),
      B0151.derivWord w (fun x => -g x) z = -B0151.derivWord w g z
  | [], _ => rfl
  | true :: w, z => by
      have ih : B0151.derivWord w (fun x => -g x) = fun x => -B0151.derivWord w g x :=
        funext (derivWord_neg g w)
      change Cyl.partialQ (B0151.derivWord w (fun x => -g x)) z =
        -Cyl.partialQ (B0151.derivWord w g) z
      rw [ih]
      exact deriv.neg
  | false :: w, z => by
      have ih : B0151.derivWord w (fun x => -g x) = fun x => -B0151.derivWord w g x :=
        funext (derivWord_neg g w)
      change Cyl.partialEta (B0151.derivWord w (fun x => -g x)) z =
        -Cyl.partialEta (B0151.derivWord w g) z
      rw [ih]
      exact deriv.neg

theorem derivWord_sub {f g : Plane → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    ∀ (w : List Bool) (z : Plane),
      B0151.derivWord w (fun x => f x - g x) z =
        B0151.derivWord w f z - B0151.derivWord w g z
  | [], _ => rfl
  | true :: w, z => by
      have hfw := B0151.contDiff_derivWord hf w
      have hgw := B0151.contDiff_derivWord hg w
      have ih : B0151.derivWord w (fun x => f x - g x) =
          fun x => B0151.derivWord w f x - B0151.derivWord w g x :=
        funext (derivWord_sub hf hg w)
      change Cyl.partialQ (B0151.derivWord w (fun x => f x - g x)) z =
        Cyl.partialQ (B0151.derivWord w f) z - Cyl.partialQ (B0151.derivWord w g) z
      rw [ih]
      have hd1 : DifferentiableAt ℝ (fun q => B0151.derivWord w f (q, z.2)) z.1 :=
        ((hfw.comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp)) z.1
      have hd2 : DifferentiableAt ℝ (fun q => B0151.derivWord w g (q, z.2)) z.1 :=
        ((hgw.comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp)) z.1
      exact deriv_sub hd1 hd2
  | false :: w, z => by
      have hfw := B0151.contDiff_derivWord hf w
      have hgw := B0151.contDiff_derivWord hg w
      have ih : B0151.derivWord w (fun x => f x - g x) =
          fun x => B0151.derivWord w f x - B0151.derivWord w g x :=
        funext (derivWord_sub hf hg w)
      change Cyl.partialEta (B0151.derivWord w (fun x => f x - g x)) z =
        Cyl.partialEta (B0151.derivWord w f) z - Cyl.partialEta (B0151.derivWord w g) z
      rw [ih]
      have hd1 : DifferentiableAt ℝ (fun e => B0151.derivWord w f (z.1, e)) z.2 :=
        ((hfw.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp)) z.2
      have hd2 : DifferentiableAt ℝ (fun e => B0151.derivWord w g (z.1, e)) z.2 :=
        ((hgw.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp)) z.2
      exact deriv_sub hd1 hd2

theorem derivWord_partialQ :
    ∀ (w : List Bool) {g : Plane → ℝ}, ContDiff ℝ ∞ g →
      B0151.derivWord w (Cyl.partialQ g) = Cyl.partialQ (B0151.derivWord w g)
  | [], _, _ => rfl
  | true :: w, g, hg => by
      change Cyl.partialQ (B0151.derivWord w (Cyl.partialQ g)) =
        Cyl.partialQ (Cyl.partialQ (B0151.derivWord w g))
      rw [derivWord_partialQ w hg]
  | false :: w, g, hg => by
      change Cyl.partialEta (B0151.derivWord w (Cyl.partialQ g)) =
        Cyl.partialQ (Cyl.partialEta (B0151.derivWord w g))
      rw [derivWord_partialQ w hg]
      exact (JetViscIBP.comm_QE (B0151.contDiff_derivWord hg w)).symm

theorem derivWord_partialEta :
    ∀ (w : List Bool) {g : Plane → ℝ}, ContDiff ℝ ∞ g →
      B0151.derivWord w (Cyl.partialEta g) = Cyl.partialEta (B0151.derivWord w g)
  | [], _, _ => rfl
  | true :: w, g, hg => by
      change Cyl.partialQ (B0151.derivWord w (Cyl.partialEta g)) =
        Cyl.partialEta (Cyl.partialQ (B0151.derivWord w g))
      rw [derivWord_partialEta w hg]
      exact JetViscIBP.comm_QE (B0151.contDiff_derivWord hg w)
  | false :: w, g, hg => by
      change Cyl.partialEta (B0151.derivWord w (Cyl.partialEta g)) =
        Cyl.partialEta (Cyl.partialEta (B0151.derivWord w g))
      rw [derivWord_partialEta w hg]

theorem hmean_derivWord_eq {c : ℝ} (hc : 0 < c) {g : Plane → ℝ}
    (hg : ContDiff ℝ ∞ g) (hper : Cyl.IsPeriodic c g) :
    ∀ (w : List Bool) (z : Plane),
      hmean c (B0151.derivWord w g) z.2 =
        B0151.derivWord w (fun x : Plane => hmean c g x.2) z
  | [], _ => rfl
  | true :: w, z => by
      have hgw := B0151.contDiff_derivWord hg w
      have hpw := periodic_derivWord_cyl hper w
      have h1 : hmean c (B0151.derivWord (true :: w) g) z.2 = 0 := by
        show c⁻¹ • ∫ q in Ioc (-c / 2) (c / 2), Cyl.partialQ (B0151.derivWord w g) (q, z.2) = 0
        rw [mm_integral_partialQ_zero hc hgw hpw z.2, smul_zero]
      have h2 : B0151.derivWord (true :: w) (fun x : Plane => hmean c g x.2) z = 0 := by
        have hfun : B0151.derivWord w (fun x : Plane => hmean c g x.2) =
            fun x : Plane => hmean c (B0151.derivWord w g) x.2 :=
          funext fun x => (hmean_derivWord_eq hc hg hper w x).symm
        change Cyl.partialQ (B0151.derivWord w (fun x : Plane => hmean c g x.2)) z = 0
        rw [hfun]
        show deriv (fun _q : ℝ => hmean c (B0151.derivWord w g) z.2) z.1 = 0
        exact deriv_const z.1 _
      exact h1.trans h2.symm
  | false :: w, z => by
      have hgw := B0151.contDiff_derivWord hg w
      have hfun : B0151.derivWord w (fun x : Plane => hmean c g x.2) =
          fun x : Plane => hmean c (B0151.derivWord w g) x.2 :=
        funext fun x => (hmean_derivWord_eq hc hg hper w x).symm
      change hmean c (Cyl.partialEta (B0151.derivWord w g)) z.2 =
        Cyl.partialEta (B0151.derivWord w (fun x : Plane => hmean c g x.2)) z
      rw [hfun]
      exact (pmi_hasDerivAt_hmean_eta hgw z.2).deriv.symm

theorem smS_derivWord {F : ℝ → Plane → ℝ}
    (hF : SmS (fun x : ℝ × Plane => F x.1 x.2)) :
    ∀ w : List Bool, SmS (fun x : ℝ × Plane => B0151.derivWord w (F x.1) x.2)
  | [] => hF
  | true :: w =>
      PartI_HF_1.smS_partialQ (F := fun r y => B0151.derivWord w (F r) y) (smS_derivWord hF w)
  | false :: w =>
      PartI_HF_1.smS_partialEta (F := fun r y => B0151.derivWord w (F r) y) (smS_derivWord hF w)

theorem smS_iteratedDeriv_slice {F : ℝ → Plane → ℝ}
    (hF : SmS (fun x : ℝ × Plane => F x.1 x.2)) (ℓ : ℕ) :
    SmS (fun x : ℝ × Plane => iteratedDeriv ℓ (fun r => F r x.2) x.1) :=
  (SmS_DtS hF ℓ).congr fun ⟨_t, w⟩ hx => iteratedDeriv_slice_eq_DtS hF ℓ hx.1 w

theorem smS_derivWord_iteratedDeriv {F : ℝ → Plane → ℝ}
    (hF : SmS (fun x : ℝ × Plane => F x.1 x.2)) (ℓ : ℕ) (w : List Bool) :
    SmS (fun x : ℝ × Plane =>
      B0151.derivWord w (fun y => iteratedDeriv ℓ (fun r => F r y) x.1) x.2) :=
  smS_derivWord (F := fun r y => iteratedDeriv ℓ (fun t => F t y) r)
    (smS_iteratedDeriv_slice hF ℓ) w

theorem smS_hmean_scalar {c : ℝ} (hc : 0 < c) {F : ℝ → Plane → ℝ}
    (hF : SmS (fun x : ℝ × Plane => F x.1 x.2)) :
    SmS (fun x : ℝ × Plane => hmean c (F x.1) x.2.2) := by
  have hm := hmeanContDiff c hc F hF
  have hproj : ContDiff ℝ ∞ (fun x : ℝ × Plane => ((x.1, x.2.2) : ℝ × ℝ)) := by fun_prop
  exact hm.comp hproj.contDiffOn
    (fun x (hx : x.1 ∈ Ioi (0 : ℝ) ∧ x.2 ∈ (univ : Set Plane)) => ⟨hx.1, mem_univ _⟩)

theorem iteratedDeriv_derivWord_eq {F : ℝ → Plane → ℝ}
    (hF : SmS (fun x : ℝ × Plane => F x.1 x.2)) (ℓ : ℕ) :
    ∀ (w : List Bool) {r : ℝ}, 0 < r → ∀ z : Plane,
      iteratedDeriv ℓ (fun t => B0151.derivWord w (F t) z) r =
        B0151.derivWord w (fun x => iteratedDeriv ℓ (fun t => F t x) r) z
  | [], _, _, _ => rfl
  | true :: w, r, hr, z => by
      have hw := smS_derivWord hF w
      change iteratedDeriv ℓ (fun t => Cyl.partialQ (B0151.derivWord w (F t)) z) r =
        Cyl.partialQ (B0151.derivWord w (fun x => iteratedDeriv ℓ (fun t => F t x) r)) z
      rw [PartI_HF_1.iteratedDeriv_partialQ_eq
        (F := fun t y => B0151.derivWord w (F t) y) hw ℓ hr z]
      have hfun : (fun x => iteratedDeriv ℓ (fun t => B0151.derivWord w (F t) x) r) =
          B0151.derivWord w (fun x => iteratedDeriv ℓ (fun t => F t x) r) :=
        funext fun x => iteratedDeriv_derivWord_eq hF ℓ w hr x
      rw [hfun]
  | false :: w, r, hr, z => by
      have hw := smS_derivWord hF w
      change iteratedDeriv ℓ (fun t => Cyl.partialEta (B0151.derivWord w (F t)) z) r =
        Cyl.partialEta (B0151.derivWord w (fun x => iteratedDeriv ℓ (fun t => F t x) r)) z
      rw [PartI_HF_1.iteratedDeriv_partialEta_eq
        (F := fun t y => B0151.derivWord w (F t) y) hw ℓ hr z]
      have hfun : (fun x => iteratedDeriv ℓ (fun t => B0151.derivWord w (F t) x) r) =
          B0151.derivWord w (fun x => iteratedDeriv ℓ (fun t => F t x) r) :=
        funext fun x => iteratedDeriv_derivWord_eq hF ℓ w hr x
      rw [hfun]

theorem abs_derivWord_iteratedDeriv_le {F : ℝ → Plane → ℝ}
    (hF : SmS (fun x : ℝ × Plane => F x.1 x.2))
    (ℓ : ℕ) (w : List Bool) {r : ℝ} (hr : 0 < r) (z : Plane) :
    |B0151.derivWord w (fun x => iteratedDeriv ℓ (fun t => F t x) r) z| ≤
      ‖ageJet ℓ w.length F r z‖ := by
  have hf : ContDiff ℝ ∞ (fun x : Plane => iteratedDeriv ℓ (fun t => F t x) r) :=
    contDiff_slice_iteratedDeriv_of_contDiffOn F hF ℓ hr
  exact (cylJetWord_proof (fun x : Plane => iteratedDeriv ℓ (fun t => F t x) r)
    hf w.length z).1 w rfl

theorem hasDerivAt_derivWord_iteratedDeriv {F : ℝ → Plane → ℝ}
    (hF : SmS (fun x : ℝ × Plane => F x.1 x.2)) (ℓ : ℕ) (w : List Bool)
    {t : ℝ} (ht : 0 < t) (z : Plane) :
    HasDerivAt
      (fun r => B0151.derivWord w (fun x => iteratedDeriv ℓ (fun s => F s x) r) z)
      (B0151.derivWord w (fun x => iteratedDeriv (ℓ + 1) (fun s => F s x) t) z) t := by
  let P : ℝ × Plane → ℝ := fun x =>
    B0151.derivWord w (fun y => iteratedDeriv ℓ (fun s => F s y) x.1) x.2
  have hP : SmS P := smS_derivWord_iteratedDeriv hF ℓ w
  have hd : HasDerivAt (fun r => P (r, z)) (deriv (fun r => P (r, z)) t) t :=
    (hasDerivAt_sliceS hP ht z).differentiableAt.hasDerivAt
  have hev : (fun r => P (r, z)) =ᶠ[nhds t]
      iteratedDeriv ℓ (fun s => B0151.derivWord w (F s) z) := by
    filter_upwards [Ioi_mem_nhds ht] with r hr
    exact (iteratedDeriv_derivWord_eq hF ℓ w hr z).symm
  have hder : deriv (fun r => P (r, z)) t =
      B0151.derivWord w (fun x => iteratedDeriv (ℓ + 1) (fun s => F s x) t) z := by
    rw [hev.deriv_eq, ← iteratedDeriv_succ, iteratedDeriv_derivWord_eq hF (ℓ + 1) w ht z]
  rwa [hder] at hd

theorem continuousOn_derivWord_iteratedDeriv {F : ℝ → Plane → ℝ}
    (hF : SmS (fun x : ℝ × Plane => F x.1 x.2)) (ℓ : ℕ) (w : List Bool) (z : Plane) :
    ContinuousOn
      (fun r => B0151.derivWord w (fun x => iteratedDeriv ℓ (fun s => F s x) r) z)
      (Ioi (0 : ℝ)) := by
  have hP := (smS_derivWord_iteratedDeriv hF ℓ w).continuousOn
  exact hP.comp (continuousOn_id.prodMk continuousOn_const) (fun r hr => mem_UU hr)

/-! ### 2. Mean pressure identity and age-jet bound for the horizontal mean -/

theorem eq_zero_of_const_tendsto_comap {C : ℝ} {g : Plane → ℝ}
    (hconst : ∀ z : Plane, g z = C)
    (ht : Tendsto g (comap (fun z : Plane => |z.2|) atTop) (𝓝 0)) : C = 0 := by
  by_contra hC
  have hpos : 0 < |C| := abs_pos.mpr hC
  have hev := (Metric.tendsto_nhds.mp ht) |C| hpos
  rw [Filter.eventually_comap, Filter.eventually_atTop] at hev
  obtain ⟨R, hR⟩ := hev
  have hlt := hR (max R 0) (le_max_left R 0) ((0 : ℝ), max R 0) (abs_of_nonneg (le_max_right R 0))
  rw [hconst ((0 : ℝ), max R 0), Real.dist_eq, sub_zero] at hlt
  exact lt_irrefl |C| hlt

theorem train_hmean_p_eq {ν c : ℝ} (hν : 0 < ν) (hc : 1 < c)
    (tr : B0140.TrainSol ν c) (htr : IsBUCTrain tr)
    {r : ℝ} (hr : 0 < r) (η : ℝ) :
    hmean c (tr.p r) η = -hmean c (fun w => tr.v r w 1 * tr.v r w 1) η := by
  have hc0 : 0 < c := zero_lt_one.trans hc
  have hT : 0 < r + 1 := add_pos hr zero_lt_one
  have hrT : r ∈ Icc (0 : ℝ) (r + 1) := ⟨hr.le, le_add_of_nonneg_right zero_le_one⟩
  have hcl : IsClassicalOn ν c (r + 1) tr.v tr.p := trainSol_isClassicalOn tr (r + 1)
  have hb : HasBoundedDerivsOn (r + 1) tr.v := htr (r + 1) hT.le
  have hdec : VelocityDecayOn (r + 1) tr.v :=
    velocityDecayOfEnergy ν c (r + 1) tr.v tr.p hν hc.le hT hcl hb
  have hG : GaugeHyp ν c (r + 1) tr.v tr.p := ⟨hν, hc.le, hT, hcl, hb, hdec⟩
  have hpmi : ∀ e : ℝ, hmean c (tr.p r) e + hmean c (fun z => tr.v r z 1 ^ 2) e =
      hmean c (tr.p r) 0 + hmean c (fun z => tr.v r z 1 ^ 2) 0 :=
    pmi_interior hG ⟨hr, lt_add_one r⟩
  have hp_dec : Tendsto (fun z : Plane => hmean c (tr.p r) z.2)
      (comap (fun z : Plane => |z.2|) atTop) (𝓝 0) :=
    gg_hmean_tendsto hc0 (tr.isTrain.pressure_decay r hr.le)
  have hv1_dec : Tendsto (fun z : Plane => tr.v r z 1)
      (comap (fun z : Plane => |z.2|) atTop) (𝓝 0) :=
    (gg_component hG hrT 1).2.2
  have hv2_dec : Tendsto (fun z : Plane => tr.v r z 1 ^ 2)
      (comap (fun z : Plane => |z.2|) atTop) (𝓝 0) := by
    have h := hv1_dec.pow 2
    rwa [zero_pow two_ne_zero] at h
  have hv_dec : Tendsto (fun z : Plane => hmean c (fun w => tr.v r w 1 ^ 2) z.2)
      (comap (fun z : Plane => |z.2|) atTop) (𝓝 0) :=
    gg_hmean_tendsto hc0 hv2_dec
  have hsum_dec : Tendsto
      (fun z : Plane => hmean c (tr.p r) z.2 + hmean c (fun w => tr.v r w 1 ^ 2) z.2)
      (comap (fun z : Plane => |z.2|) atTop) (𝓝 0) := by
    have h := hp_dec.add hv_dec
    rwa [add_zero] at h
  have hzero : hmean c (tr.p r) 0 + hmean c (fun z => tr.v r z 1 ^ 2) 0 = 0 :=
    eq_zero_of_const_tendsto_comap (fun z => hpmi z.2) hsum_dec
  have hη : hmean c (tr.p r) η + hmean c (fun z => tr.v r z 1 ^ 2) η = 0 :=
    (hpmi η).trans hzero
  have hsq : (fun z : Plane => tr.v r z 1 ^ 2) = fun w => tr.v r w 1 * tr.v r w 1 :=
    funext fun w => sq (tr.v r w 1)
  rw [hsq] at hη
  exact eq_neg_of_add_eq_zero_left hη

theorem norm_ageJet_neg_eq (F : ℝ → Plane → ℝ)
    (hF : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => F x.1 x.2) (Ioi 0 ×ˢ univ))
    (ℓ j : ℕ) {s : ℝ} (hs : 0 < s) (z : Plane) :
    ‖ageJet ℓ j (fun r w => -F r w) s z‖ = ‖ageJet ℓ j F s z‖ := by
  have h0 : ContDiffOn ℝ ∞ (fun _ : ℝ × Plane => (0 : ℝ)) (Ioi 0 ×ˢ univ) := contDiffOn_const
  have hsub := PartI_T22.ageJet_sub (fun _ _ => (0 : ℝ)) F h0 hF hs ℓ j z
  have hzero : ageJet ℓ j (fun (_ : ℝ) (_ : Plane) => (0 : ℝ)) s z = 0 := by
    unfold ageJet Train.jet
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

theorem norm_ageJet_hmean_scalar_le {c B : ℝ} (hc : 0 < c) (_hB : 0 ≤ B)
    {f : ℝ → Plane → ℝ}
    (hf : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => f x.1 x.2) (Ioi 0 ×ˢ univ))
    (ℓ m : ℕ) {s : ℝ} (hs : 0 < s) (z : Plane)
    (hpt : ∀ q ∈ Ioc (-c / 2) (c / 2), ‖ageJet ℓ m f s (q, z.2)‖ ≤ B) :
    ‖ageJet ℓ m (fun r w => hmean c (f r) w.2) s z‖ ≤ B := by
  let G : Plane → ℝ := fun w => iteratedDeriv ℓ (fun r => f r w) s
  have hG : ContDiff ℝ ∞ G := PartI_T22.contDiff_slice_iteratedDeriv hf ℓ hs
  have hhm_eq : ageJet ℓ m (fun r w => hmean c (f r) w.2) s z =
      Train.jet m (fun w : Plane => hmean c G w.2) z := by
    unfold ageJet Train.jet
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
  unfold Train.jet
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

theorem norm_ageJet_hmean_p_le {ν c : ℝ} (hν : 0 < ν) (hc : 1 < c)
    (tr : B0140.TrainSol ν c) (htr : IsBUCTrain tr)
    (ℓ k : ℕ) {s M_v : ℝ} (hs : 0 < s) (hMv : 0 ≤ M_v) (z : Plane)
    (hbd : ∀ y : Plane, ∀ r ≤ ℓ, ∀ i ≤ k, ‖ageJet r i tr.v s y‖ ≤ M_v) :
    ‖ageJet ℓ k (fun r w => hmean c (tr.p r) w.2) s z‖ ≤
      (2 : ℝ) ^ (ℓ + k) * M_v * M_v := by
  have hc0 : 0 < c := zero_lt_one.trans hc
  have hsm_v : Sm (fun x : ℝ × Plane => tr.v x.1 x.2) :=
    tr.isTrain.smooth_v.mono (Set.prod_mono Set.Ioi_subset_Ici_self Subset.rfl)
  have hsm_v1 : SmS (fun x : ℝ × Plane => tr.v x.1 x.2 1) :=
    (EuclideanSpace.proj (1 : Fin 2) : Vec →L[ℝ] ℝ).contDiff.comp_contDiffOn hsm_v
  let Vsq : ℝ → Plane → ℝ := fun r w => tr.v r w 1 * tr.v r w 1
  have hVsq_bd : ∀ y : Plane, ‖ageJet ℓ k Vsq s y‖ ≤ (2 : ℝ) ^ (ℓ + k) * M_v * M_v := by
    intro y
    refine PartI_HF_1.norm_ageJet_mul_le hsm_v1 hsm_v1 ℓ k hs hMv hMv y
      (fun r hr i hi => ?_) (fun r hr i hi => ?_)
    · exact (PartI_HF_1.norm_ageJet_vec_proj_le hsm_v 1 r i hs y).trans (hbd y r hr i hi)
    · exact (PartI_HF_1.norm_ageJet_vec_proj_le hsm_v 1 r i hs y).trans (hbd y r hr i hi)
  have hB_nn : 0 ≤ (2 : ℝ) ^ (ℓ + k) * M_v * M_v := by positivity
  have hmean_Vsq_bd :
      ‖ageJet ℓ k (fun r w => hmean c (Vsq r) w.2) s z‖ ≤
        (2 : ℝ) ^ (ℓ + k) * M_v * M_v :=
    norm_ageJet_hmean_scalar_le (f := Vsq) hc0 hB_nn (hsm_v1.mul hsm_v1) ℓ k hs
      z (fun q _ => hVsq_bd (q, z.2))
  have hage_eq :
      ageJet ℓ k (fun r w => hmean c (tr.p r) w.2) s z =
        ageJet ℓ k (fun r w => -hmean c (Vsq r) w.2) s z := by
    unfold ageJet
    congr 1
    funext w
    have hev : (fun r => hmean c (tr.p r) w.2) =ᶠ[nhds s]
        fun r => -hmean c (Vsq r) w.2 := by
      filter_upwards [Ioi_mem_nhds hs] with r hr using train_hmean_p_eq hν hc tr htr hr w.2
    exact hev.iteratedDeriv_eq ℓ
  have hsm_hm_Vsq : SmS (fun x : ℝ × Plane => hmean c (Vsq x.1) x.2.2) :=
    smS_hmean_scalar hc0 (F := Vsq) (hsm_v1.mul hsm_v1)
  rw [hage_eq,
    norm_ageJet_neg_eq (fun r w => hmean c (Vsq r) w.2) hsm_hm_Vsq ℓ k hs z]
  exact hmean_Vsq_bd

/-! ### 3. Spacetime Leibniz bound for `poissonSource` and Laplacian of `Q_w` -/

theorem norm_ageJet_poissonSource_le {V : ℝ → Plane → Vec}
    (hV : Sm (fun x : ℝ × Plane => V x.1 x.2))
    (ℓ j : ℕ) {s M : ℝ} (hs : 0 < s) (hM : 0 ≤ M) (z : Plane)
    (hbd : ∀ r ≤ ℓ, ∀ i ≤ j + 1, ‖ageJet r i V s z‖ ≤ M) :
    ‖ageJet ℓ j (fun r w => poissonSource (V r) w) s z‖ ≤
      4 * (2 : ℝ) ^ (ℓ + j) * M * M := by
  have hsm_v0 : SmS (fun x : ℝ × Plane => V x.1 x.2 0) :=
    (EuclideanSpace.proj (0 : Fin 2) : Vec →L[ℝ] ℝ).contDiff.comp_contDiffOn hV
  have hsm_v1 : SmS (fun x : ℝ × Plane => V x.1 x.2 1) :=
    (EuclideanSpace.proj (1 : Fin 2) : Vec →L[ℝ] ℝ).contDiff.comp_contDiffOn hV
  have hQ0 : SmS (fun x : ℝ × Plane => Cyl.partialQ (fun w => V x.1 w 0) x.2) :=
    PartI_HF_1.smS_partialQ (F := fun r w => V r w 0) hsm_v0
  have hQ1 : SmS (fun x : ℝ × Plane => Cyl.partialQ (fun w => V x.1 w 1) x.2) :=
    PartI_HF_1.smS_partialQ (F := fun r w => V r w 1) hsm_v1
  have hE0 : SmS (fun x : ℝ × Plane => Cyl.partialEta (fun w => V x.1 w 0) x.2) :=
    PartI_HF_1.smS_partialEta (F := fun r w => V r w 0) hsm_v0
  have hE1 : SmS (fun x : ℝ × Plane => Cyl.partialEta (fun w => V x.1 w 1) x.2) :=
    PartI_HF_1.smS_partialEta (F := fun r w => V r w 1) hsm_v1
  let P₁ : ℝ → Plane → ℝ := fun r w =>
    Cyl.partialQ (fun y => V r y 0) w * Cyl.partialQ (fun y => V r y 0) w
  let P₂ : ℝ → Plane → ℝ := fun r w =>
    Cyl.partialQ (fun y => V r y 1) w * Cyl.partialEta (fun y => V r y 0) w
  let P₃ : ℝ → Plane → ℝ := fun r w =>
    Cyl.partialEta (fun y => V r y 1) w * Cyl.partialEta (fun y => V r y 1) w
  have hsm₁ : SmS (fun x : ℝ × Plane => P₁ x.1 x.2) := hQ0.mul hQ0
  have hsm₂ : SmS (fun x : ℝ × Plane => P₂ x.1 x.2) := hQ1.mul hE0
  have hsm₃ : SmS (fun x : ℝ × Plane => P₃ x.1 x.2) := hE1.mul hE1
  have hfun : (fun r w => poissonSource (V r) w) =
      fun r w => (P₁ r w + (P₂ r w + P₂ r w)) + P₃ r w := by
    funext r w
    unfold poissonSource
    dsimp [P₁, P₂, P₃]
    ring
  have hadd1 := PartI_HF_1.ageJet_add (fun r w => P₁ r w + (P₂ r w + P₂ r w)) P₃
    (hsm₁.add (hsm₂.add hsm₂)) hsm₃ hs ℓ j z
  have hadd2 := PartI_HF_1.ageJet_add P₁ (fun r w => P₂ r w + P₂ r w)
    hsm₁ (hsm₂.add hsm₂) hs ℓ j z
  have hadd3 := PartI_HF_1.ageJet_add P₂ P₂ hsm₂ hsm₂ hs ℓ j z
  have hQ0_bd : ∀ r ≤ ℓ, ∀ i ≤ j,
      ‖ageJet r i (fun t w => Cyl.partialQ (fun y => V t y 0) w) s z‖ ≤ M := fun r hr i hi =>
    ((PartI_HF_1.norm_ageJet_partialQ_le (F := fun t w => V t w 0) hsm_v0 r i hs z).trans
      (PartI_HF_1.norm_ageJet_vec_proj_le hV 0 r (i + 1) hs z)).trans (hbd r hr (i + 1) (by omega))
  have hQ1_bd : ∀ r ≤ ℓ, ∀ i ≤ j,
      ‖ageJet r i (fun t w => Cyl.partialQ (fun y => V t y 1) w) s z‖ ≤ M := fun r hr i hi =>
    ((PartI_HF_1.norm_ageJet_partialQ_le (F := fun t w => V t w 1) hsm_v1 r i hs z).trans
      (PartI_HF_1.norm_ageJet_vec_proj_le hV 1 r (i + 1) hs z)).trans (hbd r hr (i + 1) (by omega))
  have hE0_bd : ∀ r ≤ ℓ, ∀ i ≤ j,
      ‖ageJet r i (fun t w => Cyl.partialEta (fun y => V t y 0) w) s z‖ ≤ M := fun r hr i hi =>
    ((PartI_HF_1.norm_ageJet_partialEta_le (F := fun t w => V t w 0) hsm_v0 r i hs z).trans
      (PartI_HF_1.norm_ageJet_vec_proj_le hV 0 r (i + 1) hs z)).trans (hbd r hr (i + 1) (by omega))
  have hE1_bd : ∀ r ≤ ℓ, ∀ i ≤ j,
      ‖ageJet r i (fun t w => Cyl.partialEta (fun y => V t y 1) w) s z‖ ≤ M := fun r hr i hi =>
    ((PartI_HF_1.norm_ageJet_partialEta_le (F := fun t w => V t w 1) hsm_v1 r i hs z).trans
      (PartI_HF_1.norm_ageJet_vec_proj_le hV 1 r (i + 1) hs z)).trans (hbd r hr (i + 1) (by omega))
  have hb₁ := PartI_HF_1.norm_ageJet_mul_le hQ0 hQ0 ℓ j hs hM hM z hQ0_bd hQ0_bd
  have hb₂ := PartI_HF_1.norm_ageJet_mul_le hQ1 hE0 ℓ j hs hM hM z hQ1_bd hE0_bd
  have hb₃ := PartI_HF_1.norm_ageJet_mul_le hE1 hE1 ℓ j hs hM hM z hE1_bd hE1_bd
  rw [hfun, hadd1, hadd2, hadd3]
  have htri1 := norm_add_le
    (ageJet ℓ j P₁ s z + (ageJet ℓ j P₂ s z + ageJet ℓ j P₂ s z)) (ageJet ℓ j P₃ s z)
  have htri2 := norm_add_le (ageJet ℓ j P₁ s z) (ageJet ℓ j P₂ s z + ageJet ℓ j P₂ s z)
  have htri3 := norm_add_le (ageJet ℓ j P₂ s z) (ageJet ℓ j P₂ s z)
  linarith

theorem iteratedDeriv_lapS_eq {F : ℝ → Plane → ℝ}
    (hF : SmS (fun x : ℝ × Plane => F x.1 x.2)) (ℓ : ℕ) {r : ℝ} (hr : 0 < r) (x : Plane) :
    iteratedDeriv ℓ (fun t => Train.lapS (F t) x) r =
      Train.lapS (fun y => iteratedDeriv ℓ (fun t => F t y) r) x := by
  have hQ1 := PartI_HF_1.smS_partialQ (F := F) hF
  have hQ2 := PartI_HF_1.smS_partialQ (F := fun t y => Cyl.partialQ (F t) y) hQ1
  have hE1 := PartI_HF_1.smS_partialEta (F := F) hF
  have hE2 := PartI_HF_1.smS_partialEta (F := fun t y => Cyl.partialEta (F t) y) hE1
  have hadd := iteratedDeriv_add
    (vb_slice_smooth_at (fun t y => Cyl.partialQ (Cyl.partialQ (F t)) y) hQ2 hr x ℓ)
    (vb_slice_smooth_at (fun t y => Cyl.partialEta (Cyl.partialEta (F t)) y) hE2 hr x ℓ)
  have hq : iteratedDeriv ℓ (fun t => Cyl.partialQ (Cyl.partialQ (F t)) x) r =
      Cyl.partialQ (Cyl.partialQ (fun y => iteratedDeriv ℓ (fun t => F t y) r)) x := by
    rw [PartI_HF_1.iteratedDeriv_partialQ_eq (F := fun t y => Cyl.partialQ (F t) y) hQ1 ℓ hr x]
    have hfun : (fun y => iteratedDeriv ℓ (fun t => Cyl.partialQ (F t) y) r) =
        Cyl.partialQ (fun y => iteratedDeriv ℓ (fun t => F t y) r) :=
      funext fun y => PartI_HF_1.iteratedDeriv_partialQ_eq (F := F) hF ℓ hr y
    rw [hfun]
  have he : iteratedDeriv ℓ (fun t => Cyl.partialEta (Cyl.partialEta (F t)) x) r =
      Cyl.partialEta (Cyl.partialEta (fun y => iteratedDeriv ℓ (fun t => F t y) r)) x := by
    rw [PartI_HF_1.iteratedDeriv_partialEta_eq (F := fun t y => Cyl.partialEta (F t) y) hE1 ℓ hr x]
    have hfun : (fun y => iteratedDeriv ℓ (fun t => Cyl.partialEta (F t) y) r) =
        Cyl.partialEta (fun y => iteratedDeriv ℓ (fun t => F t y) r) :=
      funext fun y => PartI_HF_1.iteratedDeriv_partialEta_eq (F := F) hF ℓ hr y
    rw [hfun]
  unfold Train.lapS
  exact hadd.trans (by rw [hq, he])

theorem lapS_derivWord_iteratedDeriv_p_eq {ν c : ℝ} (hν : 0 < ν) (hc : 1 < c)
    (tr : B0140.TrainSol ν c) (ℓ : ℕ) (w : List Bool) {r : ℝ} (hr : 0 < r) (z : Plane) :
    Train.lapS (B0151.derivWord w (fun x => iteratedDeriv ℓ (fun t => tr.p t x) r)) z =
      -B0151.derivWord w (fun x => iteratedDeriv ℓ (fun t => poissonSource (tr.v t) x) r) z := by
  have hsm_p : SmS (fun x : ℝ × Plane => tr.p x.1 x.2) :=
    tr.isTrain.smooth_p.mono (Set.prod_mono Set.Ioi_subset_Ici_self Subset.rfl)
  have hslice_p : ContDiff ℝ ∞ (fun x : Plane => iteratedDeriv ℓ (fun t => tr.p t x) r) :=
    contDiff_slice_iteratedDeriv_of_contDiffOn tr.p hsm_p ℓ hr
  have hcomm := congrFun
    (JetViscIBP.derivWord_lap w (fun x : Plane => iteratedDeriv ℓ (fun t => tr.p t x) r) hslice_p).symm z
  rw [hcomm]
  have hlap_eq : (fun x : Plane => Train.lapS (fun y => iteratedDeriv ℓ (fun t => tr.p t y) r) x) =
      fun x : Plane => -iteratedDeriv ℓ (fun t => poissonSource (tr.v t) x) r := by
    funext x
    rw [← iteratedDeriv_lapS_eq hsm_p ℓ hr x]
    have hev : (fun t => Train.lapS (tr.p t) x) =ᶠ[nhds r]
        fun t => -poissonSource (tr.v t) x := by
      filter_upwards [Ioi_mem_nhds hr] with t ht
      have ht0 : 0 < t := ht
      exact slicePoisson ν c (t + 1) tr.v tr.p hν hc.le (by linarith)
        (trainSol_isClassicalOn tr (t + 1)) t ⟨ht0.le, by linarith⟩ x
    rw [hev.iteratedDeriv_eq ℓ]
    exact iteratedDeriv_neg ℓ (fun t => poissonSource (tr.v t) x) r
  rw [hlap_eq, derivWord_neg]

/-! ### 4. Time-integrated gradient bound for `Q_w` from the differentiated momentum equation -/

theorem iteratedDeriv_succ_vel_comp_eq {ν c : ℝ} (tr : B0140.TrainSol ν c)
    (ℓ : ℕ) (d : Fin 2) {r : ℝ} (hr : 0 < r) (x : Plane) :
    iteratedDeriv (ℓ + 1) (fun t => tr.v t x d) r =
      iteratedDeriv ℓ (fun t => (ν • Train.vecLaplacian (tr.v t) x) d) r
      - iteratedDeriv ℓ (fun t => Train.advection (tr.v t) x d) r
      - iteratedDeriv ℓ (fun t => Train.gradS (tr.p t) x d) r := by
  let F₁ : ℝ → Plane → Vec := fun t y => ν • Train.vecLaplacian (tr.v t) y
  let F₂ : ℝ → Plane → Vec := fun t y => Train.advection (tr.v t) y
  let F₃ : ℝ → Plane → Vec := fun t y => Train.gradS (tr.p t) y
  have hsm_v : Sm (fun p : ℝ × Plane => tr.v p.1 p.2) :=
    tr.isTrain.smooth_v.mono (Set.prod_mono Set.Ioi_subset_Ici_self Subset.rfl)
  have hsm_p : SmS (fun p : ℝ × Plane => tr.p p.1 p.2) :=
    tr.isTrain.smooth_p.mono (Set.prod_mono Set.Ioi_subset_Ici_self Subset.rfl)
  have hsm₁ : Sm (fun p : ℝ × Plane => F₁ p.1 p.2) := PartI_T25_1.sm_smul_vecLaplacian hsm_v ν
  have hsm₂ : Sm (fun p : ℝ × Plane => F₂ p.1 p.2) := PartI_T25_1.sm_advection hsm_v
  have hsm₃ : Sm (fun p : ℝ × Plane => F₃ p.1 p.2) := contDiffOn_gradS_of_smS hsm_p
  have hsm₁d : SmS (fun p : ℝ × Plane => F₁ p.1 p.2 d) :=
    (EuclideanSpace.proj d : Vec →L[ℝ] ℝ).contDiff.comp_contDiffOn hsm₁
  have hsm₂d : SmS (fun p : ℝ × Plane => F₂ p.1 p.2 d) :=
    (EuclideanSpace.proj d : Vec →L[ℝ] ℝ).contDiff.comp_contDiffOn hsm₂
  have hsm₃d : SmS (fun p : ℝ × Plane => F₃ p.1 p.2 d) :=
    (EuclideanSpace.proj d : Vec →L[ℝ] ℝ).contDiff.comp_contDiffOn hsm₃
  rw [PartI_HF_1.iteratedDeriv_vec_proj_eq hsm_v d (ℓ + 1) hr x,
    iteratedDeriv_succ_vel_eq tr ℓ hr x]
  have hproj := PartI_HF_1.iteratedDeriv_vec_proj_eq
    (V := fun t y => F₁ t y - F₂ t y - F₃ t y) ((hsm₁.sub hsm₂).sub hsm₃) d ℓ hr x
  simp only [PiLp.sub_apply] at hproj
  rw [← hproj]
  have hsub1 := iteratedDeriv_sub
    (vb_slice_smooth_at (fun t y => F₁ t y d - F₂ t y d) (hsm₁d.sub hsm₂d) hr x ℓ)
    (vb_slice_smooth_at (fun t y => F₃ t y d) hsm₃d hr x ℓ)
  have hsub2 := iteratedDeriv_sub
    (vb_slice_smooth_at (fun t y => F₁ t y d) hsm₁d hr x ℓ)
    (vb_slice_smooth_at (fun t y => F₂ t y d) hsm₂d hr x ℓ)
  exact hsub1.trans (congrArg (· - _) hsub2)

theorem hasDerivAt_vel_word_eq_rhs {ν c : ℝ} (tr : B0140.TrainSol ν c)
    (ℓ : ℕ) (w : List Bool) (d : Fin 2) {r : ℝ} (hr : 0 < r) (z : Plane) :
    HasDerivAt
      (fun t => B0151.derivWord w (fun x => iteratedDeriv ℓ (fun s => tr.v s x d) t) z)
      (B0151.derivWord w (fun x => iteratedDeriv ℓ (fun s => (ν • Train.vecLaplacian (tr.v s) x) d) r) z
        - B0151.derivWord w (fun x => iteratedDeriv ℓ (fun s => Train.advection (tr.v s) x d) r) z
        - B0151.derivWord w (fun x => iteratedDeriv ℓ (fun s => Train.gradS (tr.p s) x d) r) z) r := by
  have hsm_v : Sm (fun p : ℝ × Plane => tr.v p.1 p.2) :=
    tr.isTrain.smooth_v.mono (Set.prod_mono Set.Ioi_subset_Ici_self Subset.rfl)
  have hsm_p : SmS (fun p : ℝ × Plane => tr.p p.1 p.2) :=
    tr.isTrain.smooth_p.mono (Set.prod_mono Set.Ioi_subset_Ici_self Subset.rfl)
  have hsm_vd : SmS (fun p : ℝ × Plane => tr.v p.1 p.2 d) :=
    (EuclideanSpace.proj d : Vec →L[ℝ] ℝ).contDiff.comp_contDiffOn hsm_v
  have hsm₁d : SmS (fun p : ℝ × Plane => (ν • Train.vecLaplacian (tr.v p.1) p.2) d) :=
    (EuclideanSpace.proj d : Vec →L[ℝ] ℝ).contDiff.comp_contDiffOn
      (PartI_T25_1.sm_smul_vecLaplacian hsm_v ν)
  have hsm₂d : SmS (fun p : ℝ × Plane => Train.advection (tr.v p.1) p.2 d) :=
    (EuclideanSpace.proj d : Vec →L[ℝ] ℝ).contDiff.comp_contDiffOn
      (PartI_T25_1.sm_advection hsm_v)
  have hsm₃d : SmS (fun p : ℝ × Plane => Train.gradS (tr.p p.1) p.2 d) :=
    (EuclideanSpace.proj d : Vec →L[ℝ] ℝ).contDiff.comp_contDiffOn
      (contDiffOn_gradS_of_smS hsm_p)
  have hd := hasDerivAt_derivWord_iteratedDeriv (F := fun s x => tr.v s x d) hsm_vd ℓ w hr z
  have hfun : (fun x : Plane => iteratedDeriv (ℓ + 1) (fun s => tr.v s x d) r) =
      fun x : Plane =>
        iteratedDeriv ℓ (fun s => (ν • Train.vecLaplacian (tr.v s) x) d) r
        - iteratedDeriv ℓ (fun s => Train.advection (tr.v s) x d) r
        - iteratedDeriv ℓ (fun s => Train.gradS (tr.p s) x d) r :=
    funext fun x => iteratedDeriv_succ_vel_comp_eq tr ℓ d hr x
  have hc1 := contDiff_slice_iteratedDeriv_of_contDiffOn
    (fun s x => (ν • Train.vecLaplacian (tr.v s) x) d) hsm₁d ℓ hr
  have hc2 := contDiff_slice_iteratedDeriv_of_contDiffOn
    (fun s x => Train.advection (tr.v s) x d) hsm₂d ℓ hr
  have hc3 := contDiff_slice_iteratedDeriv_of_contDiffOn
    (fun s x => Train.gradS (tr.p s) x d) hsm₃d ℓ hr
  have hword : B0151.derivWord w (fun x => iteratedDeriv (ℓ + 1) (fun s => tr.v s x d) r) z =
      B0151.derivWord w (fun x => iteratedDeriv ℓ (fun s => (ν • Train.vecLaplacian (tr.v s) x) d) r) z
        - B0151.derivWord w (fun x => iteratedDeriv ℓ (fun s => Train.advection (tr.v s) x d) r) z
        - B0151.derivWord w (fun x => iteratedDeriv ℓ (fun s => Train.gradS (tr.p s) x d) r) z := by
    rw [hfun, derivWord_sub (hc1.sub hc2) hc3 w z, derivWord_sub hc1 hc2 w z]
  rwa [hword] at hd

theorem gradS_word_eq_partial_Q_w {ν c : ℝ} (tr : B0140.TrainSol ν c)
    (ℓ : ℕ) (w : List Bool) {r : ℝ} (hr : 0 < r) (z : Plane) :
    B0151.derivWord w (fun x => iteratedDeriv ℓ (fun s => Train.gradS (tr.p s) x 0) r) z =
      Cyl.partialQ (B0151.derivWord w (fun x => iteratedDeriv ℓ (fun s => tr.p s x) r)) z ∧
    B0151.derivWord w (fun x => iteratedDeriv ℓ (fun s => Train.gradS (tr.p s) x 1) r) z =
      Cyl.partialEta (B0151.derivWord w (fun x => iteratedDeriv ℓ (fun s => tr.p s x) r)) z := by
  have hsm_p : SmS (fun p : ℝ × Plane => tr.p p.1 p.2) :=
    tr.isTrain.smooth_p.mono (Set.prod_mono Set.Ioi_subset_Ici_self Subset.rfl)
  have hslice_p : ContDiff ℝ ∞ (fun x : Plane => iteratedDeriv ℓ (fun s => tr.p s x) r) :=
    contDiff_slice_iteratedDeriv_of_contDiffOn tr.p hsm_p ℓ hr
  constructor
  · have h0 : (fun x : Plane => iteratedDeriv ℓ (fun s => Train.gradS (tr.p s) x 0) r) =
        Cyl.partialQ (fun x : Plane => iteratedDeriv ℓ (fun s => tr.p s x) r) := by
      funext x
      have hg0 : (fun s => Train.gradS (tr.p s) x 0) = fun s => Cyl.partialQ (tr.p s) x := by
        funext s; simp [Train.gradS]
      rw [hg0, PartI_HF_1.iteratedDeriv_partialQ_eq hsm_p ℓ hr x]
    rw [h0, derivWord_partialQ w hslice_p]
  · have h1 : (fun x : Plane => iteratedDeriv ℓ (fun s => Train.gradS (tr.p s) x 1) r) =
        Cyl.partialEta (fun x : Plane => iteratedDeriv ℓ (fun s => tr.p s x) r) := by
      funext x
      have hg1 : (fun s => Train.gradS (tr.p s) x 1) = fun s => Cyl.partialEta (tr.p s) x := by
        funext s; simp [Train.gradS]
      rw [hg1, PartI_HF_1.iteratedDeriv_partialEta_eq hsm_p ℓ hr x]
    rw [h1, derivWord_partialEta w hslice_p]

theorem abs_integral_grad_word_le {ν c : ℝ} (hν : 0 < ν) (tr : B0140.TrainSol ν c)
    (ℓ : ℕ) (w : List Bool) (d : Fin 2)
    {M_v M_adv : ℝ}
    (hMv : ∀ r : ℝ, 0 < r → ∀ z : Plane,
      ‖ageJet ℓ w.length tr.v r z‖ ≤ M_v ∧ ‖ageJet ℓ (w.length + 2) tr.v r z‖ ≤ M_v)
    (hMadv : ∀ r : ℝ, 0 < r → ∀ z : Plane,
      ‖ageJet ℓ w.length (fun t y => Train.advection (tr.v t) y) r z‖ ≤ M_adv)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (z : Plane) :
    |∫ r in a..b,
      B0151.derivWord w (fun x => iteratedDeriv ℓ (fun s => Train.gradS (tr.p s) x d) r) z| ≤
      2 * M_v + (2 * ν * M_v + M_adv) * |b - a| := by
  let F₀ : ℝ → Plane → ℝ := fun r x => tr.v r x d
  let F₁ : ℝ → Plane → ℝ := fun r x => (ν • Train.vecLaplacian (tr.v r) x) d
  let F₂ : ℝ → Plane → ℝ := fun r x => Train.advection (tr.v r) x d
  let F₃ : ℝ → Plane → ℝ := fun r x => Train.gradS (tr.p r) x d
  have hsm_v : Sm (fun p : ℝ × Plane => tr.v p.1 p.2) :=
    tr.isTrain.smooth_v.mono (Set.prod_mono Set.Ioi_subset_Ici_self Subset.rfl)
  have hsm_p : SmS (fun p : ℝ × Plane => tr.p p.1 p.2) :=
    tr.isTrain.smooth_p.mono (Set.prod_mono Set.Ioi_subset_Ici_self Subset.rfl)
  have hsm_vd : SmS (fun p : ℝ × Plane => F₀ p.1 p.2) :=
    (EuclideanSpace.proj d : Vec →L[ℝ] ℝ).contDiff.comp_contDiffOn hsm_v
  have hsm₁ : Sm (fun p : ℝ × Plane => (ν • Train.vecLaplacian (tr.v p.1) p.2)) :=
    PartI_T25_1.sm_smul_vecLaplacian hsm_v ν
  have hsm₂ : Sm (fun p : ℝ × Plane => Train.advection (tr.v p.1) p.2) :=
    PartI_T25_1.sm_advection hsm_v
  have hsm₃ : Sm (fun p : ℝ × Plane => Train.gradS (tr.p p.1) p.2) :=
    contDiffOn_gradS_of_smS hsm_p
  have hsm₁d : SmS (fun p : ℝ × Plane => F₁ p.1 p.2) :=
    (EuclideanSpace.proj d : Vec →L[ℝ] ℝ).contDiff.comp_contDiffOn hsm₁
  have hsm₂d : SmS (fun p : ℝ × Plane => F₂ p.1 p.2) :=
    (EuclideanSpace.proj d : Vec →L[ℝ] ℝ).contDiff.comp_contDiffOn hsm₂
  have hsm₃d : SmS (fun p : ℝ × Plane => F₃ p.1 p.2) :=
    (EuclideanSpace.proj d : Vec →L[ℝ] ℝ).contDiff.comp_contDiffOn hsm₃
  let V : ℝ → ℝ := fun r =>
    B0151.derivWord w (fun x => iteratedDeriv ℓ (fun s => F₀ s x) r) z
  let Visc : ℝ → ℝ := fun r =>
    B0151.derivWord w (fun x => iteratedDeriv ℓ (fun s => F₁ s x) r) z
  let Adv : ℝ → ℝ := fun r =>
    B0151.derivWord w (fun x => iteratedDeriv ℓ (fun s => F₂ s x) r) z
  let Grad : ℝ → ℝ := fun r =>
    B0151.derivWord w (fun x => iteratedDeriv ℓ (fun s => F₃ s x) r) z
  have hsub : Icc a b ⊆ Ioi (0 : ℝ) := fun r hr => ha.trans_le hr.1
  have huIcc : uIcc a b ⊆ Ioi (0 : ℝ) := by
    rw [uIcc_of_le hab]
    exact hsub
  have hcV : ContinuousOn V (Icc a b) :=
    (continuousOn_derivWord_iteratedDeriv (F := F₀) hsm_vd ℓ w z).mono hsub
  have hcVisc : ContinuousOn Visc (uIcc a b) :=
    (continuousOn_derivWord_iteratedDeriv (F := F₁) hsm₁d ℓ w z).mono huIcc
  have hcAdv : ContinuousOn Adv (uIcc a b) :=
    (continuousOn_derivWord_iteratedDeriv (F := F₂) hsm₂d ℓ w z).mono huIcc
  have hcGrad : ContinuousOn Grad (uIcc a b) :=
    (continuousOn_derivWord_iteratedDeriv (F := F₃) hsm₃d ℓ w z).mono huIcc
  have hiCA : IntervalIntegrable (fun r => Visc r - Adv r) volume a b :=
    (hcVisc.sub hcAdv).intervalIntegrable
  have hiGrad : IntervalIntegrable Grad volume a b := hcGrad.intervalIntegrable
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hcV
    (fun r hr => hasDerivAt_vel_word_eq_rhs tr ℓ w d (ha.trans hr.1) z)
    (hiCA.sub hiGrad)
  rw [intervalIntegral.integral_sub hiCA hiGrad] at hftc
  have hGrad_eq : ∫ r in a..b, Grad r = (∫ r in a..b, (Visc r - Adv r)) - (V b - V a) := by
    linarith
  have hV_bd : ∀ r : ℝ, 0 < r → |V r| ≤ M_v := by
    intro r hr
    exact ((abs_derivWord_iteratedDeriv_le (F := F₀) hsm_vd ℓ w hr z).trans
      (PartI_HF_1.norm_ageJet_vec_proj_le hsm_v d ℓ w.length hr z)).trans (hMv r hr z).1
  have hCA_bd : ∀ r : ℝ, 0 < r → |Visc r - Adv r| ≤ 2 * ν * M_v + M_adv := by
    intro r hr
    have h1 : |Visc r| ≤ 2 * ν * M_v := by
      have hw1 := (abs_derivWord_iteratedDeriv_le (F := F₁) hsm₁d ℓ w hr z).trans
        (PartI_HF_1.norm_ageJet_vec_proj_le hsm₁ d ℓ w.length hr z)
      have hw2 := PartI_T25_1.norm_ageJet_smul_vecLaplacian_le hsm_v hν.le ℓ w.length hr z
      have hw3 := (hMv r hr z).2
      have : (2 * ν) * ‖ageJet ℓ (w.length + 2) tr.v r z‖ ≤ 2 * ν * M_v :=
        mul_le_mul_of_nonneg_left hw3 (by positivity)
      exact (hw1.trans hw2).trans this
    have h2 : |Adv r| ≤ M_adv :=
      ((abs_derivWord_iteratedDeriv_le (F := F₂) hsm₂d ℓ w hr z).trans
        (PartI_HF_1.norm_ageJet_vec_proj_le hsm₂ d ℓ w.length hr z)).trans (hMadv r hr z)
    calc |Visc r - Adv r| ≤ |Visc r| + |Adv r| := abs_sub _ _
      _ ≤ 2 * ν * M_v + M_adv := add_le_add h1 h2
  have hint_CA : |∫ r in a..b, (Visc r - Adv r)| ≤ (2 * ν * M_v + M_adv) * |b - a| := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (f := fun r => Visc r - Adv r) (a := a) (b := b) (C := 2 * ν * M_v + M_adv)
      (fun r hr => by
        rw [Set.uIoc_of_le hab] at hr
        rw [Real.norm_eq_abs]
        exact hCA_bd r (ha.trans hr.1))
    simpa [Real.norm_eq_abs] using h
  have hVa : |V a| ≤ M_v := hV_bd a ha
  have hVb : |V b| ≤ M_v := hV_bd b (ha.trans_le hab)
  change |∫ r in a..b, Grad r| ≤ 2 * M_v + (2 * ν * M_v + M_adv) * |b - a|
  rw [hGrad_eq]
  have htri1 := abs_sub (∫ r in a..b, (Visc r - Adv r)) (V b - V a)
  have htri2 := abs_sub (V b) (V a)
  linarith

/-! ### 5. Oscillation bound via `PbOscLinear`, `pbTimeAvgSmooth`, and `PbAvgLimit` -/

theorem pbOscLinear_proof : PbOscLinear :=
  pbOscLinear_of cylPoisModeC2 cylPoisModeLaplace cylPoisQModeEstimates cylPoisFourierPointwise
    cylPoisQAvgReal pbGradToGrowth pbMaxPrincipleLinear

theorem pbAvgLimit_proof : PbAvgLimit :=
  pbAvgLimit_of pbHmeanTimeIntegral pbHmeanTimeContinuous pbRealAvgLimit

theorem osc_bound_of_time_grad {c T K L M1 : ℝ} (hc : 0 < c) (hT : 0 < T)
    (hM1 : ∀ q : Plane → ℝ, ContDiff ℝ 2 q → Cyl.IsPeriodic c q →
      (∃ L' : ℝ, ∀ z, |Cyl.partialQ q z| ≤ L' ∧ |Cyl.partialEta q z| ≤ L') →
      (∀ z, |Train.lapS q z| ≤ K) → ∀ z : Plane, |q z - hmean c q z.2| ≤ M1)
    (q : ℝ → Plane → ℝ)
    (hsm : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => q x.1 x.2) (Icc 0 T ×ˢ univ))
    (hper : ∀ σ ∈ Icc (0 : ℝ) T, Cyl.IsPeriodic c (q σ))
    (hlap : ∀ σ ∈ Icc (0 : ℝ) T, ∀ z : Plane, |Train.lapS (q σ) z| ≤ K)
    (hgrad : ∀ a ∈ Icc (0 : ℝ) T, ∀ b ∈ Icc (0 : ℝ) T, a ≤ b → ∀ z : Plane,
      |∫ σ in a..b, Cyl.partialQ (q σ) z| ≤ L ∧ |∫ σ in a..b, Cyl.partialEta (q σ) z| ≤ L)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) T) (z : Plane) :
    |q s z - hmean c (q s) z.2| ≤ M1 := by
  have hAvg : ∀ a ∈ Icc (0 : ℝ) T, ∀ b ∈ Icc (0 : ℝ) T, a < b → ∀ w : Plane,
      |pbAvg q a b w - hmean c (pbAvg q a b) w.2| ≤ M1 := by
    intro a ha b hb hab w
    obtain ⟨hP2, hPq, hPe, hPl⟩ := pbTimeAvgSmooth T q a b ha hb hsm
    have hba : 0 < b - a := sub_pos.2 hab
    have hsub : uIcc a b ⊆ Icc 0 T := by
      rw [uIcc_of_le hab.le]
      exact Icc_subset_Icc ha.1 hb.2
    have hq_def : pbAvg q a b = fun y => (b - a)⁻¹ * ∫ σ in a..b, q σ y := rfl
    have hC2 : ContDiff ℝ 2 (pbAvg q a b) := by
      rw [hq_def]
      exact contDiff_const.mul hP2
    have hper_avg : Cyl.IsPeriodic c (pbAvg q a b) := by
      intro y
      show (b - a)⁻¹ * ∫ σ in a..b, q σ (y.1 + c, y.2) = (b - a)⁻¹ * ∫ σ in a..b, q σ y
      congr 1
      refine intervalIntegral.integral_congr (fun σ hσ => ?_)
      exact hper σ (hsub hσ) y
    have hgrad_avg : ∃ L' : ℝ, ∀ y, |Cyl.partialQ (pbAvg q a b) y| ≤ L' ∧
        |Cyl.partialEta (pbAvg q a b) y| ≤ L' := by
      refine ⟨(b - a)⁻¹ * L, fun y => ?_⟩
      obtain ⟨h1, h2⟩ := hgrad a ha b hb hab.le y
      rw [hq_def, pbc_partialQ_const_mul, pbc_partialEta_const_mul, hPq, hPe, abs_mul, abs_mul,
        abs_of_pos (inv_pos.2 hba)]
      exact ⟨mul_le_mul_of_nonneg_left h1 (inv_pos.2 hba).le,
        mul_le_mul_of_nonneg_left h2 (inv_pos.2 hba).le⟩
    have hlap_avg : ∀ y, |Train.lapS (pbAvg q a b) y| ≤ K := by
      intro y
      rw [hq_def, pbc_lapS_const_mul, hPl, abs_mul, abs_of_pos (inv_pos.2 hba)]
      have hint : |∫ σ in a..b, Train.lapS (q σ) y| ≤ K * |b - a| := by
        have := intervalIntegral.norm_integral_le_of_norm_le_const
          (f := fun σ => Train.lapS (q σ) y) (a := a) (b := b) (C := K)
          (fun σ hσ => by
            rw [Set.uIoc_of_le hab.le] at hσ
            rw [Real.norm_eq_abs]
            exact hlap σ ⟨ha.1.trans hσ.1.le, hσ.2.trans hb.2⟩ y)
        simpa [Real.norm_eq_abs] using this
      calc (b - a)⁻¹ * |∫ σ in a..b, Train.lapS (q σ) y|
          ≤ (b - a)⁻¹ * (K * |b - a|) :=
            mul_le_mul_of_nonneg_left hint (inv_pos.2 hba).le
        _ = K := by
            rw [abs_of_pos hba]
            field_simp
    exact hM1 (pbAvg q a b) hC2 hper_avg hgrad_avg hlap_avg w
  exact pbAvgLimit_proof c T M1 q hc hT hsm.continuousOn hAvg s hs z

theorem periodic_slice_iteratedDeriv_p {ν c : ℝ} (tr : B0140.TrainSol ν c) :
    ∀ (ℓ : ℕ) {r : ℝ}, 0 < r → Cyl.IsPeriodic c (fun x => iteratedDeriv ℓ (fun t => tr.p t x) r)
  | 0, r, hr => fun x => tr.isTrain.periodic_p r hr.le x
  | ℓ + 1, r, hr => by
      intro x
      change iteratedDeriv (ℓ + 1) (fun t => tr.p t (x.1 + c, x.2)) r =
        iteratedDeriv (ℓ + 1) (fun t => tr.p t x) r
      rw [iteratedDeriv_succ, iteratedDeriv_succ]
      have hev : (fun s => iteratedDeriv ℓ (fun t => tr.p t (x.1 + c, x.2)) s) =ᶠ[nhds r]
          fun s => iteratedDeriv ℓ (fun t => tr.p t x) s := by
        filter_upwards [Ioi_mem_nhds hr] with s hs using
          periodic_slice_iteratedDeriv_p tr ℓ hs x
      exact hev.deriv_eq

/-! ### 6. Wordwise bound on `Q_w` and assembly of `TrainVelAgeStepPressFixed` -/

theorem abs_derivWord_iteratedDeriv_p_le {ν c : ℝ} (hν : 0 < ν) (hc : 1 < c)
    (tr : B0140.TrainSol ν c) (htr : IsBUCTrain tr)
    (ℓ : ℕ) (hIH : ∀ r : ℕ, r ≤ ℓ → VelOrderBoundedFixed tr r)
    (w : List Bool) :
    ∃ M_w : ℝ, ∀ s : ℝ, 0 < s → ∀ z : Plane,
      |B0151.derivWord w (fun x => iteratedDeriv ℓ (fun t => tr.p t x) s) z| ≤ M_w := by
  have hc0 : 0 < c := zero_lt_one.trans hc
  obtain ⟨M_v, hMv_nn, hMv_bd⟩ := PartI_HF_1.uniform_vel_rect (w.length + 2) ℓ hIH
  obtain ⟨M_adv0, hMadv0⟩ := trainVelAgeStepAdvFixed_proof hν hc tr htr ℓ hIH w.length
  let M_adv : ℝ := max M_adv0 0
  let K_w : ℝ := 4 * (2 : ℝ) ^ (ℓ + w.length) * M_v * M_v
  let M_mean : ℝ := (2 : ℝ) ^ (ℓ + w.length) * M_v * M_v
  obtain ⟨M1, hM1⟩ := pbOscLinear_proof c K_w hc0
  refine ⟨M1 + M_mean, fun s hs z => ?_⟩
  let Q_w : ℝ → Plane → ℝ := fun r y =>
    B0151.derivWord w (fun x => iteratedDeriv ℓ (fun t => tr.p t x) r) y
  have hsm_p : SmS (fun p : ℝ × Plane => tr.p p.1 p.2) :=
    tr.isTrain.smooth_p.mono (Set.prod_mono Set.Ioi_subset_Ici_self Subset.rfl)
  have hsm_v : Sm (fun p : ℝ × Plane => tr.v p.1 p.2) :=
    tr.isTrain.smooth_v.mono (Set.prod_mono Set.Ioi_subset_Ici_self Subset.rfl)
  have hsm_Qw : SmS (fun p : ℝ × Plane => Q_w p.1 p.2) :=
    smS_derivWord_iteratedDeriv (F := tr.p) hsm_p ℓ w
  -- 1. Bound on the horizontal mean `|hmean c (Q_w s) z.2| ≤ M_mean`
  have hmean_bd : |hmean c (Q_w s) z.2| ≤ M_mean := by
    have hslice_p : ContDiff ℝ ∞ (fun x : Plane => iteratedDeriv ℓ (fun t => tr.p t x) s) :=
      contDiff_slice_iteratedDeriv_of_contDiffOn tr.p hsm_p ℓ hs
    have hper_p : Cyl.IsPeriodic c (fun x => iteratedDeriv ℓ (fun t => tr.p t x) s) :=
      periodic_slice_iteratedDeriv_p tr ℓ hs
    have hhm_eq : hmean c (Q_w s) z.2 =
        B0151.derivWord w (fun x : Plane => iteratedDeriv ℓ (fun t => hmean c (tr.p t) x.2) s) z := by
      rw [hmean_derivWord_eq hc0 hslice_p hper_p w z]
      congr 1
      funext x
      exact (iteratedDeriv_hmean_scalar_eq (f := tr.p) hc0 hsm_p ℓ hs x.2).symm
    have hsm_hm : SmS (fun p : ℝ × Plane => hmean c (tr.p p.1) p.2.2) :=
      smS_hmean_scalar hc0 (F := tr.p) hsm_p
    rw [hhm_eq]
    exact (abs_derivWord_iteratedDeriv_le
        (F := fun t x => hmean c (tr.p t) x.2) hsm_hm ℓ w hs z).trans
      (norm_ageJet_hmean_p_le hν hc tr htr ℓ w.length hs hMv_nn z
        (fun y r hr i hi => hMv_bd s hs y r hr i (by omega)))
  -- 2. Bound on the oscillation `|Q_w s z - hmean c (Q_w s) z.2| ≤ M1` via time shift `t₀ = s / 2`
  have hosc_bd : |Q_w s z - hmean c (Q_w s) z.2| ≤ M1 := by
    let t₀ : ℝ := s / 2
    have ht₀ : 0 < t₀ := half_pos hs
    let q_s : ℝ → Plane → ℝ := fun σ y => Q_w (t₀ + σ) y
    have hshift_map : ContDiffOn ℝ ∞ (fun p : ℝ × Plane => (t₀ + p.1, p.2)) (Icc 0 s ×ˢ univ) :=
      ((contDiff_const.add contDiff_fst).prodMk contDiff_snd).contDiffOn
    have hsm_qs : ContDiffOn ℝ ∞ (fun p : ℝ × Plane => q_s p.1 p.2) (Icc 0 s ×ˢ univ) :=
      hsm_Qw.comp hshift_map (fun p hp => ⟨add_pos_of_pos_of_nonneg ht₀ hp.1.1, trivial⟩)
    have hper_qs : ∀ σ ∈ Icc (0 : ℝ) s, Cyl.IsPeriodic c (q_s σ) := by
      intro σ hσ
      exact periodic_derivWord_cyl
        (periodic_slice_iteratedDeriv_p tr ℓ (add_pos_of_pos_of_nonneg ht₀ hσ.1)) w
    have hlap_qs : ∀ σ ∈ Icc (0 : ℝ) s, ∀ y : Plane, |Train.lapS (q_s σ) y| ≤ K_w := by
      intro σ hσ y
      have hr : 0 < t₀ + σ := add_pos_of_pos_of_nonneg ht₀ hσ.1
      dsimp [q_s, Q_w]
      rw [lapS_derivWord_iteratedDeriv_p_eq hν hc tr ℓ w hr y, abs_neg]
      have hsm_ps : SmS (fun p : ℝ × Plane => poissonSource (tr.v p.1) p.2) := by
        have hv0 : SmS (fun p : ℝ × Plane => tr.v p.1 p.2 0) :=
          (EuclideanSpace.proj (0 : Fin 2) : Vec →L[ℝ] ℝ).contDiff.comp_contDiffOn hsm_v
        have hv1 : SmS (fun p : ℝ × Plane => tr.v p.1 p.2 1) :=
          (EuclideanSpace.proj (1 : Fin 2) : Vec →L[ℝ] ℝ).contDiff.comp_contDiffOn hsm_v
        have hq0 := PartI_HF_1.smS_partialQ (F := fun t x => tr.v t x 0) hv0
        have hq1 := PartI_HF_1.smS_partialQ (F := fun t x => tr.v t x 1) hv1
        have he0 := PartI_HF_1.smS_partialEta (F := fun t x => tr.v t x 0) hv0
        have he1 := PartI_HF_1.smS_partialEta (F := fun t x => tr.v t x 1) hv1
        exact (((hq0.mul hq0).add ((contDiffOn_const (c := (2 : ℝ))).mul (hq1.mul he0))).add
          (he1.mul he1)).congr (fun ⟨t, x⟩ _ => by unfold poissonSource; ring)
      exact (abs_derivWord_iteratedDeriv_le
          (F := fun t x => poissonSource (tr.v t) x) hsm_ps ℓ w hr y).trans
        (norm_ageJet_poissonSource_le hsm_v ℓ w.length hr hMv_nn y
          (fun m hm i hi => hMv_bd (t₀ + σ) hr y m hm i (by omega)))
    let L_s : ℝ := 2 * M_v + (2 * ν * M_v + M_adv) * s
    have hgrad_qs : ∀ a ∈ Icc (0 : ℝ) s, ∀ b ∈ Icc (0 : ℝ) s, a ≤ b → ∀ y : Plane,
        |∫ σ in a..b, Cyl.partialQ (q_s σ) y| ≤ L_s ∧
          |∫ σ in a..b, Cyl.partialEta (q_s σ) y| ≤ L_s := by
      intro a ha b hb hab y
      have ha' : 0 < t₀ + a := add_pos_of_pos_of_nonneg ht₀ ha.1
      have hab' : t₀ + a ≤ t₀ + b := by linarith
      have hba_le : |(t₀ + b) - (t₀ + a)| ≤ s := by
        rw [show (t₀ + b) - (t₀ + a) = b - a by ring, abs_of_nonneg (sub_nonneg.2 hab)]
        linarith [ha.1, hb.2]
      have hMv_pair : ∀ r : ℝ, 0 < r → ∀ x : Plane,
          ‖ageJet ℓ w.length tr.v r x‖ ≤ M_v ∧ ‖ageJet ℓ (w.length + 2) tr.v r x‖ ≤ M_v :=
        fun r hr x => ⟨hMv_bd r hr x ℓ le_rfl w.length (by omega),
          hMv_bd r hr x ℓ le_rfl (w.length + 2) le_rfl⟩
      have hMadv_le : ∀ r : ℝ, 0 < r → ∀ x : Plane,
          ‖ageJet ℓ w.length (fun t u => Train.advection (tr.v t) u) r x‖ ≤ M_adv :=
        fun r hr x => (hMadv0 r hr x).trans (le_max_left _ _)
      have hMadv_nn : 0 ≤ M_adv := le_max_right _ _
      have hC_le : 2 * M_v + (2 * ν * M_v + M_adv) * |(t₀ + b) - (t₀ + a)| ≤ L_s := by
        dsimp [L_s]
        have hcoeff : 0 ≤ 2 * ν * M_v + M_adv := by positivity
        linarith [mul_le_mul_of_nonneg_left hba_le hcoeff]
      have hshift_Q : (∫ σ in a..b, Cyl.partialQ (q_s σ) y) =
          ∫ r in (t₀ + a)..(t₀ + b),
            B0151.derivWord w (fun x => iteratedDeriv ℓ (fun t => Train.gradS (tr.p t) x 0) r) y := by
        rw [show (fun σ => Cyl.partialQ (q_s σ) y) = fun σ => Cyl.partialQ (Q_w (t₀ + σ)) y from rfl,
          intervalIntegral.integral_comp_add_left (fun r => Cyl.partialQ (Q_w r) y) t₀]
        refine intervalIntegral.integral_congr (fun r hr => ?_)
        rw [uIcc_of_le hab'] at hr
        exact (gradS_word_eq_partial_Q_w tr ℓ w (ha'.trans_le hr.1) y).1.symm
      have hshift_E : (∫ σ in a..b, Cyl.partialEta (q_s σ) y) =
          ∫ r in (t₀ + a)..(t₀ + b),
            B0151.derivWord w (fun x => iteratedDeriv ℓ (fun t => Train.gradS (tr.p t) x 1) r) y := by
        rw [show (fun σ => Cyl.partialEta (q_s σ) y) = fun σ => Cyl.partialEta (Q_w (t₀ + σ)) y from rfl,
          intervalIntegral.integral_comp_add_left (fun r => Cyl.partialEta (Q_w r) y) t₀]
        refine intervalIntegral.integral_congr (fun r hr => ?_)
        rw [uIcc_of_le hab'] at hr
        exact (gradS_word_eq_partial_Q_w tr ℓ w (ha'.trans_le hr.1) y).2.symm
      rw [hshift_Q, hshift_E]
      exact ⟨(abs_integral_grad_word_le hν tr ℓ w 0 hMv_pair hMadv_le ha' hab' y).trans hC_le,
        (abs_integral_grad_word_le hν tr ℓ w 1 hMv_pair hMadv_le ha' hab' y).trans hC_le⟩
    have hs_mem : s / 2 ∈ Icc (0 : ℝ) s := ⟨by linarith, by linarith⟩
    have hosc := osc_bound_of_time_grad hc0 hs hM1 q_s hsm_qs hper_qs hlap_qs hgrad_qs hs_mem z
    have hqs_eq : q_s (s / 2) = Q_w s := by
      funext y
      dsimp [q_s, t₀]
      rw [add_halves]
    rwa [hqs_eq] at hosc
  calc |Q_w s z| = |(Q_w s z - hmean c (Q_w s) z.2) + hmean c (Q_w s) z.2| := by rw [sub_add_cancel]
    _ ≤ |Q_w s z - hmean c (Q_w s) z.2| + |hmean c (Q_w s) z.2| := abs_add_le _ _
    _ ≤ M1 + M_mean := add_le_add hosc_bd hmean_bd

end PressStepFixed

/-- **Pressure age-step at fixed parameters (`trainVelAgeStepPressFixed`, Task `PartI:HF/1/1`)**:
source lines 318–322, 326–359, 427–435 of `the November 2 reference manuscript`. -/
theorem trainVelAgeStepPressFixed : TrainVelAgeStepPressFixed := by
  intro ν c hν hc tr htr ℓ hIH j
  choose M_w hM_w using fun w : List Bool =>
    PressStepFixed.abs_derivWord_iteratedDeriv_p_le hν hc tr htr ℓ hIH w
  let S : ℝ := ∑ w ∈ wordsOfLength (j + 1), M_w w
  refine ⟨2 * S, fun s hs z => ?_⟩
  have hsm_p : SmS (fun p : ℝ × Plane => tr.p p.1 p.2) :=
    tr.isTrain.smooth_p.mono (Set.prod_mono Set.Ioi_subset_Ici_self Subset.rfl)
  have hslice_p : ContDiff ℝ ∞ (fun x : Plane => iteratedDeriv ℓ (fun t => tr.p t x) s) :=
    contDiff_slice_iteratedDeriv_of_contDiffOn tr.p hsm_p ℓ hs
  have hp_jet_le : ‖ageJet ℓ (j + 1) tr.p s z‖ ≤ S := by
    calc ‖ageJet ℓ (j + 1) tr.p s z‖
        ≤ ∑ w ∈ wordsOfLength (j + 1),
            |B0151.derivWord w (fun x => iteratedDeriv ℓ (fun t => tr.p t x) s) z| :=
          cjw_norm_le_sum (fun x => iteratedDeriv ℓ (fun t => tr.p t x) s) hslice_p (j + 1) z
      _ ≤ ∑ w ∈ wordsOfLength (j + 1), M_w w :=
          Finset.sum_le_sum (fun w _ => hM_w w s hs z)
  have hgrad := norm_ageJet_gradS_tr_p_le tr ℓ j hs z
  linarith

end UnforcedLeray.Short.PartI
