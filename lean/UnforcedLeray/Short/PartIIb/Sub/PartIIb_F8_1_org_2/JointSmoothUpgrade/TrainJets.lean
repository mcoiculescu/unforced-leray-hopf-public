import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F8_1_org_2
import UnforcedLeray.Short.PartI.Tasks.TrainHeatFixed.TrainJetsBoundedFixed.PressStep

/-!
# `JointSmoothUpgrade/TrainJets.lean`

All-order mixed age-and-spatial derivative bounds on compact subintervals `[T₁, T₂] ⊂ (0, 2)` for
the shifted BUC train drift `F8Ex.shiftedDriftTrain tr σ` at arbitrary `0 < c`, `0 < ν`, `0 ≤ σ`
(without any `1 ≤ c` or `ν ≤ 1` restriction).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb.F8JointUpgrade

open UnforcedLeray
open UnforcedLeray.Train (Vec)
open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Short.PartI
open UnforcedLeray.Short.PartI.PartI_HF_1 (SmS.add SmS.mul)
open UnforcedLeray.Short.IIb (Sm mem_UU hasDerivAt_slice vb_slice_smooth_at)

/-! ## 1. Velocity axial decay and pressure horizontal-mean / Poisson identities for `0 < c` -/

/-- Periodic window integral bound for `0 < c` and `2 * r ≤ c`. -/
theorem vd_window_le_pos {c r q₀ : ℝ} (_hc : 0 < c) (hr0 : 0 < r) (hrc : 2 * r ≤ c)
    {f : ℝ → ℝ} (hf : Function.Periodic f c) (hcont : Continuous f) (hnn : ∀ q, 0 ≤ f q) :
    ∫ q in (q₀ - r)..(q₀ + r), f q ≤ ∫ q in (-c / 2)..(c / 2), f q := by
  have hmono : ∫ q in (q₀ - r)..(q₀ + r), f q ≤ ∫ q in (q₀ - r)..(q₀ - r + c), f q :=
    intervalIntegral.integral_mono_interval le_rfl (by linarith) (by linarith)
      (Filter.Eventually.of_forall hnn) (hcont.intervalIntegrable _ _)
  have hper := hf.intervalIntegral_add_eq (q₀ - r) (-c / 2)
  have hc2 : -c / 2 + c = c / 2 := by ring
  rw [hc2] at hper
  rwa [hper] at hmono

/-- Fubini integrability of the one-period slice energy `vdG w c` for arbitrary `0 < c`. -/
theorem vd_G_integrable_pos {w : Plane → Vec} {c : ℝ} (hc : 0 < c)
    (hfin : IntegrableOn (fun z => ‖w z‖ ^ 2) (Cyl.cell c)) : Integrable (vdG w c) := by
  have e : ((volume : Measure ℝ).restrict (Ico (-c / 2) (c / 2))).prod
      ((volume : Measure ℝ).restrict (univ : Set ℝ)) =
      (volume : Measure Plane).restrict (Cyl.cell c) := by
    rw [Measure.prod_restrict]
    rfl
  have h2 : Integrable (fun z : Plane => ‖w z‖ ^ 2)
      (((volume : Measure ℝ).restrict (Ico (-c / 2) (c / 2))).prod
        ((volume : Measure ℝ).restrict (univ : Set ℝ))) := by
    rw [e]
    exact hfin
  have h3 := h2.integral_prod_right
  rw [Measure.restrict_univ] at h3
  have hconv : vdG w c = fun η => ∫ q in Ico (-c / 2) (c / 2), ‖w (q, η)‖ ^ 2 := by
    funext η
    unfold vdG
    rw [intervalIntegral.integral_of_le (show -c / 2 ≤ c / 2 by linarith),
      integral_Ioc_eq_integral_Ioo, integral_Ico_eq_integral_Ioo]
  rwa [hconv]

/-- Velocity decay as `|z.2| → ∞` for any BUC train at arbitrary `0 < c`, `0 < ν`, `r ≥ 0`. -/
theorem vel_decay_pos {ν c : ℝ} (_hν : 0 < ν) (hc : 0 < c)
    (tr : B0140.TrainSol ν c) (hbuc : IsBUCTrain tr) {r : ℝ} (hr : 0 ≤ r) :
    Tendsto (tr.v r) (comap (fun z : Plane => |z.2|) atTop) (𝓝 0) := by
  let T : ℝ := r + 1
  have hT0 : 0 ≤ T := by dsimp [T]; linarith
  have hs : r ∈ Icc (0 : ℝ) T := ⟨hr, by dsimp [T]; linarith⟩
  have hcl : IsClassicalOn ν c T tr.v tr.p := trainSol_isClassicalOn tr T
  have hb : HasBoundedDerivsOn T tr.v := hbuc T hT0
  obtain ⟨B0, hB0'⟩ := vd_fderiv_bound hb
  obtain ⟨M0, hM0'⟩ := exists_sup_bound_of_hasBoundedDerivsOn hb
  let B : ℝ := max B0 0
  let M : ℝ := max M0 0
  have hB0 : 0 ≤ B := le_max_right _ _
  have hM0 : 0 ≤ M := le_max_right _ _
  have hw : ContDiff ℝ ∞ (tr.v r) := vd_contDiff_slice hcl hs
  have hBw : ∀ z, ‖fderiv ℝ (tr.v r) z‖ ≤ B := fun z => (hB0' r hs z).trans (le_max_left _ _)
  have hMw : ∀ z, ‖tr.v r z‖ ≤ M := fun z => (hM0' r hs z).trans (le_max_left _ _)
  have hper : Cyl.IsPeriodic c (tr.v r) := hcl.periodic_v r hs
  have hG : Integrable (vdG (tr.v r) c) := vd_G_integrable_pos hc (hcl.finite_energy r hs)
  have hGnn : ∀ η, 0 ≤ vdG (tr.v r) c η := fun η =>
    intervalIntegral.integral_nonneg (show -c / 2 ≤ c / 2 by linarith) (fun _ _ => sq_nonneg _)
  rw [Metric.tendsto_nhds]
  intro ε hε
  let δ : ℝ := ε ^ 2
  have hδ : 0 < δ := pow_pos hε 2
  have hden : 0 < 16 * (B * M + 1) := by nlinarith [mul_nonneg hB0 hM0]
  let ρ : ℝ := min (c / 2) (δ / (16 * (B * M + 1)))
  have hρ0 : 0 < ρ := lt_min (half_pos hc) (div_pos hδ hden)
  have hρc : 2 * ρ ≤ c := by
    have : ρ ≤ c / 2 := min_le_left _ _
    linarith
  have hρδ : 16 * B * ρ * M ≤ δ := by
    have h1 : ρ ≤ δ / (16 * (B * M + 1)) := min_le_right _ _
    have h2 : ρ * (16 * (B * M + 1)) ≤ δ := (le_div_iff₀ hden).1 h1
    nlinarith [h2, hρ0, mul_nonneg hB0 hM0]
  obtain ⟨R, hR⟩ := vd_tail hG hGnn hρ0 (mul_pos (pow_pos hρ0 2) hδ)
  rw [Filter.eventually_comap, Filter.eventually_atTop]
  refine ⟨R, fun b hb' z hz => ?_⟩
  have hzR : R ≤ |z.2| := by linarith
  have hpt : ∀ η ∈ Icc (z.2 - ρ) (z.2 + ρ),
      2 * ρ * ‖tr.v r z‖ ^ 2 - 8 * B * ρ ^ 2 * M ≤ vdG (tr.v r) c η := by
    intro η hη
    have hsl := vd_slice_lb hw hB0 hBw hMw hρ0 z.1 η
    have hper' : Function.Periodic (fun q : ℝ => ‖tr.v r (q, η)‖ ^ 2) c := by
      intro q
      have hpq : tr.v r (q + c, η) = tr.v r (q, η) := hper (q, η)
      simp only [hpq]
    have hwin : ∫ q in (z.1 - ρ)..(z.1 + ρ), ‖tr.v r (q, η)‖ ^ 2 ≤ vdG (tr.v r) c η :=
      vd_window_le_pos hc hρ0 hρc hper' (vd_cont_slice hw η) (fun _ => sq_nonneg _)
    have hd1 : ‖z - (z.1, η)‖ ≤ ρ :=
      vd_norm_le (by dsimp only; rw [sub_self, abs_zero]; exact hρ0.le)
        (by dsimp only; rw [abs_le]; constructor <;> linarith [hη.1, hη.2])
    have hl := vd_lip hw hBw (z.1, η) z
    have hl2 : ‖tr.v r z‖ - ‖tr.v r (z.1, η)‖ ≤ ‖tr.v r z - tr.v r (z.1, η)‖ :=
      norm_sub_norm_le _ _
    have hBρ : B * ‖z - (z.1, η)‖ ≤ B * ρ := mul_le_mul_of_nonneg_left hd1 hB0
    have hx2 : ‖tr.v r z‖ ^ 2 ≤ ‖tr.v r (z.1, η)‖ ^ 2 + 2 * (B * ρ) * M :=
      vd_sq_ub (mul_nonneg hB0 hρ0.le) (norm_nonneg _) (norm_nonneg _) (hMw _) (hMw _)
        (by linarith)
    have h3 := mul_le_mul_of_nonneg_left hx2 (by positivity : (0 : ℝ) ≤ 2 * ρ)
    nlinarith [h3, hsl, hwin]
  have hav : 2 * ρ * (2 * ρ * ‖tr.v r z‖ ^ 2 - 8 * B * ρ ^ 2 * M) ≤
      ∫ η in (z.2 - ρ)..(z.2 + ρ), vdG (tr.v r) c η := by
    have hint := intervalIntegral.integral_mono_on (show z.2 - ρ ≤ z.2 + ρ by linarith)
      intervalIntegrable_const hG.intervalIntegrable hpt
    rw [intervalIntegral.integral_const, smul_eq_mul, show z.2 + ρ - (z.2 - ρ) = 2 * ρ by ring]
      at hint
    exact hint
  have hI : ∫ η in (z.2 - ρ)..(z.2 + ρ), vdG (tr.v r) c η < ρ ^ 2 * δ := hR z.2 hzR
  have h3 : ρ ^ 2 * (16 * B * ρ * M) ≤ ρ ^ 2 * δ := mul_le_mul_of_nonneg_left hρδ (sq_nonneg ρ)
  have h4 : 4 * ρ ^ 2 * ‖tr.v r z‖ ^ 2 < 2 * ρ ^ 2 * δ := by nlinarith [hav, hI, h3]
  have hlt_sq : ‖tr.v r z‖ ^ 2 < ε ^ 2 := by
    by_contra hcon
    push Not at hcon
    have h5 := mul_le_mul_of_nonneg_left hcon (sq_nonneg ρ)
    nlinarith [mul_pos (pow_pos hρ0 2) hδ, h4, h5]
  rw [dist_zero_right]
  nlinarith [norm_nonneg (tr.v r z), hε]

/-- Horizontal mean of `tr.v s · 1` vanishes for all `s ≥ 0` and arbitrary `0 < c`. -/
theorem train_hmean_v1_zero_pos {ν c : ℝ} (hν : 0 < ν) (hc : 0 < c)
    (tr : B0140.TrainSol ν c) (hbuc : IsBUCTrain tr) {s : ℝ} (hs : 0 ≤ s) (η : ℝ) :
    hmean c (fun z => tr.v s z 1) η = 0 := by
  let T : ℝ := s + 1
  have hsT : s ∈ Icc (0 : ℝ) T := ⟨hs, by dsimp [T]; linarith⟩
  have hcl : IsClassicalOn ν c T tr.v tr.p := trainSol_isClassicalOn tr T
  have hv_sm : ContDiff ℝ ∞ (tr.v s) := vd_contDiff_slice hcl hsT
  have hg0 : ContDiff ℝ ∞ (fun z => tr.v s z 0) :=
    (EuclideanSpace.proj (0 : Fin 2) : Vec →L[ℝ] ℝ).contDiff.comp hv_sm
  have hg1 : ContDiff ℝ ∞ (fun z => tr.v s z 1) :=
    (EuclideanSpace.proj (1 : Fin 2) : Vec →L[ℝ] ℝ).contDiff.comp hv_sm
  have hper0 : Cyl.IsPeriodic c (fun z => tr.v s z 0) :=
    fun z => congrArg (fun x : Vec => x 0) (hcl.periodic_v s hsT z)
  have hL0 : ∀ e : ℝ, hmean c (fun z => Cyl.partialEta (fun w => tr.v s w 1) z) e = 0 := by
    intro e
    have hfun : (fun q : ℝ => Cyl.partialEta (fun w => tr.v s w 1) (q, e)) =
        fun q => -Cyl.partialQ (fun w => tr.v s w 0) (q, e) := by
      funext q
      have hsol := hcl.solenoidal s hsT (q, e)
      unfold Cyl.divergence at hsol
      linarith
    unfold hmean
    rw [hfun, integral_neg, mm_integral_partialQ_zero hc hg0 hper0 e, neg_zero, smul_zero]
  have hderiv : ∀ x : ℝ, HasDerivAt (fun e' => hmean c (fun z => tr.v s z 1) e') 0 x := by
    intro x
    have h := pmi_hasDerivAt_hmean_eta (c := c) hg1 x
    rwa [hL0 x] at h
  have hconst : ∀ z : Plane, hmean c (fun w => tr.v s w 1) z.2 =
      hmean c (fun w => tr.v s w 1) 0 :=
    fun z => is_const_of_deriv_eq_zero (fun x => (hderiv x).differentiableAt)
      (fun x => (hderiv x).deriv) z.2 0
  have hdec_v1 : Tendsto (fun z : Plane => tr.v s z 1)
      (comap (fun z : Plane => |z.2|) atTop) (𝓝 0) :=
    ((EuclideanSpace.proj (1 : Fin 2) : Vec →L[ℝ] ℝ).continuous.tendsto 0).comp
      (vel_decay_pos hν hc tr hbuc hs)
  have hzero : hmean c (fun w => tr.v s w 1) 0 = 0 :=
    PressStepFixed.eq_zero_of_const_tendsto_comap hconst (gg_hmean_tendsto hc hdec_v1)
  exact (hconst (0, η)).trans hzero

/-- Decaying-gauge pressure horizontal-mean identity `p̄(η) = -\overline{v₂²}(η)` for `0 < c`. -/
theorem train_hmean_p_eq_pos {ν c : ℝ} (hν : 0 < ν) (hc : 0 < c)
    (tr : B0140.TrainSol ν c) (hbuc : IsBUCTrain tr) {r : ℝ} (hr : 0 < r) (η : ℝ) :
    hmean c (tr.p r) η = -hmean c (fun w => tr.v r w 1 * tr.v r w 1) η := by
  let T : ℝ := r + 1
  have hrIoo : r ∈ Ioo (0 : ℝ) T := ⟨hr, lt_add_one r⟩
  have hrIcc : r ∈ Icc (0 : ℝ) T := Ioo_subset_Icc_self hrIoo
  have hcl : IsClassicalOn ν c T tr.v tr.p := trainSol_isClassicalOn tr T
  have hv_sm : ContDiff ℝ ∞ (tr.v r) := vd_contDiff_slice hcl hrIcc
  have hg0 : ContDiff ℝ ∞ (fun z => tr.v r z 0) :=
    (EuclideanSpace.proj (0 : Fin 2) : Vec →L[ℝ] ℝ).contDiff.comp hv_sm
  have hg1 : ContDiff ℝ ∞ (fun z => tr.v r z 1) :=
    (EuclideanSpace.proj (1 : Fin 2) : Vec →L[ℝ] ℝ).contDiff.comp hv_sm
  have hP : ContDiff ℝ ∞ (tr.p r) := gg_slice_contDiff hrIcc hcl.smooth_p
  have hE : ContDiff ℝ ∞ (fun w : Plane => tr.v r w 0 * tr.v r w 1) := hg0.mul hg1
  have hSq : ContDiff ℝ ∞ (fun w : Plane => tr.v r w 1 * tr.v r w 1) := hg1.mul hg1
  have hper0 : Cyl.IsPeriodic c (fun z => tr.v r z 0) :=
    fun z => congrArg (fun x : Vec => x 0) (hcl.periodic_v r hrIcc z)
  have hper1 : Cyl.IsPeriodic c (fun z => tr.v r z 1) :=
    fun z => congrArg (fun x : Vec => x 1) (hcl.periodic_v r hrIcc z)
  have hperE : Cyl.IsPeriodic c (fun w : Plane => tr.v r w 0 * tr.v r w 1) := fun z => by
    simp only [hcl.periodic_v r hrIcc z]
  have hL0 : ∀ e : ℝ, hmean c (fun z => Cyl.partialEta (fun w => tr.v r w 1) z) e = 0 := by
    intro e
    have hfun : (fun q : ℝ => Cyl.partialEta (fun w => tr.v r w 1) (q, e)) =
        fun q => -Cyl.partialQ (fun w => tr.v r w 0) (q, e) := by
      funext q
      have hsol := hcl.solenoidal r hrIcc (q, e)
      unfold Cyl.divergence at hsol
      linarith
    unfold hmean
    rw [hfun, integral_neg, mm_integral_partialQ_zero hc hg0 hper0 e, neg_zero, smul_zero]
  have hM3 : ∀ e : ℝ,
      hmean c (fun z => Cyl.partialEta (fun w => Cyl.partialEta (fun z => tr.v r z 1) w) z) e =
        0 := by
    intro e
    have h := pmi_hasDerivAt_hmean_eta (c := c) (pmi_partialEta_contDiff hg1) e
    have hev : (fun e' => hmean c (fun w => Cyl.partialEta (fun z => tr.v r z 1) w) e') =ᶠ[𝓝 e]
        fun _ => (0 : ℝ) := Filter.Eventually.of_forall hL0
    exact h.unique ((hasDerivAt_const e (0 : ℝ)).congr_of_eventuallyEq hev)
  have hM2 : ∀ e : ℝ, ∫ q in Ioc (-c / 2) (c / 2), deriv (fun t => tr.v t (q, e) 1) r = 0 := by
    intro e
    obtain ⟨_, hD⟩ := pmi_hasDerivAt_s hcl.smooth_v hrIoo e
    have hev : (fun t => ∫ q in Ioc (-c / 2) (c / 2), tr.v t (q, e) 1) =ᶠ[𝓝 r]
        fun _ => (0 : ℝ) := by
      filter_upwards [Ioo_mem_nhds hrIoo.1 hrIoo.2] with t ht
      exact pmi_integral_of_hmean hc (train_hmean_v1_zero_pos hν hc tr hbuc ht.1.le e)
    exact hD.unique ((hasDerivAt_const r (0 : ℝ)).congr_of_eventuallyEq hev)
  have hmom1 : ∀ z : Plane,
      Cyl.partialEta (tr.p r) z + Cyl.partialEta (fun w => tr.v r w 1 * tr.v r w 1) z =
        -(deriv (fun t => tr.v t z 1) r) - Cyl.partialQ (fun w => tr.v r w 0 * tr.v r w 1) z
          + ν * Train.lapS (fun w => tr.v r w 1) z := by
    intro z
    have hv' : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => tr.v x.1 x.2) (Ioo 0 T ×ˢ univ) :=
      hcl.smooth_v.mono (prod_mono Ioo_subset_Icc_self subset_rfl)
    have hca : ContDiffAt ℝ ∞ (fun x : ℝ × Plane => tr.v x.1 x.2) (r, z) :=
      hv'.contDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨hrIoo, mem_univ z⟩)
    have hdiff : DifferentiableAt ℝ (fun t => tr.v t z) r := by
      have hp : HasDerivAt (fun t : ℝ => (t, z)) (1, (0, 0)) r :=
        (hasDerivAt_id' r).prodMk (hasDerivAt_const r z)
      exact ((hca.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt r hp).differentiableAt
    have hD0 : Differentiable ℝ (fun w => tr.v r w 0) := hg0.differentiable (by simp)
    have hD1 : Differentiable ℝ (fun w => tr.v r w 1) := hg1.differentiable (by simp)
    have hmom := hcl.momentum r hrIoo z
    unfold Train.momentumResidual at hmom
    have h1 := congrArg (fun x : Vec => x 1) hmom
    simp only [Train.advection, Train.vecLaplacian, Train.gradS, PiLp.add_apply, PiLp.sub_apply,
      PiLp.smul_apply, smul_eq_mul, Train.toVec_one, PiLp.zero_apply] at h1
    rw [pmi_deriv_comp1 hdiff] at h1
    have hEm := mm_partialQ_mul hD0 hD1 z
    have hSqm := mm_partialEta_mul hD1 hD1 z
    have hdv : Cyl.partialQ (fun w => tr.v r w 0) z + Cyl.partialEta (fun w => tr.v r w 1) z = 0 :=
      hcl.solenoidal r hrIcc z
    linear_combination h1 + hSqm + hEm + (tr.v r z 1) * hdv
  have hK1 : ∀ e : ℝ,
      hmean c (fun z => Cyl.partialEta (tr.p r) z) e +
        hmean c (fun z => Cyl.partialEta (fun w => tr.v r w 1 * tr.v r w 1) z) e = 0 := by
    intro e
    have hIP : IntegrableOn (fun q => Cyl.partialEta (tr.p r) (q, e)) (Ioc (-c / 2) (c / 2)) :=
      ((pmi_cont_partialEta_slice hP e).integrableOn_Icc).mono_set Ioc_subset_Icc_self
    have hISq : IntegrableOn
        (fun q => Cyl.partialEta (fun w => tr.v r w 1 * tr.v r w 1) (q, e))
        (Ioc (-c / 2) (c / 2)) :=
      ((pmi_cont_partialEta_slice hSq e).integrableOn_Icc).mono_set Ioc_subset_Icc_self
    have iA : IntegrableOn (fun q => deriv (fun t => tr.v t (q, e) 1) r) (Ioc (-c / 2) (c / 2)) :=
      (pmi_hasDerivAt_s hcl.smooth_v hrIoo e).1
    have iE : IntegrableOn (fun q => Cyl.partialQ (fun w => tr.v r w 0 * tr.v r w 1) (q, e))
        (Ioc (-c / 2) (c / 2)) :=
      ((mm_cont_partialQ_slice hE e).integrableOn_Icc).mono_set Ioc_subset_Icc_self
    have hiQ : IntegrableOn (fun q => Cyl.partialQ (Cyl.partialQ (fun z => tr.v r z 1)) (q, e))
        (Ioc (-c / 2) (c / 2)) :=
      ((mm_cont_partialQ_slice (mm_partialQ_contDiff hg1) e).integrableOn_Icc).mono_set
        Ioc_subset_Icc_self
    have hiH : IntegrableOn
        (fun q => Cyl.partialEta (Cyl.partialEta (fun z => tr.v r z 1)) (q, e))
        (Ioc (-c / 2) (c / 2)) :=
      ((pmi_cont_partialEta_slice (pmi_partialEta_contDiff hg1) e).integrableOn_Icc).mono_set
        Ioc_subset_Icc_self
    have iL : IntegrableOn (fun q => Train.lapS (fun w => tr.v r w 1) (q, e))
        (Ioc (-c / 2) (c / 2)) := hiQ.add hiH
    have zL : ∫ q in Ioc (-c / 2) (c / 2), Train.lapS (fun w => tr.v r w 1) (q, e) = 0 := by
      unfold Train.lapS
      rw [integral_add hiQ hiH, mm_integral_partialQ_zero hc (mm_partialQ_contDiff hg1)
        hper1.partialQ e, pmi_integral_of_hmean hc (hM3 e), add_zero]
    have zE : ∫ q in Ioc (-c / 2) (c / 2),
        Cyl.partialQ (fun w => tr.v r w 0 * tr.v r w 1) (q, e) = 0 :=
      mm_integral_partialQ_zero hc hE hperE e
    have hR : ∫ q in Ioc (-c / 2) (c / 2),
        (-(deriv (fun t => tr.v t (q, e) 1) r) -
          Cyl.partialQ (fun w => tr.v r w 0 * tr.v r w 1) (q, e) +
          ν * Train.lapS (fun w => tr.v r w 1) (q, e)) = 0 := by
      have iAn : IntegrableOn (fun q => -(deriv (fun t => tr.v t (q, e) 1) r))
          (Ioc (-c / 2) (c / 2)) := iA.neg
      have iSub : IntegrableOn (fun q => -(deriv (fun t => tr.v t (q, e) 1) r) -
          Cyl.partialQ (fun w => tr.v r w 0 * tr.v r w 1) (q, e))
          (Ioc (-c / 2) (c / 2)) := iAn.sub iE
      rw [integral_add iSub (iL.const_mul ν), integral_sub iAn iE,
        integral_neg, integral_const_mul, hM2 e, zE, zL]
      ring
    have hcongr : ∫ q in Ioc (-c / 2) (c / 2),
        (Cyl.partialEta (tr.p r) (q, e) +
          Cyl.partialEta (fun w => tr.v r w 1 * tr.v r w 1) (q, e)) =
        ∫ q in Ioc (-c / 2) (c / 2),
        (-(deriv (fun t => tr.v t (q, e) 1) r) -
          Cyl.partialQ (fun w => tr.v r w 0 * tr.v r w 1) (q, e) +
          ν * Train.lapS (fun w => tr.v r w 1) (q, e)) :=
      setIntegral_congr_fun measurableSet_Ioc (fun q _ => hmom1 (q, e))
    unfold hmean
    rw [← smul_add, ← integral_add hIP hISq, hcongr, hR, smul_zero]
  have hderiv : ∀ x : ℝ, HasDerivAt
      (fun e' => hmean c (tr.p r) e' + hmean c (fun w => tr.v r w 1 * tr.v r w 1) e') 0 x :=
    fun x => ((pmi_hasDerivAt_hmean_eta (c := c) hP x).add
      (pmi_hasDerivAt_hmean_eta (c := c) hSq x)).congr_deriv (hK1 x)
  have hconst : ∀ z : Plane,
      hmean c (tr.p r) z.2 + hmean c (fun w => tr.v r w 1 * tr.v r w 1) z.2 =
        hmean c (tr.p r) 0 + hmean c (fun w => tr.v r w 1 * tr.v r w 1) 0 :=
    fun z => is_const_of_deriv_eq_zero (fun x => (hderiv x).differentiableAt)
      (fun x => (hderiv x).deriv) z.2 0
  have hv1_dec : Tendsto (fun z : Plane => tr.v r z 1)
      (comap (fun z : Plane => |z.2|) atTop) (𝓝 0) :=
    ((EuclideanSpace.proj (1 : Fin 2) : Vec →L[ℝ] ℝ).continuous.tendsto 0).comp
      (vel_decay_pos hν hc tr hbuc hr.le)
  have hv2_dec : Tendsto (fun z : Plane => tr.v r z 1 * tr.v r z 1)
      (comap (fun z : Plane => |z.2|) atTop) (𝓝 0) := by
    simpa using hv1_dec.mul hv1_dec
  have hsum_dec : Tendsto
      (fun z : Plane => hmean c (tr.p r) z.2 + hmean c (fun w => tr.v r w 1 * tr.v r w 1) z.2)
      (comap (fun z : Plane => |z.2|) atTop) (𝓝 0) := by
    simpa using (gg_hmean_tendsto hc (tr.isTrain.pressure_decay r hr.le)).add
      (gg_hmean_tendsto hc hv2_dec)
  have hzero := PressStepFixed.eq_zero_of_const_tendsto_comap hconst hsum_dec
  exact eq_neg_of_add_eq_zero_left ((hconst (0, η)).trans hzero)

/-- Slice Poisson identity `Δ(tr.p t) = -poissonSource (tr.v t)` for arbitrary `c` and `t > 0`. -/
theorem lapS_p_eq_pos {ν c : ℝ} (tr : B0140.TrainSol ν c) {t : ℝ} (ht : 0 < t) (z : Plane) :
    Train.lapS (tr.p t) z = -poissonSource (tr.v t) z := by
  let T : ℝ := t + 1
  have hT : 0 < T := by dsimp [T]; linarith
  have hs : t ∈ Icc (0 : ℝ) T := ⟨ht.le, by dsimp [T]; linarith⟩
  have hcl : IsClassicalOn ν c T tr.v tr.p := trainSol_isClassicalOn tr T
  have hv : ContDiffOn ℝ ∞ (fun x : B0238.ST => tr.v x.1 x.2) (spS T) := hcl.smooth_v
  have hp : ContDiffOn ℝ ∞ (spP tr.p) (spS T) := hcl.smooth_p
  have hL : spL T tr.v tr.p (t, z) = 0 :=
    spL_eq_zero hT hv hp (fun r hr w => hcl.momentum r hr w)
      (fun r hr w => hcl.solenoidal r (Ioo_subset_Icc_self hr) w) (spS_mem hs z)
  have hG := spD_contDiffOn hT B0238.eQ hp
  have hH := spD_contDiffOn hT B0238.eE hp
  have ha0 := spC_cdo hv 0
  have ha1 := spC_cdo hv 1
  have eP1 : Cyl.partialQ (tr.p t) = fun w => spD T B0238.eQ (spP tr.p) (t, w) :=
    funext fun w => spD_slice_Q hp hs w
  have eP2 : Cyl.partialEta (tr.p t) = fun w => spD T B0238.eE (spP tr.p) (t, w) :=
    funext fun w => spD_slice_E hp hs w
  have hlap : Train.lapS (tr.p t) z =
      spD T B0238.eQ (spD T B0238.eQ (spP tr.p)) (t, z) +
        spD T B0238.eE (spD T B0238.eE (spP tr.p)) (t, z) := by
    rw [Train.lapS, eP1, eP2, spD_slice_Q hG hs z, spD_slice_E hH hs z]
  have hpois : poissonSource (tr.v t) z = spD T B0238.eQ (spC tr.v 0) (t, z) ^ 2 +
      2 * (spD T B0238.eQ (spC tr.v 1) (t, z) * spD T B0238.eE (spC tr.v 0) (t, z)) +
      spD T B0238.eE (spC tr.v 1) (t, z) ^ 2 := by
    unfold poissonSource
    erw [spD_slice_Q ha0 hs z, spD_slice_Q ha1 hs z, spD_slice_E ha0 hs z, spD_slice_E ha1 hs z]
  rw [hlap, hpois]
  simp only [spL] at hL
  linear_combination hL

theorem lapS_derivWord_iteratedDeriv_p_eq_pos {ν c : ℝ} (tr : B0140.TrainSol ν c)
    (ℓ : ℕ) (w : List Bool) {r : ℝ} (hr : 0 < r) (z : Plane) :
    Train.lapS (B0151.derivWord w (fun x => iteratedDeriv ℓ (fun t => tr.p t x) r)) z =
      -B0151.derivWord w (fun x => iteratedDeriv ℓ (fun t => poissonSource (tr.v t) x) r) z := by
  have hsm_p : SmS (fun x : ℝ × Plane => tr.p x.1 x.2) :=
    tr.isTrain.smooth_p.mono (Set.prod_mono Set.Ioi_subset_Ici_self Subset.rfl)
  have hslice_p : ContDiff ℝ ∞ (fun x : Plane => iteratedDeriv ℓ (fun t => tr.p t x) r) :=
    contDiff_slice_iteratedDeriv_of_contDiffOn tr.p hsm_p ℓ hr
  rw [congrFun (JetViscIBP.derivWord_lap w _ hslice_p).symm z]
  have hlap_eq : (fun x : Plane => Train.lapS (fun y => iteratedDeriv ℓ (fun t => tr.p t y) r) x) =
      fun x : Plane => -iteratedDeriv ℓ (fun t => poissonSource (tr.v t) x) r := by
    funext x
    rw [← PressStepFixed.iteratedDeriv_lapS_eq hsm_p ℓ hr x]
    have hev : (fun t => Train.lapS (tr.p t) x) =ᶠ[𝓝 r]
        fun t => -poissonSource (tr.v t) x := by
      filter_upwards [Ioi_mem_nhds hr] with t ht using lapS_p_eq_pos tr ht x
    rw [hev.iteratedDeriv_eq ℓ]
    exact iteratedDeriv_neg ℓ (fun t => poissonSource (tr.v t) x) r
  rw [hlap_eq, PressStepFixed.derivWord_neg]

/-! ## 2. Compact-interval `[A, B] ⊂ (0, ∞)` induction on age order `ℓ` -/

theorem norm_ageJet_hmean_p_le_pos {ν c : ℝ} (hν : 0 < ν) (hc : 0 < c)
    (tr : B0140.TrainSol ν c) (hbuc : IsBUCTrain tr)
    (ℓ k : ℕ) {s M_v : ℝ} (hs : 0 < s) (hMv : 0 ≤ M_v) (z : Plane)
    (hbd : ∀ y : Plane, ∀ r ≤ ℓ, ∀ i ≤ k, ‖ageJet r i tr.v s y‖ ≤ M_v) :
    ‖ageJet ℓ k (fun r w => hmean c (tr.p r) w.2) s z‖ ≤
      (2 : ℝ) ^ (ℓ + k) * M_v * M_v := by
  have hsm_v : Sm (fun x : ℝ × Plane => tr.v x.1 x.2) :=
    tr.isTrain.smooth_v.mono (Set.prod_mono Set.Ioi_subset_Ici_self Subset.rfl)
  have hsm_v1 : SmS (fun x : ℝ × Plane => tr.v x.1 x.2 1) :=
    (EuclideanSpace.proj (1 : Fin 2) : Vec →L[ℝ] ℝ).contDiff.comp_contDiffOn hsm_v
  let Vsq : ℝ → Plane → ℝ := fun r w => tr.v r w 1 * tr.v r w 1
  have hVsq_bd : ∀ y : Plane, ‖ageJet ℓ k Vsq s y‖ ≤ (2 : ℝ) ^ (ℓ + k) * M_v * M_v := by
    intro y
    refine PartI_HF_1.norm_ageJet_mul_le hsm_v1 hsm_v1 ℓ k hs hMv hMv y
      (fun r hr i hi => (PartI_HF_1.norm_ageJet_vec_proj_le hsm_v 1 r i hs y).trans
        (hbd y r hr i hi))
      (fun r hr i hi => (PartI_HF_1.norm_ageJet_vec_proj_le hsm_v 1 r i hs y).trans
        (hbd y r hr i hi))
  have hB_nn : 0 ≤ (2 : ℝ) ^ (ℓ + k) * M_v * M_v := by positivity
  have hmean_Vsq_bd :=
    PressStepFixed.norm_ageJet_hmean_scalar_le (f := Vsq) hc hB_nn (hsm_v1.mul hsm_v1) ℓ k hs
      z (fun q _ => hVsq_bd (q, z.2))
  have hage_eq :
      ageJet ℓ k (fun r w => hmean c (tr.p r) w.2) s z =
        ageJet ℓ k (fun r w => -hmean c (Vsq r) w.2) s z := by
    unfold ageJet
    congr 1
    funext w
    have hev : (fun r => hmean c (tr.p r) w.2) =ᶠ[𝓝 s]
        fun r => -hmean c (Vsq r) w.2 := by
      filter_upwards [Ioi_mem_nhds hs] with r hr using train_hmean_p_eq_pos hν hc tr hbuc hr w.2
    exact hev.iteratedDeriv_eq ℓ
  have hsm_hm_Vsq : SmS (fun x : ℝ × Plane => hmean c (Vsq x.1) x.2.2) :=
    PressStepFixed.smS_hmean_scalar hc (F := Vsq) (hsm_v1.mul hsm_v1)
  rw [hage_eq, PressStepFixed.norm_ageJet_neg_eq (fun r w => hmean c (Vsq r) w.2) hsm_hm_Vsq ℓ k hs z]
  exact hmean_Vsq_bd

theorem abs_integral_grad_word_le_on_Icc {ν c : ℝ} (hν : 0 < ν) (tr : B0140.TrainSol ν c)
    (ℓ : ℕ) (w : List Bool) (d : Fin 2)
    {A B M_v M_adv : ℝ} (hA : 0 < A)
    (hMv : ∀ r ∈ Icc A B, ∀ z : Plane,
      ‖ageJet ℓ w.length tr.v r z‖ ≤ M_v ∧ ‖ageJet ℓ (w.length + 2) tr.v r z‖ ≤ M_v)
    (hMadv : ∀ r ∈ Icc A B, ∀ z : Plane,
      ‖ageJet ℓ w.length (fun t y => Train.advection (tr.v t) y) r z‖ ≤ M_adv)
    {a b : ℝ} (ha : a ∈ Icc A B) (hb : b ∈ Icc A B) (hab : a ≤ b) (z : Plane) :
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
  let V : ℝ → ℝ := fun r => B0151.derivWord w (fun x => iteratedDeriv ℓ (fun s => F₀ s x) r) z
  let Visc : ℝ → ℝ := fun r => B0151.derivWord w (fun x => iteratedDeriv ℓ (fun s => F₁ s x) r) z
  let Adv : ℝ → ℝ := fun r => B0151.derivWord w (fun x => iteratedDeriv ℓ (fun s => F₂ s x) r) z
  let Grad : ℝ → ℝ := fun r => B0151.derivWord w (fun x => iteratedDeriv ℓ (fun s => F₃ s x) r) z
  have ha0 : 0 < a := hA.trans_le ha.1
  have hsub : Icc a b ⊆ Ioi (0 : ℝ) := fun r hr => ha0.trans_le hr.1
  have huIcc : uIcc a b ⊆ Ioi (0 : ℝ) := by
    rw [uIcc_of_le hab]
    exact hsub
  have hcV : ContinuousOn V (Icc a b) :=
    (PressStepFixed.continuousOn_derivWord_iteratedDeriv (F := F₀) hsm_vd ℓ w z).mono hsub
  have hcVisc : ContinuousOn Visc (uIcc a b) :=
    (PressStepFixed.continuousOn_derivWord_iteratedDeriv (F := F₁) hsm₁d ℓ w z).mono huIcc
  have hcAdv : ContinuousOn Adv (uIcc a b) :=
    (PressStepFixed.continuousOn_derivWord_iteratedDeriv (F := F₂) hsm₂d ℓ w z).mono huIcc
  have hcGrad : ContinuousOn Grad (uIcc a b) :=
    (PressStepFixed.continuousOn_derivWord_iteratedDeriv (F := F₃) hsm₃d ℓ w z).mono huIcc
  have hiCA : IntervalIntegrable (fun r => Visc r - Adv r) volume a b :=
    (hcVisc.sub hcAdv).intervalIntegrable
  have hiGrad : IntervalIntegrable Grad volume a b := hcGrad.intervalIntegrable
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hcV
    (fun r hr => PressStepFixed.hasDerivAt_vel_word_eq_rhs tr ℓ w d (ha0.trans hr.1) z)
    (hiCA.sub hiGrad)
  rw [intervalIntegral.integral_sub hiCA hiGrad] at hftc
  have hGrad_eq : ∫ r in a..b, Grad r = (∫ r in a..b, (Visc r - Adv r)) - (V b - V a) := by
    linarith
  have hV_bd : ∀ r ∈ Icc A B, |V r| ≤ M_v := by
    intro r hr
    have hr0 : 0 < r := hA.trans_le hr.1
    exact ((PressStepFixed.abs_derivWord_iteratedDeriv_le (F := F₀) hsm_vd ℓ w hr0 z).trans
      (PartI_HF_1.norm_ageJet_vec_proj_le hsm_v d ℓ w.length hr0 z)).trans (hMv r hr z).1
  have hCA_bd : ∀ r ∈ Icc A B, |Visc r - Adv r| ≤ 2 * ν * M_v + M_adv := by
    intro r hr
    have hr0 : 0 < r := hA.trans_le hr.1
    have h1 : |Visc r| ≤ 2 * ν * M_v := by
      have hw1 := (PressStepFixed.abs_derivWord_iteratedDeriv_le (F := F₁) hsm₁d ℓ w hr0 z).trans
        (PartI_HF_1.norm_ageJet_vec_proj_le hsm₁ d ℓ w.length hr0 z)
      have hw2 := PartI_T25_1.norm_ageJet_smul_vecLaplacian_le hsm_v hν.le ℓ w.length hr0 z
      have hw3 : (2 * ν) * ‖ageJet ℓ (w.length + 2) tr.v r z‖ ≤ 2 * ν * M_v :=
        mul_le_mul_of_nonneg_left (hMv r hr z).2 (by positivity)
      exact (hw1.trans hw2).trans hw3
    have h2 : |Adv r| ≤ M_adv :=
      ((PressStepFixed.abs_derivWord_iteratedDeriv_le (F := F₂) hsm₂d ℓ w hr0 z).trans
        (PartI_HF_1.norm_ageJet_vec_proj_le hsm₂ d ℓ w.length hr0 z)).trans (hMadv r hr z)
    calc |Visc r - Adv r| ≤ |Visc r| + |Adv r| := abs_sub _ _
      _ ≤ 2 * ν * M_v + M_adv := add_le_add h1 h2
  have hint_CA : |∫ r in a..b, (Visc r - Adv r)| ≤ (2 * ν * M_v + M_adv) * |b - a| := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (f := fun r => Visc r - Adv r) (a := a) (b := b) (C := 2 * ν * M_v + M_adv)
      (fun r hr => by
        rw [Set.uIoc_of_le hab] at hr
        rw [Real.norm_eq_abs]
        exact hCA_bd r ⟨ha.1.trans hr.1.le, hr.2.trans hb.2⟩)
    simpa [Real.norm_eq_abs] using h
  have hVa : |V a| ≤ M_v := hV_bd a ha
  have hVb : |V b| ≤ M_v := hV_bd b hb
  change |∫ r in a..b, Grad r| ≤ 2 * M_v + (2 * ν * M_v + M_adv) * |b - a|
  rw [hGrad_eq]
  have htri1 := abs_sub (∫ r in a..b, (Visc r - Adv r)) (V b - V a)
  have htri2 := abs_sub (V b) (V a)
  linarith

/-- Uniform rectangle bound across `m ≤ L` and `i ≤ K` on `Icc A B`. -/
theorem rect_ageJet_bd_on_Icc {ν c A B : ℝ} {tr : B0140.TrainSol ν c} (K L : ℕ)
    (hIH : ∀ m ≤ L, ∀ j : ℕ, ∃ M : ℝ, 0 ≤ M ∧
      ∀ r ∈ Icc A B, ∀ z : Plane, ‖ageJet m j tr.v r z‖ ≤ M) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ r ∈ Icc A B, ∀ z : Plane, ∀ m ≤ L, ∀ i ≤ K, ‖ageJet m i tr.v r z‖ ≤ M := by
  choose Mf hMf using fun (m : ℕ) (hm : m ≤ L) (i : ℕ) => hIH m hm i
  let Mtot : ℝ := ∑ m ∈ Finset.range (L + 1),
    if hm : m ≤ L then ∑ i ∈ Finset.range (K + 1), Mf m hm i else 0
  have hMtot_nn : 0 ≤ Mtot := by
    refine Finset.sum_nonneg fun m _ => ?_
    split_ifs with hm
    · exact Finset.sum_nonneg fun i _ => (hMf m hm i).1
    · exact le_rfl
  refine ⟨Mtot, hMtot_nn, fun r hr z m hm i hi => ?_⟩
  have h1 : ‖ageJet m i tr.v r z‖ ≤ Mf m hm i := (hMf m hm i).2 r hr z
  have h2 : Mf m hm i ≤ ∑ j ∈ Finset.range (K + 1), Mf m hm j :=
    Finset.single_le_sum (fun j _ => (hMf m hm j).1) (Finset.mem_range.2 (by omega))
  have h3 : (if hm' : m ≤ L then ∑ j ∈ Finset.range (K + 1), Mf m hm' j else 0) ≤ Mtot :=
    Finset.single_le_sum
      (f := fun m' => if hm' : m' ≤ L then ∑ j ∈ Finset.range (K + 1), Mf m' hm' j else 0)
      (s := Finset.range (L + 1))
      (fun m' _ => by
        split_ifs with hm'
        · exact Finset.sum_nonneg fun j _ => (hMf m' hm' j).1
        · exact le_rfl)
      (Finset.mem_range.2 (by omega))
  simp only [hm, ↓reduceDIte] at h3
  exact (h1.trans h2).trans h3

/-- Advection age-jet bound on `Icc A B`. -/
theorem advection_ageJet_bd_on_Icc {ν c A B : ℝ} (hA : 0 < A) {tr : B0140.TrainSol ν c}
    (ℓ j : ℕ)
    (hIH : ∀ m ≤ ℓ, ∀ i : ℕ, ∃ M : ℝ, 0 ≤ M ∧
      ∀ r ∈ Icc A B, ∀ z : Plane, ‖ageJet m i tr.v r z‖ ≤ M) :
    ∃ M_adv : ℝ, 0 ≤ M_adv ∧
      ∀ r ∈ Icc A B, ∀ z : Plane,
        ‖ageJet ℓ j (fun t w => Train.advection (tr.v t) w) r z‖ ≤ M_adv := by
  obtain ⟨M, hM, hbd⟩ := rect_ageJet_bd_on_Icc (j + 1) ℓ hIH
  refine ⟨4 * (2 : ℝ) ^ (ℓ + j) * M * M, by positivity, fun s hs z => ?_⟩
  have hs0 : 0 < s := hA.trans_le hs.1
  have hsm_v : Sm (fun x : ℝ × Plane => tr.v x.1 x.2) :=
    tr.isTrain.smooth_v.mono (Set.prod_mono Set.Ioi_subset_Ici_self Subset.rfl)
  have hsm_adv : Sm (fun x : ℝ × Plane => Train.advection (tr.v x.1) x.2) :=
    PartI_T25_1.sm_advection hsm_v
  have hsm_vk : ∀ k : Fin 2, SmS (fun x : ℝ × Plane => tr.v x.1 x.2 k) := fun k =>
    (EuclideanSpace.proj k : Vec →L[ℝ] ℝ).contDiff.comp_contDiffOn hsm_v
  have hcomp_bd : ∀ k : Fin 2,
      ‖ageJet ℓ j (fun r w => Train.advection (tr.v r) w k) s z‖ ≤
        2 * (2 : ℝ) ^ (ℓ + j) * M * M := by
    intro k
    let P₀ : ℝ → Plane → ℝ := fun r w => tr.v r w 0 * Cyl.partialQ (fun x => tr.v r x k) w
    let P₁ : ℝ → Plane → ℝ := fun r w => tr.v r w 1 * Cyl.partialEta (fun x => tr.v r x k) w
    have hsm_Q : SmS (fun x : ℝ × Plane => Cyl.partialQ (fun y => tr.v x.1 y k) x.2) :=
      PartI_HF_1.smS_partialQ (F := fun r y => tr.v r y k) (hsm_vk k)
    have hsm_E : SmS (fun x : ℝ × Plane => Cyl.partialEta (fun y => tr.v x.1 y k) x.2) :=
      PartI_HF_1.smS_partialEta (F := fun r y => tr.v r y k) (hsm_vk k)
    have heq : (fun r w => Train.advection (tr.v r) w k) = fun r w => P₀ r w + P₁ r w :=
      funext fun r => funext fun w => PartI_HF_1.advection_apply (tr.v r) w k
    rw [heq, PartI_HF_1.ageJet_add P₀ P₁ ((hsm_vk 0).mul hsm_Q) ((hsm_vk 1).mul hsm_E) hs0 ℓ j z]
    have hP₀_bd : ‖ageJet ℓ j P₀ s z‖ ≤ (2 : ℝ) ^ (ℓ + j) * M * M :=
      PartI_HF_1.norm_ageJet_mul_le (hsm_vk 0) hsm_Q ℓ j hs0 hM hM z
        (fun r hr i hi => (PartI_HF_1.norm_ageJet_vec_proj_le hsm_v 0 r i hs0 z).trans
          (hbd s hs z r hr i (by omega)))
        (fun r hr i hi => (PartI_HF_1.norm_ageJet_partialQ_le (F := fun r x => tr.v r x k)
            (hsm_vk k) r i hs0 z).trans
          ((PartI_HF_1.norm_ageJet_vec_proj_le hsm_v k r (i + 1) hs0 z).trans
            (hbd s hs z r hr (i + 1) (by omega))))
    have hP₁_bd : ‖ageJet ℓ j P₁ s z‖ ≤ (2 : ℝ) ^ (ℓ + j) * M * M :=
      PartI_HF_1.norm_ageJet_mul_le (hsm_vk 1) hsm_E ℓ j hs0 hM hM z
        (fun r hr i hi => (PartI_HF_1.norm_ageJet_vec_proj_le hsm_v 1 r i hs0 z).trans
          (hbd s hs z r hr i (by omega)))
        (fun r hr i hi => (PartI_HF_1.norm_ageJet_partialEta_le (F := fun r x => tr.v r x k)
            (hsm_vk k) r i hs0 z).trans
          ((PartI_HF_1.norm_ageJet_vec_proj_le hsm_v k r (i + 1) hs0 z).trans
            (hbd s hs z r hr (i + 1) (by omega))))
    have htri := norm_add_le (ageJet ℓ j P₀ s z) (ageJet ℓ j P₁ s z)
    linarith
  have hvec := PartI_HF_1.norm_ageJet_vec_le (V := fun r w => Train.advection (tr.v r) w)
    hsm_adv ℓ j hs0 z
  linarith [hcomp_bd 0, hcomp_bd 1]

/-- Pressure-gradient age-jet bound on `Icc A B` (`0 < A < B`) for arbitrary `0 < c`, `0 < ν`. -/
theorem press_ageJet_bd_on_Icc {ν c A B : ℝ} (hν : 0 < ν) (hc : 0 < c) (hA : 0 < A) (hAB : A < B)
    (tr : B0140.TrainSol ν c) (hbuc : IsBUCTrain tr) (ℓ j : ℕ)
    (hIH : ∀ m ≤ ℓ, ∀ i : ℕ, ∃ M : ℝ, 0 ≤ M ∧
      ∀ r ∈ Icc A B, ∀ z : Plane, ‖ageJet m i tr.v r z‖ ≤ M) :
    ∃ M_press : ℝ, 0 ≤ M_press ∧
      ∀ r ∈ Icc A B, ∀ z : Plane,
        ‖ageJet ℓ j (fun t w => Train.gradS (tr.p t) w) r z‖ ≤ M_press := by
  have hw_bd : ∀ w : List Bool, ∃ M_w : ℝ, 0 ≤ M_w ∧
      ∀ r ∈ Icc A B, ∀ z : Plane,
        |B0151.derivWord w (fun x => iteratedDeriv ℓ (fun t => tr.p t x) r) z| ≤ M_w := by
    intro w
    obtain ⟨M_v, hMv_nn, hMv_bd⟩ := rect_ageJet_bd_on_Icc (w.length + 2) ℓ hIH
    obtain ⟨M_adv, hMadv_nn, hMadv_bd⟩ := advection_ageJet_bd_on_Icc hA ℓ w.length hIH
    let K_w : ℝ := 4 * (2 : ℝ) ^ (ℓ + w.length) * M_v * M_v
    let M_mean : ℝ := (2 : ℝ) ^ (ℓ + w.length) * M_v * M_v
    obtain ⟨M1, hM1⟩ := PressStepFixed.pbOscLinear_proof c K_w hc
    let M1' : ℝ := max M1 0
    refine ⟨M1' + M_mean, by positivity, fun s hs z => ?_⟩
    have hs0 : 0 < s := hA.trans_le hs.1
    let Q_w : ℝ → Plane → ℝ := fun r y =>
      B0151.derivWord w (fun x => iteratedDeriv ℓ (fun t => tr.p t x) r) y
    have hsm_p : SmS (fun p : ℝ × Plane => tr.p p.1 p.2) :=
      tr.isTrain.smooth_p.mono (Set.prod_mono Set.Ioi_subset_Ici_self Subset.rfl)
    have hsm_v : Sm (fun p : ℝ × Plane => tr.v p.1 p.2) :=
      tr.isTrain.smooth_v.mono (Set.prod_mono Set.Ioi_subset_Ici_self Subset.rfl)
    have hsm_Qw : SmS (fun p : ℝ × Plane => Q_w p.1 p.2) :=
      PressStepFixed.smS_derivWord_iteratedDeriv (F := tr.p) hsm_p ℓ w
    have hmean_bd : |hmean c (Q_w s) z.2| ≤ M_mean := by
      have hslice_p : ContDiff ℝ ∞ (fun x : Plane => iteratedDeriv ℓ (fun t => tr.p t x) s) :=
        contDiff_slice_iteratedDeriv_of_contDiffOn tr.p hsm_p ℓ hs0
      have hper_p : Cyl.IsPeriodic c (fun x => iteratedDeriv ℓ (fun t => tr.p t x) s) :=
        PressStepFixed.periodic_slice_iteratedDeriv_p tr ℓ hs0
      have hhm_eq : hmean c (Q_w s) z.2 =
          B0151.derivWord w (fun x : Plane => iteratedDeriv ℓ (fun t => hmean c (tr.p t) x.2) s)
            z := by
        rw [PressStepFixed.hmean_derivWord_eq hc hslice_p hper_p w z]
        congr 1
        funext x
        exact (PressStepFixed.iteratedDeriv_hmean_scalar_eq (f := tr.p) hc hsm_p ℓ hs0 x.2).symm
      rw [hhm_eq]
      exact (PressStepFixed.abs_derivWord_iteratedDeriv_le
          (F := fun t x => hmean c (tr.p t) x.2)
          (PressStepFixed.smS_hmean_scalar hc (F := tr.p) hsm_p) ℓ w hs0 z).trans
        (norm_ageJet_hmean_p_le_pos hν hc tr hbuc ℓ w.length hs0 hMv_nn z
          (fun y m hm i hi => hMv_bd s hs y m hm i (by omega)))
    have hosc_bd : |Q_w s z - hmean c (Q_w s) z.2| ≤ M1' := by
      let T : ℝ := B - A
      have hT : 0 < T := sub_pos.2 hAB
      let q_AB : ℝ → Plane → ℝ := fun τ y => Q_w (A + τ) y
      have hshift_map : ContDiffOn ℝ ∞ (fun p : ℝ × Plane => (A + p.1, p.2)) (Icc 0 T ×ˢ univ) :=
        ((contDiff_const.add contDiff_fst).prodMk contDiff_snd).contDiffOn
      have hsm_q : ContDiffOn ℝ ∞ (fun p : ℝ × Plane => q_AB p.1 p.2) (Icc 0 T ×ˢ univ) :=
        hsm_Qw.comp hshift_map (fun p hp => ⟨add_pos_of_pos_of_nonneg hA hp.1.1, trivial⟩)
      have hper_q : ∀ τ ∈ Icc (0 : ℝ) T, Cyl.IsPeriodic c (q_AB τ) := fun τ hτ =>
        PressStepFixed.periodic_derivWord_cyl
          (PressStepFixed.periodic_slice_iteratedDeriv_p tr ℓ (add_pos_of_pos_of_nonneg hA hτ.1)) w
      have hlap_q : ∀ τ ∈ Icc (0 : ℝ) T, ∀ y : Plane, |Train.lapS (q_AB τ) y| ≤ K_w := by
        intro τ hτ y
        have hr0 : 0 < A + τ := add_pos_of_pos_of_nonneg hA hτ.1
        have hrAB : A + τ ∈ Icc A B := ⟨by linarith [hτ.1], by dsimp [T] at hτ; linarith [hτ.2]⟩
        dsimp [q_AB, Q_w]
        rw [lapS_derivWord_iteratedDeriv_p_eq_pos tr ℓ w hr0 y, abs_neg]
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
        exact (PressStepFixed.abs_derivWord_iteratedDeriv_le
            (F := fun t x => poissonSource (tr.v t) x) hsm_ps ℓ w hr0 y).trans
          (PressStepFixed.norm_ageJet_poissonSource_le hsm_v ℓ w.length hr0 hMv_nn y
            (fun m hm i hi => hMv_bd (A + τ) hrAB y m hm i (by omega)))
      let L_AB : ℝ := 2 * M_v + (2 * ν * M_v + M_adv) * T
      have hgrad_q : ∀ a ∈ Icc (0 : ℝ) T, ∀ b ∈ Icc (0 : ℝ) T, a ≤ b → ∀ y : Plane,
          |∫ τ in a..b, Cyl.partialQ (q_AB τ) y| ≤ L_AB ∧
            |∫ τ in a..b, Cyl.partialEta (q_AB τ) y| ≤ L_AB := by
        intro a ha b hb hab y
        have haAB : A + a ∈ Icc A B := ⟨by linarith [ha.1], by dsimp [T] at ha; linarith [ha.2]⟩
        have hbAB : A + b ∈ Icc A B := ⟨by linarith [hb.1], by dsimp [T] at hb; linarith [hb.2]⟩
        have hab' : A + a ≤ A + b := by linarith
        have hba_le : |(A + b) - (A + a)| ≤ T := by
          rw [show (A + b) - (A + a) = b - a by ring, abs_of_nonneg (sub_nonneg.2 hab)]
          linarith [ha.1, hb.2]
        have hMv_pair : ∀ r ∈ Icc A B, ∀ x : Plane,
            ‖ageJet ℓ w.length tr.v r x‖ ≤ M_v ∧ ‖ageJet ℓ (w.length + 2) tr.v r x‖ ≤ M_v :=
          fun r hr x => ⟨hMv_bd r hr x ℓ le_rfl w.length (by omega),
            hMv_bd r hr x ℓ le_rfl (w.length + 2) le_rfl⟩
        have hC_le : 2 * M_v + (2 * ν * M_v + M_adv) * |(A + b) - (A + a)| ≤ L_AB := by
          dsimp [L_AB]
          have hcoeff : 0 ≤ 2 * ν * M_v + M_adv := by positivity
          linarith [mul_le_mul_of_nonneg_left hba_le hcoeff]
        have hshift_Q : (∫ τ in a..b, Cyl.partialQ (q_AB τ) y) =
            ∫ r in (A + a)..(A + b),
              B0151.derivWord w (fun x => iteratedDeriv ℓ (fun t => Train.gradS (tr.p t) x 0) r)
                y := by
          rw [show (fun τ => Cyl.partialQ (q_AB τ) y) = fun τ => Cyl.partialQ (Q_w (A + τ)) y
            from rfl, intervalIntegral.integral_comp_add_left (fun r => Cyl.partialQ (Q_w r) y) A]
          refine intervalIntegral.integral_congr (fun r hr => ?_)
          rw [uIcc_of_le hab'] at hr
          exact (PressStepFixed.gradS_word_eq_partial_Q_w tr ℓ w
            ((hA.trans_le haAB.1).trans_le hr.1) y).1.symm
        have hshift_E : (∫ τ in a..b, Cyl.partialEta (q_AB τ) y) =
            ∫ r in (A + a)..(A + b),
              B0151.derivWord w (fun x => iteratedDeriv ℓ (fun t => Train.gradS (tr.p t) x 1) r)
                y := by
          rw [show (fun τ => Cyl.partialEta (q_AB τ) y) = fun τ => Cyl.partialEta (Q_w (A + τ)) y
            from rfl, intervalIntegral.integral_comp_add_left (fun r => Cyl.partialEta (Q_w r) y) A]
          refine intervalIntegral.integral_congr (fun r hr => ?_)
          rw [uIcc_of_le hab'] at hr
          exact (PressStepFixed.gradS_word_eq_partial_Q_w tr ℓ w
            ((hA.trans_le haAB.1).trans_le hr.1) y).2.symm
        rw [hshift_Q, hshift_E]
        exact ⟨(abs_integral_grad_word_le_on_Icc hν tr ℓ w 0 hA hMv_pair hMadv_bd
            haAB hbAB hab' y).trans hC_le,
          (abs_integral_grad_word_le_on_Icc hν tr ℓ w 1 hA hMv_pair hMadv_bd
            haAB hbAB hab' y).trans hC_le⟩
      have hs_mem : s - A ∈ Icc (0 : ℝ) T :=
        ⟨sub_nonneg.2 hs.1, by dsimp [T]; linarith [hs.2]⟩
      have hosc := PressStepFixed.osc_bound_of_time_grad hc hT hM1 q_AB hsm_q hper_q hlap_q
        hgrad_q hs_mem z
      have hq_eq : q_AB (s - A) = Q_w s := by
        funext y
        dsimp [q_AB]
        rw [add_sub_cancel]
      rw [hq_eq] at hosc
      exact hosc.trans (le_max_left _ _)
    calc |Q_w s z| = |(Q_w s z - hmean c (Q_w s) z.2) + hmean c (Q_w s) z.2| := by
          rw [sub_add_cancel]
      _ ≤ |Q_w s z - hmean c (Q_w s) z.2| + |hmean c (Q_w s) z.2| := abs_add_le _ _
      _ ≤ M1' + M_mean := add_le_add hosc_bd hmean_bd
  choose M_w hM_w using hw_bd
  let S : ℝ := ∑ w ∈ wordsOfLength (j + 1), M_w w
  have hS_nn : 0 ≤ S := Finset.sum_nonneg fun w _ => (hM_w w).1
  refine ⟨2 * S, by positivity, fun s hs z => ?_⟩
  have hs0 : 0 < s := hA.trans_le hs.1
  have hsm_p : SmS (fun p : ℝ × Plane => tr.p p.1 p.2) :=
    tr.isTrain.smooth_p.mono (Set.prod_mono Set.Ioi_subset_Ici_self Subset.rfl)
  have hslice_p : ContDiff ℝ ∞ (fun x : Plane => iteratedDeriv ℓ (fun t => tr.p t x) s) :=
    contDiff_slice_iteratedDeriv_of_contDiffOn tr.p hsm_p ℓ hs0
  have hp_jet_le : ‖ageJet ℓ (j + 1) tr.p s z‖ ≤ S :=
    (cjw_norm_le_sum (fun x => iteratedDeriv ℓ (fun t => tr.p t x) s) hslice_p (j + 1) z).trans
      (Finset.sum_le_sum fun w _ => (hM_w w).2 s hs z)
  linarith [norm_ageJet_gradS_tr_p_le tr ℓ j hs0 z]

/-- All-order velocity age-jet bounds on any compact subinterval `[A, B] ⊂ (0, ∞)` (`0 < A < B`)
for arbitrary `0 < c` and `0 < ν`. -/
theorem vel_ageJet_bdd_on_Icc {ν c A B : ℝ} (hν : 0 < ν) (hc : 0 < c) (hA : 0 < A) (hAB : A < B)
    (tr : B0140.TrainSol ν c) (hbuc : IsBUCTrain tr) :
    ∀ ℓ j : ℕ, ∃ M : ℝ, 0 ≤ M ∧
      ∀ r ∈ Icc A B, ∀ z : Plane, ‖ageJet ℓ j tr.v r z‖ ≤ M := by
  intro ℓ
  induction ℓ using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero =>
      intro j
      have hB0 : 0 ≤ B := (hA.trans hAB).le
      obtain ⟨M₀, hM₀⟩ := hbuc B hB0 j
      refine ⟨max M₀ 0, le_max_right _ _, fun r hr z => ?_⟩
      have hr0 : r ∈ Icc (0 : ℝ) B := ⟨hA.le.trans hr.1, hr.2⟩
      exact (hM₀ r hr0 z).trans (le_max_left _ _)
    | succ m =>
      intro j
      have hIH : ∀ r ≤ m, ∀ i : ℕ, ∃ M : ℝ, 0 ≤ M ∧
          ∀ t ∈ Icc A B, ∀ z : Plane, ‖ageJet r i tr.v t z‖ ≤ M :=
        fun r hr => ih r (Nat.lt_succ_of_le hr)
      obtain ⟨M_visc, hMv_nn, hVisc⟩ := hIH m le_rfl (j + 2)
      obtain ⟨M_adv, hMa_nn, hAdv⟩ := advection_ageJet_bd_on_Icc hA m j hIH
      obtain ⟨M_press, hMp_nn, hPress⟩ := press_ageJet_bd_on_Icc hν hc hA hAB tr hbuc m j hIH
      refine ⟨(2 * ν) * M_visc + M_adv + M_press, by positivity, fun s hs z => ?_⟩
      have hs0 : 0 < s := hA.trans_le hs.1
      have h1 := norm_ageJet_succ_vel_le tr hν.le m j hs0 z
      have h2 : (2 * ν) * ‖ageJet m (j + 2) tr.v s z‖ ≤ (2 * ν) * M_visc :=
        mul_le_mul_of_nonneg_left (hVisc s hs z) (by positivity)
      linarith [hAdv s hs z, hPress s hs z]

/-! ## 3. Shifted train time-derivative slices `dtIterV` on `(0, 2)` -/

/-- `m`-th time derivative slice of a drift `V : ℝ → Plane → RMerid`. -/
def dtIterV (m : ℕ) (V : ℝ → B0579.Plane → F8Ex.RMerid) : ℝ → B0579.Plane → F8Ex.RMerid :=
  fun s y => iteratedDeriv m (fun r => V r y) s

theorem iteratedDeriv_comp_add_const_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) (σ : ℝ) :
    ∀ (m : ℕ) (s : ℝ), iteratedDeriv m (fun r => f (σ + r)) s = iteratedDeriv m f (σ + s)
  | 0, _ => rfl
  | m + 1, s => by
      rw [iteratedDeriv_succ, iteratedDeriv_succ]
      have hfun : iteratedDeriv m (fun t => f (σ + t)) =
          fun r => iteratedDeriv m f (σ + r) :=
        funext (iteratedDeriv_comp_add_const_eq f σ m)
      rw [hfun]
      exact deriv_comp_const_add (iteratedDeriv m f) σ s

theorem dtIterV_shiftedDriftTrain_eq {ν c : ℝ} (tr : B0140.TrainSol ν c) (σ : ℝ)
    (m : ℕ) (s : ℝ) (y : B0579.Plane) :
    dtIterV m (F8Ex.shiftedDriftTrain tr σ) s y =
      iteratedDeriv m (fun r => tr.v r y) (σ + s) :=
  iteratedDeriv_comp_add_const_eq (fun r => tr.v r y) σ m s

theorem dtIterV_shiftedDriftTrain_smoothOn {ν c : ℝ} (tr : B0140.TrainSol ν c)
    {σ : ℝ} (hσ : 0 ≤ σ) (m : ℕ) :
    ContDiffOn ℝ ∞ (fun x : Coord => dtIterV m (F8Ex.shiftedDriftTrain tr σ) x.1 x.2)
      (Ioo (0 : ℝ) 2 ×ˢ univ) := by
  have hsm_v : Sm (fun p : ℝ × Plane => tr.v p.1 p.2) :=
    tr.isTrain.smooth_v.mono (Set.prod_mono Set.Ioi_subset_Ici_self Subset.rfl)
  have hDtU : Sm (PartI_T25_1.DtU m (fun p : ℝ × Plane => tr.v p.1 p.2)) :=
    PartI_T25_1.sm_DtU hsm_v m
  let sh : Coord → ℝ × Plane := fun x => (σ + x.1, x.2)
  have hsh : ContDiff ℝ ∞ sh := (contDiff_const.add contDiff_fst).prodMk contDiff_snd
  have hcomp : ContDiffOn ℝ ∞
      (fun x : Coord => PartI_T25_1.DtU m (fun p : ℝ × Plane => tr.v p.1 p.2) (sh x))
      (Ioo (0 : ℝ) 2 ×ˢ univ) :=
    hDtU.comp hsh.contDiffOn (fun x hx => ⟨add_pos_of_nonneg_of_pos hσ hx.1.1, trivial⟩)
  refine hcomp.congr fun x hx => ?_
  rw [dtIterV_shiftedDriftTrain_eq]
  exact PartI_T25_1.iteratedDeriv_slice_eq_DtU hsm_v m
    (add_pos_of_nonneg_of_pos hσ hx.1.1) x.2

theorem dtIterV_shiftedDriftTrain_slice_smooth {ν c : ℝ} (tr : B0140.TrainSol ν c)
    {σ : ℝ} (hσ : 0 ≤ σ) (m : ℕ) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 2) :
    ContDiff ℝ ∞ (dtIterV m (F8Ex.shiftedDriftTrain tr σ) s) := by
  have h := (dtIterV_shiftedDriftTrain_smoothOn tr hσ m).comp
    (contDiff_const.prodMk contDiff_id).contDiffOn
    (s := univ) (fun y _ => ⟨hs, mem_univ y⟩)
  exact contDiffOn_univ.1 h

theorem dtIterV_shiftedDriftTrain_periodic {ν c : ℝ} (tr : B0140.TrainSol ν c)
    {σ : ℝ} (hσ : 0 ≤ σ) :
    ∀ (m : ℕ) {s : ℝ}, s ∈ Ioo (0 : ℝ) 2 →
      Cyl.IsPeriodic c (dtIterV m (F8Ex.shiftedDriftTrain tr σ) s) := by
  have hper_tr : ∀ (m : ℕ) {r : ℝ}, 0 < r →
      Cyl.IsPeriodic c (fun y => iteratedDeriv m (fun t => tr.v t y) r) := by
    intro m
    induction m with
    | zero =>
      intro r hr y
      exact tr.isTrain.periodic_v r hr.le y
    | succ m ih =>
      intro r hr y
      change iteratedDeriv (m + 1) (fun t => tr.v t (y.1 + c, y.2)) r =
        iteratedDeriv (m + 1) (fun t => tr.v t y) r
      rw [iteratedDeriv_succ, iteratedDeriv_succ]
      have hev : (fun t => iteratedDeriv m (fun u => tr.v u (y.1 + c, y.2)) t) =ᶠ[𝓝 r]
          fun t => iteratedDeriv m (fun u => tr.v u y) t := by
        filter_upwards [Ioi_mem_nhds hr] with t ht using ih ht y
      exact hev.deriv_eq
  intro m s hs y
  rw [dtIterV_shiftedDriftTrain_eq, dtIterV_shiftedDriftTrain_eq]
  exact hper_tr m (add_pos_of_nonneg_of_pos hσ hs.1) y

/-- Norm bound `‖slicePdIterR α f y‖ ≤ ‖iteratedFDeriv ℝ n f y‖` for any `C^∞` vector field `f`. -/
theorem norm_slicePdIterR_le_iteratedFDeriv :
    ∀ {n : ℕ} (α : Fin n → Fin 2) {f : B0579.Plane → F8Ex.RMerid},
      ContDiff ℝ ∞ f → ∀ y : B0579.Plane,
        ‖F8Ex.slicePdIterR α f y‖ ≤ ‖iteratedFDeriv ℝ n f y‖
  | 0, _, f, _, y => by
      simp [F8Ex.slicePdIterR]
  | n + 1, α, f, hf, y => by
      have hdir_norm : ∀ i : Fin 2, ‖B0579.dir i‖ ≤ 1 := by
        intro i
        fin_cases i <;> simp [B0579.dir, Prod.norm_def]
      have hiterD : ∀ {m : ℕ} (β : Fin m → Fin 2),
          F8Ex.slicePdIterR β f = Sob.iterD (List.ofFn fun i => B0579.dir (β i)) f := by
        intro m β
        induction m with
        | zero =>
            simp [F8Ex.slicePdIterR, Sob.iterD]
        | succ m ihm =>
            funext z
            simp only [F8Ex.slicePdIterR, F8Ex.slicePdR, List.ofFn_succ, Sob.iterD_cons]
            rw [ihm (Fin.tail β)]
            rfl
      rw [hiterD α]
      let vs : List Plane := List.ofFn fun i : Fin (n + 1) => B0579.dir (α i)
      have hlen : vs.length = n + 1 := List.length_ofFn
      have heq := congrFun (csr_iterD_eq (n + 1) f (hf.of_le (by simp)) vs
        (by omega)) y
      rw [heq, ← hlen]
      have hle := ContinuousMultilinearMap.le_opNorm
        (iteratedFDeriv ℝ vs.length f y) (csrDirs vs)
      have hprod : ∏ i : Fin vs.length, ‖csrDirs vs i‖ ≤ 1 := by
        refine (Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun i _ => ?_)).trans
          Finset.prod_const_one.le
        have hmem : csrDirs vs i ∈ vs := List.get_mem vs i
        rw [List.mem_ofFn] at hmem
        obtain ⟨k, hk⟩ := hmem
        rw [← hk]
        exact hdir_norm (α k)
      calc ‖iteratedFDeriv ℝ vs.length f y (csrDirs vs)‖
          ≤ ‖iteratedFDeriv ℝ vs.length f y‖ * ∏ i : Fin vs.length, ‖csrDirs vs i‖ := hle
        _ ≤ ‖iteratedFDeriv ℝ vs.length f y‖ * 1 :=
            mul_le_mul_of_nonneg_left hprod (norm_nonneg _)
        _ = ‖iteratedFDeriv ℝ vs.length f y‖ := mul_one _

/-- **Main export of `TrainJets.lean`**: for arbitrary `0 < c`, `0 < ν`, `0 ≤ σ`, any BUC train
`tr : B0140.TrainSol ν c`, any compact subinterval `[T₁, T₂] ⊂ (0, 2)` (`0 < T₁`, `T₁ < T₂`),
any time-derivative order `m : ℕ`, and any spatial multi-index `α : Fin n → Fin 2`,
`slicePdIterR α (dtIterV m (shiftedDriftTrain tr σ) s)` is uniformly bounded on `[T₁, T₂] × ℝ²`. -/
theorem dtIterV_shiftedDriftTrain_bdd_on_Icc {ν c : ℝ} (hc : 0 < c) (hν : 0 < ν)
    (tr : B0140.TrainSol ν c) (hbuc : IsBUCTrain tr) {σ : ℝ} (hσ : 0 ≤ σ)
    {T₁ T₂ : ℝ} (hT₁ : 0 < T₁) (hT₁₂ : T₁ < T₂) (hT₂ : T₂ < 2)
    (m : ℕ) {n : ℕ} (α : Fin n → Fin 2) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ s ∈ Icc T₁ T₂, ∀ y : B0579.Plane,
        ‖F8Ex.slicePdIterR α (dtIterV m (F8Ex.shiftedDriftTrain tr σ) s) y‖ ≤ M := by
  let A : ℝ := σ + T₁
  let B : ℝ := σ + T₂
  have hA : 0 < A := add_pos_of_nonneg_of_pos hσ hT₁
  have hAB : A < B := by dsimp [A, B]; linarith
  obtain ⟨M, hM_nn, hM⟩ := vel_ageJet_bdd_on_Icc hν hc hA hAB tr hbuc m n
  refine ⟨M, hM_nn, fun s hs y => ?_⟩
  have hsIoo : s ∈ Ioo (0 : ℝ) 2 := ⟨hT₁.trans_le hs.1, hs.2.trans_lt hT₂⟩
  have hsm := dtIterV_shiftedDriftTrain_slice_smooth tr hσ m hsIoo
  have h1 := norm_slicePdIterR_le_iteratedFDeriv α hsm y
  have hfun : dtIterV m (F8Ex.shiftedDriftTrain tr σ) s =
      fun z => iteratedDeriv m (fun r => tr.v r z) (σ + s) :=
    funext (dtIterV_shiftedDriftTrain_eq tr σ m s)
  have h2 : ‖iteratedFDeriv ℝ n (dtIterV m (F8Ex.shiftedDriftTrain tr σ) s) y‖ =
      ‖ageJet m n tr.v (σ + s) y‖ := by
    unfold ageJet Train.jet
    rw [hfun]
  have hsAB : σ + s ∈ Icc A B := ⟨by dsimp [A]; linarith [hs.1], by dsimp [B]; linarith [hs.2]⟩
  exact h1.trans (h2.le.trans (hM (σ + s) hsAB y))

theorem hasDerivAt_slicePdIterR_dtIterV {ν c : ℝ} (tr : B0140.TrainSol ν c)
    {σ : ℝ} (hσ : 0 ≤ σ) (m : ℕ) {n : ℕ} (α : Fin n → Fin 2)
    {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 2) (y : B0579.Plane) :
    HasDerivAt
      (fun t => F8Ex.slicePdIterR α (dtIterV m (F8Ex.shiftedDriftTrain tr σ) t) y)
      (F8Ex.slicePdIterR α (dtIterV (m + 1) (F8Ex.shiftedDriftTrain tr σ) s) y) s := by
  let V := F8Ex.shiftedDriftTrain tr σ
  have hsm_m := dtIterV_shiftedDriftTrain_smoothOn tr hσ m
  have hcomm : ∀ {k : ℕ} (β : Fin k → Fin 2),
      ContDiffOn ℝ ∞ (fun x : Coord => F8Ex.slicePdIterR β (dtIterV m V x.1) x.2)
        (Ioo (0 : ℝ) 2 ×ˢ univ) ∧
      ∀ {t : ℝ}, t ∈ Ioo (0 : ℝ) 2 → ∀ z : B0579.Plane,
        deriv (fun r => F8Ex.slicePdIterR β (dtIterV m V r) z) t =
          F8Ex.slicePdIterR β (dtIterV (m + 1) V t) z := by
    intro k β
    induction k with
    | zero =>
        refine ⟨hsm_m, fun {t} _ z => ?_⟩
        simp only [F8Ex.slicePdIterR, dtIterV, iteratedDeriv_succ]
    | succ k ihk =>
        obtain ⟨hsm_tail, hder_tail⟩ := ihk (Fin.tail β)
        have hpd_eq : ∀ x ∈ Ioo (0 : ℝ) 2 ×ˢ (univ : Set B0579.Plane),
            F8Ex.slicePdIterR β (dtIterV m V x.1) x.2 =
              F8Ex.pdR (β 0)
                (fun w : Coord => F8Ex.slicePdIterR (Fin.tail β) (dtIterV m V w.1) w.2) x := by
          intro x hx
          simp only [F8Ex.slicePdIterR]
          exact (F8Ex.pdR_uncurry_eq_slicePdR hsm_tail hx.1 (β 0) x.2).symm
        have hsm_cur : ContDiffOn ℝ ∞
            (fun x : Coord => F8Ex.slicePdIterR β (dtIterV m V x.1) x.2)
            (Ioo (0 : ℝ) 2 ×ˢ univ) := by
          have hpd : ContDiffOn ℝ ∞
              (F8Ex.pdR (β 0)
                (fun w : Coord => F8Ex.slicePdIterR (Fin.tail β) (dtIterV m V w.1) w.2))
              (Ioo (0 : ℝ) 2 ×ˢ univ) :=
            (hsm_tail.fderivWithin (IsOpen.uniqueDiffOn (isOpen_Ioo.prod isOpen_univ))
              (by simp)).clm_apply contDiffOn_const
                |>.congr (fun w hw => by
                  unfold F8Ex.pdR
                  rw [fderivWithin_of_isOpen (isOpen_Ioo.prod isOpen_univ) hw])
          exact hpd.congr hpd_eq
        refine ⟨hsm_cur, fun {t} ht z => ?_⟩
        -- Commute `deriv (t := ·)` and `slicePdR (β 0)` on the smooth function `G(r, w)`
        let G : Coord → F8Ex.RMerid :=
          fun w => F8Ex.slicePdIterR (Fin.tail β) (dtIterV m V w.1) w.2
        have hG_at : ContDiffAt ℝ ∞ G (t, z) :=
          hsm_tail.contDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨ht, trivial⟩)
        -- Second derivative symmetry of `G` in `(1, 0)` and `(0, dir (β 0))`
        have hsymm : fderiv ℝ (fun w : Coord => fderiv ℝ G w (0, B0579.dir (β 0))) (t, z)
            (1, (0, 0)) =
            fderiv ℝ (fun w : Coord => fderiv ℝ G w (1, (0, 0))) (t, z)
              (0, B0579.dir (β 0)) := by
          have hG2 : ContDiffAt ℝ (2 : WithTop ℕ∞) G (t, z) := hG_at.of_le (by simp)
          have hd2 : DifferentiableAt ℝ (fderiv ℝ G) (t, z) :=
            (hG2.fderiv_right (by norm_num)).differentiableAt one_ne_zero
          have hl : fderiv ℝ (fun w : Coord => fderiv ℝ G w (0, B0579.dir (β 0))) (t, z)
              (1, (0, 0)) =
              fderiv ℝ (fderiv ℝ G) (t, z) (1, (0, 0)) (0, B0579.dir (β 0)) := by
            have hcomp := (ContinuousLinearMap.apply ℝ F8Ex.RMerid
              ((0 : ℝ), B0579.dir (β 0))).hasFDerivAt.comp (t, z) hd2.hasFDerivAt
            exact congrArg (fun L => L (1, (0, 0))) hcomp.fderiv
          have hr : fderiv ℝ (fun w : Coord => fderiv ℝ G w (1, (0, 0))) (t, z)
              (0, B0579.dir (β 0)) =
              fderiv ℝ (fderiv ℝ G) (t, z) (0, B0579.dir (β 0)) (1, (0, 0)) := by
            have hcomp := (ContinuousLinearMap.apply ℝ F8Ex.RMerid
              ((1 : ℝ), ((0 : ℝ), (0 : ℝ)))).hasFDerivAt.comp (t, z) hd2.hasFDerivAt
            exact congrArg (fun L => L (0, B0579.dir (β 0))) hcomp.fderiv
          rw [hl, hr]
          exact (ContDiffAt.isSymmSndFDerivAt (n := 2) hG2 (by simp)).eq
            (1, (0, 0)) (0, B0579.dir (β 0))
        have h_lhs : deriv (fun r => F8Ex.slicePdIterR β (dtIterV m V r) z) t =
            fderiv ℝ (fun w : Coord => fderiv ℝ G w (0, B0579.dir (β 0))) (t, z) (1, (0, 0)) := by
          have hev : (fun r => F8Ex.slicePdIterR β (dtIterV m V r) z) =ᶠ[𝓝 t]
              fun r => fderiv ℝ G (r, z) (0, B0579.dir (β 0)) := by
            filter_upwards [isOpen_Ioo.mem_nhds ht] with r hr
            have := hpd_eq (r, z) ⟨hr, trivial⟩
            simpa [F8Ex.pdR, F8Ex.sdir_eq_zero_dir, G] using this
          rw [hev.deriv_eq]
          have hd1 : DifferentiableAt ℝ (fun w : Coord => fderiv ℝ G w (0, B0579.dir (β 0)))
              (t, z) :=
            (((hG_at.fderiv_right (m := 1) (by simp)).clm_apply contDiffAt_const).differentiableAt
              one_ne_zero)
          have hpath : HasDerivAt (fun r : ℝ => ((r, z) : Coord)) (1, (0, 0)) t :=
            (hasDerivAt_id t).prodMk (hasDerivAt_const t z)
          exact (hd1.hasFDerivAt.comp_hasDerivAt t hpath).deriv
        have h_rhs : F8Ex.slicePdIterR β (dtIterV (m + 1) V t) z =
            fderiv ℝ (fun w : Coord => fderiv ℝ G w (1, (0, 0))) (t, z) (0, B0579.dir (β 0)) := by
          simp only [F8Ex.slicePdIterR]
          have hfun_z : F8Ex.slicePdIterR (Fin.tail β) (dtIterV (m + 1) V t) =
              fun y => fderiv ℝ G (t, y) (1, (0, 0)) := by
            funext y
            rw [← hder_tail ht y]
            have hdG : DifferentiableAt ℝ G (t, y) :=
              (hsm_tail.contDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨ht, trivial⟩))
                |>.differentiableAt (by simp)
            have hpath : HasDerivAt (fun r : ℝ => ((r, y) : Coord)) (1, (0, 0)) t :=
              (hasDerivAt_id t).prodMk (hasDerivAt_const t y)
            exact (hdG.hasFDerivAt.comp_hasDerivAt t hpath).deriv
          unfold F8Ex.slicePdR
          rw [hfun_z]
          have hd2 : DifferentiableAt ℝ (fun w : Coord => fderiv ℝ G w (1, (0, 0))) (t, z) :=
            (((hG_at.fderiv_right (m := 1) (by simp)).clm_apply contDiffAt_const).differentiableAt
              one_ne_zero)
          have hemb : HasFDerivAt (fun y : B0579.Plane => ((t, y) : Coord))
              ((0 : B0579.Plane →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ B0579.Plane)) z :=
            (hasFDerivAt_const t z).prodMk (hasFDerivAt_id z)
          have hcomp_z := (hd2.hasFDerivAt.comp z hemb).fderiv
          change (fderiv ℝ ((fun w : Coord => fderiv ℝ G w (1, (0, 0))) ∘ Prod.mk t) z)
              (B0579.dir (β 0)) = _
          rw [hcomp_z]
          simp
        rw [h_lhs, h_rhs, hsymm]
  obtain ⟨hsm_α, hder_α⟩ := hcomm α
  have hd_at : DifferentiableAt ℝ (fun t => F8Ex.slicePdIterR α (dtIterV m V t) y) s := by
    have hsm_at : ContDiffAt ℝ ∞ (fun x : Coord => F8Ex.slicePdIterR α (dtIterV m V x.1) x.2)
        (s, y) :=
      hsm_α.contDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨hs, trivial⟩)
    have hp : HasDerivAt (fun t : ℝ => ((t, y) : Coord)) (1, (0, 0)) s :=
      (hasDerivAt_id' s).prodMk (hasDerivAt_const s y)
    exact ((hsm_at.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt s hp).differentiableAt
  rw [← hder_α hs y]
  exact hd_at.hasDerivAt

end UnforcedLeray.Short.IIb.F8JointUpgrade
