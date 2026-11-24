import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_2.L4
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_2.L5
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_2.L3
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_3_2_11_2_2_2.ParamTop
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T16_1_1.L1_Smooth
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T16_1_1.L2_JointMeas
import UnforcedLeray.Short.PartIIIa.T15_SepKernelBounds

/-!
# All-order smoothness of `sepW` off the source disk (source 3604-3621)

Source of record: `the November 2 reference manuscript` (73 pages).

`sepWSmoothOn_of` (`Sub/IIIb-D2_3_1_1/L2.lean`) gives `C²`; the proofs of its five leaves hold at
every order: `K_t` is `C^∞` (`IIIa.heatLerayKSmoothAll`), the `x`-derivatives of `K_t` are jointly
measurable at every order (`IIIa.heatLerayKJointMeas`), `sep:kernel` holds at every order
(`IIIa.sepKernelBounds`), and the majorant integrability (`L5`) is uniform in the order.  Hence
`y ↦ sepW ν μ T y τ i` is `C^n` on `ϱ y > r_o` for every `n`, for every separated source with finite
`Y₂` moment (`sepW_contDiffOn_nat`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-! ## 1. The integrand at every order -/

lemma sd_term (K : Space → ℝ) (hK : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) K) (c : ℂ) (e w y : Space)
    (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun y' => c * (((fderiv ℝ K (y' - w) e : ℝ)) : ℂ)) y‖ ≤
      ‖c‖ * ‖e‖ * ‖iteratedFDeriv ℝ (n + 1) K (y - w)‖ := by
  have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y' : Space => fderiv ℝ K (y' - w)) :=
    ((hK.fderiv_right (by simp)).comp (contDiff_id.sub contDiff_const))
  let L : (Space →L[ℝ] ℝ) →L[ℝ] ℂ :=
    (c • Complex.ofRealCLM).comp (ContinuousLinearMap.apply ℝ ℝ e)
  have hL : ∀ f : Space →L[ℝ] ℝ, L f = c * ((f e : ℝ) : ℂ) := by
    intro f; simp [L]
  have hfun : (fun y' : Space => c * (((fderiv ℝ K (y' - w) e : ℝ)) : ℂ)) =
      L ∘ (fun y' : Space => fderiv ℝ K (y' - w)) := by
    funext y'; simp [hL]
  have hLn : ‖L‖ ≤ ‖c‖ * ‖e‖ := by
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun f => ?_
    rw [hL, norm_mul, Complex.norm_real]
    have : ‖f e‖ ≤ ‖f‖ * ‖e‖ := f.le_opNorm e
    nlinarith [norm_nonneg c, norm_nonneg f, norm_nonneg e]
  rw [hfun]
  have h2 := L.norm_iteratedFDeriv_comp_left (f := fun y' : Space => fderiv ℝ K (y' - w))
    (x := y) (N := ((⊤ : ℕ∞) : WithTop ℕ∞)) (n := n) (h1.contDiffAt)
    (by exact_mod_cast le_top)
  refine h2.trans ?_
  have h3 : iteratedFDeriv ℝ n (fun y' : Space => fderiv ℝ K (y' - w)) y =
      iteratedFDeriv ℝ n (fderiv ℝ K) (y - w) := iteratedFDeriv_comp_sub (f := fderiv ℝ K) n w y
  rw [h3, norm_iteratedFDeriv_fderiv]
  exact mul_le_mul_of_nonneg_right hLn (norm_nonneg _)

lemma sd_sum {ι : Type} (u : Finset ι) (f : ι → Space → ℂ) (n : ℕ)
    (hf : ∀ i ∈ u, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (f i)) (y : Space) :
    ‖iteratedFDeriv ℝ n (fun w => ∑ i ∈ u, f i w) y‖ ≤ ∑ i ∈ u, ‖iteratedFDeriv ℝ n (f i) y‖ := by
  rw [iteratedFDeriv_fun_sum_apply
    (fun i hi => ((hf i hi).of_le (by exact_mod_cast le_top)).contDiffAt)]
  exact norm_sum_le _ _

lemma sd_term_cd (K : Space → ℝ) (hK : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) K) (c : ℂ)
    (e w : Space) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y' : Space => c * (((fderiv ℝ K (y' - w) e : ℝ)) : ℂ)) := by
  have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y' : Space => fderiv ℝ K (y' - w)) :=
    ((hK.fderiv_right (by simp)).comp (contDiff_id.sub contDiff_const))
  exact contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (h1.clm_apply contDiff_const))

lemma sd_phi (ν : ℝ) (μ : ℂ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (τ : ℝ) (i : Fin 3)
    (l : ℝ) (z : Space) (hl : l ∈ Ioo (0 : ℝ) 1) (hν : 0 < ν) (n : ℕ) (y : Space) :
    ‖iteratedFDeriv ℝ n (sepPhi ν μ T τ i (l, z)) y‖ ≤
      ∑ j : Fin 3, ∑ k : Fin 3, ‖(-2 * (l : ℂ) ^ (2 * μ + 2) *
          ((T (τ + 2 * Real.log l) z j k : ℝ) : ℂ))‖ * ‖coordinateVector k‖ *
        ‖iteratedFDeriv ℝ (n + 1) (fun x => IIIa.heatLerayK (ν * (1 - l ^ 2)) i j x)
          (y - l • z)‖ := by
  have ht : 0 < ν * (1 - l ^ 2) := by
    have := hl.1; have := hl.2; nlinarith [mul_pos hν (sub_pos.2 (show l ^ 2 < 1 by nlinarith))]
  have hK : ∀ j, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x => IIIa.heatLerayK (ν * (1 - l ^ 2)) i j x) :=
    fun j => IIIa.heatLerayKSmoothAll _ ht i j
  have hfun : sepPhi ν μ T τ i (l, z) = fun y' => ∑ j : Fin 3, ∑ k : Fin 3,
      (-2 * (l : ℂ) ^ (2 * μ + 2) * ((T (τ + 2 * Real.log l) z j k : ℝ) : ℂ)) *
        ((fderiv ℝ (fun x => IIIa.heatLerayK (ν * (1 - l ^ 2)) i j x) (y' - l • z)
          (coordinateVector k) : ℝ) : ℂ) := by
    funext y'
    unfold sepPhi
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [hfun]
  refine (sd_sum _ _ n (fun j _ => ContDiff.sum fun k _ => sd_term_cd _ (hK j) _ _ _) y).trans ?_
  refine Finset.sum_le_sum fun j _ => ?_
  refine (sd_sum _ _ n (fun k _ => sd_term_cd _ (hK j) _ _ _) y).trans ?_
  refine Finset.sum_le_sum fun k _ => ?_
  exact sd_term _ (hK j) _ _ _ y n

theorem sd_sepPhi_contDiff (ν : ℝ) (μ : ℂ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (τ : ℝ)
    (i : Fin 3) (l : ℝ) (z : Space) (hν : 0 < ν) (hl : l ∈ Ioo (0 : ℝ) 1) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (sepPhi ν μ T τ i (l, z)) := by
  have ht : 0 < ν * (1 - l ^ 2) := by
    have := hl.1; have := hl.2; nlinarith [mul_pos hν (sub_pos.2 (show l ^ 2 < 1 by nlinarith))]
  unfold sepPhi
  refine contDiff_const.mul (ContDiff.sum fun j _ => ContDiff.sum fun k _ => ?_)
  refine ContDiff.mul ?_ contDiff_const
  have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x => fderiv ℝ (fun x => IIIa.heatLerayK (ν * (1 - l ^ 2)) i j x) x) :=
    (IIIa.heatLerayKSmoothAll _ ht i j).fderiv_right (by simp)
  have h3 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : Space => y - l • z) :=
    contDiff_id.sub contDiff_const
  exact Complex.ofRealCLM.contDiff.comp ((h1.comp h3).clm_apply contDiff_const)

/-! ## 2. Measurability at every order -/

theorem sd_sepPhiMeasurable (ν : ℝ) (μ : ℂ) (P rOut : ℝ)
    (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (hν : 0 < ν) (hS : IIIa.IsSepSource P rOut T)
    (τ : ℝ) (i : Fin 3) (n : ℕ) (y : Space) :
    AEStronglyMeasurable (fun p => iteratedFDeriv ℝ n (sepPhi ν μ T τ i p) y) sepRho := by
  choose L hL using fun k : Fin 3 => exists_deriv_clm n (coordinateVector k)
  let a : Fin 3 → Fin 3 → ℝ × Space → ℂ := fun j k p =>
    -2 * (p.1 : ℂ) ^ (2 * μ + 2) * ((T (τ + 2 * Real.log p.1) p.2 j k : ℝ) : ℂ)
  have ha : ∀ j k, Measurable (a j k) := by
    intro j k
    have h1 : Measurable fun p : ℝ × Space => T (τ + 2 * Real.log p.1) p.2 j k :=
      (hS.measurable j k).comp
        (((measurable_const.add (measurable_const.mul
          (Real.measurable_log.comp measurable_fst)))).prodMk measurable_snd)
    have h2' : Measurable fun p : ℝ × Space => (p.1 : ℂ) ^ (2 * μ + 2) :=
      (Complex.measurable_ofReal.comp measurable_fst).pow_const _
    exact (measurable_const.mul h2').mul (Complex.measurable_ofReal.comp h1)
  let R : ℝ × Space → ContinuousMultilinearMap ℝ (fun _ : Fin n => Space) ℂ := fun p =>
    ∑ j : Fin 3, ∑ k : Fin 3, a j k p • L k
      (if 0 < ν * (1 - p.1 ^ 2) then
        iteratedFDeriv ℝ (n + 1) (fun x => IIIa.heatLerayK (ν * (1 - p.1 ^ 2)) i j x)
          (y - p.1 • p.2) else 0)
  have hR : StronglyMeasurable R := by
    simp only [R]
    refine Finset.stronglyMeasurable_fun_sum _ fun j _ =>
      Finset.stronglyMeasurable_fun_sum _ fun k _ => ?_
    refine ((ha j k).stronglyMeasurable).smul ?_
    refine (L k).continuous.comp_stronglyMeasurable ?_
    have hm : Measurable fun p : ℝ × Space => (ν * (1 - p.1 ^ 2), y - p.1 • p.2) :=
      (measurable_const.mul (measurable_const.sub (measurable_fst.pow_const 2))).prodMk
        (measurable_const.sub (measurable_fst.smul measurable_snd))
    exact (IIIa.heatLerayKJointMeas i j (n + 1)).comp_measurable hm
  refine hR.aestronglyMeasurable.congr ?_
  filter_upwards [ae_mem_Ioo_sepRho] with p hp
  have ht : 0 < ν * (1 - p.1 ^ 2) := by
    have := hp.1; have := hp.2; nlinarith [mul_pos hν (sub_pos.2 (show p.1 ^ 2 < 1 by nlinarith))]
  have hK : ∀ j, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x => IIIa.heatLerayK (ν * (1 - p.1 ^ 2)) i j x) :=
    fun j => IIIa.heatLerayKSmoothAll _ ht i j
  have hg : ∀ j k, ContDiff ℝ n (fun x : Space =>
      ((fderiv ℝ (fun x => IIIa.heatLerayK (ν * (1 - p.1 ^ 2)) i j x) x
        (coordinateVector k) : ℝ) : ℂ)) := by
    intro j k
    refine Complex.ofRealCLM.contDiff.comp
      ((ContinuousLinearMap.apply ℝ ℝ (coordinateVector k)).contDiff.comp ?_)
    exact ((hK j).fderiv_right (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) (by simp)).of_le
      (by exact_mod_cast le_top)
  have hsum : sepPhi ν μ T τ i p = fun y' => ∑ j : Fin 3, ∑ k : Fin 3, a j k p •
      ((fun x : Space => ((fderiv ℝ (fun x => IIIa.heatLerayK (ν * (1 - p.1 ^ 2)) i j x) x
        (coordinateVector k) : ℝ) : ℂ)) (y' - p.1 • p.2)) := by
    funext y'
    simp only [sepPhi, a, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [hsum]
  have hk : ∀ j k, ContDiff ℝ n (fun y' : Space => a j k p •
      ((fun x : Space => ((fderiv ℝ (fun x => IIIa.heatLerayK (ν * (1 - p.1 ^ 2)) i j x) x
        (coordinateVector k) : ℝ) : ℂ)) (y' - p.1 • p.2))) :=
    fun j k => ((hg j k).comp (contDiff_id.sub contDiff_const)).const_smul _
  have hj : ∀ j, ContDiffAt ℝ n (fun y' : Space => ∑ k : Fin 3, a j k p •
      ((fun x : Space => ((fderiv ℝ (fun x => IIIa.heatLerayK (ν * (1 - p.1 ^ 2)) i j x) x
        (coordinateVector k) : ℝ) : ℂ)) (y' - p.1 • p.2))) y :=
    fun j => (ContDiff.sum fun k _ => hk j k).contDiffAt
  symm
  simp only [R, ht, ite_true]
  rw [iteratedFDeriv_fun_sum_apply (fun j _ => hj j)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [iteratedFDeriv_fun_sum_apply (fun k _ => (hk j k).contDiffAt)]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hc : ContDiffAt ℝ n (fun y' : Space => ((fderiv ℝ
      (fun x => IIIa.heatLerayK (ν * (1 - p.1 ^ 2)) i j x) (y' - p.1 • p.2)
      (coordinateVector k) : ℝ) : ℂ)) y :=
    ((hg j k).comp (contDiff_id.sub contDiff_const)).contDiffAt
  rw [iteratedFDeriv_const_smul_apply' hc]
  congr 1
  rw [iteratedFDeriv_comp_sub (f := fun x : Space => ((fderiv ℝ
      (fun x => IIIa.heatLerayK (ν * (1 - p.1 ^ 2)) i j x) x (coordinateVector k) : ℝ) : ℂ)),
    hL k _ _ ((hK j).of_le (by exact_mod_cast le_top))]

/-! ## 3. The pointwise bound at every order -/

lemma sd_kern (n : ℕ) : ∃ Cn : ℝ, 0 ≤ Cn ∧ ∀ x : Space, x ≠ 0 → ∀ i k : Fin 3, ∀ t : ℝ, 0 < t →
    ‖iteratedFDeriv ℝ (n + 1) (fun y => IIIa.heatLerayK t i k y) x‖ ≤ Cn * ‖x‖ ^ (-4 - (n : ℝ)) := by
  obtain ⟨C0, h0⟩ := IIIa.sepKernelBounds n
  refine ⟨|C0|, abs_nonneg _, ?_⟩
  intro x hx i k t ht
  have hp : 0 ≤ ‖x‖ ^ (-4 - (n : ℝ)) := by positivity
  exact ((h0 x hx i k).1 t ht).trans (mul_le_mul_of_nonneg_right (le_abs_self _) hp)

theorem sd_gapPointwise (ν : ℝ) (μ : ℂ) (rOut P : ℝ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ)
    (hν : 0 < ν) (hr : 0 ≤ rOut) (hS : IIIa.IsSepSource P rOut T) (τ : ℝ) (i : Fin 3)
    (y0 : Space) (hy0 : rOut < ϱ y0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ Metric.ball y0 ε, ∀ l ∈ Ioo (0 : ℝ) 1,
      ∀ z : Space, ‖iteratedFDeriv ℝ n (sepPhi ν μ T τ i (l, z)) y‖ ≤
        C * sepMajorant μ T τ n (l, z) := by
  set d : ℝ := (ϱ y0 - rOut) / 2 with hd
  have hd0 : 0 < d := by rw [hd]; linarith
  set c : ℝ := d / (1 + (‖y0‖ + 1) + d) with hc
  have hc0 : 0 < c := by rw [hc]; positivity
  have hc1 : c ≤ 1 := by
    rw [hc, div_le_one (by positivity)]; linarith [norm_nonneg y0]
  refine ⟨min d 1, lt_min hd0 one_pos, fun n => ?_⟩
  obtain ⟨Cn, hCn0, hCn⟩ := sd_kern n
  refine ⟨18 * Cn * c ^ (-4 - (n : ℝ)), by positivity, ?_⟩
  intro y hy l hl z
  have hl0 : 0 < l := hl.1
  by_cases hz : rOut < ϱ z
  · have hT : T (τ + 2 * Real.log l) z = 0 := hS.support _ _ hz
    refine (sd_phi ν μ T τ i l z hl hν n y).trans ?_
    have : ∀ j k : Fin 3, ‖(-2 * (l : ℂ) ^ (2 * μ + 2) *
          ((T (τ + 2 * Real.log l) z j k : ℝ) : ℂ))‖ = 0 := by
      intro j k; simp [hT]
    simp only [this, zero_mul, Finset.sum_const_zero]
    exact mul_nonneg (by positivity) (L4_majorant_nonneg μ T τ n l z hl0)
  · push Not at hz
    have hyb : ‖y - y0‖ < min d 1 := by simpa [dist_eq_norm] using hy
    have hgeom := L4_geom rOut d (min d 1) y0 y z l hl hz hyb (min_le_left _ _) (min_le_right _ _)
      hd0 (by rw [hd]; linarith)
    have hx0 : 0 < ‖y - l • z‖ := lt_of_lt_of_le (by positivity) hgeom |>.trans_le' le_rfl
    have hx : y - l • z ≠ 0 := norm_pos_iff.1 hx0
    refine (sd_phi ν μ T τ i l z hl hν n y).trans ?_
    have hpow : ‖y - l • z‖ ^ (-4 - (n : ℝ)) ≤
        c ^ (-4 - (n : ℝ)) * (1 + l * ‖z‖) ^ (-(4 + (n : ℝ))) := by
      have h1 : ‖y - l • z‖ ^ (-4 - (n : ℝ)) ≤ (c * (1 + l * ‖z‖)) ^ (-4 - (n : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) hgeom
          (by linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)])
      rw [Real.mul_rpow hc0.le (by positivity)] at h1
      have h4 : (1 + l * ‖z‖) ^ (-4 - (n : ℝ)) = (1 + l * ‖z‖) ^ (-(4 + (n : ℝ))) := by
        congr 1; ring
      rw [h4] at h1
      exact h1
    have hterm : ∀ j k : Fin 3, ‖(-2 * (l : ℂ) ^ (2 * μ + 2) *
          ((T (τ + 2 * Real.log l) z j k : ℝ) : ℂ))‖ * ‖coordinateVector k‖ *
        ‖iteratedFDeriv ℝ (n + 1) (fun x => IIIa.heatLerayK (ν * (1 - l ^ 2)) i j x)
          (y - l • z)‖ ≤ 2 * Cn * c ^ (-4 - (n : ℝ)) * sepMajorant μ T τ n (l, z) := by
      intro j k
      have ht : 0 < ν * (1 - l ^ 2) := by
        have := hl.2; nlinarith [mul_pos hν (sub_pos.2 (show l ^ 2 < 1 by nlinarith))]
      have hk := hCn _ hx i j _ ht
      have he : ‖coordinateVector k‖ = 1 := by simp [coordinateVector]
      have hn1 : ‖(-2 * (l : ℂ) ^ (2 * μ + 2) * ((T (τ + 2 * Real.log l) z j k : ℝ) : ℂ))‖ ≤
          2 * l ^ (2 * μ.re + 2) * IIIa.tensorNorm (T (τ + 2 * Real.log l) z) := by
        rw [norm_mul, norm_mul, norm_neg, Complex.norm_real,
          Complex.norm_cpow_eq_rpow_re_of_pos hl0]
        simp only [Complex.add_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat,
          zero_mul, sub_zero, Real.norm_eq_abs]
        have := L4_entry (T (τ + 2 * Real.log l) z) j k
        have hp : 0 ≤ l ^ (2 * μ.re + 2) := by positivity
        have h2' : ‖(2 : ℂ)‖ = 2 := by simp
        rw [h2']
        nlinarith
      rw [he, mul_one]
      calc _ ≤ (2 * l ^ (2 * μ.re + 2) * IIIa.tensorNorm (T (τ + 2 * Real.log l) z)) *
            (Cn * (c ^ (-4 - (n : ℝ)) * (1 + l * ‖z‖) ^ (-(4 + (n : ℝ))))) := by
            refine mul_le_mul hn1 (hk.trans (mul_le_mul_of_nonneg_left hpow hCn0)) (norm_nonneg _)
              (mul_nonneg (by positivity) (Real.sqrt_nonneg _))
        _ = 2 * Cn * c ^ (-4 - (n : ℝ)) * sepMajorant μ T τ n (l, z) := by
            unfold sepMajorant; simp only; ring
    refine (Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => hterm j k).trans ?_
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hm := L4_majorant_nonneg μ T τ n l z hl0
    push_cast
    nlinarith

/-! ## 4. The majorant is integrable at every order -/

theorem sd_majorantIntegrable (μ : ℂ) (P rOut : ℝ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ)
    (hμ : -(1 / 4) < μ.re) (hP : 0 < P) (hS : IIIa.IsSepSource P rOut T) (hM : SepMoment P T)
    (τ : ℝ) (n : ℕ) : Integrable (sepMajorant μ T τ n) sepRho := by
  refine ⟨(l5Meas μ P rOut T hS τ n).aestronglyMeasurable, ?_⟩
  obtain ⟨C, hC0, hC⟩ := l5Holder n
  obtain ⟨hfm, hfp, hfi⟩ := l5Moment P rOut T hP hS hM
  set a : ℝ := 2 * μ.re + 2 - 3 / 2 with ha
  have hfin := l5PerSum P hP (fMom T) hfm hfp hfi (a + 1) (by rw [ha]; linarith) τ
  rw [← l5ChangeVar (fMom T) hfm a τ] at hfin
  have hmeas : Measurable (fun p => ENNReal.ofReal (sepMajorant μ T τ n p)) :=
    (l5Meas μ P rOut T hS τ n).ennreal_ofReal
  unfold HasFiniteIntegral
  have hnn : ∀ p : ℝ × Space, p.1 ∈ Ioo (0 : ℝ) 1 → 0 ≤ sepMajorant μ T τ n p := by
    intro p hp
    have := hp.1
    unfold sepMajorant IIIa.tensorNorm
    positivity
  calc ∫⁻ p, ‖sepMajorant μ T τ n p‖ₑ ∂sepRho
      = ∫⁻ p, ENNReal.ofReal (sepMajorant μ T τ n p) ∂sepRho := by
        refine lintegral_congr_ae ?_
        filter_upwards [ae_mem_Ioo_sepRho] with p hp
        exact Real.enorm_of_nonneg (hnn p hp)
    _ = ∫⁻ l in Ioo (0 : ℝ) 1, ∫⁻ z, ENNReal.ofReal (sepMajorant μ T τ n (l, z)) := by
        unfold sepRho
        exact lintegral_prod _ hmeas.aemeasurable
    _ ≤ ∫⁻ l in Ioo (0 : ℝ) 1, ENNReal.ofReal C *
          (ENNReal.ofReal (l ^ a) * fMom T (τ + 2 * Real.log l)) := by
        refine setLIntegral_mono' measurableSet_Ioo fun l hl => ?_
        have hl0 : 0 < l := hl.1
        have hpt : ∀ z : Space, ENNReal.ofReal (sepMajorant μ T τ n (l, z)) =
            ENNReal.ofReal (l ^ (2 * μ.re + 2)) *
              (ENNReal.ofReal ((1 + l * ‖z‖) ^ (-(4 + (n : ℝ)))) *
                IIIa.srcNorm T (τ + 2 * Real.log l) z) := by
          intro z
          unfold sepMajorant IIIa.srcNorm
          simp only
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity), mul_assoc]
        simp only [hpt]
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        have hF : Measurable (IIIa.srcNorm T (τ + 2 * Real.log l)) := by
          unfold IIIa.srcNorm IIIa.tensorNorm
          have hm : ∀ i j, Measurable fun z : Space => T (τ + 2 * Real.log l) z i j :=
            fun i j => (hS.measurable i j).comp (measurable_const.prodMk measurable_id)
          fun_prop
        have hH := hC l hl _ hF
        calc ENNReal.ofReal (l ^ (2 * μ.re + 2)) *
              ∫⁻ z, ENNReal.ofReal ((1 + l * ‖z‖) ^ (-(4 + (n : ℝ)))) *
                IIIa.srcNorm T (τ + 2 * Real.log l) z
            ≤ ENNReal.ofReal (l ^ (2 * μ.re + 2)) *
              (ENNReal.ofReal (C * l ^ (-(3 / 2 : ℝ))) * fMom T (τ + 2 * Real.log l)) :=
              mul_le_mul' le_rfl hH
          _ = ENNReal.ofReal C * (ENNReal.ofReal (l ^ a) * fMom T (τ + 2 * Real.log l)) := by
              have hpw : l ^ (2 * μ.re + 2) * (C * l ^ (-(3 / 2 : ℝ))) = C * l ^ a := by
                have : l ^ a = l ^ (2 * μ.re + 2) * l ^ (-(3 / 2 : ℝ)) := by
                  rw [← Real.rpow_add hl0, ha]; ring_nf
                rw [this]; ring
              rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), hpw, ENNReal.ofReal_mul hC0,
                mul_assoc]
    _ = ENNReal.ofReal C * ∫⁻ l in Ioo (0 : ℝ) 1,
          ENNReal.ofReal (l ^ a) * fMom T (τ + 2 * Real.log l) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin

/-! ## 5. All-order smoothness of `sepW` off the source disk -/

theorem sepW_contDiffOn_top (ν : ℝ) (μ : ℂ) (rOut P : ℝ)
    (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (hν : 0 < ν) (hμ : -(1 / 4) < μ.re)
    (hr : 0 ≤ rOut) (hP : 0 < P) (hS : IIIa.IsSepSource P rOut T) (hM : SepMoment P T)
    (τ : ℝ) (i : Fin 3) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => IIIa.sepW ν μ T y τ i)
      {y : Space | rOut < ϱ y} := by
  refine contDiffOn_of_locally_contDiffOn fun y₀ hy₀ => ?_
  obtain ⟨ε, hε, hb⟩ := sd_gapPointwise ν μ rOut P T hν hr hS τ i y₀ hy₀
  choose C hC0 hCb using hb
  refine ⟨Metric.ball y₀ ε, Metric.isOpen_ball, Metric.mem_ball_self hε, ?_⟩
  have hint : ∀ n : ℕ, Integrable (fun p => C n * sepMajorant μ T τ n p) sepRho :=
    fun n => (sd_majorantIntegrable μ P rOut T hμ hP hS hM τ n).const_mul (C n)
  have hbound : ∀ n : ℕ, ∀ᵐ p ∂sepRho, ∀ y ∈ Metric.ball y₀ ε,
      ‖iteratedFDeriv ℝ n (sepPhi ν μ T τ i p) y‖ ≤ C n * sepMajorant μ T τ n p := by
    intro n
    filter_upwards [ae_mem_Ioo_sepRho] with p hp y hy
    exact hCb n y hy p.1 hp p.2
  have key : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => ∫ p, sepPhi ν μ T τ i p y ∂sepRho)
      (Metric.ball y₀ ε) := by
    refine contDiffOn_infty.2 fun n => ?_
    refine paramContDiffOn_nat n sepRho (sepPhi ν μ T τ i) (Metric.ball y₀ ε)
      (fun n p => C n * sepMajorant μ T τ n p) Metric.isOpen_ball ?_ hint hbound ?_
    · filter_upwards [ae_mem_Ioo_sepRho] with p hp
      exact (sd_sepPhi_contDiff ν μ T τ i p.1 p.2 hν hp).contDiffOn
    · intro k y _
      exact sd_sepPhiMeasurable ν μ P rOut T hν hS τ i k y
  refine (key.mono inter_subset_right).congr fun y hy => ?_
  apply sepW_eq_integral
  have hm : AEStronglyMeasurable (fun p => sepPhi ν μ T τ i p y) sepRho := by
    have := (continuousMultilinearCurryFin0 ℝ Space ℂ).continuous.comp_aestronglyMeasurable
      (sd_sepPhiMeasurable ν μ P rOut T hν hS τ i 0 y)
    refine this.congr (Filter.Eventually.of_forall fun p => ?_)
    simp [iteratedFDeriv_zero_eq_comp]
  refine Integrable.mono' (hint 0) hm ?_
  filter_upwards [hbound 0] with p hp
  have := hp y hy.2
  simpa [norm_iteratedFDeriv_zero] using this

end UnforcedLeray.Short.PartIIIb.Concrete
