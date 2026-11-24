import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomY.GeomYB.TaylorWidth.SepComm.MainLeibniz.SmoothW

/-!
# Spatial smoothness and far-field `O(ϱ^{-4})` decay of `newtonX0`

Helper for `PartIII-b:C/rep/8/1/1/2/5/2/1/1` (`YBWidth.sepCommMainLeibniz`).
Source `the November 2 reference manuscript`
lines 3604-3610, 3735-3766, 5415-5432.

For `newtonX0 ε μ G` where `G` is supported in `√(x'₁² + x'₂²) ≤ ρo`:
1. `newtonX0_contDiffOn`: `newtonX0 ε μ G τ` is `C^∞` on `{y' : Space | ρo / ε < ϱ y'}`;
2. `newtonX0_decay`: for each `n : ℕ`, `‖iteratedFDeriv ℝ n (newtonX0 ε μ G τ) y'‖ ≤ C_n * (ϱ y' ^ 4)⁻¹`
   for `2 * (ρo / ε) + 2 ≤ ϱ y'`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Short.IIIa

namespace YBWidth

open YBComm PhasePrim

/-! ## 1. Shifted directional derivative operators at arbitrary order -/

private def derivShiftCLM (n : ℕ) (v : Space) :
    ContinuousMultilinearMap ℝ (fun _ : Fin (n + 1) => Space) ℝ →L[ℝ]
      ContinuousMultilinearMap ℝ (fun _ : Fin n => Space) ℂ :=
  (ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin n => Space) ℝ ℂ
      Complex.ofRealCLM).comp
    ((ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin n => Space) (Space →L[ℝ] ℝ) ℝ
      (ContinuousLinearMap.apply ℝ ℝ v)).comp
      (continuousMultilinearCurryRightEquiv' ℝ n Space ℝ).toContinuousLinearEquiv.toContinuousLinearMap)

private theorem derivShiftCLM_apply (n : ℕ) (v : Space)
    (M : ContinuousMultilinearMap ℝ (fun _ : Fin (n + 1) => Space) ℝ) (m : Fin n → Space) :
    derivShiftCLM n v M m = ((M (Fin.snoc m v) : ℝ) : ℂ) := by
  simp [derivShiftCLM, continuousMultilinearCurryRightEquiv_apply']

private theorem norm_derivShiftCLM_le (n : ℕ) (k : Fin 3)
    (M : ContinuousMultilinearMap ℝ (fun _ : Fin (n + 1) => Space) ℝ) :
    ‖derivShiftCLM n (coordinateVector k) M‖ ≤ ‖M‖ := by
  refine ContinuousMultilinearMap.opNorm_le_bound (norm_nonneg M) fun m => ?_
  rw [derivShiftCLM_apply, Complex.norm_real, Real.norm_eq_abs]
  have h := M.le_opNorm (Fin.snoc m (coordinateVector k))
  rw [Fin.prod_univ_castSucc] at h
  simp only [Fin.snoc_castSucc, Fin.snoc_last, IIIa.mp_norm_e, mul_one] at h
  exact (Real.norm_eq_abs _).symm ▸ h

private theorem iteratedFDeriv_fderiv_shift (n : ℕ) (v a x : Space) {f : Space → ℝ}
    (hf : ContDiffAt ℝ ∞ f (x - a)) :
    iteratedFDeriv ℝ n (fun y => ((fderiv ℝ f (y - a) v : ℝ) : ℂ)) x =
      derivShiftCLM n v (iteratedFDeriv ℝ (n + 1) f (x - a)) := by
  rw [iteratedFDeriv_comp_sub (f := fun z : Space => ((fderiv ℝ f z v : ℝ) : ℂ))]
  have h1 : iteratedFDeriv ℝ n (fderiv ℝ f) (x - a) =
      (continuousMultilinearCurryRightEquiv' ℝ n Space ℝ) (iteratedFDeriv ℝ (n + 1) f (x - a)) := by
    rw [iteratedFDeriv_succ_eq_comp_right]; simp
  have hd : ContDiffAt ℝ n (fderiv ℝ f) (x - a) :=
    hf.fderiv_right (m := n) (by exact_mod_cast le_top)
  have h2 : iteratedFDeriv ℝ n (fun y => fderiv ℝ f y v) (x - a) =
      (ContinuousLinearMap.apply ℝ ℝ v).compContinuousMultilinearMap
        (iteratedFDeriv ℝ n (fderiv ℝ f) (x - a)) :=
    (ContinuousLinearMap.apply ℝ ℝ v).iteratedFDeriv_comp_left (f := fderiv ℝ f) hd le_rfl
  have h3 : ContDiffAt ℝ n (fun y => fderiv ℝ f y v) (x - a) :=
    (ContinuousLinearMap.apply ℝ ℝ v).contDiff.contDiffAt.comp (x - a) hd
  have h4 : iteratedFDeriv ℝ n (fun y => ((fderiv ℝ f y v : ℝ) : ℂ)) (x - a) =
      Complex.ofRealCLM.compContinuousMultilinearMap
        (iteratedFDeriv ℝ n (fun y => fderiv ℝ f y v) (x - a)) :=
    Complex.ofRealCLM.iteratedFDeriv_comp_left (f := fun y => fderiv ℝ f y v) h3 le_rfl
  rw [h4, h2, h1]
  rfl

private theorem contDiffAt_fderiv_shift (n : ℕ∞) (v a x : Space) {f : Space → ℝ}
    (hf : ContDiffAt ℝ ∞ f (x - a)) :
    ContDiffAt ℝ n (fun y => ((fderiv ℝ f (y - a) v : ℝ) : ℂ)) x := by
  have hd : ContDiffAt ℝ n (fderiv ℝ f) (x - a) :=
    hf.fderiv_right (m := n) (by exact_mod_cast (le_top : n + 1 ≤ ⊤))
  have hsub : ContDiffAt ℝ n (fun y : Space => y - a) x :=
    (contDiff_id.sub contDiff_const).contDiffAt
  exact Complex.ofRealCLM.contDiff.contDiffAt.comp x
    ((ContinuousLinearMap.apply ℝ ℝ v).contDiff.contDiffAt.comp x (hd.comp x hsub))

private theorem iteratedFDeriv_sum_fderiv_shift (n : ℕ) (K : Fin 3 → Space → ℝ) (a x : Space)
    (hK : ∀ j, ContDiffAt ℝ ∞ (K j) (x - a)) (b : ℂ) (c : Fin 3 → Fin 3 → ℝ) :
    iteratedFDeriv ℝ n (fun x' : Space => b * ∑ j : Fin 3, ∑ k : Fin 3,
      ((fderiv ℝ (K j) (x' - a) (coordinateVector k) : ℝ) : ℂ) * (c j k : ℂ)) x =
    ∑ j : Fin 3, ∑ k : Fin 3, (b * (c j k : ℂ)) •
      derivShiftCLM n (coordinateVector k) (iteratedFDeriv ℝ (n + 1) (K j) (x - a)) := by
  let g : Fin 3 → Fin 3 → Space → ℂ := fun j k x' =>
    ((fderiv ℝ (K j) (x' - a) (coordinateVector k) : ℝ) : ℂ)
  have hfun : (fun x' : Space => b * ∑ j : Fin 3, ∑ k : Fin 3,
      g j k x' * (c j k : ℂ)) =
      fun x' : Space => ∑ j : Fin 3, ∑ k : Fin 3, (b * (c j k : ℂ)) • g j k x' := by
    funext x'
    simp only [smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
  have hg : ∀ j k, ContDiffAt ℝ n (g j k) x :=
    fun j k => contDiffAt_fderiv_shift n (coordinateVector k) a x (hK j)
  have hk : ∀ j k, ContDiffAt ℝ n (fun x' => (b * (c j k : ℂ)) • g j k x') x :=
    fun j k => (hg j k).const_smul _
  have hj : ∀ j, ContDiffAt ℝ n (fun x' => ∑ k : Fin 3, (b * (c j k : ℂ)) • g j k x') x :=
    fun j => ContDiffAt.sum fun k _ => hk j k
  change iteratedFDeriv ℝ n (fun x' : Space => b * ∑ j : Fin 3, ∑ k : Fin 3,
      g j k x' * (c j k : ℂ)) x = _
  rw [hfun, iteratedFDeriv_fun_sum_apply (fun j _ => hj j)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [iteratedFDeriv_fun_sum_apply (fun k _ => hk j k)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [iteratedFDeriv_const_smul_apply' (hg j k),
    iteratedFDeriv_fderiv_shift n (coordinateVector k) a x (hK j)]

/-! ## 2. Smoothness and derivative bounds for `sepVmu0` -/

private theorem mpVF_iteratedFDeriv_eq (n : ℕ) (μ : ℂ) (ρo : ℝ)
    (G : ℝ × ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ)
    (hGs : ∀ x' Y, ρo < Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2) → G x' Y = 0)
    (p : ℝ × ((ℝ × ℝ) × ℝ)) (x : Space)
    (hne : Real.sqrt (p.2.1.1 ^ 2 + p.2.1.2 ^ 2) ≤ ρo → x - p.1 • IIIa.mpV3 p.2 ≠ 0)
    (i : Fin 3) :
    iteratedFDeriv ℝ n (fun x' => IIIa.mpVF μ G p x' i) x =
      ∑ j : Fin 3, ∑ k : Fin 3,
        ((-2 * (p.1 : ℂ) ^ (2 * μ + 2)) * ((G p.2.1 p.2.2 j k : ℝ) : ℂ)) •
          derivShiftCLM n (coordinateVector k)
            (iteratedFDeriv ℝ (n + 1) (fun y => IIIa.heatLerayK0 i j y)
              (x - p.1 • IIIa.mpV3 p.2)) := by
  by_cases hw : Real.sqrt (p.2.1.1 ^ 2 + p.2.1.2 ^ 2) ≤ ρo
  · have hK : ∀ j, ContDiffAt ℝ ∞ (fun y => IIIa.heatLerayK0 i j y) (x - p.1 • IIIa.mpV3 p.2) :=
      fun j => IIIa.mp_K0_contDiffAt _ (hne hw) i j
    have heq : (fun x' => IIIa.mpVF μ G p x' i) =
        fun x' => (-2 * (p.1 : ℂ) ^ (2 * μ + 2)) * ∑ j : Fin 3, ∑ k : Fin 3,
          ((fderiv ℝ (fun y => IIIa.heatLerayK0 i j y) (x' - p.1 • IIIa.mpV3 p.2)
            (coordinateVector k) : ℝ) : ℂ) * ((G p.2.1 p.2.2 j k : ℝ) : ℂ) := by
      funext x'; unfold IIIa.mpVF; ring
    rw [heq]
    exact iteratedFDeriv_sum_fderiv_shift n (fun j y => IIIa.heatLerayK0 i j y)
      (p.1 • IIIa.mpV3 p.2) x hK (-2 * (p.1 : ℂ) ^ (2 * μ + 2)) (fun j k => G p.2.1 p.2.2 j k)
  · have hw' : ρo < Real.sqrt (p.2.1.1 ^ 2 + p.2.1.2 ^ 2) := lt_of_not_ge hw
    have h0 : G p.2.1 p.2.2 = 0 := hGs _ _ hw'
    have hf : (fun x' => IIIa.mpVF μ G p x' i) = 0 := funext fun x' => IIIa.mpVF_zero μ G p h0 x' i
    rw [hf]
    have h0' : iteratedFDeriv ℝ n (0 : Space → ℂ) x = 0 := by simp
    have h0_smul : ∀ (M : Space [×n]→L[ℝ] ℂ), (0 : ℂ) • M = 0 := fun M => by ext v; simp
    rw [h0', h0]
    simp [Matrix.zero_apply, h0_smul]

set_option maxHeartbeats 1000000 in
private theorem mp_V_iter_comp_bound (n : ℕ) (μ : ℂ) (hμ : -(1 / 4) < μ.re) (ρo ρi : ℝ)
    (hρo : 0 ≤ ρo) (hρ : ρo < ρi) (G : ℝ × ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ)
    (hGm : ∀ i j, Measurable fun w : (ℝ × ℝ) × ℝ => G w.1 w.2 i j)
    (hGs : ∀ x' Y, ρo < Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2) → G x' Y = 0)
    (hint : Integrable (fun w : (ℝ × ℝ) × ℝ => IIIa.tensorNorm (G w.1 w.2)) volume)
    (xo : Space) (hxo : ρi ≤ Real.sqrt (xo 0 ^ 2 + xo 1 ^ 2)) (i : Fin 3) :
    ContDiffAt ℝ ∞ (fun x => IIIa.sepVmu0 μ G x i) xo ∧
      ‖iteratedFDeriv ℝ n (fun x => IIIa.sepVmu0 μ G x i) xo‖ ≤
        (18 * max (Classical.choose (IIIa.sepKernelBounds n)) 0 *
          ((ρi - ρo) / 2) ^ (-4 - (n : ℝ))) *
          ∫ p : ℝ × ((ℝ × ℝ) × ℝ), IIIa.tensorNorm (G p.2.1 p.2.2) ∂IIIa.mpRho2 := by
  let CK : ℕ → ℝ := fun m => Classical.choose (IIIa.sepKernelBounds m)
  have hCK : ∀ m (x : Space), x ≠ 0 → ∀ i' j' : Fin 3,
      ‖iteratedFDeriv ℝ (m + 1) (fun y => IIIa.heatLerayK0 i' j' y) x‖ ≤
        CK m * ‖x‖ ^ (-4 - (m : ℝ)) :=
    fun m x hx i' j' => (Classical.choose_spec (IIIa.sepKernelBounds m) x hx i' j').2.1
  set D1 := (ρi - ρo) / 2 with hD1
  have hD1pos : 0 < D1 := by rw [hD1]; linarith
  set U : Set Space := Metric.ball xo D1
  have hU : IsOpen U := Metric.isOpen_ball
  have hxoU : xo ∈ U := Metric.mem_ball_self hD1pos
  set F : ℝ × ((ℝ × ℝ) × ℝ) → Space → ℂ := fun p x => IIIa.mpVF μ G p x i
  have hgapU : ∀ p : ℝ × ((ℝ × ℝ) × ℝ), p.1 ∈ Ioo (0 : ℝ) 1 →
      Real.sqrt (p.2.1.1 ^ 2 + p.2.1.2 ^ 2) ≤ ρo →
      ∀ x ∈ U, D1 ≤ ‖x - p.1 • IIIa.mpV3 p.2‖ ∧ x - p.1 • IIIa.mpV3 p.2 ≠ 0 := by
    intro p hp hw x hx
    have hxn : ‖xo - x‖ < D1 := by rw [← dist_eq_norm, dist_comm]; exact hx
    have hg := IIIa.mp_gap ρo ρi xo x hxo p.1 hp p.2 hw
    have hnorm : D1 ≤ ‖x - p.1 • IIIa.mpV3 p.2‖ :=
      le_trans (by rw [hD1]; linarith) (IIIa.rho_le_norm _)
    refine ⟨hnorm, fun h0 => ?_⟩
    rw [h0, norm_zero] at hnorm; linarith
  have hsmooth : ∀ᵐ p ∂IIIa.mpRho2, ContDiffOn ℝ ∞ (F p) U := by
    filter_upwards [IIIa.mpRho2_ae_mem] with p hp
    by_cases hw : Real.sqrt (p.2.1.1 ^ 2 + p.2.1.2 ^ 2) ≤ ρo
    · intro x hx
      refine (ContDiffAt.mul contDiffAt_const (ContDiffAt.mul contDiffAt_const
        (ContDiffAt.sum fun j _ => ContDiffAt.sum fun k _ => ?_))).contDiffWithinAt
      refine ContDiffAt.mul ?_ contDiffAt_const
      have hne := (hgapU p hp hw x hx).2
      have hK := IIIa.mp_K0_contDiffAt _ hne i j
      exact contDiffAt_fderiv_shift ⊤ (coordinateVector k) (p.1 • IIIa.mpV3 p.2) x hK
    · have hw' : ρo < Real.sqrt (p.2.1.1 ^ 2 + p.2.1.2 ^ 2) := lt_of_not_ge hw
      have h0 : G p.2.1 p.2.2 = 0 := hGs _ _ hw'
      have hf : F p = 0 := funext fun x' => IIIa.mpVF_zero μ G p h0 x' i
      rw [hf]
      exact contDiffOn_const
  have hmeas : ∀ (m : ℕ), ∀ x ∈ U,
      AEStronglyMeasurable (fun p => iteratedFDeriv ℝ m (F p) x) IIIa.mpRho2 := by
    intro m x hx
    set S : Set (ℝ × ((ℝ × ℝ) × ℝ)) :=
      {p | p.1 ∈ Ioo (0 : ℝ) 1 ∧ Real.sqrt (p.2.1.1 ^ 2 + p.2.1.2 ^ 2) ≤ ρo}
    have hS : MeasurableSet S := by
      have hS1 : MeasurableSet {p : ℝ × ((ℝ × ℝ) × ℝ) | p.1 ∈ Ioo (0 : ℝ) 1} :=
        measurableSet_Ioo.preimage measurable_fst
      have hS2 : MeasurableSet {p : ℝ × ((ℝ × ℝ) × ℝ) |
          Real.sqrt (p.2.1.1 ^ 2 + p.2.1.2 ^ 2) ≤ ρo} :=
        (isClosed_le (by fun_prop) continuous_const).measurableSet
      exact hS1.inter hS2
    have hu_cont : Continuous fun p : ℝ × ((ℝ × ℝ) × ℝ) => x - p.1 • IIIa.mpV3 p.2 :=
      continuous_const.sub (continuous_fst.smul (IIIa.mpV3_continuous.comp continuous_snd))
    have hu_maps : MapsTo (fun p : ℝ × ((ℝ × ℝ) × ℝ) => x - p.1 • IIIa.mpV3 p.2) S {0}ᶜ :=
      fun p hp => (hgapU p hp.1 hp.2 x hx).2
    have hcp : Measurable fun p : ℝ × ((ℝ × ℝ) × ℝ) => -2 * (p.1 : ℂ) ^ (2 * μ + 2) :=
      measurable_const.mul ((Complex.measurable_ofReal.comp measurable_fst).pow_const _)
    have hR : AEStronglyMeasurable (fun p : ℝ × ((ℝ × ℝ) × ℝ) =>
        ∑ j : Fin 3, ∑ k : Fin 3,
          ((-2 * (p.1 : ℂ) ^ (2 * μ + 2)) * ((G p.2.1 p.2.2 j k : ℝ) : ℂ)) •
            S.indicator (fun q => derivShiftCLM m (coordinateVector k)
              (iteratedFDeriv ℝ (m + 1) (fun y => IIIa.heatLerayK0 i j y)
                (x - q.1 • IIIa.mpV3 q.2))) p) IIIa.mpRho2 := by
      refine Finset.aestronglyMeasurable_fun_sum _ fun j _ =>
        Finset.aestronglyMeasurable_fun_sum _ fun k _ => ?_
      have hc : Measurable fun p : ℝ × ((ℝ × ℝ) × ℝ) =>
          (-2 * (p.1 : ℂ) ^ (2 * μ + 2)) * ((G p.2.1 p.2.2 j k : ℝ) : ℂ) :=
        hcp.mul (Complex.measurable_ofReal.comp ((hGm j k).comp measurable_snd))
      have hK0_cd : ContDiffOn ℝ ∞ (fun y => IIIa.heatLerayK0 i j y) {0}ᶜ :=
        fun y hy => (IIIa.mp_K0_contDiffAt y hy i j).contDiffWithinAt
      have hK0_cont : ContinuousOn
          (iteratedFDeriv ℝ (m + 1) (fun y => IIIa.heatLerayK0 i j y)) {0}ᶜ :=
        ContinuousOn.continuousOn_iteratedFDeriv hK0_cd isOpen_compl_singleton
          (by exact_mod_cast le_top)
      have hg_cont : ContinuousOn (fun q : ℝ × ((ℝ × ℝ) × ℝ) =>
          derivShiftCLM m (coordinateVector k)
            (iteratedFDeriv ℝ (m + 1) (fun y => IIIa.heatLerayK0 i j y)
              (x - q.1 • IIIa.mpV3 q.2))) S :=
        (derivShiftCLM m (coordinateVector k)).continuous.comp_continuousOn
          (hK0_cont.comp hu_cont.continuousOn hu_maps)
      have hg_ind : AEStronglyMeasurable (S.indicator (fun q : ℝ × ((ℝ × ℝ) × ℝ) =>
          derivShiftCLM m (coordinateVector k)
            (iteratedFDeriv ℝ (m + 1) (fun y => IIIa.heatLerayK0 i j y)
              (x - q.1 • IIIa.mpV3 q.2)))) IIIa.mpRho2 :=
        (aestronglyMeasurable_indicator_iff hS).2 (hg_cont.aestronglyMeasurable hS)
      exact hc.aestronglyMeasurable.smul hg_ind
    refine hR.congr ?_
    have h0_smul : ∀ (M : Space [×m]→L[ℝ] ℂ), (0 : ℂ) • M = 0 := fun M => by ext v; simp
    filter_upwards [IIIa.mpRho2_ae_mem] with p hp
    rw [mpVF_iteratedFDeriv_eq m μ ρo G hGs p x (fun hw => (hgapU p hp hw x hx).2) i]
    by_cases hw : Real.sqrt (p.2.1.1 ^ 2 + p.2.1.2 ^ 2) ≤ ρo
    · have hpS : p ∈ S := ⟨hp, hw⟩
      simp [Set.indicator_of_mem hpS]
    · have hw' : ρo < Real.sqrt (p.2.1.1 ^ 2 + p.2.1.2 ^ 2) := lt_of_not_ge hw
      have h0 : G p.2.1 p.2.2 = 0 := hGs _ _ hw'
      simp [h0, Matrix.zero_apply, h0_smul]
  have hdom : ∀ (m : ℕ) (p : ℝ × ((ℝ × ℝ) × ℝ)), p.1 ∈ Ioo (0 : ℝ) 1 → ∀ x ∈ U,
      ‖iteratedFDeriv ℝ m (F p) x‖ ≤
        (18 * max (CK m) 0 * D1 ^ (-4 - (m : ℝ))) * IIIa.tensorNorm (G p.2.1 p.2.2) := by
    intro m p hp x hx
    rw [mpVF_iteratedFDeriv_eq m μ ρo G hGs p x (fun hw => (hgapU p hp hw x hx).2) i]
    have hCM0 : 0 ≤ max (CK m) 0 := le_max_right _ _
    have hD1p : 0 ≤ D1 ^ (-4 - (m : ℝ)) := Real.rpow_nonneg hD1pos.le _
    have htn : 0 ≤ IIIa.tensorNorm (G p.2.1 p.2.2) := tn_nonneg _
    by_cases hw : Real.sqrt (p.2.1.1 ^ 2 + p.2.1.2 ^ 2) ≤ ρo
    · obtain ⟨hnorm, hne⟩ := hgapU p hp hw x hx
      have hw1 := IIIa.mp_norm_cpow_le μ hμ p.1 hp
      have hterm : ∀ j k : Fin 3,
          ‖((-2 * (p.1 : ℂ) ^ (2 * μ + 2)) * ((G p.2.1 p.2.2 j k : ℝ) : ℂ)) •
            derivShiftCLM m (coordinateVector k)
              (iteratedFDeriv ℝ (m + 1) (fun y => IIIa.heatLerayK0 i j y)
                (x - p.1 • IIIa.mpV3 p.2))‖ ≤
            2 * (max (CK m) 0 * D1 ^ (-4 - (m : ℝ))) * IIIa.tensorNorm (G p.2.1 p.2.2) := by
        intro j k
        rw [norm_smul, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
        have hn2 : ‖(-2 : ℂ)‖ = 2 := by simp
        rw [hn2]
        have hc : 2 * ‖(p.1 : ℂ) ^ (2 * μ + 2)‖ * |G p.2.1 p.2.2 j k| ≤
            2 * 1 * IIIa.tensorNorm (G p.2.1 p.2.2) := by
          gcongr
          exact IIIa.mp_entry_le _ j k
        have hd1 := norm_derivShiftCLM_le m k
          (iteratedFDeriv ℝ (m + 1) (fun y => IIIa.heatLerayK0 i j y) (x - p.1 • IIIa.mpV3 p.2))
        have hd2 : ‖iteratedFDeriv ℝ (m + 1) (fun y => IIIa.heatLerayK0 i j y)
            (x - p.1 • IIIa.mpV3 p.2)‖ ≤ max (CK m) 0 * D1 ^ (-4 - (m : ℝ)) := by
          refine (hCK m _ hne i j).trans ?_
          have hpow : ‖x - p.1 • IIIa.mpV3 p.2‖ ^ (-4 - (m : ℝ)) ≤ D1 ^ (-4 - (m : ℝ)) :=
            Real.rpow_le_rpow_of_nonpos hD1pos hnorm (by have := m.cast_nonneg (α := ℝ); linarith)
          calc CK m * ‖x - p.1 • IIIa.mpV3 p.2‖ ^ (-4 - (m : ℝ))
              ≤ max (CK m) 0 * ‖x - p.1 • IIIa.mpV3 p.2‖ ^ (-4 - (m : ℝ)) :=
                mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (norm_nonneg _) _)
            _ ≤ max (CK m) 0 * D1 ^ (-4 - (m : ℝ)) :=
                mul_le_mul_of_nonneg_left hpow hCM0
        calc (2 * ‖(p.1 : ℂ) ^ (2 * μ + 2)‖ * |G p.2.1 p.2.2 j k|) *
              ‖derivShiftCLM m (coordinateVector k) _‖
            ≤ (2 * 1 * IIIa.tensorNorm (G p.2.1 p.2.2)) * (max (CK m) 0 * D1 ^ (-4 - (m : ℝ))) :=
              mul_le_mul hc (hd1.trans hd2) (norm_nonneg _) (by positivity)
          _ = 2 * (max (CK m) 0 * D1 ^ (-4 - (m : ℝ))) * IIIa.tensorNorm (G p.2.1 p.2.2) := by ring
      refine (norm_sum_le _ _).trans ?_
      have hj : ∀ j : Fin 3,
          ‖∑ k : Fin 3, ((-2 * (p.1 : ℂ) ^ (2 * μ + 2)) * ((G p.2.1 p.2.2 j k : ℝ) : ℂ)) •
            derivShiftCLM m (coordinateVector k)
              (iteratedFDeriv ℝ (m + 1) (fun y => IIIa.heatLerayK0 i j y)
                (x - p.1 • IIIa.mpV3 p.2))‖ ≤
          3 * (2 * (max (CK m) 0 * D1 ^ (-4 - (m : ℝ))) * IIIa.tensorNorm (G p.2.1 p.2.2)) := by
        intro j
        refine (norm_sum_le _ _).trans ?_
        calc ∑ k : Fin 3, _ ≤ ∑ _k : Fin 3, _ := Finset.sum_le_sum fun k _ => hterm j k
          _ = _ := by simp [Finset.sum_const]
      calc ∑ j : Fin 3, _ ≤ ∑ _j : Fin 3, _ := Finset.sum_le_sum fun j _ => hj j
        _ = _ := by simp [Finset.sum_const]; ring
    · have hw' : ρo < Real.sqrt (p.2.1.1 ^ 2 + p.2.1.2 ^ 2) := lt_of_not_ge hw
      have h0 : G p.2.1 p.2.2 = 0 := hGs _ _ hw'
      have h0_smul : ∀ (M : Space [×m]→L[ℝ] ℂ), (0 : ℂ) • M = 0 := fun M => by ext v; simp
      simp [h0, Matrix.zero_apply, h0_smul, IIIa.tensorNorm]
  have hTn := IIIa.mp_tn_integrable G hint
  have hLoc : UnforcedLeray.L09.LocDominated IIIa.mpRho2 F U := by
    intro m x hx
    refine ⟨U, hU.mem_nhds hx,
      fun p => (18 * max (CK m) 0 * D1 ^ (-4 - (m : ℝ))) * IIIa.tensorNorm (G p.2.1 p.2.2),
      hTn.const_mul _, ?_⟩
    filter_upwards [IIIa.mpRho2_ae_mem] with p hp y' hy'
    exact hdom m p hp y' hy'
  obtain ⟨_, hi0, _⟩ := IIIa.mp_V_diff IIIa.sepKernelBounds μ hμ ρo ρi hρo hρ G hGm hGs hint xo hxo i
  have hEq : (fun x => IIIa.sepVmu0 μ G x i) =ᶠ[𝓝 xo] fun x => ∫ p, F p x ∂IIIa.mpRho2 := by
    filter_upwards [hU.mem_nhds hxoU] with x hx
    exact IIIa.mp_V_link μ G x i (hi0 x hx)
  have hcd : ContDiffAt ℝ ∞ (fun x => IIIa.sepVmu0 μ G x i) xo :=
    ((UnforcedLeray.L09.contDiffOn_integral hU hsmooth hmeas hLoc).contDiffAt
      (hU.mem_nhds hxoU)).congr_of_eventuallyEq hEq
  have hItEq : iteratedFDeriv ℝ n (fun x => IIIa.sepVmu0 μ G x i) xo =
      ∫ p, iteratedFDeriv ℝ n (F p) xo ∂IIIa.mpRho2 := by
    rw [(hEq.iteratedFDeriv ℝ n).eq_of_nhds]
    exact UnforcedLeray.L09.iteratedFDeriv_integral_eq hU hsmooth hmeas hLoc n hxoU
  refine ⟨hcd, ?_⟩
  rw [hItEq, ← integral_const_mul]
  refine norm_integral_le_of_norm_le (hTn.const_mul _) ?_
  filter_upwards [IIIa.mpRho2_ae_mem] with p hp using hdom n p hp xo hxoU

private theorem sepVmu0_contDiffAt_and_bound (n : ℕ) (μ : ℂ) (hμ : -(1 / 4) < μ.re) (ρo ρi : ℝ)
    (hρo : 0 ≤ ρo) (hρ : ρo < ρi) (G : ℝ × ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ)
    (hGm : ∀ i j, Measurable fun w : (ℝ × ℝ) × ℝ => G w.1 w.2 i j)
    (hGs : ∀ x' Y, ρo < Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2) → G x' Y = 0)
    (hint : Integrable (fun w : (ℝ × ℝ) × ℝ => IIIa.tensorNorm (G w.1 w.2)) volume)
    (xo : Space) (hxo : ρi ≤ Real.sqrt (xo 0 ^ 2 + xo 1 ^ 2)) :
    ContDiffAt ℝ ∞ (IIIa.sepVmu0 μ G) xo ∧
      ‖iteratedFDeriv ℝ n (IIIa.sepVmu0 μ G) xo‖ ≤
        (54 * max (Classical.choose (IIIa.sepKernelBounds n)) 0 *
          ((ρi - ρo) / 2) ^ (-4 - (n : ℝ))) *
          ∫ p : ℝ × ((ℝ × ℝ) × ℝ), IIIa.tensorNorm (G p.2.1 p.2.2) ∂IIIa.mpRho2 := by
  have hcomp := fun i => mp_V_iter_comp_bound n μ hμ ρo ρi hρo hρ G hGm hGs hint xo hxo i
  have hcd : ContDiffAt ℝ ∞ (IIIa.sepVmu0 μ G) xo :=
    contDiffAt_pi.2 fun i => (hcomp i).1
  refine ⟨hcd, ?_⟩
  have hsmAt : ∀ i : Fin 3, ContDiffAt ℝ n (fun x => IIIa.sepVmu0 μ G x i) xo :=
    fun i => (hcomp i).1.of_le (by exact_mod_cast le_top)
  rw [IIIa.sepDiff_iteratedFDeriv_pi hsmAt]
  refine (norm_sum_le _ _).trans ?_
  have hb : ∀ i : Fin 3,
      ‖(ContinuousLinearMap.single ℝ (fun _ : Fin 3 => ℂ) i).compContinuousMultilinearMap
        (iteratedFDeriv ℝ n (fun x => IIIa.sepVmu0 μ G x i) xo)‖ ≤
      (18 * max (Classical.choose (IIIa.sepKernelBounds n)) 0 *
        ((ρi - ρo) / 2) ^ (-4 - (n : ℝ))) *
        ∫ p : ℝ × ((ℝ × ℝ) × ℝ), IIIa.tensorNorm (G p.2.1 p.2.2) ∂IIIa.mpRho2 := by
    intro i
    refine (ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _).trans ?_
    have h1i := ContinuousLinearMap.norm_single_le_one ℝ (E := fun _ : Fin 3 => ℂ) i
    calc ‖ContinuousLinearMap.single ℝ (fun _ : Fin 3 => ℂ) i‖ *
          ‖iteratedFDeriv ℝ n (fun x => IIIa.sepVmu0 μ G x i) xo‖
        ≤ 1 * ‖iteratedFDeriv ℝ n (fun x => IIIa.sepVmu0 μ G x i) xo‖ := by gcongr
      _ ≤ _ := by rw [one_mul]; exact (hcomp i).2
  calc ∑ i : Fin 3,
        ‖(ContinuousLinearMap.single ℝ (fun _ : Fin 3 => ℂ) i).compContinuousMultilinearMap
          (iteratedFDeriv ℝ n (fun x => IIIa.sepVmu0 μ G x i) xo)‖
      ≤ ∑ _i : Fin 3, (18 * max (Classical.choose (IIIa.sepKernelBounds n)) 0 *
          ((ρi - ρo) / 2) ^ (-4 - (n : ℝ))) *
          ∫ p : ℝ × ((ℝ × ℝ) × ℝ), IIIa.tensorNorm (G p.2.1 p.2.2) ∂IIIa.mpRho2 :=
        Finset.sum_le_sum fun i _ => hb i
    _ = _ := by simp [Finset.sum_const]; ring

/-! ## 3. Smoothness and far-field `O(ϱ^{-4})` decay of `newtonX0` -/

private theorem iteratedFDeriv_comp_smul_space (n : ℕ) {ε : ℝ} (hε : 0 < ε)
    (f : Space → Fin 3 → ℂ) (y' : Space) :
    iteratedFDeriv ℝ n (fun y : Space => f (ε • y)) y' =
      (ε ^ n : ℝ) • iteratedFDeriv ℝ n f (ε • y') := by
  let g : Space ≃L[ℝ] Space := ContinuousLinearEquiv.smulLeft (Units.mk0 ε hε.ne')
  have h1 := g.iteratedFDerivWithin_comp_right f uniqueDiffOn_univ (mem_univ (g y')) n
  simp only [preimage_univ, iteratedFDerivWithin_univ] at h1
  have hg : g y' = ε • y' := rfl
  change iteratedFDeriv ℝ n (f ∘ ⇑g) y' = _
  rw [h1, hg]
  ext m i
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
    smul_apply, Pi.smul_apply]
  have hm : (fun idx : Fin n => (g : Space →L[ℝ] Space) (m idx)) = fun idx => ε • m idx := rfl
  rw [hm, ContinuousMultilinearMap.map_smul_univ]
  simp [Finset.prod_const]

private theorem sepVmu0_contDiffOn (μ : ℂ) (hμ : -(1 / 4) < μ.re) (ρo : ℝ) (hρo : 0 ≤ ρo)
    (G : ℝ × ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ)
    (hGm : ∀ i j, Measurable fun w : (ℝ × ℝ) × ℝ => G w.1 w.2 i j)
    (hGs : ∀ x' Y, ρo < Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2) → G x' Y = 0)
    (hint : Integrable (fun w : (ℝ × ℝ) × ℝ => IIIa.tensorNorm (G w.1 w.2)) volume) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (IIIa.sepVmu0 μ G) {x : Space | ρo < ϱ x} := by
  intro xo hxo
  have hρ : ρo < ϱ xo := hxo
  exact (sepVmu0_contDiffAt_and_bound 0 μ hμ ρo (ϱ xo) hρo hρ G hGm hGs hint xo le_rfl).1.contDiffWithinAt

/-- `newtonX0 ε μ G τ` is `C^∞` on `{y' : Space | ρo / ε < ϱ y'}`. -/
theorem newtonX0_contDiffOn {ε μ ρo : ℝ} (hε : 0 < ε) (hμ : -(1 / 4) < μ) (hρo : 0 ≤ ρo)
    (G : ℝ × ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ)
    (hGm : ∀ i j, Measurable fun w : (ℝ × ℝ) × ℝ => G w.1 w.2 i j)
    (hGs : ∀ x' Y, ρo < Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2) → G x' Y = 0)
    (hint : Integrable (fun w : (ℝ × ℝ) × ℝ => IIIa.tensorNorm (G w.1 w.2)) volume)
    (τ : ℝ) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (newtonX0 ε μ G τ) {y' : Space | ρo / ε < ϱ y'} := by
  have hm0 : -(1 / 4) < ((μ : ℂ)).re := by simpa using hμ
  have hm1 : -(1 / 4) < ((μ : ℂ) + 1).re := by simp; linarith
  have hV0 := sepVmu0_contDiffOn (μ : ℂ) hm0 ρo hρo G hGm hGs hint
  have hV1 := sepVmu0_contDiffOn ((μ : ℂ) + 1) hm1 ρo hρo G hGm hGs hint
  have hmaps : MapsTo (fun y' : Space => ε • y') {y' : Space | ρo / ε < ϱ y'}
      {x : Space | ρo < ϱ x} := by
    intro y' hy'
    have hy'' : ρo / ε < ϱ y' := hy'
    show ρo < ϱ (ε • y')
    rw [ϱ_smul, abs_of_pos hε]
    exact (div_lt_iff₀' hε).1 hy''
  have hsmul : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y' : Space => ε • y')
      {y' : Space | ρo / ε < ϱ y'} :=
    (contDiff_const_smul ε).contDiffOn
  have hsub : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y' : Space => (ε ^ 2 : ℝ) • (IIIa.sepVmu0 (μ : ℂ) G (ε • y') -
        IIIa.sepVmu0 ((μ : ℂ) + 1) G (ε • y'))) {y' : Space | ρo / ε < ϱ y'} :=
    ((hV0.comp hsmul hmaps).sub (hV1.comp hsmul hmaps)).const_smul (ε ^ 2 : ℝ)
  exact (PhasePrim.reMap.contDiff.comp_contDiffOn hsub).congr fun y' _ => by
    simp [newtonX0, map_smul]

/-- All spatial derivatives of `newtonX0 ε μ G τ` decay as `O(ϱ^{-4})` for
`2 * (ρo / ε) + 2 ≤ ϱ y'`. -/
theorem newtonX0_decay {ε μ ρo : ℝ} (hε : 0 < ε) (hμ : -(1 / 4) < μ) (hρo : 0 ≤ ρo)
    (G : ℝ × ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ)
    (hGm : ∀ i j, Measurable fun w : (ℝ × ℝ) × ℝ => G w.1 w.2 i j)
    (hGs : ∀ x' Y, ρo < Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2) → G x' Y = 0)
    (hint : Integrable (fun w : (ℝ × ℝ) × ℝ => IIIa.tensorNorm (G w.1 w.2)) volume)
    (τ : ℝ) (n : ℕ) :
    ∃ C : ℝ, ∀ y' : Space, 2 * (ρo / ε) + 2 ≤ ϱ y' →
      ‖iteratedFDeriv ℝ n (newtonX0 ε μ G τ) y'‖ ≤ C * (ϱ y' ^ 4)⁻¹ := by
  have hm0 : -(1 / 4) < ((μ : ℂ)).re := by simpa using hμ
  have hm1 : -(1 / 4) < ((μ : ℂ) + 1).re := by simp; linarith
  set K := max (Classical.choose (IIIa.sepKernelBounds n)) 0
  have hK0 : 0 ≤ K := le_max_right _ _
  set I := ∫ p : ℝ × ((ℝ × ℝ) × ℝ), IIIa.tensorNorm (G p.2.1 p.2.2) ∂IIIa.mpRho2
  have hI0 : 0 ≤ I := integral_nonneg fun _ => tn_nonneg _
  set C_base := 54 * K * (ε / 4) ^ (-4 - (n : ℝ)) * I
  have hC_base0 : 0 ≤ C_base := by positivity
  refine ⟨‖PhasePrim.reMap‖ * ε ^ (2 + n) * (2 * C_base), fun y' hy' => ?_⟩
  have hrO : 0 ≤ ρo / ε := div_nonneg hρo hε.le
  have hy'1 : 1 ≤ ϱ y' := by linarith
  have hy'_pos : 0 < ϱ y' := by linarith
  set xo := ε • y'
  have hϱ_xo : ϱ xo = ε * ϱ y' := by rw [ϱ_smul, abs_of_pos hε]
  have hρo_le : ρo ≤ ε * (ϱ y' / 2) := by
    have : ρo / ε ≤ ϱ y' / 2 := by linarith
    exact (div_le_iff₀' hε).1 this
  have hρ_lt : ρo < ϱ xo := by
    rw [hϱ_xo]
    linarith [mul_pos hε hy'_pos]
  obtain ⟨hV0_cd, hV0_bnd⟩ := sepVmu0_contDiffAt_and_bound n (μ : ℂ) hm0 ρo (ϱ xo) hρo hρ_lt
    G hGm hGs hint xo le_rfl
  obtain ⟨hV1_cd, hV1_bnd⟩ := sepVmu0_contDiffAt_and_bound n ((μ : ℂ) + 1) hm1 ρo (ϱ xo) hρo hρ_lt
    G hGm hGs hint xo le_rfl
  have hD1_ge : (ε / 4) * ϱ y' ≤ (ϱ xo - ρo) / 2 := by
    rw [hϱ_xo]
    linarith
  have hpow : ((ϱ xo - ρo) / 2) ^ (-4 - (n : ℝ)) ≤
      (ε / 4) ^ (-4 - (n : ℝ)) * (ϱ y' ^ 4)⁻¹ := by
    have h1 : ((ϱ xo - ρo) / 2) ^ (-4 - (n : ℝ)) ≤ ((ε / 4) * ϱ y') ^ (-4 - (n : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hD1_ge
        (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
    rw [Real.mul_rpow (by positivity) hy'_pos.le] at h1
    have h2 : (ϱ y') ^ (-4 - (n : ℝ)) ≤ (ϱ y') ^ (-4 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hy'1 (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
    have h3 : (ϱ y') ^ (-4 : ℝ) = (ϱ y' ^ 4)⁻¹ := by
      rw [Real.rpow_neg hy'_pos.le, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    calc ((ϱ xo - ρo) / 2) ^ (-4 - (n : ℝ))
        ≤ (ε / 4) ^ (-4 - (n : ℝ)) * (ϱ y') ^ (-4 - (n : ℝ)) := h1
      _ ≤ (ε / 4) ^ (-4 - (n : ℝ)) * (ϱ y') ^ (-4 : ℝ) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = (ε / 4) ^ (-4 - (n : ℝ)) * (ϱ y' ^ 4)⁻¹ := by rw [h3]
  have hb0 : ‖iteratedFDeriv ℝ n (IIIa.sepVmu0 (μ : ℂ) G) xo‖ ≤ C_base * (ϱ y' ^ 4)⁻¹ := by
    refine hV0_bnd.trans ?_
    calc (54 * K * ((ϱ xo - ρo) / 2) ^ (-4 - (n : ℝ))) * I
        ≤ (54 * K * ((ε / 4) ^ (-4 - (n : ℝ)) * (ϱ y' ^ 4)⁻¹)) * I :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hpow (by positivity)) hI0
      _ = C_base * (ϱ y' ^ 4)⁻¹ := by unfold C_base; ring
  have hb1 : ‖iteratedFDeriv ℝ n (IIIa.sepVmu0 ((μ : ℂ) + 1) G) xo‖ ≤ C_base * (ϱ y' ^ 4)⁻¹ := by
    refine hV1_bnd.trans ?_
    calc (54 * K * ((ϱ xo - ρo) / 2) ^ (-4 - (n : ℝ))) * I
        ≤ (54 * K * ((ε / 4) ^ (-4 - (n : ℝ)) * (ϱ y' ^ 4)⁻¹)) * I :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hpow (by positivity)) hI0
      _ = C_base * (ϱ y' ^ 4)⁻¹ := by unfold C_base; ring
  have hsmul : ContDiffAt ℝ n (fun y : Space => ε • y) y' :=
    (contDiff_const_smul ε).contDiffAt
  have hV0_cd' : ContDiffAt ℝ n (IIIa.sepVmu0 (μ : ℂ) G) (ε • y') :=
    hV0_cd.of_le (by exact_mod_cast le_top)
  have hV1_cd' : ContDiffAt ℝ n (IIIa.sepVmu0 ((μ : ℂ) + 1) G) (ε • y') :=
    hV1_cd.of_le (by exact_mod_cast le_top)
  have h0n : ContDiffAt ℝ n (fun y : Space => IIIa.sepVmu0 (μ : ℂ) G (ε • y)) y' :=
    hV0_cd'.comp y' hsmul
  have h1n : ContDiffAt ℝ n (fun y : Space => IIIa.sepVmu0 ((μ : ℂ) + 1) G (ε • y)) y' :=
    hV1_cd'.comp y' hsmul
  have hfn : newtonX0 ε μ G τ = ⇑PhasePrim.reMap ∘
      fun y => (ε ^ 2 : ℝ) • (IIIa.sepVmu0 (μ : ℂ) G (ε • y) -
        IIIa.sepVmu0 ((μ : ℂ) + 1) G (ε • y)) := by
    funext y
    simp [newtonX0, map_smul]
  have hid : iteratedFDeriv ℝ n (newtonX0 ε μ G τ) y' =
      PhasePrim.reMap.compContinuousMultilinearMap
        ((ε ^ (2 + n) : ℝ) • (iteratedFDeriv ℝ n (IIIa.sepVmu0 (μ : ℂ) G) xo -
          iteratedFDeriv ℝ n (IIIa.sepVmu0 ((μ : ℂ) + 1) G) xo)) := by
    rw [hfn, PhasePrim.reMap.iteratedFDeriv_comp_left ((h0n.sub h1n).const_smul (ε ^ 2 : ℝ)) le_rfl,
      iteratedFDeriv_const_smul_apply' (h0n.sub h1n)]
    change PhasePrim.reMap.compContinuousMultilinearMap
        ((ε ^ 2 : ℝ) • iteratedFDeriv ℝ n ((fun y => IIIa.sepVmu0 (μ : ℂ) G (ε • y)) -
          (fun y => IIIa.sepVmu0 ((μ : ℂ) + 1) G (ε • y))) y') = _
    rw [iteratedFDeriv_sub_apply h0n h1n,
      iteratedFDeriv_comp_smul_space n hε _ y', iteratedFDeriv_comp_smul_space n hε _ y',
      ← smul_sub, smul_smul, ← pow_add]
  rw [hid]
  refine (ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _).trans ?_
  rw [norm_smul, Real.norm_of_nonneg (by positivity)]
  have hsub := (norm_sub_le _ _).trans (add_le_add hb0 hb1)
  calc ‖PhasePrim.reMap‖ * (ε ^ (2 + n) *
        ‖iteratedFDeriv ℝ n (IIIa.sepVmu0 (μ : ℂ) G) xo -
          iteratedFDeriv ℝ n (IIIa.sepVmu0 ((μ : ℂ) + 1) G) xo‖)
      ≤ ‖PhasePrim.reMap‖ * (ε ^ (2 + n) * (C_base * (ϱ y' ^ 4)⁻¹ + C_base * (ϱ y' ^ 4)⁻¹)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hsub (by positivity)) (norm_nonneg _)
    _ = ‖PhasePrim.reMap‖ * ε ^ (2 + n) * (2 * C_base) * (ϱ y' ^ 4)⁻¹ := by ring

end YBWidth

end UnforcedLeray.Short.PartIIIb.Concrete

end
