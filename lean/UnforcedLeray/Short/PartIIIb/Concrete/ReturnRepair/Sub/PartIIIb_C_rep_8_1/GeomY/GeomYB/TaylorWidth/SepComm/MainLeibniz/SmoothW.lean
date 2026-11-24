import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomY.GeomYB.TaylorWidth.SepComm.MainLeibniz.Split

/-!
# Spatial smoothness and far-field `O(ϱ^{-4})` decay of `srcX0` for `meanLift G`

Helper for `PartIII-b:C/rep/8/1/1/2/5/2/1/1` (`YBWidth.sepCommMainLeibniz`).
Source `the November 2 reference manuscript`
lines 3604-3623, 3735-3766, 5415-5432.

For `T = IIIa.thinSource ε (IIIa.meanLift G)` where `G` is supported in `√(x'₁² + x'₂²) ≤ ρo`:
1. `srcX0_meanLift_timeIndep`: `srcX0 ν μ T t = srcX0 ν μ T τ` for all `t, τ`;
2. `srcX0_meanLift_contDiffOn`: `srcX0 ν μ T τ` is `C^∞` on `{y' : Space | ρo / ε < ϱ y'}`;
3. `srcX0_meanLift_decay`: for each `n : ℕ`, `‖iteratedFDeriv ℝ n (srcX0 ν μ T τ) y'‖ ≤ C_n * (ϱ y' ^ 4)⁻¹`
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

/-- `srcX0 ν μ (IIIa.thinSource ε (IIIa.meanLift G))` is independent of the phase variable `t`. -/
theorem srcX0_meanLift_timeIndep (ν ε μ : ℝ) (G : ℝ × ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ)
    (t τ : ℝ) :
    srcX0 ν μ (IIIa.thinSource ε (IIIa.meanLift G)) t =
      srcX0 ν μ (IIIa.thinSource ε (IIIa.meanLift G)) τ := by
  funext y
  have hW : ∀ m : ℂ,
      IIIa.sepW ν m (IIIa.thinSource ε (IIIa.meanLift G)) y t =
        IIIa.sepW ν m (IIIa.thinSource ε (IIIa.meanLift G)) y τ := by
    intro m
    rfl
  unfold srcX0
  rw [hW (μ : ℂ), hW ((μ : ℂ) + 1)]

/-- Pointwise bound on `sepDom (2 * m.re + 2) j D` for `IIIa.thinSource ε (IIIa.meanLift G)`. -/
private theorem sepDom_thin_meanLift_le {ε D : ℝ} {m : ℂ} (hε : 0 < ε) (hD : 0 < D)
    (hm : -(1 / 4) < m.re) (G : ℝ × ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ)
    (hGm : ∀ i j, Measurable fun w : (ℝ × ℝ) × ℝ => G w.1 w.2 i j)
    (j : ℕ) (τ : ℝ) (y : Space) :
    IIIa.sepDom (2 * m.re + 2) j D
        (IIIa.srcNorm (IIIa.thinSource ε (IIIa.meanLift G))) τ y ≤
      ENNReal.ofReal (D ^ (-4 - (j : ℝ))) *
        (ENNReal.ofReal (ε⁻¹) ^ 2 *
          ∫⁻ w : (ℝ × ℝ) × ℝ, ENNReal.ofReal (IIIa.tensorNorm (G w.1 w.2))) := by
  set κ : ℝ≥0∞ := ENNReal.ofReal (D ^ (-4 - (j : ℝ)))
  have hkd : ∀ x : Space, IIIa.sepKd j D x ≤ κ := by
    intro x
    unfold IIIa.sepKd
    split_ifs with hx
    · refine ENNReal.ofReal_le_ofReal ?_
      exact Real.rpow_le_rpow_of_nonpos hD hx (by linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)])
    · exact zero_le
  have ha : 0 ≤ 2 * m.re + 2 := by linarith
  calc IIIa.sepDom (2 * m.re + 2) j D
        (IIIa.srcNorm (IIIa.thinSource ε (IIIa.meanLift G))) τ y
      ≤ ∫⁻ l in Ioo (0 : ℝ) 1, κ *
          ∫⁻ z : Space,
            IIIa.srcNorm (IIIa.thinSource ε (IIIa.meanLift G)) (τ + 2 * Real.log l) z := by
        unfold IIIa.sepDom
        refine setLIntegral_mono' measurableSet_Ioo fun l hl => ?_
        have h1 : ENNReal.ofReal (l ^ (2 * m.re + 2)) ≤ 1 := by
          rw [← ENNReal.ofReal_one]
          exact ENNReal.ofReal_le_ofReal (Real.rpow_le_one hl.1.le hl.2.le ha)
        calc ENNReal.ofReal (l ^ (2 * m.re + 2)) *
              ∫⁻ z : Space, IIIa.sepKd j D (y - l • z) *
                IIIa.srcNorm (IIIa.thinSource ε (IIIa.meanLift G)) (τ + 2 * Real.log l) z
            ≤ 1 * ∫⁻ z : Space, κ *
                IIIa.srcNorm (IIIa.thinSource ε (IIIa.meanLift G)) (τ + 2 * Real.log l) z := by
              gcongr with z
              exact hkd _
          _ = κ * ∫⁻ z : Space,
                IIIa.srcNorm (IIIa.thinSource ε (IIIa.meanLift G)) (τ + 2 * Real.log l) z := by
              rw [one_mul, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ = κ * (ENNReal.ofReal (ε⁻¹) ^ 2 *
          ∫⁻ w : (ℝ × ℝ) × ℝ, ENNReal.ofReal (IIIa.tensorNorm (G w.1 w.2))) := by
        simp_rw [IIIa.mp_src_lintegral ε hε G hGm]
        rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioo, sub_zero,
          ENNReal.ofReal_one, mul_one]

set_option maxHeartbeats 1000000 in
private theorem sepW_contDiffAt_of_sepDom (ν : ℝ) (hν : 0 < ν) (μ : ℂ)
    (rOut rIn P : ℝ) (hrO : 0 ≤ rOut) (hrr : rOut < rIn)
    (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (hT : IIIa.IsSepSource P rOut T)
    (τ : ℝ) (y : Space) (hy : rIn ≤ Real.sqrt (y 0 ^ 2 + y 1 ^ 2))
    (hfin : IIIa.sepDom (2 * μ.re + 2) 0 (rIn - rOut) (IIIa.srcNorm T) τ y < ⊤) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y' => IIIa.sepW ν μ T y' τ) y := by
  have h1 := IIIa.heatLerayKSmoothAll
  have h3 := IIIa.sepDiffFMeas
  have h4 := IIIa.sepDiffFDerivBound
  have h5 := IIIa.sepDiffWEqIntegral
  have h6 := IIIa.sepDiffMajIntegrable
  choose C hC0 hC using h4 IIIa.sepKernelBounds
  have hD : 0 < rIn - rOut := by linarith
  set D := rIn - rOut
  set U : Set Space := Metric.ball y (D / 2)
  have hU : IsOpen U := Metric.isOpen_ball
  have hyU : y ∈ U := Metric.mem_ball_self (by linarith)
  set F := IIIa.sepDiffF ν μ T τ
  have hsm : ∀ p : ℝ × Space, p.1 ∈ Ioo (0 : ℝ) 1 → ∀ i, ContDiff ℝ ∞ (fun y' => F p y' i) :=
    fun p hp i => IIIa.sepDiffF_contDiff h1 ν μ T τ hν p hp i
  have hsmAt : ∀ (m : ℕ) (p : ℝ × Space), p.1 ∈ Ioo (0 : ℝ) 1 → ∀ (y' : Space) (i : Fin 3),
      ContDiffAt ℝ m (fun y' => F p y' i) y' := fun m p hp y' i =>
    ((hsm p hp i).of_le (by exact_mod_cast le_top)).contDiffAt
  have hoff : ∀ p : ℝ × Space, rOut < Real.sqrt (p.2 0 ^ 2 + p.2 1 ^ 2) → F p = 0 :=
    fun p hp => IIIa.sepDiffF_eq_zero ν μ T τ p (hT.support _ _ hp)
  have hpi : ∀ (m : ℕ) (p : ℝ × Space), p.1 ∈ Ioo (0 : ℝ) 1 → ∀ y' : Space,
      y' - p.1 • p.2 ≠ 0 → ‖iteratedFDeriv ℝ m (F p) y'‖ ≤ 3 * C m *
        (p.1 ^ (2 * μ.re + 2) * ‖y' - p.1 • p.2‖ ^ (-4 - (m : ℝ)) *
          IIIa.tensorNorm (T (τ + 2 * Real.log p.1) p.2)) := by
    intro m p hp y' hne
    rw [IIIa.sepDiff_iteratedFDeriv_pi (fun i => hsmAt m p hp y' i)]
    refine (norm_sum_le _ _).trans ?_
    have hb : ∀ i : Fin 3,
        ‖(ContinuousLinearMap.single ℝ (fun _ : Fin 3 => ℂ) i).compContinuousMultilinearMap
          (iteratedFDeriv ℝ m (fun y'' => F p y'' i) y')‖ ≤ C m *
          (p.1 ^ (2 * μ.re + 2) * ‖y' - p.1 • p.2‖ ^ (-4 - (m : ℝ)) *
            IIIa.tensorNorm (T (τ + 2 * Real.log p.1) p.2)) := by
      intro i
      refine (ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _).trans ?_
      have h1i := ContinuousLinearMap.norm_single_le_one ℝ (E := fun _ : Fin 3 => ℂ) i
      have h2i := hC m ν μ T τ hν p.1 p.2 y' hp hne i
      calc ‖ContinuousLinearMap.single ℝ (fun _ : Fin 3 => ℂ) i‖ *
            ‖iteratedFDeriv ℝ m (fun y'' => F p y'' i) y'‖
          ≤ 1 * ‖iteratedFDeriv ℝ m (fun y'' => F p y'' i) y'‖ := by gcongr
        _ ≤ _ := by rw [one_mul]; exact h2i
    calc ∑ i : Fin 3,
          ‖(ContinuousLinearMap.single ℝ (fun _ : Fin 3 => ℂ) i).compContinuousMultilinearMap
            (iteratedFDeriv ℝ m (fun y'' => F p y'' i) y')‖
        ≤ ∑ _i : Fin 3, C m * (p.1 ^ (2 * μ.re + 2) * ‖y' - p.1 • p.2‖ ^ (-4 - (m : ℝ)) *
            IIIa.tensorNorm (T (τ + 2 * Real.log p.1) p.2)) := Finset.sum_le_sum fun i _ => hb i
      _ = _ := by simp [Finset.sum_const]; ring
  have hgapU : ∀ p : ℝ × Space, p.1 ∈ Ioo (0 : ℝ) 1 → Real.sqrt (p.2 0 ^ 2 + p.2 1 ^ 2) ≤ rOut →
      ∀ y' ∈ U, D ≤ ‖y - p.1 • p.2‖ ∧ ‖y - p.1 • p.2‖ ≤ 2 * ‖y' - p.1 • p.2‖ := by
    intro p hp hz y' hy'
    have hg := IIIa.radial_gap y p.2 p.1 rOut rIn hp hz hy
    have hd : ‖y - y'‖ < D / 2 := by
      rw [← dist_eq_norm, dist_comm]; exact hy'
    have ht := norm_sub_le_norm_sub_add_norm_sub y y' (p.1 • p.2)
    exact ⟨hg, by linarith⟩
  have hdom : ∀ (m : ℕ) (p : ℝ × Space), p.1 ∈ Ioo (0 : ℝ) 1 → ∀ y' ∈ U,
      ‖iteratedFDeriv ℝ m (F p) y'‖ ≤
        (3 * C m * 2 ^ (4 + (m : ℝ)) * D ^ (-(m : ℝ))) * IIIa.sepDiffMaj μ T τ y p := by
    intro m p hp y' hy'
    have hl0 : 0 ≤ p.1 ^ (2 * μ.re + 2) := Real.rpow_nonneg hp.1.le _
    have htn : 0 ≤ IIIa.tensorNorm (T (τ + 2 * Real.log p.1) p.2) := Real.sqrt_nonneg _
    by_cases hz : Real.sqrt (p.2 0 ^ 2 + p.2 1 ^ 2) ≤ rOut
    · obtain ⟨hg1, hg2⟩ := hgapU p hp hz y' hy'
      have hne : y' - p.1 • p.2 ≠ 0 := by
        intro h0; rw [h0, norm_zero] at hg2; linarith
      have hw := IIIa.sepDiff_gapWeight D ‖y - p.1 • p.2‖ ‖y' - p.1 • p.2‖ m hD hg1 hg2
      refine (hpi m p hp y' hne).trans ?_
      unfold IIIa.sepDiffMaj
      have hC3 : 0 ≤ 3 * C m := by linarith [hC0 m]
      calc 3 * C m * (p.1 ^ (2 * μ.re + 2) * ‖y' - p.1 • p.2‖ ^ (-4 - (m : ℝ)) *
            IIIa.tensorNorm (T (τ + 2 * Real.log p.1) p.2))
          ≤ 3 * C m * (p.1 ^ (2 * μ.re + 2) * (2 ^ (4 + (m : ℝ)) * D ^ (-(m : ℝ)) *
              ‖y - p.1 • p.2‖ ^ (-4 : ℝ)) * IIIa.tensorNorm (T (τ + 2 * Real.log p.1) p.2)) := by
            gcongr
        _ = _ := by ring
    · have hz' : rOut < Real.sqrt (p.2 0 ^ 2 + p.2 1 ^ 2) := lt_of_not_ge hz
      rw [hoff p hz']
      have h0 : iteratedFDeriv ℝ m (0 : Space → Fin 3 → ℂ) y' = 0 := by simp
      rw [h0, norm_zero]
      have hTz : T (τ + 2 * Real.log p.1) p.2 = 0 := hT.support _ _ hz'
      unfold IIIa.sepDiffMaj
      rw [hTz]
      simp [IIIa.tensorNorm]
  have hInt : Integrable (IIIa.sepDiffMaj μ T τ y) IIIa.sepDiffRho :=
    h6 μ rOut rIn P T hrO hrr hT τ y hy hfin
  have hLoc : UnforcedLeray.L09.LocDominated IIIa.sepDiffRho F U := by
    intro m x hx
    refine ⟨U, hU.mem_nhds hx,
      fun p => (3 * C m * 2 ^ (4 + (m : ℝ)) * D ^ (-(m : ℝ))) * IIIa.sepDiffMaj μ T τ y p,
      hInt.const_mul _, ?_⟩
    filter_upwards [IIIa.sepDiffRho_ae_mem] with p hp y' hy'
    exact hdom m p hp y' hy'
  have hsmooth : ∀ᵐ p ∂IIIa.sepDiffRho, ContDiffOn ℝ ∞ (F p) U := by
    filter_upwards [IIIa.sepDiffRho_ae_mem] with p hp
    exact (contDiff_pi.2 (hsm p hp)).contDiffOn
  have hmeas : ∀ (m : ℕ), ∀ x ∈ U,
      AEStronglyMeasurable (fun p => iteratedFDeriv ℝ m (F p) x) IIIa.sepDiffRho := by
    intro m x _
    have hR : AEStronglyMeasurable (fun p => ∑ i : Fin 3,
        (ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin m => Space) ℂ
          (Fin 3 → ℂ) (ContinuousLinearMap.single ℝ (fun _ : Fin 3 => ℂ) i))
          (iteratedFDeriv ℝ m (fun y' => F p y' i) x)) IIIa.sepDiffRho := by
      refine Finset.aestronglyMeasurable_fun_sum _ fun i _ => ?_
      exact (ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin m => Space) ℂ
        (Fin 3 → ℂ) (ContinuousLinearMap.single ℝ (fun _ : Fin 3 => ℂ) i)).continuous
          |>.comp_aestronglyMeasurable (h3 ν μ P rOut T hν hT τ i m x)
    refine hR.congr ?_
    filter_upwards [IIIa.sepDiffRho_ae_mem] with p hp
    rw [IIIa.sepDiff_iteratedFDeriv_pi (fun i => hsmAt m p hp x i)]
    rfl
  have hFint : ∀ y' ∈ U, Integrable (fun p => F p y') IIIa.sepDiffRho := by
    intro y' hy'
    have hm : AEStronglyMeasurable (fun p => F p y') IIIa.sepDiffRho := by
      have := (continuousMultilinearCurryFin0 ℝ Space (Fin 3 → ℂ)).continuous
        |>.comp_aestronglyMeasurable (hmeas 0 y' hy')
      refine this.congr (Eventually.of_forall fun p => ?_)
      simp
    refine Integrable.mono' (hInt.const_mul (3 * C 0 * 2 ^ (4 + ((0 : ℕ) : ℝ)) *
      D ^ (-((0 : ℕ) : ℝ)))) hm ?_
    filter_upwards [IIIa.sepDiffRho_ae_mem] with p hp
    rw [← norm_iteratedFDeriv_zero (𝕜 := ℝ)]
    exact hdom 0 p hp y' hy'
  have hEq : (fun y' => IIIa.sepW ν μ T y' τ) =ᶠ[𝓝 y] fun y' => ∫ p, F p y' ∂IIIa.sepDiffRho := by
    filter_upwards [hU.mem_nhds hyU] with y' hy' using h5 ν μ T τ y' (hFint y' hy')
  exact ((UnforcedLeray.L09.contDiffOn_integral hU hsmooth hmeas hLoc).contDiffAt
    (hU.mem_nhds hyU)).congr_of_eventuallyEq hEq

private theorem sepW_meanLift_contDiffOn {ν c ε ρo : ℝ} {m : ℂ}
    (hν : 0 < ν) (hc : 0 < c) (hε : 0 < ε) (hρo : 0 ≤ ρo) (hm : -(1 / 4) < m.re)
    (G : ℝ × ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ)
    (hGm : ∀ i j, Measurable fun w : (ℝ × ℝ) × ℝ => G w.1 w.2 i j)
    (hGs : ∀ x' Y, ρo < Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2) → G x' Y = 0)
    (hint : Integrable (fun w : (ℝ × ℝ) × ℝ => IIIa.tensorNorm (G w.1 w.2)) volume)
    (τ : ℝ) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y' => IIIa.sepW ν m (IIIa.thinSource ε (IIIa.meanLift G)) y' τ)
      {y' : Space | ρo / ε < ϱ y'} := by
  intro y hy
  have hy' : ρo / ε < ϱ y := hy
  set rOut := ρo / ε
  set rIn := (rOut + ϱ y) / 2 with hrIn_def
  have hrO : 0 ≤ rOut := div_nonneg hρo hε.le
  have hrr : rOut < rIn := by rw [hrIn_def]; linarith
  have hy_rIn : rIn ≤ Real.sqrt (y 0 ^ 2 + y 1 ^ 2) := by
    change rIn ≤ ϱ y
    rw [hrIn_def]; linarith
  have hD : 0 < rIn - rOut := by linarith
  set T := IIIa.thinSource ε (IIIa.meanLift G)
  have hsrc : IIIa.IsSepSource (2 * ε * c) rOut T :=
    IIIa.t17s_isSepSource ε c ρo hε hc _ (fun i' j' =>
      (hGm i' j').comp (f := fun w : (ℝ × ℝ) × ℝ × ℝ => (w.1, w.2.1)) (by fun_prop))
      (fun _ _ _ => rfl) (fun x' Y q h => hGs x' Y h)
  have hfin : IIIa.sepDom (2 * m.re + 2) 0 (rIn - rOut) (IIIa.srcNorm T) τ y < ⊤ := by
    refine (sepDom_thin_meanLift_le hε hD hm G hGm 0 τ y).trans_lt ?_
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top) hint.lintegral_lt_top)
  exact (sepW_contDiffAt_of_sepDom ν hν m rOut rIn (2 * ε * c) hrO hrr T hsrc τ y hy_rIn
    hfin).contDiffWithinAt

/-- `srcX0 ν μ (IIIa.thinSource ε (IIIa.meanLift G)) τ` is `C^∞` on `{y' : Space | ρo / ε < ϱ y'}`. -/
theorem srcX0_meanLift_contDiffOn {ν c ε μ ρo : ℝ}
    (hν : 0 < ν) (hc : 0 < c) (hε : 0 < ε) (hμ : -(1 / 4) < μ) (hρo : 0 ≤ ρo)
    (G : ℝ × ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ)
    (hGm : ∀ i j, Measurable fun w : (ℝ × ℝ) × ℝ => G w.1 w.2 i j)
    (hGs : ∀ x' Y, ρo < Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2) → G x' Y = 0)
    (hint : Integrable (fun w : (ℝ × ℝ) × ℝ => IIIa.tensorNorm (G w.1 w.2)) volume)
    (τ : ℝ) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (srcX0 ν μ (IIIa.thinSource ε (IIIa.meanLift G)) τ)
      {y' : Space | ρo / ε < ϱ y'} := by
  have hm0 : -(1 / 4) < ((μ : ℂ)).re := by simpa using hμ
  have hm1 : -(1 / 4) < ((μ : ℂ) + 1).re := by simp; linarith
  have hW0 := sepW_meanLift_contDiffOn hν hc hε hρo hm0 G hGm hGs hint τ
  have hW1 := sepW_meanLift_contDiffOn hν hc hε hρo hm1 G hGm hGs hint τ
  exact PhasePrim.reMap.contDiff.comp_contDiffOn (hW0.sub hW1)

private theorem sepW_meanLift_decay {ν c ε ρo : ℝ} {m : ℂ}
    (hν : 0 < ν) (hc : 0 < c) (hε : 0 < ε) (hρo : 0 ≤ ρo) (hm : -(1 / 4) < m.re)
    (G : ℝ × ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ)
    (hGm : ∀ i j, Measurable fun w : (ℝ × ℝ) × ℝ => G w.1 w.2 i j)
    (hGs : ∀ x' Y, ρo < Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2) → G x' Y = 0)
    (hint : Integrable (fun w : (ℝ × ℝ) × ℝ => IIIa.tensorNorm (G w.1 w.2)) volume)
    (τ : ℝ) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y' : Space, 2 * (ρo / ε) + 2 ≤ ϱ y' →
      ‖iteratedFDeriv ℝ n
        (fun y'' => IIIa.sepW ν m (IIIa.thinSource ε (IIIa.meanLift G)) y'' τ) y'‖ ≤
        C * (ϱ y' ^ 4)⁻¹ := by
  obtain ⟨C0, hC0, hdom⟩ :=
    (IIIa.sepWDominated_of IIIa.sepWDiffUnder_proved) IIIa.sepKernelBounds n
  set M_enn : ℝ≥0∞ :=
    ENNReal.ofReal (ε⁻¹) ^ 2 *
      ∫⁻ w : (ℝ × ℝ) × ℝ, ENNReal.ofReal (IIIa.tensorNorm (G w.1 w.2))
  have hM_lt : M_enn < ⊤ :=
    ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top) hint.lintegral_lt_top
  set M : ℝ := M_enn.toReal
  have hM_nn : 0 ≤ M := ENNReal.toReal_nonneg
  have hM_eq : ENNReal.ofReal M = M_enn := ENNReal.ofReal_toReal hM_lt.ne
  refine ⟨C0 * M * 16, by positivity, fun y' hy' => ?_⟩
  set rOut := ρo / ε
  have hrO : 0 ≤ rOut := div_nonneg hρo hε.le
  have hy'_pos : 0 < ϱ y' := by linarith
  have hrr : rOut < ϱ y' := by linarith
  have hP : 0 < 2 * ε * c := by positivity
  set T := IIIa.thinSource ε (IIIa.meanLift G)
  have hsrc : IIIa.IsSepSource (2 * ε * c) rOut T :=
    IIIa.t17s_isSepSource ε c ρo hε hc _ (fun i' j' =>
      (hGm i' j').comp (f := fun w : (ℝ × ℝ) × ℝ × ℝ => (w.1, w.2.1)) (by fun_prop))
      (fun _ _ _ => rfl) (fun x' Y q h => hGs x' Y h)
  set D := ϱ y' - rOut
  have hD_half : ϱ y' / 2 ≤ D := by show ϱ y' / 2 ≤ ϱ y' - rOut; linarith
  have hD1 : 1 ≤ D := by linarith
  have hD_pos : 0 < D := by linarith
  have hfin0 : IIIa.sepDom (2 * m.re + 2) 0 D (IIIa.srcNorm T) τ y' < ⊤ :=
    (sepDom_thin_meanLift_le hε hD_pos hm G hGm 0 τ y').trans_lt
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hM_lt)
  have hw := hdom ν hν m hm rOut (ϱ y') (2 * ε * c) hrO hrr hP T hsrc τ y' le_rfl hfin0
  have hw' : ‖iteratedFDeriv ℝ n (fun y'' => IIIa.sepW ν m T y'' τ) y'‖ₑ ≤
      ENNReal.ofReal (C0 * M * D ^ (-4 - (n : ℝ))) := by
    calc ‖iteratedFDeriv ℝ n (fun y'' => IIIa.sepW ν m T y'' τ) y'‖ₑ
        = IIIa.wDerivNorm ν m T n τ y' := rfl
      _ ≤ ENNReal.ofReal C0 * IIIa.sepDom (2 * m.re + 2) n D (IIIa.srcNorm T) τ y' := hw
      _ ≤ ENNReal.ofReal C0 * (ENNReal.ofReal (D ^ (-4 - (n : ℝ))) * M_enn) := by
          gcongr
          exact sepDom_thin_meanLift_le hε hD_pos hm G hGm n τ y'
      _ = ENNReal.ofReal (C0 * M * D ^ (-4 - (n : ℝ))) := by
          rw [← hM_eq, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hC0]
          congr 1; ring
  rw [← ofReal_norm] at hw'
  have hreal : ‖iteratedFDeriv ℝ n (fun y'' => IIIa.sepW ν m T y'' τ) y'‖ ≤
      C0 * M * D ^ (-4 - (n : ℝ)) :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hw'
  refine hreal.trans ?_
  have hpow1 : D ^ (-4 - (n : ℝ)) ≤ D ^ (-4 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hD1 (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
  have hpow2 : D ^ (-4 : ℝ) ≤ 16 * (ϱ y' ^ 4)⁻¹ := by
    have h1 : D ^ (-4 : ℝ) ≤ (ϱ y' / 2) ^ (-4 : ℝ) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hD_half (by norm_num)
    have h2 : (ϱ y' / 2) ^ (-4 : ℝ) = 16 * (ϱ y' ^ 4)⁻¹ := by
      rw [Real.div_rpow hy'_pos.le (by norm_num), Real.rpow_neg hy'_pos.le,
        Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
        show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, Real.rpow_natCast]
      ring
    exact h1.trans h2.le
  calc C0 * M * D ^ (-4 - (n : ℝ))
      ≤ C0 * M * (16 * (ϱ y' ^ 4)⁻¹) :=
        mul_le_mul_of_nonneg_left (hpow1.trans hpow2) (by positivity)
    _ = C0 * M * 16 * (ϱ y' ^ 4)⁻¹ := by ring

/-- All spatial derivatives of `srcX0 ν μ (IIIa.thinSource ε (IIIa.meanLift G)) τ` decay as
`O(ϱ^{-4})` for `2 * (ρo / ε) + 2 ≤ ϱ y'`. -/
theorem srcX0_meanLift_decay {ν c ε μ ρo : ℝ}
    (hν : 0 < ν) (hc : 0 < c) (hε : 0 < ε) (hμ : -(1 / 4) < μ) (hρo : 0 ≤ ρo)
    (G : ℝ × ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ)
    (hGm : ∀ i j, Measurable fun w : (ℝ × ℝ) × ℝ => G w.1 w.2 i j)
    (hGs : ∀ x' Y, ρo < Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2) → G x' Y = 0)
    (hint : Integrable (fun w : (ℝ × ℝ) × ℝ => IIIa.tensorNorm (G w.1 w.2)) volume)
    (τ : ℝ) (n : ℕ) :
    ∃ C : ℝ, ∀ y' : Space, 2 * (ρo / ε) + 2 ≤ ϱ y' →
      ‖iteratedFDeriv ℝ n (srcX0 ν μ (IIIa.thinSource ε (IIIa.meanLift G)) τ) y'‖ ≤
        C * (ϱ y' ^ 4)⁻¹ := by
  have hm0 : -(1 / 4) < ((μ : ℂ)).re := by simpa using hμ
  have hm1 : -(1 / 4) < ((μ : ℂ) + 1).re := by simp; linarith
  obtain ⟨C0, hC0, hb0⟩ := sepW_meanLift_decay hν hc hε hρo hm0 G hGm hGs hint τ n
  obtain ⟨C1, hC1, hb1⟩ := sepW_meanLift_decay hν hc hε hρo hm1 G hGm hGs hint τ n
  refine ⟨‖PhasePrim.reMap‖ * (C0 + C1), fun y' hy' => ?_⟩
  have hrO : 0 ≤ ρo / ε := div_nonneg hρo hε.le
  have hy'_mem : ρo / ε < ϱ y' := by linarith
  have hopen : IsOpen {y : Space | ρo / ε < ϱ y} := isOpen_lt continuous_const continuous_ϱ
  set T := IIIa.thinSource ε (IIIa.meanLift G)
  have hW0 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => IIIa.sepW ν (μ : ℂ) T z τ) y' :=
    (sepW_meanLift_contDiffOn hν hc hε hρo hm0 G hGm hGs hint τ).contDiffAt
      (hopen.mem_nhds hy'_mem)
  have hW1 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => IIIa.sepW ν ((μ : ℂ) + 1) T z τ) y' :=
    (sepW_meanLift_contDiffOn hν hc hε hρo hm1 G hGm hGs hint τ).contDiffAt
      (hopen.mem_nhds hy'_mem)
  have hn : (n : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by exact_mod_cast le_top
  have hfun : srcX0 ν μ T τ =
      ⇑PhasePrim.reMap ∘ ((fun z => IIIa.sepW ν (μ : ℂ) T z τ) -
        (fun z => IIIa.sepW ν ((μ : ℂ) + 1) T z τ)) := rfl
  rw [hfun]
  refine (PhasePrim.reMap.norm_iteratedFDeriv_comp_left (hW0.sub hW1) hn).trans ?_
  have hsub_eq : iteratedFDeriv ℝ n
      (fun z => IIIa.sepW ν (μ : ℂ) T z τ - IIIa.sepW ν ((μ : ℂ) + 1) T z τ) y' =
      iteratedFDeriv ℝ n (fun z => IIIa.sepW ν (μ : ℂ) T z τ) y' -
        iteratedFDeriv ℝ n (fun z => IIIa.sepW ν ((μ : ℂ) + 1) T z τ) y' :=
    iteratedFDeriv_sub_apply (hW0.of_le hn) (hW1.of_le hn)
  rw [hsub_eq]
  have hsub := (norm_sub_le _ _).trans (add_le_add (hb0 y' hy') (hb1 y' hy'))
  calc ‖PhasePrim.reMap‖ *
        ‖iteratedFDeriv ℝ n (fun z => IIIa.sepW ν (μ : ℂ) T z τ) y' -
          iteratedFDeriv ℝ n (fun z => IIIa.sepW ν ((μ : ℂ) + 1) T z τ) y'‖
      ≤ ‖PhasePrim.reMap‖ * (C0 * (ϱ y' ^ 4)⁻¹ + C1 * (ϱ y' ^ 4)⁻¹) :=
        mul_le_mul_of_nonneg_left hsub (norm_nonneg _)
    _ = ‖PhasePrim.reMap‖ * (C0 + C1) * (ϱ y' ^ 4)⁻¹ := by ring

end YBWidth

end UnforcedLeray.Short.PartIIIb.Concrete

end
