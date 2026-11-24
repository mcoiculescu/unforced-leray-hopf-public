import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Continuity.WardY.Defs
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T16_1_1
import UnforcedLeray.Short.PartIIIa.T15_SepKernelBounds

/-!
# `PartIII-b:C/cont/WY/1`: `SepWSubDom`, `μ`-Lipschitz domination of `sepW` and its derivatives

Source of record: `the November 2 reference manuscript`
(73 pages), lines 3604-3623 (`sep:kernel`, `sep:resolvent`), 5701-5704.

For `l ∈ (0, 1)` and `μ, μ' ≥ 0`, the Mean Value Theorem on `t ↦ l^{2t+2}` together with
`(-log l) l^{1/4} ≤ 4` gives `|l^{2μ+2} - l^{2μ'+2}| ≤ 8 |μ - μ'| l^{2(-1/8)+2}`.
Differentiating `sepW` under the `(λ, z)` integral via `L09.iteratedFDeriv_integral_eq` (as in
`sepWDiffUnder_of`, `PartIII-a/Sub/PartIII-a_T16_1_1/Defs.lean`) at both `μ` and `μ'` and factoring
`(l^{2μ+2} - l^{2μ'+2}) • sepDiffF ν (-1) T τ p` yields `SepWSubDom` with `C = 24 * C_j`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- For `l ∈ (0, 1)`, `(-log l) * l^{1/4} ≤ 4`. -/
private theorem neg_log_mul_rpow_le {l : ℝ} (hl : l ∈ Ioo (0 : ℝ) 1) :
    (-Real.log l) * l ^ (1 / 4 : ℝ) ≤ 4 := by
  have h1 : 1 + (-Real.log l) / 4 ≤ Real.exp ((-Real.log l) / 4) := by
    linarith [Real.add_one_le_exp ((-Real.log l) / 4)]
  have h2 : Real.exp ((-Real.log l) / 4) = l ^ (-1 / 4 : ℝ) := by
    rw [Real.rpow_def_of_pos hl.1]
    congr 1
    ring
  have h3 : (-Real.log l) / 4 ≤ l ^ (-1 / 4 : ℝ) := by linarith
  have h4 : 0 ≤ l ^ (1 / 4 : ℝ) := Real.rpow_nonneg hl.1.le _
  have h5 : l ^ (-1 / 4 : ℝ) * l ^ (1 / 4 : ℝ) = 1 := by
    rw [← Real.rpow_add hl.1]
    norm_num
  nlinarith [mul_le_mul_of_nonneg_right h3 h4]

/-- Mean value bound `|l^{2μ+2} - l^{2μ'+2}| ≤ 8 * |μ - μ'| * l^{2(-1/8)+2}` for `l ∈ (0, 1)`,
`μ, μ' ≥ 0`. -/
private theorem rpow_sub_rpow_le {l μ μ' : ℝ} (hl : l ∈ Ioo (0 : ℝ) 1)
    (hμ : 0 ≤ μ) (hμ' : 0 ≤ μ') :
    |l ^ (2 * μ + 2) - l ^ (2 * μ' + 2)| ≤ 8 * |μ - μ'| * l ^ (2 * (-1 / 8 : ℝ) + 2) := by
  have hderiv : ∀ t : ℝ, HasDerivAt (fun s : ℝ => l ^ (2 * s + 2))
      (Real.log l * 2 * l ^ (2 * t + 2)) t := by
    intro t
    have hg : HasDerivAt (fun s : ℝ => 2 * s + 2) 2 t := by
      simpa using ((hasDerivAt_id t).const_mul (2 : ℝ)).add_const (2 : ℝ)
    exact hg.const_rpow hl.1
  have hbound : ∀ t ∈ Ici (0 : ℝ),
      ‖deriv (fun s : ℝ => l ^ (2 * s + 2)) t‖ ≤ 8 * l ^ (2 * (-1 / 8 : ℝ) + 2) := by
    intro t ht
    have ht0 : 0 ≤ t := ht
    rw [(hderiv t).deriv, Real.norm_eq_abs, abs_mul, abs_mul]
    have hlpos : 0 ≤ l ^ (2 * t + 2) := Real.rpow_nonneg hl.1.le _
    have hlog : |Real.log l| = -Real.log l := abs_of_neg (Real.log_neg hl.1 hl.2)
    rw [abs_of_nonneg hlpos, show |(2 : ℝ)| = 2 by norm_num, hlog]
    have hsplit : l ^ (2 * t + 2) = l ^ (2 * (-1 / 8 : ℝ) + 2) * l ^ (2 * t + 1 / 4) := by
      rw [← Real.rpow_add hl.1]
      congr 1
      ring
    have hexp : l ^ (2 * t + 1 / 4) ≤ l ^ (1 / 4 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge hl.1 hl.2.le (by linarith)
    have hlog0 : 0 ≤ -Real.log l := by linarith [Real.log_neg hl.1 hl.2]
    have ha0 : 0 ≤ l ^ (2 * (-1 / 8 : ℝ) + 2) := Real.rpow_nonneg hl.1.le _
    have hstep1 : (-Real.log l) * 2 * l ^ (2 * t + 2) ≤
        l ^ (2 * (-1 / 8 : ℝ) + 2) * (2 * ((-Real.log l) * l ^ (1 / 4 : ℝ))) := by
      rw [hsplit]
      nlinarith [mul_le_mul_of_nonneg_left hexp (mul_nonneg ha0 hlog0)]
    have hstep2 := neg_log_mul_rpow_le hl
    nlinarith
  have hmvt := Convex.norm_image_sub_le_of_norm_deriv_le (s := Ici (0 : ℝ))
    (fun t _ => (hderiv t).differentiableAt) hbound (convex_Ici 0) hμ' hμ
  simp only [Real.norm_eq_abs] at hmvt
  linarith

/-- For `p.1 > 0` and real `m`, `sepDiffF ν (m : ℂ) T τ p y = (p.1 ^ (2 * m + 2)) • sepDiffF ν (-1) T τ p y`. -/
private theorem sepDiffF_eq_smul (ν m : ℝ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (τ : ℝ)
    (p : ℝ × Space) (hp : 0 < p.1) (y : Space) :
    IIIa.sepDiffF ν (m : ℂ) T τ p y =
      (p.1 ^ (2 * m + 2)) • IIIa.sepDiffF ν (-1 : ℂ) T τ p y := by
  funext i
  simp only [IIIa.sepDiffF, Pi.smul_apply, Complex.real_smul]
  have h1 : (p.1 : ℂ) ^ (2 * (-1 : ℂ) + 2) = 1 := by
    rw [show (2 * (-1 : ℂ) + 2 : ℂ) = 0 by ring, Complex.cpow_zero]
  have h2 : (p.1 : ℂ) ^ (2 * (m : ℂ) + 2) = ((p.1 ^ (2 * m + 2) : ℝ) : ℂ) := by
    have he : (2 * (m : ℂ) + 2 : ℂ) = ((2 * m + 2 : ℝ) : ℂ) := by push_cast; ring
    rw [he, Complex.ofReal_cpow hp.le]
  rw [h1, h2, one_mul]
  ring

set_option maxHeartbeats 1000000 in
/-- Differentiation of `sepW ν (μ : ℂ) T` under the `(λ, z)` integral and integrability of the
differentiated integrand on `sepDiffRho`. -/
private theorem sepW_iteratedFDeriv_integral (j : ℕ) (ν μ rOut rIn P : ℝ)
    (hν : 0 < ν) (hμ : -(1 / 4 : ℝ) < μ) (hrO : 0 ≤ rOut) (hrr : rOut < rIn) (hP : 0 < P)
    (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (hT : IIIa.IsSepSource P rOut T)
    (τ : ℝ) (y : Space) (hy : rIn ≤ Real.sqrt (y 0 ^ 2 + y 1 ^ 2))
    (hfin : IIIa.sepDom (2 * ((μ : ℂ)).re + 2) 0 (rIn - rOut) (IIIa.srcNorm T) τ y < ⊤) :
    iteratedFDeriv ℝ j (fun y' => IIIa.sepW ν (μ : ℂ) T y' τ) y =
        ∫ p, iteratedFDeriv ℝ j (IIIa.sepDiffF ν (μ : ℂ) T τ p) y ∂IIIa.sepDiffRho ∧
      Integrable (fun p => iteratedFDeriv ℝ j (IIIa.sepDiffF ν (μ : ℂ) T τ p) y)
        IIIa.sepDiffRho := by
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
  set F := IIIa.sepDiffF ν (μ : ℂ) T τ
  have hsm : ∀ p : ℝ × Space, p.1 ∈ Ioo (0 : ℝ) 1 → ∀ i, ContDiff ℝ ∞ (fun y' => F p y' i) :=
    fun p hp i => IIIa.sepDiffF_contDiff h1 ν (μ : ℂ) T τ hν p hp i
  have hsmAt : ∀ (n : ℕ) (p : ℝ × Space), p.1 ∈ Ioo (0 : ℝ) 1 → ∀ (y' : Space) (i : Fin 3),
      ContDiffAt ℝ n (fun y' => F p y' i) y' := fun n p hp y' i =>
    ((hsm p hp i).of_le (by exact_mod_cast le_top)).contDiffAt
  have hoff : ∀ p : ℝ × Space, rOut < Real.sqrt (p.2 0 ^ 2 + p.2 1 ^ 2) → F p = 0 :=
    fun p hp => IIIa.sepDiffF_eq_zero ν (μ : ℂ) T τ p (hT.support _ _ hp)
  have hpi : ∀ (n : ℕ) (p : ℝ × Space), p.1 ∈ Ioo (0 : ℝ) 1 → ∀ y' : Space,
      y' - p.1 • p.2 ≠ 0 → ‖iteratedFDeriv ℝ n (F p) y'‖ ≤ 3 * C n *
        (p.1 ^ (2 * (μ : ℂ).re + 2) * ‖y' - p.1 • p.2‖ ^ (-4 - (n : ℝ)) *
          IIIa.tensorNorm (T (τ + 2 * Real.log p.1) p.2)) := by
    intro n p hp y' hne
    rw [IIIa.sepDiff_iteratedFDeriv_pi (fun i => hsmAt n p hp y' i)]
    refine (norm_sum_le _ _).trans ?_
    have hb : ∀ i : Fin 3,
        ‖(ContinuousLinearMap.single ℝ (fun _ : Fin 3 => ℂ) i).compContinuousMultilinearMap
          (iteratedFDeriv ℝ n (fun y'' => F p y'' i) y')‖ ≤ C n *
            (p.1 ^ (2 * (μ : ℂ).re + 2) * ‖y' - p.1 • p.2‖ ^ (-4 - (n : ℝ)) *
              IIIa.tensorNorm (T (τ + 2 * Real.log p.1) p.2)) := by
      intro i
      refine (ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _).trans ?_
      have h1i := ContinuousLinearMap.norm_single_le_one ℝ (E := fun _ : Fin 3 => ℂ) i
      have h2i := hC n ν (μ : ℂ) T τ hν p.1 p.2 y' hp hne i
      calc ‖ContinuousLinearMap.single ℝ (fun _ : Fin 3 => ℂ) i‖ *
            ‖iteratedFDeriv ℝ n (fun y'' => F p y'' i) y'‖
          ≤ 1 * ‖iteratedFDeriv ℝ n (fun y'' => F p y'' i) y'‖ := by gcongr
        _ ≤ _ := by rw [one_mul]; exact h2i
    calc ∑ i : Fin 3, ‖(ContinuousLinearMap.single ℝ (fun _ : Fin 3 => ℂ) i).compContinuousMultilinearMap
          (iteratedFDeriv ℝ n (fun y'' => F p y'' i) y')‖
        ≤ ∑ _i : Fin 3, C n * (p.1 ^ (2 * (μ : ℂ).re + 2) * ‖y' - p.1 • p.2‖ ^ (-4 - (n : ℝ)) *
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
  have hdom : ∀ (n : ℕ) (p : ℝ × Space), p.1 ∈ Ioo (0 : ℝ) 1 → ∀ y' ∈ U,
      ‖iteratedFDeriv ℝ n (F p) y'‖ ≤
        (3 * C n * 2 ^ (4 + (n : ℝ)) * D ^ (-(n : ℝ))) * IIIa.sepDiffMaj (μ : ℂ) T τ y p := by
    intro n p hp y' hy'
    have hl0 : 0 ≤ p.1 ^ (2 * (μ : ℂ).re + 2) := Real.rpow_nonneg hp.1.le _
    have htn : 0 ≤ IIIa.tensorNorm (T (τ + 2 * Real.log p.1) p.2) := Real.sqrt_nonneg _
    by_cases hz : Real.sqrt (p.2 0 ^ 2 + p.2 1 ^ 2) ≤ rOut
    · obtain ⟨hg1, hg2⟩ := hgapU p hp hz y' hy'
      have hne : y' - p.1 • p.2 ≠ 0 := by
        intro h0; rw [h0, norm_zero] at hg2; linarith
      have hw := IIIa.sepDiff_gapWeight D ‖y - p.1 • p.2‖ ‖y' - p.1 • p.2‖ n hD hg1 hg2
      refine (hpi n p hp y' hne).trans ?_
      unfold IIIa.sepDiffMaj
      have hC3 : 0 ≤ 3 * C n := by linarith [hC0 n]
      calc 3 * C n * (p.1 ^ (2 * (μ : ℂ).re + 2) * ‖y' - p.1 • p.2‖ ^ (-4 - (n : ℝ)) *
            IIIa.tensorNorm (T (τ + 2 * Real.log p.1) p.2))
          ≤ 3 * C n * (p.1 ^ (2 * (μ : ℂ).re + 2) * (2 ^ (4 + (n : ℝ)) * D ^ (-(n : ℝ)) *
              ‖y - p.1 • p.2‖ ^ (-4 : ℝ)) * IIIa.tensorNorm (T (τ + 2 * Real.log p.1) p.2)) := by
            gcongr
        _ = _ := by ring
    · push_neg at hz
      rw [hoff p hz]
      have h0 : iteratedFDeriv ℝ n (0 : Space → Fin 3 → ℂ) y' = 0 := by
        simpa using congrFun (iteratedFDeriv_zero_fun (𝕜 := ℝ) (E := Space) (F := Fin 3 → ℂ) (n := n)) y'
      rw [h0, norm_zero]
      have hTz : T (τ + 2 * Real.log p.1) p.2 = 0 := hT.support _ _ hz
      unfold IIIa.sepDiffMaj
      rw [hTz]
      simp [IIIa.tensorNorm]
  have hInt : Integrable (IIIa.sepDiffMaj (μ : ℂ) T τ y) IIIa.sepDiffRho :=
    h6 (μ : ℂ) rOut rIn P T hrO hrr hT τ y hy hfin
  have hLoc : L09.LocDominated IIIa.sepDiffRho F U := by
    intro n x hx
    refine ⟨U, hU.mem_nhds hx,
      fun p => (3 * C n * 2 ^ (4 + (n : ℝ)) * D ^ (-(n : ℝ))) * IIIa.sepDiffMaj (μ : ℂ) T τ y p,
      hInt.const_mul _, ?_⟩
    filter_upwards [IIIa.sepDiffRho_ae_mem] with p hp y' hy'
    exact hdom n p hp y' hy'
  have hsmooth : ∀ᵐ p ∂IIIa.sepDiffRho, ContDiffOn ℝ ∞ (F p) U := by
    filter_upwards [IIIa.sepDiffRho_ae_mem] with p hp
    exact (contDiff_pi.2 (hsm p hp)).contDiffOn
  have hmeas : ∀ (n : ℕ), ∀ x ∈ U,
      AEStronglyMeasurable (fun p => iteratedFDeriv ℝ n (F p) x) IIIa.sepDiffRho := by
    intro n x _
    have hR : AEStronglyMeasurable (fun p => ∑ i : Fin 3,
        (ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin n => Space) ℂ
          (Fin 3 → ℂ) (ContinuousLinearMap.single ℝ (fun _ : Fin 3 => ℂ) i))
          (iteratedFDeriv ℝ n (fun y' => F p y' i) x)) IIIa.sepDiffRho := by
      refine Finset.aestronglyMeasurable_fun_sum _ fun i _ => ?_
      exact (ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin n => Space) ℂ
        (Fin 3 → ℂ) (ContinuousLinearMap.single ℝ (fun _ : Fin 3 => ℂ) i)).continuous
          |>.comp_aestronglyMeasurable (h3 ν (μ : ℂ) P rOut T hν hT τ i n x)
    refine hR.congr ?_
    filter_upwards [IIIa.sepDiffRho_ae_mem] with p hp
    rw [IIIa.sepDiff_iteratedFDeriv_pi (fun i => hsmAt n p hp x i)]
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
  have hEq : (fun y' => IIIa.sepW ν (μ : ℂ) T y' τ) =ᶠ[𝓝 y]
      fun y' => ∫ p, F p y' ∂IIIa.sepDiffRho := by
    filter_upwards [hU.mem_nhds hyU] with y' hy' using h5 ν (μ : ℂ) T τ y' (hFint y' hy')
  refine ⟨?_, ?_⟩
  · rw [(hEq.iteratedFDeriv (𝕜 := ℝ) j).eq_of_nhds]
    exact L09.iteratedFDeriv_integral_eq hU hsmooth hmeas hLoc j hyU
  · refine Integrable.mono' (hInt.const_mul (3 * C j * 2 ^ (4 + (j : ℝ)) * D ^ (-(j : ℝ))))
      (hmeas j y hyU) ?_
    filter_upwards [IIIa.sepDiffRho_ae_mem] with p hp
    exact hdom j p hp y hyU

set_option maxHeartbeats 1000000 in
/-- **Leaf 1** (`PartIII-b:C/cont/WY/1`): `SepWSubDom`. -/
theorem sepWSubDom_proved : SepWSubDom := by
  intro j
  choose C hC0 hC using IIIa.sepDiffFDerivBound IIIa.sepKernelBounds
  refine ⟨24 * C j, by linarith [hC0 j], ?_⟩
  intro ν μ μ' rOut rIn P hν hμ hμ' hrO hrr hP T hT τ y hy hfin
  have ha1 : 2 * (-1 / 8 : ℝ) + 2 ≤ 2 * ((μ : ℂ)).re + 2 := by
    simp only [Complex.ofReal_re]; linarith
  have ha2 : 2 * (-1 / 8 : ℝ) + 2 ≤ 2 * ((μ' : ℂ)).re + 2 := by
    simp only [Complex.ofReal_re]; linarith
  have hfin1 : IIIa.sepDom (2 * ((μ : ℂ)).re + 2) 0 (rIn - rOut) (IIIa.srcNorm T) τ y < ⊤ :=
    lt_of_le_of_lt (sepDom_anti_a ha1 (rIn - rOut) (IIIa.srcNorm T) τ y) hfin
  have hfin2 : IIIa.sepDom (2 * ((μ' : ℂ)).re + 2) 0 (rIn - rOut) (IIIa.srcNorm T) τ y < ⊤ :=
    lt_of_le_of_lt (sepDom_anti_a ha2 (rIn - rOut) (IIIa.srcNorm T) τ y) hfin
  obtain ⟨hEq1, hInt1⟩ := sepW_iteratedFDeriv_integral j ν μ rOut rIn P hν (by linarith)
    hrO hrr hP T hT τ y hy hfin1
  obtain ⟨hEq2, hInt2⟩ := sepW_iteratedFDeriv_integral j ν μ' rOut rIn P hν (by linarith)
    hrO hrr hP T hT τ y hy hfin2
  rw [hEq1, hEq2, ← integral_sub hInt1 hInt2]
  have hpi0 : ∀ p : ℝ × Space, p.1 ∈ Ioo (0 : ℝ) 1 → y - p.1 • p.2 ≠ 0 →
      ‖iteratedFDeriv ℝ j (IIIa.sepDiffF ν (-1 : ℂ) T τ p) y‖ ≤ 3 * C j *
        (‖y - p.1 • p.2‖ ^ (-4 - (j : ℝ)) * IIIa.tensorNorm (T (τ + 2 * Real.log p.1) p.2)) := by
    intro p hp hne
    have hsmAt : ∀ i : Fin 3,
        ContDiffAt ℝ j (fun y' => IIIa.sepDiffF ν (-1 : ℂ) T τ p y' i) y := fun i =>
      ((IIIa.sepDiffF_contDiff IIIa.heatLerayKSmoothAll ν (-1 : ℂ) T τ hν p hp i).of_le
        (by exact_mod_cast le_top)).contDiffAt
    rw [IIIa.sepDiff_iteratedFDeriv_pi hsmAt]
    refine (norm_sum_le _ _).trans ?_
    have hb : ∀ i : Fin 3,
        ‖(ContinuousLinearMap.single ℝ (fun _ : Fin 3 => ℂ) i).compContinuousMultilinearMap
          (iteratedFDeriv ℝ j (fun y'' => IIIa.sepDiffF ν (-1 : ℂ) T τ p y'' i) y)‖ ≤ C j *
            (‖y - p.1 • p.2‖ ^ (-4 - (j : ℝ)) *
              IIIa.tensorNorm (T (τ + 2 * Real.log p.1) p.2)) := by
      intro i
      refine (ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _).trans ?_
      have h1i := ContinuousLinearMap.norm_single_le_one ℝ (E := fun _ : Fin 3 => ℂ) i
      have h2i := hC j ν (-1 : ℂ) T τ hν p.1 p.2 y hp hne i
      have hex : p.1 ^ (2 * (-1 : ℂ).re + 2) = 1 := by
        rw [show 2 * (-1 : ℂ).re + 2 = 0 by simp, Real.rpow_zero]
      rw [hex, one_mul] at h2i
      calc ‖ContinuousLinearMap.single ℝ (fun _ : Fin 3 => ℂ) i‖ *
            ‖iteratedFDeriv ℝ j (fun y'' => IIIa.sepDiffF ν (-1 : ℂ) T τ p y'' i) y‖
          ≤ 1 * ‖iteratedFDeriv ℝ j (fun y'' => IIIa.sepDiffF ν (-1 : ℂ) T τ p y'' i) y‖ := by gcongr
        _ ≤ _ := by rw [one_mul]; exact h2i
    calc ∑ i : Fin 3, ‖(ContinuousLinearMap.single ℝ (fun _ : Fin 3 => ℂ) i).compContinuousMultilinearMap
          (iteratedFDeriv ℝ j (fun y'' => IIIa.sepDiffF ν (-1 : ℂ) T τ p y'' i) y)‖
        ≤ ∑ _i : Fin 3, C j * (‖y - p.1 • p.2‖ ^ (-4 - (j : ℝ)) *
            IIIa.tensorNorm (T (τ + 2 * Real.log p.1) p.2)) := Finset.sum_le_sum fun i _ => hb i
      _ = _ := by simp [Finset.sum_const]; ring
  set a0 : ℝ := 2 * (-1 / 8 : ℝ) + 2
  have hmB : AEMeasurable (fun p : ℝ × Space => ENNReal.ofReal (p.1 ^ a0 *
      ‖y - p.1 • p.2‖ ^ (-4 - (j : ℝ)) * IIIa.tensorNorm (T (τ + 2 * Real.log p.1) p.2)))
      ((volume.restrict (Ioo (0 : ℝ) 1)).prod volume) := by
    refine (ENNReal.measurable_ofReal.comp ?_).aemeasurable
    have hφ : Measurable fun q : ℝ × Space => (τ + 2 * Real.log q.1, q.2) :=
      (measurable_const.add (measurable_const.mul
        (Real.measurable_log.comp measurable_fst))).prodMk measurable_snd
    have hTn : Measurable fun q : ℝ × Space => IIIa.tensorNorm (T (τ + 2 * Real.log q.1) q.2) := by
      unfold IIIa.tensorNorm
      refine Measurable.sqrt ?_
      refine Finset.measurable_sum _ fun i _ => ?_
      refine Finset.measurable_sum _ fun k _ => ?_
      exact ((hT.measurable i k).comp hφ).pow_const 2
    exact ((measurable_fst.pow_const _).mul
      ((measurable_const.sub (measurable_fst.smul measurable_snd)).norm.pow_const _)).mul hTn
  have hK0 : 0 ≤ 24 * C j * |μ - μ'| := mul_nonneg (by linarith [hC0 j]) (abs_nonneg _)
  calc ‖∫ p, (iteratedFDeriv ℝ j (IIIa.sepDiffF ν (μ : ℂ) T τ p) y -
          iteratedFDeriv ℝ j (IIIa.sepDiffF ν (μ' : ℂ) T τ p) y) ∂IIIa.sepDiffRho‖ₑ
      ≤ ∫⁻ p, ‖iteratedFDeriv ℝ j (IIIa.sepDiffF ν (μ : ℂ) T τ p) y -
          iteratedFDeriv ℝ j (IIIa.sepDiffF ν (μ' : ℂ) T τ p) y‖ₑ ∂IIIa.sepDiffRho :=
        enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ p, ENNReal.ofReal (24 * C j * |μ - μ'|) * ENNReal.ofReal (p.1 ^ a0 *
          ‖y - p.1 • p.2‖ ^ (-4 - (j : ℝ)) * IIIa.tensorNorm (T (τ + 2 * Real.log p.1) p.2))
          ∂IIIa.sepDiffRho := by
        refine lintegral_mono_ae ?_
        filter_upwards [IIIa.sepDiffRho_ae_mem] with p hp
        rw [← ENNReal.ofReal_mul hK0, ← ofReal_norm]
        refine ENNReal.ofReal_le_ofReal ?_
        by_cases hz : Real.sqrt (p.2 0 ^ 2 + p.2 1 ^ 2) ≤ rOut
        · have hg := IIIa.radial_gap y p.2 p.1 rOut rIn hp hz hy
          have hne : y - p.1 • p.2 ≠ 0 := by
            intro h0; rw [h0, norm_zero] at hg; linarith
          have hcd0 : ContDiff ℝ ∞ (IIIa.sepDiffF ν (-1 : ℂ) T τ p) :=
            contDiff_pi.2 (fun i => IIIa.sepDiffF_contDiff IIIa.heatLerayKSmoothAll ν (-1 : ℂ)
              T τ hν p hp i)
          have hcdAt : ContDiffAt ℝ j (IIIa.sepDiffF ν (-1 : ℂ) T τ p) y :=
            (hcd0.of_le (by exact_mod_cast le_top)).contDiffAt
          have hf1 : IIIa.sepDiffF ν (μ : ℂ) T τ p =
              (p.1 ^ (2 * μ + 2)) • IIIa.sepDiffF ν (-1 : ℂ) T τ p :=
            funext (sepDiffF_eq_smul ν μ T τ p hp.1)
          have hf2 : IIIa.sepDiffF ν (μ' : ℂ) T τ p =
              (p.1 ^ (2 * μ' + 2)) • IIIa.sepDiffF ν (-1 : ℂ) T τ p :=
            funext (sepDiffF_eq_smul ν μ' T τ p hp.1)
          rw [hf1, hf2, iteratedFDeriv_const_smul_apply hcdAt,
            iteratedFDeriv_const_smul_apply hcdAt, ← sub_smul, norm_smul, Real.norm_eq_abs]
          have hmvt := rpow_sub_rpow_le hp hμ hμ'
          have hder := hpi0 p hp hne
          have h1 : 0 ≤ ‖y - p.1 • p.2‖ ^ (-4 - (j : ℝ)) *
              IIIa.tensorNorm (T (τ + 2 * Real.log p.1) p.2) :=
            mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (Real.sqrt_nonneg _)
          have h2 : 0 ≤ 8 * |μ - μ'| * p.1 ^ a0 :=
            mul_nonneg (mul_nonneg (by norm_num) (abs_nonneg _)) (Real.rpow_nonneg hp.1.le _)
          calc |p.1 ^ (2 * μ + 2) - p.1 ^ (2 * μ' + 2)| *
                ‖iteratedFDeriv ℝ j (IIIa.sepDiffF ν (-1 : ℂ) T τ p) y‖
              ≤ (8 * |μ - μ'| * p.1 ^ a0) * (3 * C j *
                  (‖y - p.1 • p.2‖ ^ (-4 - (j : ℝ)) *
                    IIIa.tensorNorm (T (τ + 2 * Real.log p.1) p.2))) :=
                mul_le_mul hmvt hder (norm_nonneg _) h2
            _ = 24 * C j * |μ - μ'| * (p.1 ^ a0 *
                  ‖y - p.1 • p.2‖ ^ (-4 - (j : ℝ)) *
                    IIIa.tensorNorm (T (τ + 2 * Real.log p.1) p.2)) := by ring
        · push_neg at hz
          have hTz : T (τ + 2 * Real.log p.1) p.2 = 0 := hT.support _ _ hz
          rw [IIIa.sepDiffF_eq_zero ν (μ : ℂ) T τ p hTz,
            IIIa.sepDiffF_eq_zero ν (μ' : ℂ) T τ p hTz, sub_self, norm_zero, hTz]
          simp [IIIa.tensorNorm]
    _ = ENNReal.ofReal (24 * C j * |μ - μ'|) * ∫⁻ p, ENNReal.ofReal (p.1 ^ a0 *
          ‖y - p.1 • p.2‖ ^ (-4 - (j : ℝ)) * IIIa.tensorNorm (T (τ + 2 * Real.log p.1) p.2))
          ∂IIIa.sepDiffRho := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal (24 * C j * |μ - μ'|) * ∫⁻ l in Ioo (0 : ℝ) 1, ENNReal.ofReal (l ^ a0) *
          ∫⁻ z : Space, ENNReal.ofReal (‖y - l • z‖ ^ (-4 - (j : ℝ))) *
            IIIa.srcNorm T (τ + 2 * Real.log l) z := by
        congr 1
        rw [show IIIa.sepDiffRho = (volume.restrict (Ioo (0 : ℝ) 1)).prod volume from rfl,
          lintegral_prod _ hmB]
        refine setLIntegral_congr_fun measurableSet_Ioo (fun l hl => ?_)
        simp only
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine lintegral_congr fun z => ?_
        unfold IIIa.srcNorm
        rw [ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg hl.1.le _)
          (Real.rpow_nonneg (norm_nonneg _) _)),
          ENNReal.ofReal_mul (Real.rpow_nonneg hl.1.le _), mul_assoc]
    _ ≤ ENNReal.ofReal (24 * C j * |μ - μ'|) *
          IIIa.sepDom a0 j (rIn - rOut) (IIIa.srcNorm T) τ y := by
        unfold IIIa.sepDom
        refine mul_le_mul' le_rfl (setLIntegral_mono' measurableSet_Ioo fun l hl => ?_)
        refine mul_le_mul' le_rfl (lintegral_mono fun z => ?_)
        by_cases hz : Real.sqrt (z 0 ^ 2 + z 1 ^ 2) ≤ rOut
        · have hg := IIIa.radial_gap y z l rOut rIn hl hz hy
          unfold IIIa.sepKd
          rw [if_pos hg]
        · push_neg at hz
          have hT0 := hT.support (τ + 2 * Real.log l) z hz
          have : IIIa.srcNorm T (τ + 2 * Real.log l) z = 0 := by
            unfold IIIa.srcNorm IIIa.tensorNorm; rw [hT0]; simp
          rw [this]; simp

end UnforcedLeray.Short.PartIIIb.Concrete
