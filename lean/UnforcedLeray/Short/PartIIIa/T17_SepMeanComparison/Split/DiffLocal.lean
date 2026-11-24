import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T16_1_1
import UnforcedLeray.Short.PartIIIa.T17_SepMeanComparison.Split.TonelliMain

/-!
# Split helper: local integral representation and differentiability of `sepW` (T17/1)

Extracted from `sepWDiffUnder_of`: at a receiver with finite order-0 majorant, near `y` the
integrand of `sepW` is `sepDiffRho`-integrable, `sepW` is its integral, and `sepW` is
differentiable at `y`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

set_option maxHeartbeats 1000000 in
theorem t17s_local (hK : SepKernelBounds) (ν : ℝ) (hν : 0 < ν) (μ : ℂ)
    (rOut rIn P : ℝ) (hrO : 0 ≤ rOut) (hrr : rOut < rIn)
    (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (hT : IsSepSource P rOut T) (τ : ℝ) (y : Space)
    (hy : rIn ≤ Real.sqrt (y 0 ^ 2 + y 1 ^ 2))
    (hfin : sepDom (2 * μ.re + 2) 0 (rIn - rOut) (srcNorm T) τ y < ⊤) :
    (∀ᶠ y' in 𝓝 y, Integrable (fun p => sepDiffF ν μ T τ p y') sepDiffRho ∧
        sepW ν μ T y' τ = ∫ p, sepDiffF ν μ T τ p y' ∂sepDiffRho) ∧
      DifferentiableAt ℝ (fun y' => sepW ν μ T y' τ) y := by
  have h1 := heatLerayKSmoothAll
  have h3 := sepDiffFMeas
  have h4 := sepDiffFDerivBound
  have h5 := sepDiffWEqIntegral
  have h6 := sepDiffMajIntegrable
  choose C hC0 hC using h4 hK
  have hD : 0 < rIn - rOut := by linarith
  set D := rIn - rOut with hDdef
  set U : Set Space := Metric.ball y (D / 2) with hUdef
  have hU : IsOpen U := Metric.isOpen_ball
  have hyU : y ∈ U := Metric.mem_ball_self (by linarith)
  set F := sepDiffF ν μ T τ with hFdef
  have hsm : ∀ p : ℝ × Space, p.1 ∈ Ioo (0 : ℝ) 1 → ∀ i, ContDiff ℝ ∞ (fun y' => F p y' i) :=
    fun p hp i => sepDiffF_contDiff h1 ν μ T τ hν p hp i
  have hsmAt : ∀ (n : ℕ) (p : ℝ × Space), p.1 ∈ Ioo (0 : ℝ) 1 → ∀ (y' : Space) (i : Fin 3),
      ContDiffAt ℝ n (fun y' => F p y' i) y' := fun n p hp y' i =>
    ((hsm p hp i).of_le (by exact_mod_cast le_top)).contDiffAt
  have hoff : ∀ p : ℝ × Space, rOut < Real.sqrt (p.2 0 ^ 2 + p.2 1 ^ 2) → F p = 0 :=
    fun p hp => sepDiffF_eq_zero ν μ T τ p (hT.support _ _ hp)
  -- the `Fin 3`-valued derivative bound off the singularity
  have hpi : ∀ (n : ℕ) (p : ℝ × Space), p.1 ∈ Ioo (0 : ℝ) 1 → ∀ y' : Space,
      y' - p.1 • p.2 ≠ 0 → ‖iteratedFDeriv ℝ n (F p) y'‖ ≤ 3 * C n *
        (p.1 ^ (2 * μ.re + 2) * ‖y' - p.1 • p.2‖ ^ (-4 - (n : ℝ)) *
          tensorNorm (T (τ + 2 * Real.log p.1) p.2)) := by
    intro n p hp y' hne
    rw [sepDiff_iteratedFDeriv_pi (fun i => hsmAt n p hp y' i)]
    refine (norm_sum_le _ _).trans ?_
    have hb : ∀ i : Fin 3, ‖(ContinuousLinearMap.single ℝ (fun _ : Fin 3 => ℂ) i).compContinuousMultilinearMap
        (iteratedFDeriv ℝ n (fun y'' => F p y'' i) y')‖ ≤ C n *
          (p.1 ^ (2 * μ.re + 2) * ‖y' - p.1 • p.2‖ ^ (-4 - (n : ℝ)) *
            tensorNorm (T (τ + 2 * Real.log p.1) p.2)) := by
      intro i
      refine (ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _).trans ?_
      have h1i := ContinuousLinearMap.norm_single_le_one ℝ (E := fun _ : Fin 3 => ℂ) i
      have h2i := hC n ν μ T τ hν p.1 p.2 y' hp hne i
      calc ‖ContinuousLinearMap.single ℝ (fun _ : Fin 3 => ℂ) i‖ *
            ‖iteratedFDeriv ℝ n (fun y'' => F p y'' i) y'‖
          ≤ 1 * ‖iteratedFDeriv ℝ n (fun y'' => F p y'' i) y'‖ := by gcongr
        _ ≤ _ := by rw [one_mul]; exact h2i
    calc ∑ i : Fin 3, ‖(ContinuousLinearMap.single ℝ (fun _ : Fin 3 => ℂ) i).compContinuousMultilinearMap
          (iteratedFDeriv ℝ n (fun y'' => F p y'' i) y')‖
        ≤ ∑ _i : Fin 3, C n * (p.1 ^ (2 * μ.re + 2) * ‖y' - p.1 • p.2‖ ^ (-4 - (n : ℝ)) *
            tensorNorm (T (τ + 2 * Real.log p.1) p.2)) := Finset.sum_le_sum fun i _ => hb i
      _ = _ := by simp [Finset.sum_const]; ring
  -- the gap on `U`
  have hgapU : ∀ p : ℝ × Space, p.1 ∈ Ioo (0 : ℝ) 1 → Real.sqrt (p.2 0 ^ 2 + p.2 1 ^ 2) ≤ rOut →
      ∀ y' ∈ U, D ≤ ‖y - p.1 • p.2‖ ∧ ‖y - p.1 • p.2‖ ≤ 2 * ‖y' - p.1 • p.2‖ := by
    intro p hp hz y' hy'
    have hg := radial_gap y p.2 p.1 rOut rIn hp hz hy
    have hd : ‖y - y'‖ < D / 2 := by
      rw [← dist_eq_norm, dist_comm]; exact hy'
    have ht := norm_sub_le_norm_sub_add_norm_sub y y' (p.1 • p.2)
    exact ⟨hg, by linarith⟩
  -- local domination at every order
  have hdom : ∀ (n : ℕ) (p : ℝ × Space), p.1 ∈ Ioo (0 : ℝ) 1 → ∀ y' ∈ U,
      ‖iteratedFDeriv ℝ n (F p) y'‖ ≤
        (3 * C n * 2 ^ (4 + (n : ℝ)) * D ^ (-(n : ℝ))) * sepDiffMaj μ T τ y p := by
    intro n p hp y' hy'
    have hl0 : 0 ≤ p.1 ^ (2 * μ.re + 2) := Real.rpow_nonneg hp.1.le _
    have htn : 0 ≤ tensorNorm (T (τ + 2 * Real.log p.1) p.2) := Real.sqrt_nonneg _
    by_cases hz : Real.sqrt (p.2 0 ^ 2 + p.2 1 ^ 2) ≤ rOut
    · obtain ⟨hg1, hg2⟩ := hgapU p hp hz y' hy'
      have hne : y' - p.1 • p.2 ≠ 0 := by
        intro h0; rw [h0, norm_zero] at hg2; linarith
      have hw := sepDiff_gapWeight D ‖y - p.1 • p.2‖ ‖y' - p.1 • p.2‖ n hD hg1 hg2
      refine (hpi n p hp y' hne).trans ?_
      unfold sepDiffMaj
      have hC3 : 0 ≤ 3 * C n := by linarith [hC0 n]
      calc 3 * C n * (p.1 ^ (2 * μ.re + 2) * ‖y' - p.1 • p.2‖ ^ (-4 - (n : ℝ)) *
            tensorNorm (T (τ + 2 * Real.log p.1) p.2))
          ≤ 3 * C n * (p.1 ^ (2 * μ.re + 2) * (2 ^ (4 + (n : ℝ)) * D ^ (-(n : ℝ)) *
              ‖y - p.1 • p.2‖ ^ (-4 : ℝ)) * tensorNorm (T (τ + 2 * Real.log p.1) p.2)) := by
            gcongr
        _ = _ := by ring
    · push_neg at hz
      rw [hoff p hz]
      have h0 : iteratedFDeriv ℝ n (0 : Space → Fin 3 → ℂ) y' = 0 := by
        simpa using congrFun (iteratedFDeriv_zero_fun (𝕜 := ℝ) (E := Space) (F := Fin 3 → ℂ) (n := n)) y'
      rw [h0, norm_zero]
      have hTz : T (τ + 2 * Real.log p.1) p.2 = 0 := hT.support _ _ hz
      unfold sepDiffMaj
      rw [hTz]
      simp [tensorNorm]
  have hInt : Integrable (sepDiffMaj μ T τ y) sepDiffRho :=
    h6 μ rOut rIn P T hrO hrr hT τ y hy hfin
  have hLoc : L09.LocDominated sepDiffRho F U := by
    intro n x hx
    refine ⟨U, hU.mem_nhds hx,
      fun p => (3 * C n * 2 ^ (4 + (n : ℝ)) * D ^ (-(n : ℝ))) * sepDiffMaj μ T τ y p,
      hInt.const_mul _, ?_⟩
    filter_upwards [sepDiffRho_ae_mem] with p hp y' hy'
    exact hdom n p hp y' hy'
  have hsmooth : ∀ᵐ p ∂sepDiffRho, ContDiffOn ℝ ∞ (F p) U := by
    filter_upwards [sepDiffRho_ae_mem] with p hp
    exact (contDiff_pi.2 (hsm p hp)).contDiffOn
  have hmeas : ∀ (n : ℕ), ∀ x ∈ U,
      AEStronglyMeasurable (fun p => iteratedFDeriv ℝ n (F p) x) sepDiffRho := by
    intro n x _
    have hR : AEStronglyMeasurable (fun p => ∑ i : Fin 3,
        (ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin n => Space) ℂ
          (Fin 3 → ℂ) (ContinuousLinearMap.single ℝ (fun _ : Fin 3 => ℂ) i))
          (iteratedFDeriv ℝ n (fun y' => F p y' i) x)) sepDiffRho := by
      refine Finset.aestronglyMeasurable_fun_sum _ fun i _ => ?_
      exact (ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin n => Space) ℂ
        (Fin 3 → ℂ) (ContinuousLinearMap.single ℝ (fun _ : Fin 3 => ℂ) i)).continuous
          |>.comp_aestronglyMeasurable (h3 ν μ P rOut T hν hT τ i n x)
    refine hR.congr ?_
    filter_upwards [sepDiffRho_ae_mem] with p hp
    rw [sepDiff_iteratedFDeriv_pi (fun i => hsmAt n p hp x i)]
    rfl
  have hFint : ∀ y' ∈ U, Integrable (fun p => F p y') sepDiffRho := by
    intro y' hy'
    have hm : AEStronglyMeasurable (fun p => F p y') sepDiffRho := by
      have := (continuousMultilinearCurryFin0 ℝ Space (Fin 3 → ℂ)).continuous
        |>.comp_aestronglyMeasurable (hmeas 0 y' hy')
      refine this.congr (Eventually.of_forall fun p => ?_)
      simp
    refine Integrable.mono' (hInt.const_mul (3 * C 0 * 2 ^ (4 + ((0 : ℕ) : ℝ)) *
      D ^ (-((0 : ℕ) : ℝ)))) hm ?_
    filter_upwards [sepDiffRho_ae_mem] with p hp
    rw [← norm_iteratedFDeriv_zero (𝕜 := ℝ)]
    exact hdom 0 p hp y' hy'
  have hEq : (fun y' => sepW ν μ T y' τ) =ᶠ[𝓝 y] fun y' => ∫ p, F p y' ∂sepDiffRho := by
    filter_upwards [hU.mem_nhds hyU] with y' hy' using h5 ν μ T τ y' (hFint y' hy')
  refine ⟨?_, ?_⟩
  · filter_upwards [hU.mem_nhds hyU] with y' hy'
    exact ⟨hFint y' hy', h5 ν μ T τ y' (hFint y' hy')⟩
  · have hd := L09.hasFDerivAt_integral_of_locDominated hU hsmooth hmeas hLoc hyU
    exact (hd.differentiableAt).congr_of_eventuallyEq hEq

end UnforcedLeray.Short.IIIa

end
