import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_8_2_1_2.Statements

/-!
# `newtonCurlTimeComm`: the phase derivative commutes with the Newton curl potential

Proves `NewtonCurlTimeComm` (`Statements.lean`).
Two steps. (a) `∂_τ (N * φ) = N * ∂_τ φ` for the vector Newton potential: the component integral
`z ↦ ∫ N(x) φ(z - (0,x))_i dx` is differentiated under the integral sign in direction `(1,0)`
(`IteratedFDeriv` integral rule of `Lib/Kernels/ParamIntegral.lean`, with the local domination
of `SelectedProjectedPotentialJointSmooth.lean` copied). (b) `∂_τ curl A = curl ∂_τ A` for smooth
`A`, from the symmetry of second derivatives.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.SolApprox

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.B0412 UnforcedLeray.RieszLp
open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PressureAnalysis UnforcedLeray.Kernels
open UnforcedLeray.Blueprint
open NavierStokesR3.ComparisonCutoffs

/-- Local domination and measurability of the Newton parameter integrand (copy of the hypotheses
of `contDiff_newtonSourceParamIntegral`). -/
private theorem nct_hyp {P : ℝ} {D : ℝ × Space → ℝ} (hD : IsPhaseTest P D) :
    (∀ᵐ x ∂(volume : Measure Space), ContDiff ℝ ∞
        (fun p : ℝ × Space => newtonPotential x * D (p - (0, x)))) ∧
    (∀ (n : ℕ) (p : ℝ × Space), AEStronglyMeasurable (fun x : Space =>
        iteratedFDeriv ℝ n (fun q : ℝ × Space => newtonPotential x * D (q - (0, x))) p) volume) ∧
    LocDominated volume
      (fun (x : Space) (p : ℝ × Space) => newtonPotential x * D (p - (0, x))) univ := by
  let F : Space → ℝ × Space → ℝ := fun x p => newtonPotential x * D (p - (0, x))
  have hsmooth : ∀ᵐ x ∂(volume : Measure Space), ContDiff ℝ ∞ (F x) := by
    filter_upwards [] with x
    exact contDiff_const.mul (hD.smooth.comp (by fun_prop))
  have hmeas : ∀ (n : ℕ) (p : ℝ × Space),
      AEStronglyMeasurable (fun x => iteratedFDeriv ℝ n (F x) p) volume := by
    intro n p
    have hcont : Continuous (fun x : Space =>
        iteratedFDeriv ℝ n D (p - (0, x))) :=
      (hD.smooth.continuous_iteratedFDeriv (by exact_mod_cast le_top)).comp (by fun_prop)
    have hmul := aestronglyMeasurable_newtonPotential.smul hcont.aestronglyMeasurable
    refine hmul.congr (Eventually.of_forall fun x => ?_)
    simpa [F, smul_eq_mul] using
      (iteratedFDeriv_newtonSourceIntegrand hD.smooth x n p).symm
  have hdom : LocDominated volume F univ := by
    intro n p hp
    obtain ⟨R, hR⟩ := hD.bounded_support
    let R₀ := max R 0
    let K := R₀ + ‖p.2‖ + 1
    let sourceSet : Set (ℝ × Space) := Set.Icc (p.1 - 1) (p.1 + 1) ×ˢ closedBall 0 R₀
    have hsourceCompact : IsCompact sourceSet :=
      isCompact_Icc.prod (isCompact_closedBall (0 : Space) R₀)
    obtain ⟨B, hB0, hB⟩ := exists_norm_bound_on_compact
      (fun z => iteratedFDeriv ℝ n D z)
      (hD.smooth.continuous_iteratedFDeriv (by exact_mod_cast le_top)) hsourceCompact
    let b : Space → ℝ := fun x => B * (closedBall 0 K).indicator (fun x => |newtonPotential x|) x
    refine ⟨ball p 1, ball_mem_nhds p (by norm_num), b, ?_, Eventually.of_forall fun x q hq => ?_⟩
    · have hN := integrable_newtonPotential_abs_on_closedBall K
      have hb := hN.mul_const B
      exact hb.congr (Eventually.of_forall fun x => by simpa [b, mul_comm])
    · rw [iteratedFDeriv_newtonSourceIntegrand hD.smooth x n q]
      by_cases hx : x ∈ closedBall 0 K
      · have hqnorm : ‖q - p‖ < 1 := by simpa [mem_ball, dist_eq_norm] using hq
        have hfst : |q.1 - p.1| ≤ ‖q - p‖ := by
          have := norm_fst_le (q - p)
          simpa [Real.norm_eq_abs] using this
        have hphase : q.1 ∈ Set.Icc (p.1 - 1) (p.1 + 1) := by
          rw [Set.mem_Icc]
          have habs := abs_lt.mp (lt_of_le_of_lt hfst hqnorm)
          constructor <;> linarith
        have hsource : ‖iteratedFDeriv ℝ n D (q - (0, x))‖ ≤ B := by
          by_cases hy : ‖(q - (0, x)).2‖ ≤ R₀
          · exact hB _ ⟨by simpa using hphase, by simpa using hy⟩
          · rw [iteratedFDeriv_newtonSource_zero R hR n
              (q - (0, x)) (lt_of_not_ge hy)]
            simpa using hB0
        rw [norm_smul, Real.norm_eq_abs]
        calc
          |newtonPotential x| * ‖iteratedFDeriv ℝ n D (q - (0, x))‖ ≤
              |newtonPotential x| * B := mul_le_mul_of_nonneg_left hsource (abs_nonneg _)
          _ = b x := by simp [b, hx, mul_comm]
      · have hxgt : K < ‖x‖ := by
          simpa [K, mem_closedBall, dist_zero_right, not_le] using hx
        have hqnorm : ‖q - p‖ < 1 := by simpa [mem_ball, dist_eq_norm] using hq
        have hysub : ‖q.2 - p.2‖ ≤ ‖q - p‖ := norm_snd_le (q - p)
        have hsourceNorm : R₀ < ‖(q - (0, x)).2‖ := by
          by_contra h
          have hy : ‖q.2 - x‖ ≤ R₀ := le_of_not_gt h
          have hxle : ‖x‖ ≤ ‖q.2‖ + ‖q.2 - x‖ := by
            calc
              ‖x‖ = ‖q.2 - (q.2 - x)‖ := by congr 1; abel
              _ ≤ ‖q.2‖ + ‖q.2 - x‖ := norm_sub_le _ _
          have hqsp : ‖q.2‖ ≤ ‖p.2‖ + 1 := by
            calc
              ‖q.2‖ ≤ ‖p.2‖ + ‖q.2 - p.2‖ := by
                calc ‖q.2‖ = ‖p.2 + (q.2 - p.2)‖ := by congr 1; abel
                  _ ≤ _ := norm_add_le _ _
              _ ≤ ‖p.2‖ + 1 := by nlinarith [hysub, hqnorm]
          linarith [hxle]
        have hzero : iteratedFDeriv ℝ n D (q - (0, x)) = 0 := by
          exact iteratedFDeriv_newtonSource_zero R hR n
            (q - (0, x)) hsourceNorm
        simp [hzero, b, hx]
  exact ⟨hsmooth, hmeas, hdom⟩

/-- Derivative of the Newton parameter integral: differentiation under the integral sign. -/
private theorem nct_fderiv {P : ℝ} {D : ℝ × Space → ℝ} (hD : IsPhaseTest P D)
    (z v : ℝ × Space) :
    fderiv ℝ (fun w : ℝ × Space => ∫ x, newtonPotential x * D (w - (0, x))) z v =
      ∫ x, newtonPotential x * fderiv ℝ D (z - (0, x)) v := by
  obtain ⟨hsmooth, hmeas, hdom⟩ := nct_hyp hD
  have h1 : iteratedFDeriv ℝ 1 (fun w : ℝ × Space => ∫ x, newtonPotential x * D (w - (0, x))) z
      = ∫ x, iteratedFDeriv ℝ 1 (fun q : ℝ × Space => newtonPotential x * D (q - (0, x))) z :=
    iteratedFDeriv_integral_eq isOpen_univ hsmooth hmeas hdom 1 (mem_univ z)
  have h2 : fderiv ℝ (fun w : ℝ × Space => ∫ x, newtonPotential x * D (w - (0, x))) z v =
      iteratedFDeriv ℝ 1 (fun w : ℝ × Space => ∫ x, newtonPotential x * D (w - (0, x))) z ![v] := by
    rw [iteratedFDeriv_one_apply]
    rfl
  rw [h2, h1]
  have h3 := ContinuousLinearMap.integral_comp_comm
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 1 => ℝ × Space) ℝ ![v])
    (hdom.integrable hmeas 1 (mem_univ z))
  have h4 : (∫ x, iteratedFDeriv ℝ 1 (fun q : ℝ × Space => newtonPotential x * D (q - (0, x))) z)
      ![v] = ∫ x, iteratedFDeriv ℝ 1 (fun q : ℝ × Space => newtonPotential x * D (q - (0, x)))
        z ![v] := h3.symm
  rw [h4]
  apply integral_congr_ae
  filter_upwards with x
  rw [iteratedFDeriv_newtonSourceIntegrand hD.smooth x 1 z]
  simp [iteratedFDeriv_one_apply, smul_eq_mul]

/-- Derivative of a smooth map followed by a coordinate. -/
private theorem nct_fderiv_component {g : ℝ × Space → Space} (hg : Differentiable ℝ g)
    (i : Fin 3) (y v : ℝ × Space) :
    fderiv ℝ (fun x : ℝ × Space => g x i) y v = fderiv ℝ g y v i := by
  have hB : HasFDerivAt (fun x : ℝ × Space => (EuclideanSpace.proj i : Space →L[ℝ] ℝ) (g x))
      ((EuclideanSpace.proj i : Space →L[ℝ] ℝ).comp (fderiv ℝ g y)) y :=
    (EuclideanSpace.proj i : Space →L[ℝ] ℝ).hasFDerivAt.comp y (hg y).hasFDerivAt
  have hfun : (fun x : ℝ × Space => g x i) =
      fun x : ℝ × Space => (EuclideanSpace.proj i : Space →L[ℝ] ℝ) (g x) := rfl
  rw [hfun, hB.fderiv]
  rfl

/-- Component formula of the joint vector Newton potential. -/
private theorem nct_pot_apply (Ψ : ℝ × Space → Space) (z : ℝ × Space) (i : Fin 3) :
    projectedTestNewtonVectorPotential Ψ z i =
      ∫ x, newtonPotential x * Ψ (z - (0, x)) i := by
  unfold projectedTestNewtonVectorPotential
  rw [sum_smul_coordinateVector_apply]

/-- Step (a): `∂_τ (N * φ) = N * ∂_τ φ`. -/
private theorem nct_dtau {P : ℝ} (φ : ℝ × Space → Space) (hφ : IsPhaseTest P φ) :
    dτ (projectedTestNewtonVectorPotential φ) = projectedTestNewtonVectorPotential (dτ φ) := by
  have hA := contDiff_projectedTestNewtonVectorPotential hφ
  have hAd : Differentiable ℝ (projectedTestNewtonVectorPotential φ) := hA.differentiable (by simp)
  have hφd : Differentiable ℝ φ := hφ.smooth.differentiable (by simp)
  funext z
  ext i
  have hφi : IsPhaseTest P (fun q : ℝ × Space => φ q i) :=
    hφ.clm_comp (EuclideanSpace.proj i : Space →L[ℝ] ℝ)
  have hLi : dτ (projectedTestNewtonVectorPotential φ) z i =
      fderiv ℝ (fun w => projectedTestNewtonVectorPotential φ w i) z (1, 0) := by
    unfold dτ
    exact (nct_fderiv_component hAd i z (1, 0)).symm
  have hcomp : (fun w : ℝ × Space => projectedTestNewtonVectorPotential φ w i) =
      fun w => ∫ x, newtonPotential x * (fun q : ℝ × Space => φ q i) (w - (0, x)) := by
    funext w
    exact nct_pot_apply φ w i
  rw [hLi, hcomp, nct_fderiv hφi z (1, 0), nct_pot_apply (dτ φ) z i]
  apply integral_congr_ae
  filter_upwards with x
  rw [nct_fderiv_component hφd i (z - (0, x)) (1, 0)]
  rfl

/-- The derivative of a `C²` map in a fixed direction. -/
private theorem nct_fderiv_clm_const {A : ℝ × Space → Space} (hA : ContDiff ℝ ∞ A)
    (z v w : ℝ × Space) :
    fderiv ℝ (fun u : ℝ × Space => fderiv ℝ A u w) z v = fderiv ℝ (fderiv ℝ A) z v w := by
  have hH : ContDiff ℝ ∞ (fderiv ℝ A) := hA.fderiv_right (m := ∞) (by simp)
  have hc : DifferentiableAt ℝ (fderiv ℝ A) z := (hH.differentiable (by simp)) z
  rw [fderiv_clm_apply hc (differentiableAt_const w)]
  simp

/-- Step (b): `∂_τ curl A = curl ∂_τ A` for a smooth field `A`. -/
private theorem nct_curl_comm {A : ℝ × Space → Space} (hA : ContDiff ℝ ∞ A) :
    dτ (spatialCurlST A) = spatialCurlST (dτ A) := by
  funext z
  have hH : ContDiff ℝ ∞ (fderiv ℝ A) := hA.fderiv_right (m := ∞) (by simp)
  have hHd : Differentiable ℝ (fderiv ℝ A) := hH.differentiable (by simp)
  have hsymm : ∀ v w : ℝ × Space,
      fderiv ℝ (fderiv ℝ A) z v w = fderiv ℝ (fderiv ℝ A) z w v :=
    fun v w => (hA.contDiffAt.isSymmSndFDerivAt (by simp)) v w
  have hS : spatialCurlST A = fun w => ∑ j : Fin 3,
      UnforcedLeray.L09.crossCLM (coordinateVector j) (fderiv ℝ A w (0, coordinateVector j)) := by
    funext w
    simp only [spatialCurlST, UnforcedLeray.L09.crossCLM_apply]
  have hL : dτ (spatialCurlST A) z = ∑ j : Fin 3,
      UnforcedLeray.L09.crossCLM (coordinateVector j)
        (fderiv ℝ (fderiv ℝ A) z (1, 0) (0, coordinateVector j)) := by
    rw [hS]
    unfold dτ
    have hsumd : ∀ j ∈ (Finset.univ : Finset (Fin 3)),
        DifferentiableAt ℝ (fun w : ℝ × Space =>
          UnforcedLeray.L09.crossCLM (coordinateVector j) (fderiv ℝ A w (0, coordinateVector j))) z :=
      fun j _ => (UnforcedLeray.L09.crossCLM (coordinateVector j)).differentiableAt.comp z
        ((hHd z).clm_apply (differentiableAt_const _))
    rw [fderiv_fun_sum hsumd, ContinuousLinearMap.sum_apply]
    apply Finset.sum_congr rfl
    intro j _
    have hg : DifferentiableAt ℝ (fun w : ℝ × Space => fderiv ℝ A w (0, coordinateVector j)) z :=
      (hHd z).clm_apply (differentiableAt_const _)
    have hfd : fderiv ℝ (fun w : ℝ × Space => fderiv ℝ A w (0, coordinateVector j)) z (1, 0) =
        fderiv ℝ (fderiv ℝ A) z (1, 0) (0, coordinateVector j) :=
      nct_fderiv_clm_const hA z (1, 0) (0, coordinateVector j)
    have hcomp := ((UnforcedLeray.L09.crossCLM (coordinateVector j)).hasFDerivAt.comp z
      hg.hasFDerivAt).fderiv
    rw [show (fun w : ℝ × Space => UnforcedLeray.L09.crossCLM (coordinateVector j)
        (fderiv ℝ A w (0, coordinateVector j))) =
        (UnforcedLeray.L09.crossCLM (coordinateVector j)) ∘
          (fun w : ℝ × Space => fderiv ℝ A w (0, coordinateVector j)) from rfl, hcomp]
    rw [ContinuousLinearMap.comp_apply, hfd]
  have hR : spatialCurlST (dτ A) z = ∑ j : Fin 3,
      UnforcedLeray.L09.crossCLM (coordinateVector j)
        (fderiv ℝ (fderiv ℝ A) z (0, coordinateVector j) (1, 0)) := by
    unfold spatialCurlST
    apply Finset.sum_congr rfl
    intro j _
    rw [UnforcedLeray.L09.crossCLM_apply]
    congr 1
    have hdA : dτ A = fun w => fderiv ℝ A w (1, 0) := rfl
    rw [hdA]
    exact nct_fderiv_clm_const hA z (0, coordinateVector j) (1, 0)
  rw [hL, hR]
  apply Finset.sum_congr rfl
  intro j _
  rw [hsymm (1, 0) (0, coordinateVector j)]

theorem newtonCurlTimeComm : UnforcedLeray.Short.PartIIIb.Concrete.SolApprox.NewtonCurlTimeComm := by
  intro P φ hφ
  unfold projectedTestNewtonVectorPotentialCurl
  rw [nct_curl_comm (contDiff_projectedTestNewtonVectorPotential hφ), nct_dtau φ hφ]

end UnforcedLeray.Short.PartIIIb.Concrete.SolApprox
