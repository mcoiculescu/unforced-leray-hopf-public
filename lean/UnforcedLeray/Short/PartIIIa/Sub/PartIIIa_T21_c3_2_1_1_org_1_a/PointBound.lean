import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_1_org_1_a.Interaction
import UnforcedLeray.Short.PartIIIa.Clock.FrameAmplitudeProof.ComplCoupling.HeatBound
import UnforcedLeray.Short.PartIIIa.Clock.FrameAmplitudeProof.ComplCoupling.EulerSubBound
import UnforcedLeray.Short.PartIIIa.Clock.FrameStableProof.ShortBlock.OscillatorForce
import UnforcedLeray.Short.PartIIIa.Clock.FrameFacts.EBound.Weighted

/-!
# Helper for `PartIII-a:T21/c3/2/1/1/org/1/a`: uniform bound of the damped complement interaction

For each age `r` with `θ(r) ≥ b` the bounded perturbation `movDampedComplInt` of the damped
complement generator (`eq:short-causal-damped-complement`, SP 2920-2925, 2974-2978) is bounded on
`X_{m,d(r)}` by a constant `K_A` independent of `ν`, the train, and `r`:

* the localized interaction `-(K_d W)·∇E_mov` by `cxInter_bound` and the rescaled train bound;
* the finite-rank terms by `PerFrameFacts` (`E`, `Λ`), the dual generator bounds
  `MovLamDualHeatBound`/`MovLamDualEulerSubBound` (`H₀`), the oscillator residual and the
  linearised Euler operator on `E_j` (`K₀`), and the rate `β₀`.

The map `W ↦ movDampedComplInt W` is additive (a.e.), homogeneous, and depends on `W` only through
integrals over the cell.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter UnforcedLeray.Blueprint.Planar
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa.BlockPropagatorInteriorSub.OrgSplit.RelIntA

open UnforcedLeray.Short.IIIa.CompactDuhamelGapSub UnforcedLeray.Short.IIIa.ComplCouplingSub
  UnforcedLeray.Short.IIIa.EulerErrorSub

/-! ### Scalar and norm helpers -/

theorem ofReal_le_of_le_toReal {x c : ℝ} {N : ℝ≥0∞} (hN : N ≠ ⊤) (hc : 0 ≤ c)
    (h : x ≤ c * N.toReal) : ENNReal.ofReal x ≤ ENNReal.ofReal c * N := by
  calc ENNReal.ofReal x ≤ ENNReal.ofReal (c * N.toReal) := ENNReal.ofReal_le_ofReal h
    _ = ENNReal.ofReal c * ENNReal.ofReal N.toReal := ENNReal.ofReal_mul hc
    _ = ENNReal.ofReal c * N := by rw [ENNReal.ofReal_toReal hN]

theorem le_toReal_of_ofReal_le {x c : ℝ} {N : ℝ≥0∞} (hN : N ≠ ⊤) (hc : 0 ≤ c)
    (h : ENNReal.ofReal x ≤ ENNReal.ofReal c * N) : x ≤ c * N.toReal := by
  rw [← ENNReal.ofReal_toReal hN, ← ENNReal.ofReal_mul hc] at h
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hc ENNReal.toReal_nonneg)).1 h

theorem xNorm_const_mul_le {d m : ℝ} (c : ℂ) (f : ℝ × ℝ → ℂ) :
    xNorm d m (fun y => c * f y) ≤ ENNReal.ofReal ‖c‖ * xNorm d m f := by
  unfold xNorm
  have h : ∀ᵐ y ∂(B0579.cellMeasure d m), ‖c * f y‖ ≤ ‖c‖ * ‖f y‖ :=
    Eventually.of_forall fun y => (norm_mul _ _).le
  exact eLpNorm_le_mul_eLpNorm_of_ae_le_mul h 2

theorem xNorm_mul_const_le {d m : ℝ} (c : ℂ) (f : ℝ × ℝ → ℂ) :
    xNorm d m (fun y => f y * c) ≤ ENNReal.ofReal ‖c‖ * xNorm d m f := by
  unfold xNorm
  have h : ∀ᵐ y ∂(B0579.cellMeasure d m), ‖f y * c‖ ≤ ‖c‖ * ‖f y‖ :=
    Eventually.of_forall fun y => by rw [norm_mul, mul_comm]
  exact eLpNorm_le_mul_eLpNorm_of_ae_le_mul h 2

theorem xNorm_add_le {d m : ℝ} {f g : ℝ × ℝ → ℂ}
    (hf : AEStronglyMeasurable f (B0579.cellMeasure d m))
    (hg : AEStronglyMeasurable g (B0579.cellMeasure d m)) :
    xNorm d m (fun y => f y + g y) ≤ xNorm d m f + xNorm d m g := by
  unfold xNorm
  exact eLpNorm_add_le hf hg (by norm_num)

theorem xNorm_neg_eq {d m : ℝ} (f : ℝ × ℝ → ℂ) : xNorm d m (fun y => -f y) = xNorm d m f := by
  unfold xNorm
  exact eLpNorm_neg f 2 _

/-- Bound of a two-term combination `∑ i, c i * f i`. -/
theorem xNorm_sum2_le {d m : ℝ} (c : Fin 2 → ℂ) (f : Fin 2 → ℝ × ℝ → ℂ)
    (hf : ∀ i, AEStronglyMeasurable (f i) (B0579.cellMeasure d m)) (A : ℝ≥0∞)
    (hA : ∀ i, ENNReal.ofReal ‖c i‖ * xNorm d m (f i) ≤ A) :
    xNorm d m (fun y => ∑ i, c i * f i y) ≤ 2 * A := by
  simp only [Fin.sum_univ_two]
  calc xNorm d m (fun y => c 0 * f 0 y + c 1 * f 1 y)
      ≤ xNorm d m (fun y => c 0 * f 0 y) + xNorm d m (fun y => c 1 * f 1 y) :=
        xNorm_add_le ((hf 0).const_mul _) ((hf 1).const_mul _)
    _ ≤ A + A := add_le_add ((xNorm_const_mul_le _ _).trans (hA 0))
          ((xNorm_const_mul_le _ _).trans (hA 1))
    _ = 2 * A := by rw [two_mul]

/-- Bound of a two-term combination `∑ j, f j * c j`. -/
theorem xNorm_sum2_le' {d m : ℝ} (c : Fin 2 → ℂ) (f : Fin 2 → ℝ × ℝ → ℂ)
    (hf : ∀ i, AEStronglyMeasurable (f i) (B0579.cellMeasure d m)) (A : ℝ≥0∞)
    (hA : ∀ i, ENNReal.ofReal ‖c i‖ * xNorm d m (f i) ≤ A) :
    xNorm d m (fun y => ∑ i, f i y * c i) ≤ 2 * A := by
  have h := xNorm_sum2_le c f hf A hA
  have heq : (fun y => ∑ i, f i y * c i) = fun y => ∑ i, c i * f i y := by
    funext y
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [heq]
  exact h

/-! ### Algebraic properties of `movDampedComplInt` -/

theorem movDampedComplInt_add_of (κ : PlanarFrameKernels) (P : PlanarData) {ν : ℝ}
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (r : ℝ) (W₁ W₂ : ℝ × ℝ → ℂ)
    (y : ℝ × ℝ)
    (hkv : ∀ k, kerVelCx (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) (fun z => W₁ z + W₂ z) y k =
      kerVelCx (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) W₁ y k +
        kerVelCx (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) W₂ y k)
    (hH : ∀ i, movH0 κ tr r i (fun z => W₁ z + W₂ z) = movH0 κ tr r i W₁ + movH0 κ tr r i W₂)
    (hΛ : ∀ j, movLamPair κ ν r j (fun z => W₁ z + W₂ z) =
      movLamPair κ ν r j W₁ + movLamPair κ ν r j W₂) :
    movDampedComplInt κ P tr r (fun z => W₁ z + W₂ z) y =
      movDampedComplInt κ P tr r W₁ y + movDampedComplInt κ P tr r W₂ y := by
  unfold movDampedComplInt movLInt movFrameRankPert
  simp only [hkv, hH, hΛ, Fin.sum_univ_two]
  ring

theorem movDampedComplInt_smul (κ : PlanarFrameKernels) (P : PlanarData) {ν : ℝ}
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (r : ℝ) (c : ℂ) (W : ℝ × ℝ → ℂ)
    (y : ℝ × ℝ) :
    movDampedComplInt κ P tr r (fun z => c * W z) y = c * movDampedComplInt κ P tr r W y := by
  have hkv : ∀ k, kerVelCx (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) (fun z => c * W z) y k =
      c * kerVelCx (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) W y k := by
    intro k
    unfold kerVelCx
    rw [← integral_const_mul]
    congr 1
    funext z
    ring
  have hH : ∀ i, movH0 κ tr r i (fun z => c * W z) = c * movH0 κ tr r i W := by
    intro i
    unfold movH0
    have hc : (∫ y in movingCell ν (ν ^ (-2 : ℝ)) r,
        movingPhi ν (fun r' => physLamDual κ tr r' i) r y * (c * W y)) =
        c * ∫ y in movingCell ν (ν ^ (-2 : ℝ)) r,
          movingPhi ν (fun r' => physLamDual κ tr r' i) r y * W y := by
      rw [← integral_const_mul]
      congr 1
      funext z
      ring
    rw [hc]
    ring
  have hΛ : ∀ j, movLamPair κ ν r j (fun z => c * W z) = c * movLamPair κ ν r j W := by
    intro j
    unfold movLamPair
    rw [← integral_const_mul]
    congr 1
    funext z
    ring
  unfold movDampedComplInt movLInt movFrameRankPert
  simp only [hkv, hH, hΛ, Fin.sum_univ_two]
  ring

/-- `movDampedComplInt` depends on `W` only through integrals over the cell. -/
theorem movDampedComplInt_congr (κ : PlanarFrameKernels) (P : PlanarData) {ν : ℝ}
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (r : ℝ) {W₁ W₂ : ℝ × ℝ → ℂ}
    (h : W₁ =ᵐ[volume.restrict (B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)))] W₂) :
    movDampedComplInt κ P tr r W₁ = movDampedComplInt κ P tr r W₂ := by
  have hkv : ∀ y k, kerVelCx (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) W₁ y k =
      kerVelCx (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) W₂ y k := by
    intro y k
    unfold kerVelCx
    refine integral_congr_ae ?_
    filter_upwards [h] with z hz
    rw [hz]
  have hH : ∀ i, movH0 κ tr r i W₁ = movH0 κ tr r i W₂ := by
    intro i
    unfold movH0
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [h] with z hz
    rw [hz]
  have hΛ : ∀ j, movLamPair κ ν r j W₁ = movLamPair κ ν r j W₂ := by
    intro j
    unfold movLamPair
    refine integral_congr_ae ?_
    filter_upwards [h] with z hz
    rw [hz]
  funext y
  unfold movDampedComplInt movLInt movFrameRankPert
  simp only [hkv, hH, hΛ]

/-! ### The rescaled train coefficients -/

theorem trainCoeff_bounds (m : ℝ) :
    ∃ C_T b_T ν_T : ℝ, 0 ≤ C_T ∧ 0 < ν_T ∧
      ∀ ν ∈ Ioc 0 ν_T, ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
        UnforcedLeray.Short.PartI.IsBUCTrain tr →
        ∀ r : ℝ, 0 ≤ r → b_T ≤ clockTheta ν r →
          (∀ (y : ℝ × ℝ) (k : Fin 2), |movingTrainV tr r y k| ≤ C_T) ∧
          IIb.IsCylWeightedCoeff (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m C_T
            (fun y => (movingTrainGradE tr r y 0, movingTrainGradE tr r y 1)) := by
  obtain ⟨b₀, hb⟩ := PerturbDuhamelSub.rescaledTrainBounds_uncond m
  obtain ⟨C, ν₀, hν₀, hC⟩ := hb b₀ le_rfl
  refine ⟨2 * max C 0, b₀, ν₀, by positivity, hν₀, fun ν hν tr htr r hr hθ => ?_⟩
  obtain ⟨hV, hE⟩ := hC ν hν tr htr r hr hθ
  have hCm : C ≤ max C 0 := le_max_left _ _
  have hCm0 : 0 ≤ max C 0 := le_max_right _ _
  refine ⟨fun y k => ?_, ?_, fun y hy => ?_⟩
  · have h0 := hV 0 (by norm_num) y
    rw [norm_iteratedFDeriv_zero] at h0
    calc |movingTrainV tr r y k| = ‖movingTrainV tr r y k‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖movingTrainV tr r y‖ := norm_le_pi_norm _ k
      _ ≤ C := h0
      _ ≤ 2 * max C 0 := by linarith
  · exact (continuous_movingTrainGradE tr hr 0).prodMk (continuous_movingTrainGradE tr hr 1)
  · have h1 := hE 1 (by norm_num) y hy
    rw [norm_iteratedFDeriv_one] at h1
    have hdir : ∀ k : Fin 2, ‖B0579.dir k‖ ≤ 1 := by
      intro k
      fin_cases k <;> simp [B0579.dir]
    have hg : ∀ k : Fin 2, |movingTrainGradE tr r y k| ≤
        ‖fderiv ℝ (movingTrainE tr r) y‖ := by
      intro k
      rw [← DirectEulerSub.pd_movingTrainE_eq_movingTrainGradE tr hν.1 hr k y]
      unfold B0579.pd
      rw [← Real.norm_eq_abs]
      calc ‖fderiv ℝ (movingTrainE tr r) y (B0579.dir k)‖
          ≤ ‖fderiv ℝ (movingTrainE tr r) y‖ * ‖B0579.dir k‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ ‖fderiv ℝ (movingTrainE tr r) y‖ * 1 :=
            mul_le_mul_of_nonneg_left (hdir k) (norm_nonneg _)
        _ = ‖fderiv ℝ (movingTrainE tr r) y‖ := mul_one _
    have hexp : B0579.jb y ^ (m / 2 + 1) = B0579.jb y ^ ((m + 2) / 2) := by
      congr 1
      ring
    have hjb : 0 ≤ B0579.jb y ^ (m / 2 + 1) := Real.rpow_nonneg (B0579.jb_pos y).le _
    calc (|movingTrainGradE tr r y 0| + |movingTrainGradE tr r y 1|) * B0579.jb y ^ (m / 2 + 1)
        ≤ (2 * ‖fderiv ℝ (movingTrainE tr r) y‖) * B0579.jb y ^ (m / 2 + 1) := by
          refine mul_le_mul_of_nonneg_right ?_ hjb
          linarith [hg 0, hg 1]
      _ = 2 * (B0579.jb y ^ ((m + 2) / 2) * ‖fderiv ℝ (movingTrainE tr r) y‖) := by
          rw [hexp]
          ring
      _ ≤ 2 * C := by linarith
      _ ≤ 2 * max C 0 := by linarith

end UnforcedLeray.Short.IIIa.BlockPropagatorInteriorSub.OrgSplit.RelIntA
