import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_3_1
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.AdjWeakChi.XNorm
import UnforcedLeray.Short.PartIIIa.Clock.FrameStableProof.ShortBlock.PerturbDuhamel.WeakFlowDuhamel.Gronwall

/-!
# Part III-a, task `PartIII-a:T21/c3/3/1/1` (`WeakFlowDuhamel.lean`, SP 2919-2925, 2937-2958, 2982-2988)

Source of record: `the November 2 reference manuscript` (SP), lines 2919-2925,
2937-2958, and 2982-2988 (`eq:short-causal-damped-complement`, `eq:short-causal-free-moving`,
`eq:short-causal-stable-moving`).

## Mathematical content and proved infrastructure

This module develops the uniform parameter-selection, constant-combination, free moving energy
rate specialization, integrating-factor calculus, and `ENNReal` Duhamel assembly for
`WeakFlowComplPerturbDuhamel κ` (`PartIII-a:T21/c3/3/1/1`):

1. **`b`-independent extraction of `C_loc ≥ 0` from `AdjointLocalizedBound m` and complement
   pairing bound (`exists_unif_adjointLocalized_bound`, `ofReal_norm_integral_chi_compl_le`,
   SP 2953-2958, 3052-3058)**:
   * Because `b` enters `AdjointLocalizedBound m` only through the lower bound `b ≤ clockTheta ν r`,
     instantiating `AdjointLocalizedBound m` once at `b_loc = max 1 b₀` produces a single constant
     `C_loc ≥ 0` and threshold `ν_loc > 0` valid for all `b ≥ b_loc`.
   * Combines `ComplCouplingSub.memLp_compl` with `PerturbDuhamelSub.ofReal_norm_integral_chi_le`
     to bound the cell pairing of the adjoint localized interaction density `χ` against
     `compl F w r` along any `IsLinearisedFlow`.

2. **`b`-uniform free moving energy rate `normGrowthConst m + 1` (`freeMovingEnergy_rate_le_add_one`,
   SP 2937-2958)**:
   * Combines `FreeMovingEnergy` at `ε = 1` with `PerturbDuhamelSub.normGrowthConst_div_add_one_le`
     (`normGrowthConst m / b + 1 ≤ normGrowthConst m + 1` for `1 ≤ b`) and `movingZ_mono` to obtain
     the `b`-uniform exponential growth rate `normGrowthConst m + 1` on every sub-interval
     `[s₁, s₂] ⊆ [t₁, t₂]`.

3. **Combined perturbation rate `C_pert = C_loc + C_H0`, `μ_raw = normGrowthConst m + 1 + C_pert`,
   and integrating-factor identities (`mu_raw_pos`, `ofReal_add_mul_xNorm`,
   `xNorm_add_loc_and_complCoupling_le`, `exp_mu_raw_split`, `hasDerivAt_exp_mu_raw`,
   `lintegral_exp_mu_raw`)**:
   * Combines any localized interaction term bounded by `C_loc` with
     `complFiniteRankCoupling F r (movH0 κ tr r · (compl F w r))` bounded by `C_H0` into a single
     perturbation rate `C_pert = C_loc + C_H0`.
   * Specializes the moving-time integrating factor calculus to `μ_raw = normGrowthConst m + 1 + C_pert`.

4. **Mode-forcing scalar homogeneity and `ENNReal` Duhamel/Gronwall integral assembly
   (`xNorm_smul_complModeForce`, `duhamel_ennreal_bound_of_split`)**:
   * Scalar homogeneity of `xNorm d m` on `complModeForce κ P F tr r j` and monotonic `ENNReal`
     Lebesgue integral assembly on `Ioc t₁ t₂`.

5. **Analytical sub-leaf `WeakFlowProjectedGronwall κ` and conditional assembly
   `weakFlowComplPerturbDuhamel_of`**:
   * `WeakFlowProjectedGronwall κ`: weak-flow testing of `compl F w r = frameProj F r (movingW ν w r)`
     along `IsLinearisedFlow` combining the `normGrowthConst m + 1` free moving energy bound, the
     `C_loc` adjoint localized interaction bound, and the `C_H0` finite-rank coupling bound into the
     homogeneous + forcing Duhamel split at `t₂`.
   * `weakFlowComplPerturbDuhamel_of`: combines `WeakFlowProjectedGronwall κ` with
     `exists_unif_adjointLocalized_bound`, `PerturbDuhamelSub.xNorm_complCoupling_movH0_le_const`,
     `freeMovingEnergy_rate_le_add_one`, and `duhamel_ennreal_bound_of_split` to establish
     `WeakFlowComplPerturbDuhamel κ` with zero sorry.

6. **Free-rate reduction (`exists_bound_xNorm_compl`, `ComplFreeRateDuhamel`,
   `weakFlowProjectedGronwall_of_freeRate`, `weakFlowComplPerturbDuhamel_of_freeRate`)**:
   * `exists_bound_xNorm_compl`: `r ↦ ‖compl F w r‖_{X_{m,d(r)}}` is bounded on `[t₁, t₂]`
     (strong continuity of the weak flow, `xNorm_JscaleInv_le`, `xNorm_frameProj_le`).
   * `ComplFreeRateDuhamel κ` (the remaining analytic leaf): the Duhamel inequality of the
     complement relative to the free moving evolution, i.e. at the free rate
     `μ₀ = normGrowthConst m + 1`, with the perturbation `L_int - E H₀` entering through
     `(C_loc + C_H0) ‖compl F w r‖` and the mode forcing through a measurable minorant `G` of
     `∑_j |α_j(r)| ‖complModeForce_j(r)‖` (SP 2919-2925, 2937-2958).
   * `weakFlowProjectedGronwall_of_freeRate`: the moving-time Gronwall lemma
     (`WeakFlowGronwallSub.gronwall_movingZ`, helper `WeakFlowDuhamel/Gronwall.lean`) turns the
     free-rate inequality into `WeakFlowProjectedGronwall κ` with
     `μ_raw = normGrowthConst m + 1 + (C_loc + C_H0)`; hence
     `ComplFreeRateDuhamel κ → WeakFlowComplPerturbDuhamel κ`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Blueprint.Planar
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

open FrameShortBlockSub ComplCouplingSub PerturbDuhamelSub

namespace WeakFlowDuhamelSub

/-! ## 1. `b`-independent extraction of `C_loc ≥ 0` from `AdjointLocalizedBound m` -/

/-- **Uniform `b`-independent extraction of `C_loc ≥ 0` from `AdjointLocalizedBound m`**
(SP 2953-2958, 3052-3058): instantiating `AdjointLocalizedBound m` at `b_loc = max 1 b₀` yields a
fixed constant `C_loc ≥ 0` and threshold `b_loc ≥ 1` (both independent of `b`) such that for every
`b ≥ b_loc`, there exists `ν_loc > 0` for which the adjoint localized interaction `χ` satisfies both
the `H^1_{-m, d(r)}` and `X_{-m, d(r)}` bounds with constant `C_loc`. -/
theorem exists_unif_adjointLocalized_bound {m : ℝ} (hAdj : AdjointLocalizedBound m) :
    ∃ C_loc b_loc : ℝ, 0 ≤ C_loc ∧ 1 ≤ b_loc ∧
      ∀ b : ℝ, b_loc ≤ b →
        ∃ ν_loc : ℝ, 0 < ν_loc ∧
          ∀ ν ∈ Ioc 0 ν_loc,
            ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
              PartI.IsBUCTrain tr →
              ∀ r : ℝ, 0 ≤ r → b ≤ clockTheta ν r →
              ∀ Φ : ℝ × ℝ → ℂ,
                let d := cellLen (ν ^ (-2 : ℝ)) (clockA ν r)
                MemLp Φ 2 (B0579.cellMeasure d (-m)) →
                ∃ (χ : ℝ × ℝ → ℂ) (gχ : Fin 2 → ℝ × ℝ → ℂ),
                  (∀ j, HasWeakCellDerivC d j χ (gχ j)) ∧
                  h1Norm d m χ gχ ≤ ENNReal.ofReal C_loc * xNorm d (-m) Φ ∧
                  xNorm d (-m) χ ≤ ENNReal.ofReal C_loc * xNorm d (-m) Φ ∧
                  ∀ ψ uψ, B0579.IsCylTest d ψ → IsKernelBiotSavart d ψ uψ →
                    ∫ y in B0579.cell d, χ y * (ψ y : ℂ) =
                      ∫ y in B0579.cell d,
                        Φ y * ((uψ y 0 * B0579.pd 0 (movingTrainE tr r) y +
                          uψ y 1 * B0579.pd 1 (movingTrainE tr r) y : ℝ) : ℂ) := by
  obtain ⟨b₀, hb₀⟩ := hAdj
  set b_loc : ℝ := max 1 b₀
  have hb_loc1 : 1 ≤ b_loc := le_max_left 1 b₀
  obtain ⟨C, ν_loc, hν_loc, hLoc⟩ := hb₀ b_loc (le_max_right 1 b₀)
  set C_loc : ℝ := max C 0
  have hC_loc0 : 0 ≤ C_loc := le_max_right C 0
  have hC_le : ENNReal.ofReal C ≤ ENNReal.ofReal C_loc :=
    ENNReal.ofReal_le_ofReal (le_max_left C 0)
  refine ⟨C_loc, b_loc, hC_loc0, hb_loc1, fun b hb => ⟨ν_loc, hν_loc, ?_⟩⟩
  intro ν hν tr hbuc r hr hθ Φ d hΦ
  obtain ⟨χ, gχ, hder, hh1, hdual⟩ := hLoc ν hν tr hbuc r hr (hb.trans hθ) Φ hΦ
  have hh1' : h1Norm d m χ gχ ≤ ENNReal.ofReal C_loc * xNorm d (-m) Φ :=
    hh1.trans (mul_le_mul_of_nonneg_right hC_le zero_le)
  have hx_le : xNorm d (-m) χ ≤ ENNReal.ofReal C_loc * xNorm d (-m) Φ :=
    (xNorm_le_h1Norm d m χ gχ).trans hh1'
  exact ⟨χ, gχ, hder, hh1', hx_le, hdual⟩

/-- Pairing bound of an adjoint localized interaction density `χ` against `compl F w r` along any
weak linearised flow `IsLinearisedFlow`. -/
theorem ofReal_norm_integral_chi_compl_le {ν m b K t₁ r C_loc : ℝ}
    (F : MovingFrame ν (ν ^ (-2 : ℝ)) m b K)
    (hm : 8 < m) (hν : 0 < ν) (ht₁ : 0 ≤ t₁) (htr : t₁ ≤ r) (hbr : b ≤ clockTheta ν r)
    {tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))}
    {f : ℝ × ℝ → ℂ} {w : ℝ → ℝ × ℝ → ℂ} {u : ℝ → ℝ × ℝ → Fin 2 → ℂ}
    (hw : IsLinearisedFlow ν (ν ^ (-2 : ℝ)) m tr t₁ f w u)
    {χ Φ : ℝ × ℝ → ℂ}
    (hχ : MemLp χ 2 (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) (-m)))
    (hx : xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) (-m) χ ≤
      ENNReal.ofReal C_loc * xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) (-m) Φ) :
    ENNReal.ofReal ‖∫ y in movingCell ν (ν ^ (-2 : ℝ)) r, χ y * compl F w r y‖ ≤
      ENNReal.ofReal C_loc *
        xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) (-m) Φ *
        xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m (compl F w r) := by
  have hm0 : 0 ≤ m := by linarith
  have hcompl : MemLp (compl F w r) 2
      (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m) :=
    memLp_compl F hm0 hν ht₁ htr hbr hw
  exact ofReal_norm_integral_chi_le hχ hcompl hx

/-! ## 2. `b`-uniform free moving energy bound at rate `normGrowthConst m + 1` -/

/-- **`b`-uniform free moving energy bound at rate `normGrowthConst m + 1`** (SP 2937-2958):
combining `FreeMovingEnergy` at `ε = 1` with `normGrowthConst_div_add_one_le`
(`normGrowthConst m / b + 1 ≤ normGrowthConst m + 1` for `1 ≤ b`) yields a threshold `b_free ≥ 1`
such that for every `b ≥ b_free`, any free cylinder flow `IsFreeCylFlow m tr s₁ f₀ ω₀` on
`[s₁, s₂]` with `b ≤ clockTheta ν s₂` satisfies the moving `X_{m, d}` bound with `b`-independent
exponential rate `normGrowthConst m + 1`. -/
theorem freeMovingEnergy_rate_le_add_one (hFree : FreeMovingEnergy) {m : ℝ} (hm : 8 < m) :
    ∃ b_free : ℝ, 1 ≤ b_free ∧
      ∀ b : ℝ, b_free ≤ b →
        ∃ ν_free : ℝ, 0 < ν_free ∧
          ∀ ν ∈ Ioc 0 ν_free,
            ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
              UnforcedLeray.Short.PartI.IsBUCTrain tr →
              ∀ s₁ s₂ : ℝ, 0 ≤ s₁ → s₁ ≤ s₂ → b ≤ clockTheta ν s₂ →
                ∀ f₀ : B0579.Plane → ℝ, B0579.IsCylTest (ν ^ (-2 : ℝ)) f₀ →
                  ∀ ω₀ : ℝ → B0579.Plane → ℝ,
                    UnforcedLeray.Short.IIb.IsFreeCylFlow m tr s₁ f₀ ω₀ →
                    xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν s₂)) m
                        (JscaleInv (clockA ν s₂) (fun x => ((ω₀ s₂ x : ℝ) : ℂ))) ≤
                      ENNReal.ofReal
                          (Real.exp ((normGrowthConst m + 1) * (movingZ ν s₂ - movingZ ν s₁))) *
                        xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν s₁)) m
                          (JscaleInv (clockA ν s₁) (fun x => ((f₀ x : ℝ) : ℂ))) := by
  obtain ⟨b_f, hFreeB⟩ := hFree m hm 1 zero_lt_one
  refine ⟨max 1 b_f, le_max_left 1 b_f, fun b hb => ?_⟩
  have hb1 : 1 ≤ b := (le_max_left 1 b_f).trans hb
  obtain ⟨ν_free, hν_free, H⟩ := hFreeB b ((le_max_right 1 b_f).trans hb)
  refine ⟨ν_free, hν_free, fun ν hν tr htr s₁ s₂ hs₁ hs₁₂ hbs₂ f₀ hf₀ ω₀ hω₀ => ?_⟩
  have hm0 : 0 ≤ m := by linarith
  have hbound := H ν hν tr htr s₁ s₂ hs₁ hs₁₂ hbs₂ f₀ hf₀ ω₀ hω₀
  have hrate : normGrowthConst m / b + 1 ≤ normGrowthConst m + 1 :=
    normGrowthConst_div_add_one_le hm0 hb1
  have hdz : 0 ≤ movingZ ν s₂ - movingZ ν s₁ :=
    sub_nonneg.2 (FrameStableSub.movingZ_le_movingZ hν.1 hs₁ hs₁₂)
  have hexp :
      Real.exp ((normGrowthConst m / b + 1) * (movingZ ν s₂ - movingZ ν s₁)) ≤
        Real.exp ((normGrowthConst m + 1) * (movingZ ν s₂ - movingZ ν s₁)) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hrate hdz)
  exact hbound.trans (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hexp) zero_le)

/-! ## 3. Combined perturbation rate `C_pert = C_loc + C_H0` and integrating-factor calculus -/

/-- Positivity of the raw complement growth rate `μ_raw = normGrowthConst m + 1 + C_pert` for
`8 < m` and `0 ≤ C_pert`. -/
theorem mu_raw_pos {m C_pert : ℝ} (hm : 8 < m) (hC : 0 ≤ C_pert) :
    0 < normGrowthConst m + 1 + C_pert := by
  have hm0 : 0 ≤ m := by linarith
  have h0 : 0 ≤ normGrowthConst m := normGrowthConst_nonneg hm0
  linarith

/-- Additivity of `ENNReal.ofReal` coefficients on a common `ℝ≥0∞` factor. -/
theorem ofReal_add_mul_xNorm {C₁ C₂ : ℝ} (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (X : ℝ≥0∞) :
    ENNReal.ofReal C₁ * X + ENNReal.ofReal C₂ * X = ENNReal.ofReal (C₁ + C₂) * X := by
  rw [← add_mul, ENNReal.ofReal_add hC₁ hC₂]

/-- Triangle inequality combining a localized perturbation field `L_loc` (bounded by `C_loc`) and
the finite-rank coupling `complFiniteRankCoupling F r (movH0 κ tr r · (compl F w r))` (bounded by
`C_H0`) into a single perturbation bound with constant `C_pert = C_loc + C_H0`. -/
theorem xNorm_add_loc_and_complCoupling_le (κ : PlanarFrameKernels)
    {ν m b K r C_loc C_H0 : ℝ}
    (F : MovingFrame ν (ν ^ (-2 : ℝ)) m b K)
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)))
    (w : ℝ → ℝ × ℝ → ℂ)
    (hr : 0 ≤ r) (hbr : b ≤ clockTheta ν r)
    (hC_loc : 0 ≤ C_loc) (hC_H0 : 0 ≤ C_H0)
    {L_loc : ℝ × ℝ → ℂ}
    (hL_meas : AEStronglyMeasurable L_loc
      (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m))
    (hL_bdd : xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m L_loc ≤
      ENNReal.ofReal C_loc * xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m (compl F w r))
    (hH0_bdd : xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m
        (complFiniteRankCoupling F r (movH0 κ tr r · (compl F w r))) ≤
      ENNReal.ofReal C_H0 * xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m (compl F w r)) :
    xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m
        (fun y => L_loc y + complFiniteRankCoupling F r (movH0 κ tr r · (compl F w r)) y) ≤
      ENNReal.ofReal (C_loc + C_H0) *
        xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m (compl F w r) := by
  set d := cellLen (ν ^ (-2 : ℝ)) (clockA ν r)
  have hH0_meas := aesm_complFiniteRankCoupling F hr hbr (movH0 κ tr r · (compl F w r))
  have htri :
      xNorm d m (fun y => L_loc y + complFiniteRankCoupling F r (movH0 κ tr r · (compl F w r)) y) ≤
        xNorm d m L_loc +
          xNorm d m (complFiniteRankCoupling F r (movH0 κ tr r · (compl F w r))) :=
    eLpNorm_add_le hL_meas hH0_meas (by norm_num)
  calc xNorm d m (fun y => L_loc y + complFiniteRankCoupling F r (movH0 κ tr r · (compl F w r)) y)
      ≤ ENNReal.ofReal C_loc * xNorm d m (compl F w r) +
          ENNReal.ofReal C_H0 * xNorm d m (compl F w r) :=
        htri.trans (add_le_add hL_bdd hH0_bdd)
    _ = ENNReal.ofReal (C_loc + C_H0) * xNorm d m (compl F w r) :=
        ofReal_add_mul_xNorm hC_loc hC_H0 _

/-- Factorization of the raw exponential factor into the free moving growth factor and the
perturbation Gronwall factor. -/
theorem exp_mu_raw_split (m C_pert Δz : ℝ) :
    Real.exp ((normGrowthConst m + 1 + C_pert) * Δz) =
      Real.exp ((normGrowthConst m + 1) * Δz) * Real.exp (C_pert * Δz) := by
  rw [← Real.exp_add]
  congr 1
  ring

/-- Age derivative of the integrating factor `r ↦ Real.exp (μ_raw * (movingZ ν t₂ - movingZ ν r))`
for `μ_raw = normGrowthConst m + 1 + C_pert`. -/
theorem hasDerivAt_exp_mu_raw {ν m C_pert t₂ r : ℝ} (hν : 0 < ν) (hr : 0 ≤ r) :
    let μ_raw := normGrowthConst m + 1 + C_pert
    HasDerivAt (fun s => Real.exp (μ_raw * (movingZ ν t₂ - movingZ ν s)))
      (-μ_raw * (clockA ν r) ^ (-2 : ℝ) * Real.exp (μ_raw * (movingZ ν t₂ - movingZ ν r))) r :=
  hasDerivAt_exp_movingZ_sub t₂ (normGrowthConst m + 1 + C_pert) hν hr

/-- Exact `ℝ≥0∞` Lebesgue integral of the `μ_raw` integrating factor derivative on `Ioc t₁ t₂`. -/
theorem lintegral_exp_mu_raw {ν m C_pert t₁ t₂ : ℝ}
    (hm : 8 < m) (hC : 0 ≤ C_pert) (hν : 0 < ν) (ht₁ : 0 ≤ t₁) (h12 : t₁ ≤ t₂) :
    let μ_raw := normGrowthConst m + 1 + C_pert
    (∫⁻ r in Ioc t₁ t₂,
      ENNReal.ofReal
        (μ_raw * (clockA ν r) ^ (-2 : ℝ) * Real.exp (μ_raw * (movingZ ν t₂ - movingZ ν r)))) =
      ENNReal.ofReal (Real.exp (μ_raw * (movingZ ν t₂ - movingZ ν t₁)) - 1) :=
  lintegral_mul_exp_movingZ_sub (mu_raw_pos hm hC).le hν ht₁ h12

/-! ## 4. Mode-forcing scalar homogeneity and `ENNReal` Duhamel/Gronwall integral assembly -/

/-- Scalar homogeneity of `xNorm d m` on `complModeForce`:
`xNorm d m (fun y => a * complModeForce κ P F tr r j y) = ENNReal.ofReal ‖a‖ * xNorm d m (complModeForce κ P F tr r j)`. -/
theorem xNorm_smul_complModeForce (κ : PlanarFrameKernels) (P : PlanarData)
    {ν m b K : ℝ} (F : MovingFrame ν (ν ^ (-2 : ℝ)) m b K)
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (d r : ℝ) (j : Fin 2) (a : ℂ) :
    xNorm d m (fun y => a * complModeForce κ P F tr r j y) =
      ENNReal.ofReal ‖a‖ * xNorm d m (complModeForce κ P F tr r j) := by
  unfold xNorm
  have hsmul : (fun y => a * complModeForce κ P F tr r j y) =
      a • complModeForce κ P F tr r j := rfl
  rw [hsmul, eLpNorm_const_smul, ofReal_norm]

/-- **Abstract `ENNReal` Duhamel/Gronwall assembly on `[t₁, t₂]`**:
If `xNorm d₂ m V₂ ≤ H + ∫⁻ r in Ioc t₁ t₂, G r`, where `H` is bounded by the homogeneous `μ_raw`
exponential term and `G r` is bounded on `Ioc t₁ t₂` by the `μ_raw`-weighted mode-forcing sum, then
`V₂` satisfies the Duhamel inequality of `ShortComplPerturbDuhamel`. -/
theorem duhamel_ennreal_bound_of_split
    {t₁ t₂ d₁ d₂ m : ℝ} {V₁ V₂ : ℝ × ℝ → ℂ}
    {H : ℝ≥0∞} {G : ℝ → ℝ≥0∞}
    {homFactor : ℝ} {forceFactor : ℝ → ℝ} {forceSum : ℝ → ℝ≥0∞}
    (hsplit : xNorm d₂ m V₂ ≤ H + ∫⁻ r in Ioc t₁ t₂, G r)
    (hH : H ≤ ENNReal.ofReal homFactor * xNorm d₁ m V₁)
    (hG : ∀ r ∈ Ioc t₁ t₂,
      G r ≤ ENNReal.ofReal (forceFactor r) * forceSum r) :
    xNorm d₂ m V₂ ≤
      ENNReal.ofReal homFactor * xNorm d₁ m V₁ +
        ∫⁻ r in Ioc t₁ t₂, ENNReal.ofReal (forceFactor r) * forceSum r := by
  refine hsplit.trans (add_le_add hH (lintegral_mono_ae ?_))
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
  exact hG r hr

/-! ## 5. Analytical sub-leaf `WeakFlowProjectedGronwall` and conditional assembly -/

/-- **Sub-leaf (`WeakFlowProjectedGronwall`, SP 2919-2925, 2937-2958, 2982-2988)**:
Along any weak linearised flow `IsLinearisedFlow ν (ν ^ (-2 : ℝ)) m tr t₁ f w u` with
`HasZeroCirculation (ν ^ (-2 : ℝ)) f` on `[t₁, t₂]` with `1 ≤ b ≤ clockTheta ν t₂`, if:
1. every free cylinder flow on any sub-interval `[s₁, s₂] ⊆ [t₁, t₂]` satisfies the moving energy
   bound with rate `normGrowthConst m + 1`,
2. at every `r ∈ Icc t₁ t₂`, the adjoint localized interaction satisfies the `H^1_{-m, d(r)}` and
   `X_{-m, d(r)}` duality bound with constant `C_loc ≥ 0`, and
3. at every `r ∈ Icc t₁ t₂`, the finite-rank coupling
   `complFiniteRankCoupling F r (movH0 κ tr r · (compl F w r))` is bounded in `X_{m, d(r)}` by
   `C_H0 * xNorm d(r) m (compl F w r)`,
then weak-flow testing of `compl F w r = frameProj F r (movingW ν w r)` with the integrating factor
`Real.exp (μ_raw * (movingZ ν t₂ - movingZ ν r))` (`μ_raw = normGrowthConst m + 1 + (C_loc + C_H0)`)
splits `xNorm d(t₂) m (compl F w t₂)` into a homogeneous term `H` and an integrated mode-forcing
term `∫⁻ r in Ioc t₁ t₂, G r`. -/
def WeakFlowProjectedGronwall (κ : PlanarFrameKernels) : Prop :=
  IsSeedKernels κ →
  ∀ (P : PlanarData), IsPlanarReference P →
  ∀ m : ℝ, 8 < m →
  ∀ K C_loc C_H0 b : ℝ, 0 ≤ C_loc → 0 ≤ C_H0 → 1 ≤ b →
  ∀ ν : ℝ, ∀ (hν : 0 < ν), ∀ hF : PerFrameFacts κ ν m b K,
    ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
      UnforcedLeray.Short.PartI.IsBUCTrain tr →
      ∀ t₁ t₂ : ℝ, 0 ≤ t₁ → t₁ ≤ t₂ → b ≤ clockTheta ν t₂ →
        ∀ f w u, IsLinearisedFlow ν (ν ^ (-2 : ℝ)) m tr t₁ f w u →
          HasZeroCirculation (ν ^ (-2 : ℝ)) f →
          let F := periodizedFrame κ ν m b K hν hF
          let μ_raw := normGrowthConst m + 1 + (C_loc + C_H0)
          (∀ s₁ s₂ : ℝ, t₁ ≤ s₁ → s₁ ≤ s₂ → s₂ ≤ t₂ →
            ∀ f₀ : B0579.Plane → ℝ, B0579.IsCylTest (ν ^ (-2 : ℝ)) f₀ →
              ∀ ω₀ : ℝ → B0579.Plane → ℝ,
                UnforcedLeray.Short.IIb.IsFreeCylFlow m tr s₁ f₀ ω₀ →
                xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν s₂)) m
                    (JscaleInv (clockA ν s₂) (fun x => ((ω₀ s₂ x : ℝ) : ℂ))) ≤
                  ENNReal.ofReal
                      (Real.exp ((normGrowthConst m + 1) * (movingZ ν s₂ - movingZ ν s₁))) *
                    xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν s₁)) m
                      (JscaleInv (clockA ν s₁) (fun x => ((f₀ x : ℝ) : ℂ)))) →
          (∀ r ∈ Icc t₁ t₂, ∀ Φ : ℝ × ℝ → ℂ,
            let d := cellLen (ν ^ (-2 : ℝ)) (clockA ν r)
            MemLp Φ 2 (B0579.cellMeasure d (-m)) →
            ∃ (χ : ℝ × ℝ → ℂ) (gχ : Fin 2 → ℝ × ℝ → ℂ),
              (∀ j, HasWeakCellDerivC d j χ (gχ j)) ∧
              h1Norm d m χ gχ ≤ ENNReal.ofReal C_loc * xNorm d (-m) Φ ∧
              xNorm d (-m) χ ≤ ENNReal.ofReal C_loc * xNorm d (-m) Φ ∧
              ∀ ψ uψ, B0579.IsCylTest d ψ → IsKernelBiotSavart d ψ uψ →
                ∫ y in B0579.cell d, χ y * (ψ y : ℂ) =
                  ∫ y in B0579.cell d,
                    Φ y * ((uψ y 0 * B0579.pd 0 (movingTrainE tr r) y +
                      uψ y 1 * B0579.pd 1 (movingTrainE tr r) y : ℝ) : ℂ)) →
          (∀ r ∈ Icc t₁ t₂,
            xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m
                (complFiniteRankCoupling F r (movH0 κ tr r · (compl F w r))) ≤
              ENNReal.ofReal C_H0 *
                xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m (compl F w r)) →
          ∃ (H : ℝ≥0∞) (G : ℝ → ℝ≥0∞),
            xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν t₂)) m (compl F w t₂) ≤
              H + ∫⁻ r in Ioc t₁ t₂, G r ∧
            H ≤ ENNReal.ofReal (Real.exp (μ_raw * (movingZ ν t₂ - movingZ ν t₁))) *
              xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν t₁)) m (compl F w t₁) ∧
            ∀ r ∈ Ioc t₁ t₂,
              G r ≤
                ENNReal.ofReal
                    ((clockA ν r) ^ (-2 : ℝ) *
                      Real.exp (μ_raw * (movingZ ν t₂ - movingZ ν r))) *
                  (∑ j : Fin 2,
                    ENNReal.ofReal ‖ampl F w r j‖ *
                      xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m
                        (complModeForce κ P F tr r j))

/-- **Conditional assembly of `WeakFlowComplPerturbDuhamel κ` (`PartIII-a:T21/c3/3/1/1`)**:
Combines `WeakFlowProjectedGronwall κ` with `exists_unif_adjointLocalized_bound`,
`PerturbDuhamelSub.xNorm_complCoupling_movH0_le_const`, `freeMovingEnergy_rate_le_add_one`, and
`duhamel_ennreal_bound_of_split` to establish `WeakFlowComplPerturbDuhamel κ` with zero sorry. -/
theorem weakFlowComplPerturbDuhamel_of (κ : PlanarFrameKernels)
    (hProj : WeakFlowProjectedGronwall κ) :
    WeakFlowComplPerturbDuhamel κ := by
  intro hAdjAll hHeat hEuler hFree hSeed P hP m hm K
  obtain ⟨C_loc, b_loc, hC_loc, hb_loc1, hLocB⟩ :=
    exists_unif_adjointLocalized_bound (hAdjAll m hm)
  obtain ⟨C_H0, b_H0, hC_H0, hb_H01, hH0B⟩ :=
    xNorm_complCoupling_movH0_le_const hHeat hEuler hSeed hm K
  obtain ⟨b_free, hb_free1, hFreeB⟩ :=
    freeMovingEnergy_rate_le_add_one hFree hm
  set C_pert : ℝ := C_loc + C_H0
  set b₀ : ℝ := max b_free (max b_loc b_H0)
  have hC_pert : 0 ≤ C_pert := add_nonneg hC_loc hC_H0
  have hb₀1 : 1 ≤ b₀ := hb_free1.trans (le_max_left _ _)
  refine ⟨C_pert, b₀, hC_pert, hb₀1, fun b hb => ?_⟩
  have hb_free : b_free ≤ b := (le_max_left b_free _).trans hb
  have hb_loc : b_loc ≤ b :=
    (le_trans (le_max_left b_loc b_H0) (le_max_right b_free _)).trans hb
  have hb_H0 : b_H0 ≤ b :=
    (le_trans (le_max_right b_loc b_H0) (le_max_right b_free _)).trans hb
  have hb1 : 1 ≤ b := hb₀1.trans hb
  obtain ⟨ν_free, hν_free, hFree_ν⟩ := hFreeB b hb_free
  obtain ⟨ν_loc, hν_loc, hLoc_ν⟩ := hLocB b hb_loc
  obtain ⟨ν_H0, hν_H0, hH0_ν⟩ := hH0B b hb_H0
  set ν₀ : ℝ := min ν_free (min ν_loc ν_H0)
  have hν₀ : 0 < ν₀ := lt_min hν_free (lt_min hν_loc hν_H0)
  refine ⟨ν₀, hν₀, fun ν hν hF tr htr t₁ t₂ ht₁ h12 hbt₂ f w u hFlow hCirc => ?_⟩
  dsimp only
  have hν_in_free : ν ∈ Ioc 0 ν_free :=
    ⟨hν.1, hν.2.trans (min_le_left _ _)⟩
  have hν_in_loc : ν ∈ Ioc 0 ν_loc :=
    ⟨hν.1, hν.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩
  have hν_in_H0 : ν ∈ Ioc 0 ν_H0 :=
    ⟨hν.1, hν.2.trans ((min_le_right _ _).trans (min_le_right _ _))⟩
  have hFree_sub :
      ∀ s₁ s₂ : ℝ, t₁ ≤ s₁ → s₁ ≤ s₂ → s₂ ≤ t₂ →
        ∀ f₀ : B0579.Plane → ℝ, B0579.IsCylTest (ν ^ (-2 : ℝ)) f₀ →
          ∀ ω₀ : ℝ → B0579.Plane → ℝ,
            UnforcedLeray.Short.IIb.IsFreeCylFlow m tr s₁ f₀ ω₀ →
            xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν s₂)) m
                (JscaleInv (clockA ν s₂) (fun x => ((ω₀ s₂ x : ℝ) : ℂ))) ≤
              ENNReal.ofReal
                  (Real.exp ((normGrowthConst m + 1) * (movingZ ν s₂ - movingZ ν s₁))) *
                xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν s₁)) m
                  (JscaleInv (clockA ν s₁) (fun x => ((f₀ x : ℝ) : ℂ))) := by
    intro s₁ s₂ hs₁ hs₁₂ hs₂ f₀ hf₀ ω₀ hω₀
    have hs₁0 : 0 ≤ s₁ := ht₁.trans hs₁
    have hs₂0 : 0 ≤ s₂ := hs₁0.trans hs₁₂
    have hbs₂ : b ≤ clockTheta ν s₂ := hbt₂.trans (theta_anti hν.1 hs₂0 hs₂)
    exact hFree_ν ν hν_in_free tr htr s₁ s₂ hs₁0 hs₁₂ hbs₂ f₀ hf₀ ω₀ hω₀
  have hLoc_sub :
      ∀ r ∈ Icc t₁ t₂, ∀ Φ : ℝ × ℝ → ℂ,
        let d := cellLen (ν ^ (-2 : ℝ)) (clockA ν r)
        MemLp Φ 2 (B0579.cellMeasure d (-m)) →
        ∃ (χ : ℝ × ℝ → ℂ) (gχ : Fin 2 → ℝ × ℝ → ℂ),
          (∀ j, HasWeakCellDerivC d j χ (gχ j)) ∧
          h1Norm d m χ gχ ≤ ENNReal.ofReal C_loc * xNorm d (-m) Φ ∧
          xNorm d (-m) χ ≤ ENNReal.ofReal C_loc * xNorm d (-m) Φ ∧
          ∀ ψ uψ, B0579.IsCylTest d ψ → IsKernelBiotSavart d ψ uψ →
            ∫ y in B0579.cell d, χ y * (ψ y : ℂ) =
              ∫ y in B0579.cell d,
                Φ y * ((uψ y 0 * B0579.pd 0 (movingTrainE tr r) y +
                  uψ y 1 * B0579.pd 1 (movingTrainE tr r) y : ℝ) : ℂ) := by
    intro r hr Φ d hΦ
    have hr0 : 0 ≤ r := ht₁.trans hr.1
    have hbr : b ≤ clockTheta ν r := hbt₂.trans (theta_anti hν.1 hr0 hr.2)
    exact hLoc_ν ν hν_in_loc tr htr r hr0 hbr Φ hΦ
  have hH0_sub :
      ∀ r ∈ Icc t₁ t₂,
        xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m
            (complFiniteRankCoupling (periodizedFrame κ ν m b K hν.1 hF) r
              (movH0 κ tr r · (compl (periodizedFrame κ ν m b K hν.1 hF) w r))) ≤
          ENNReal.ofReal C_H0 *
            xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m
              (compl (periodizedFrame κ ν m b K hν.1 hF) w r) := by
    intro r hr
    have hr0 : 0 ≤ r := ht₁.trans hr.1
    have hbr : b ≤ clockTheta ν r := hbt₂.trans (theta_anti hν.1 hr0 hr.2)
    exact hH0_ν ν hν_in_H0 hF tr htr t₁ r ht₁ hr.1 hbr f w u hFlow
  obtain ⟨H, G, hsplit, hH, hG⟩ :=
    hProj hSeed P hP m hm K C_loc C_H0 b hC_loc hC_H0 hb1 ν hν.1 hF tr htr
      t₁ t₂ ht₁ h12 hbt₂ f w u hFlow hCirc hFree_sub hLoc_sub hH0_sub
  exact duhamel_ennreal_bound_of_split hsplit hH hG

/-! ## 6. Free-rate reduction: boundedness, the free-rate Duhamel leaf, and Gronwall -/

/-- **Boundedness of the moving complement norm on `[t₁, t₂]`**: along a weak linearised flow,
`r ↦ ‖compl F w r‖_{X_{m,d(r)}}` is bounded on `[t₁, t₂]` by a finite constant (strong continuity
of `w` in `X_{m,c}` on the compact `[t₁, t₂]`, the scaling bound `xNorm_JscaleInv_le`, and the
projection bound `xNorm_frameProj_le`). -/
theorem exists_bound_xNorm_compl {ν m b K : ℝ} (F : MovingFrame ν (ν ^ (-2 : ℝ)) m b K)
    (hν : 0 < ν) (hm : 0 ≤ m)
    {tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))} {t₁ t₂ : ℝ} (ht₁ : 0 ≤ t₁)
    (hbt₂ : b ≤ clockTheta ν t₂)
    {f : ℝ × ℝ → ℂ} {w : ℝ → ℝ × ℝ → ℂ} {u : ℝ → ℝ × ℝ → Fin 2 → ℂ}
    (hw : IsLinearisedFlow ν (ν ^ (-2 : ℝ)) m tr t₁ f w u) :
    ∃ M : ℝ≥0∞, M ≠ ⊤ ∧ ∀ r ∈ Icc t₁ t₂,
      xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m (compl F w r) ≤ M := by
  have hcont : ∀ r ∈ Icc t₁ t₂,
      ContinuousWithinAt (fun r' => xNorm (ν ^ (-2 : ℝ)) m (w r')) (Icc t₁ t₂) r := by
    intro r hr
    have h := xNorm_continuousWithinAt_of_strongCont (c := ν ^ (-2 : ℝ)) (m := -m) (t := t₁)
      (s := t₂) (φ := w)
      (fun r' hr' => by rw [neg_neg]; exact hw.memX r' hr'.1)
      (fun r' hr' => by
        rw [neg_neg]
        exact (hw.strongCont r' hr'.1).mono_left (nhdsWithin_mono _ Icc_subset_Ici_self)) r hr
    simpa only [neg_neg] using h
  have hG : ContinuousOn (fun r' => (xNorm (ν ^ (-2 : ℝ)) m (w r')).toReal) (Icc t₁ t₂) := by
    intro r hr
    have hF : xNorm (ν ^ (-2 : ℝ)) m (w r) ≠ ⊤ := (hw.memX r hr.1).2.ne
    have hT : ContinuousAt ENNReal.toReal (xNorm (ν ^ (-2 : ℝ)) m (w r)) :=
      ENNReal.continuousAt_toReal hF
    exact ContinuousAt.comp_continuousWithinAt
      (f := fun r' => xNorm (ν ^ (-2 : ℝ)) m (w r')) (x := r) hT (hcont r hr)
  obtain ⟨B, hB⟩ := (isCompact_Icc.image_of_continuousOn hG).bddAbove
  have hwB : ∀ r ∈ Icc t₁ t₂, xNorm (ν ^ (-2 : ℝ)) m (w r) ≤ ENNReal.ofReal B := by
    intro r hr
    have hF : xNorm (ν ^ (-2 : ℝ)) m (w r) ≠ ⊤ := (hw.memX r hr.1).2.ne
    calc xNorm (ν ^ (-2 : ℝ)) m (w r)
        = ENNReal.ofReal ((xNorm (ν ^ (-2 : ℝ)) m (w r)).toReal) :=
          (ENNReal.ofReal_toReal hF).symm
      _ ≤ ENNReal.ofReal B := ENNReal.ofReal_le_ofReal (hB (Set.mem_image_of_mem _ hr))
  refine ⟨ENNReal.ofReal (1 + 2 * max K 0 ^ 2) *
      (ENNReal.ofReal (clockA ν t₂ ^ ((3 : ℝ) / 2)) * ENNReal.ofReal B),
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top), ?_⟩
  intro r hr
  have hr0 : 0 ≤ r := ht₁.trans hr.1
  have hbr : b ≤ clockTheta ν r := hbt₂.trans (theta_anti hν hr0 hr.2)
  have hW := memLp_movingW hm hν ht₁ hr.1 hw
  have hproj := xNorm_frameProj_le F hr0 hbr hW.1
  have hscale := xNorm_JscaleInv_le (ν ^ (-2 : ℝ)) m (clockA ν r) hm
    (one_le_clockA hν.le hr0) (w r) (hw.memX r hr.1)
  have ha : clockA ν r ^ ((3 : ℝ) / 2) ≤ clockA ν t₂ ^ ((3 : ℝ) / 2) := by
    have h1 : ν * r ≤ ν * t₂ := mul_le_mul_of_nonneg_left hr.2 hν.le
    refine Real.rpow_le_rpow (by unfold clockA; positivity) ?_ (by norm_num)
    unfold clockA
    linarith
  calc xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m (compl F w r)
      = xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m (frameProj F r (movingW ν w r)) := rfl
    _ ≤ ENNReal.ofReal (1 + 2 * max K 0 ^ 2) *
          xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m (movingW ν w r) := hproj
    _ ≤ ENNReal.ofReal (1 + 2 * max K 0 ^ 2) *
          (ENNReal.ofReal (clockA ν r ^ ((3 : ℝ) / 2)) * xNorm (ν ^ (-2 : ℝ)) m (w r)) := by
        gcongr
        exact hscale
    _ ≤ ENNReal.ofReal (1 + 2 * max K 0 ^ 2) *
          (ENNReal.ofReal (clockA ν t₂ ^ ((3 : ℝ) / 2)) * ENNReal.ofReal B) := by
        gcongr
        exact hwB r hr

/-- **Analytical leaf (`ComplFreeRateDuhamel`, SP 2919-2925, 2937-2958)**: the Duhamel inequality
of the moving complement relative to the free moving evolution. Along any weak linearised flow
`IsLinearisedFlow` with `HasZeroCirculation` on `[t₁, t₂]`, under the same three hypotheses as
`WeakFlowProjectedGronwall` (free moving bound at rate `μ₀ = normGrowthConst m + 1` on
sub-intervals, adjoint localized bound `C_loc`, finite-rank coupling bound `C_H0`), the complement
`W_⊥ = compl F w`, which solves `∂_z W_⊥ = (θ⁻¹ D - V·∇) W_⊥ + L_int W_⊥ - E H₀ W_⊥ +
∑_j α_j complModeForce_j`, satisfies for every `s ∈ [t₁, t₂]`
`‖W_⊥(s)‖ ≤ e^{μ₀ (z_s - z_{t₁})} ‖W_⊥(t₁)‖ +
  ∫_{(t₁, s]} a(r)⁻² e^{μ₀ (z_s - z_r)} ((C_loc + C_H0) ‖W_⊥(r)‖ + G(r)) dr`
for some a.e.-measurable `G ≤ ∑_j |α_j(r)| ‖complModeForce_j(r)‖_{X_{m,d(r)}}` (for instance
`G(r) = ‖∑_j α_j(r) complModeForce_j(r)‖`). No Gronwall step is included: the perturbation
`L_int - E H₀` is kept on the right-hand side at the free rate. -/
def ComplFreeRateDuhamel (κ : PlanarFrameKernels) : Prop :=
  IsSeedKernels κ →
  ∀ (P : PlanarData), IsPlanarReference P →
  ∀ m : ℝ, 8 < m →
  ∀ K C_loc C_H0 b : ℝ, 0 ≤ C_loc → 0 ≤ C_H0 → 1 ≤ b →
  ∀ ν : ℝ, ∀ (hν : 0 < ν), ∀ hF : PerFrameFacts κ ν m b K,
    ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
      UnforcedLeray.Short.PartI.IsBUCTrain tr →
      ∀ t₁ t₂ : ℝ, 0 ≤ t₁ → t₁ ≤ t₂ → b ≤ clockTheta ν t₂ →
        ∀ f w u, IsLinearisedFlow ν (ν ^ (-2 : ℝ)) m tr t₁ f w u →
          HasZeroCirculation (ν ^ (-2 : ℝ)) f →
          let F := periodizedFrame κ ν m b K hν hF
          let μ₀ := normGrowthConst m + 1
          (∀ s₁ s₂ : ℝ, t₁ ≤ s₁ → s₁ ≤ s₂ → s₂ ≤ t₂ →
            ∀ f₀ : B0579.Plane → ℝ, B0579.IsCylTest (ν ^ (-2 : ℝ)) f₀ →
              ∀ ω₀ : ℝ → B0579.Plane → ℝ,
                UnforcedLeray.Short.IIb.IsFreeCylFlow m tr s₁ f₀ ω₀ →
                xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν s₂)) m
                    (JscaleInv (clockA ν s₂) (fun x => ((ω₀ s₂ x : ℝ) : ℂ))) ≤
                  ENNReal.ofReal
                      (Real.exp ((normGrowthConst m + 1) * (movingZ ν s₂ - movingZ ν s₁))) *
                    xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν s₁)) m
                      (JscaleInv (clockA ν s₁) (fun x => ((f₀ x : ℝ) : ℂ)))) →
          (∀ r ∈ Icc t₁ t₂, ∀ Φ : ℝ × ℝ → ℂ,
            let d := cellLen (ν ^ (-2 : ℝ)) (clockA ν r)
            MemLp Φ 2 (B0579.cellMeasure d (-m)) →
            ∃ (χ : ℝ × ℝ → ℂ) (gχ : Fin 2 → ℝ × ℝ → ℂ),
              (∀ j, HasWeakCellDerivC d j χ (gχ j)) ∧
              h1Norm d m χ gχ ≤ ENNReal.ofReal C_loc * xNorm d (-m) Φ ∧
              xNorm d (-m) χ ≤ ENNReal.ofReal C_loc * xNorm d (-m) Φ ∧
              ∀ ψ uψ, B0579.IsCylTest d ψ → IsKernelBiotSavart d ψ uψ →
                ∫ y in B0579.cell d, χ y * (ψ y : ℂ) =
                  ∫ y in B0579.cell d,
                    Φ y * ((uψ y 0 * B0579.pd 0 (movingTrainE tr r) y +
                      uψ y 1 * B0579.pd 1 (movingTrainE tr r) y : ℝ) : ℂ)) →
          (∀ r ∈ Icc t₁ t₂,
            xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m
                (complFiniteRankCoupling F r (movH0 κ tr r · (compl F w r))) ≤
              ENNReal.ofReal C_H0 *
                xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m (compl F w r)) →
          ∃ G : ℝ → ℝ≥0∞,
            AEMeasurable G (volume.restrict (Ioc t₁ t₂)) ∧
            (∀ᵐ r ∂(volume.restrict (Ioc t₁ t₂)),
              G r ≤ ∑ j : Fin 2, ENNReal.ofReal ‖ampl F w r j‖ *
                xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m (complModeForce κ P F tr r j)) ∧
            ∀ s ∈ Icc t₁ t₂,
              xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)) m (compl F w s) ≤
                ENNReal.ofReal (Real.exp (μ₀ * (movingZ ν s - movingZ ν t₁))) *
                    xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν t₁)) m (compl F w t₁) +
                  ∫⁻ r in Ioc t₁ s,
                    ENNReal.ofReal ((clockA ν r) ^ (-2 : ℝ) *
                        Real.exp (μ₀ * (movingZ ν s - movingZ ν r))) *
                      (ENNReal.ofReal (C_loc + C_H0) *
                          xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m (compl F w r) + G r)

/-- **Gronwall step (`ComplFreeRateDuhamel κ → WeakFlowProjectedGronwall κ`)**: the free-rate
Duhamel inequality, the boundedness `exists_bound_xNorm_compl`, and the moving-time Gronwall lemma
`WeakFlowGronwallSub.gronwall_movingZ` give the homogeneous + forcing split at `t₂` with
`μ_raw = normGrowthConst m + 1 + (C_loc + C_H0)`. -/
theorem weakFlowProjectedGronwall_of_freeRate (κ : PlanarFrameKernels)
    (hA : ComplFreeRateDuhamel κ) : WeakFlowProjectedGronwall κ := by
  intro hSeed P hP m hm K C_loc C_H0 b hC_loc hC_H0 hb1 ν hν hF tr htr t₁ t₂ ht₁ h12 hbt₂
    f w u hFlow hCirc F μ_raw hFree hLoc hH0
  obtain ⟨G, hGm, hGle, hMild⟩ := hA hSeed P hP m hm K C_loc C_H0 b hC_loc hC_H0 hb1 ν hν hF
    tr htr t₁ t₂ ht₁ h12 hbt₂ f w u hFlow hCirc hFree hLoc hH0
  have hm0 : 0 ≤ m := by linarith
  obtain ⟨M, hM, hφM⟩ := exists_bound_xNorm_compl F hν hm0 ht₁ hbt₂ hFlow
  have hμ₀ : 0 ≤ normGrowthConst m + 1 := by
    have := normGrowthConst_nonneg hm0
    linarith
  have hC : 0 ≤ C_loc + C_H0 := add_nonneg hC_loc hC_H0
  set G' : ℝ → ℝ≥0∞ := hGm.mk G with hG'_def
  have hG'm : Measurable G' := hGm.measurable_mk
  have hGG' : G =ᵐ[volume.restrict (Ioc t₁ t₂)] G' := hGm.ae_eq_mk
  have hMild' : ∀ s ∈ Icc t₁ t₂,
      xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)) m (compl F w s) ≤
        ENNReal.ofReal (Real.exp ((normGrowthConst m + 1) * (movingZ ν s - movingZ ν t₁))) *
            xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν t₁)) m (compl F w t₁) +
          ∫⁻ r in Ioc t₁ s,
            ENNReal.ofReal ((clockA ν r) ^ (-2 : ℝ) *
                Real.exp ((normGrowthConst m + 1) * (movingZ ν s - movingZ ν r))) *
              (ENNReal.ofReal (C_loc + C_H0) *
                  xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m (compl F w r) + G' r) := by
    intro s hs
    refine (hMild s hs).trans (le_of_eq ?_)
    congr 1
    refine lintegral_congr_ae ?_
    filter_upwards [ae_restrict_of_ae_restrict_of_subset (Ioc_subset_Ioc_right hs.2) hGG']
      with r hr
    rw [hr]
  have hgr := WeakFlowGronwallSub.gronwall_movingZ hν ht₁ h12 hμ₀ hC hM hφM hG'm hMild'
  refine ⟨ENNReal.ofReal (Real.exp (μ_raw * (movingZ ν t₂ - movingZ ν t₁))) *
      xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν t₁)) m (compl F w t₁),
    fun r => ENNReal.ofReal ((clockA ν r) ^ (-2 : ℝ) *
        Real.exp (μ_raw * (movingZ ν t₂ - movingZ ν r))) *
      (∑ j : Fin 2, ENNReal.ofReal ‖ampl F w r j‖ *
        xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m (complModeForce κ P F tr r j)),
    ?_, le_rfl, fun r _ => le_rfl⟩
  refine hgr.trans (add_le_add le_rfl (lintegral_mono_ae ?_))
  filter_upwards [hGG', hGle] with r h1 h2
  rw [← h1]
  gcongr

/-- **Free-rate reduction of the target (`PartIII-a:T21/c3/3/1/1`)**:
`ComplFreeRateDuhamel κ → WeakFlowComplPerturbDuhamel κ`. -/
theorem weakFlowComplPerturbDuhamel_of_freeRate (κ : PlanarFrameKernels)
    (hA : ComplFreeRateDuhamel κ) : WeakFlowComplPerturbDuhamel κ :=
  weakFlowComplPerturbDuhamel_of κ (weakFlowProjectedGronwall_of_freeRate κ hA)

end WeakFlowDuhamelSub

end UnforcedLeray.Short.IIIa
