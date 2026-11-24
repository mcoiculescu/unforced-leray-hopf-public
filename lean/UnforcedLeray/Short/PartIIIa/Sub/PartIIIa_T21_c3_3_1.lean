import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_3
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c5_3
import UnforcedLeray.Short.PartIIIa.Clock.WeakSmoothing.LocalizedBound
import UnforcedLeray.Short.PartIIIa.Clock.FrameStableProof.ShortBlock.EulerError

/-!
# Part III-a, task `PartIII-a:T21/c3/3/1` sub-infrastructure: perturbed Duhamel inequality for the complement (`ShortComplPerturbDuhamel`, SP 2919-2925, 2937-2958, 2982-2988)

Source of record: `the November 2 reference manuscript`
(SP), lines 2919-2925, 2937-2958, and 2982-2988 (`eq:short-causal-damped-complement`,
`eq:short-causal-free-moving`, `eq:short-causal-stable-moving`).

## Mathematical structure and proved infrastructure in this file

On a short moving block `[t₁, t₂]` with `b ≤ clockTheta ν t₂`, the moving complement
`W_⊥(r) = compl F w r = (1 - E(r) Λ(r)) (movingW ν w r)` satisfies the projected moving equation
(SP 2919-2925):
`∂_z W_⊥ = (θ⁻¹ D - V · ∇) W_⊥ + L_{int, d(r)} W_⊥ - E(r) H_0(r) W_⊥ + ∑_j a_j(r) complModeForce_j(r)`.

1. **Unconditional rescaled train, localized source, and adjoint localized interaction bounds
   (`rescaledTrainBounds_uncond`, `localizedSourceBounds_uncond`, `adjointLocalizedBound_uncond`,
   `xNorm_le_h1Norm`, `adjointLocalized_xNorm_and_pairing_bound`, `ofReal_norm_integral_chi_le`)**:
   * Discharges `RescaledTrainBounds m` unconditionally from `EulerErrorSub.rescaledTrainBoundsBUC_uncond m`.
   * Discharges `LocalizedSourceBounds m` and `AdjointLocalizedBound m` unconditionally for all
     `8 < m` via `localizedSourceBounds` and `adjointLocalizedBound`.
   * Proves `xNorm c (-m) φ ≤ h1Norm c m φ g` and combines `adjointLocalizedBound_uncond` with
     `ComplCouplingSub.xNorm_pairing_bound` to establish the unconditional dual-pairing `X_{m, d(r)}`
     bound for the localized interaction `L_{int, d(r)}`.

2. **Uniform `X_{m, d(r)}` operator norm bound for the finite-rank coupling `-E(r) H_0(r)` on
   `compl F w r` (`complFiniteRankCoupling`, `aesm_complFiniteRankCoupling`,
   `xNorm_complFiniteRankCoupling_le`, `xNorm_complCoupling_movH0_le`,
   `xNorm_complCoupling_movH0_le_const`)**:
   * Defines `complFiniteRankCoupling F r c_i y = - ∑ i : Fin 2, c_i i * F.E r i y` and proves
     measurability and the operator bound
     `xNorm d(r) m (complFiniteRankCoupling F r c_i) ≤ (∑ i : Fin 2, ENNReal.ofReal ‖c_i i‖) * ENNReal.ofReal (max K 0)`.
   * Combines this with `ComplCouplingSub.ofReal_norm_movH0_compl_le` (`Sub/PartIII-a_T21_c5_3.lean`)
     to prove that under `MovLamDualHeatBound κ` and `MovLamDualEulerSubBound κ`, the finite-rank
     coupling `-E(r) H_0(r) (compl F w r)` is bounded in `X_{m, d(r)}` by
     `ENNReal.ofReal (C_H0 / clockTheta ν r) * xNorm d(r) m (compl F w r) ≤ ENNReal.ofReal C_H0 * xNorm d(r) m (compl F w r)`.

3. **Unconditional moving-time integrating factor and growth-rate calculus on `[t₁, t₂]`
   (`normGrowthConst_nonneg`, `normGrowthConst_div_add_one_le`, `hasDerivAt_exp_movingZ_sub`,
   `integral_mul_exp_movingZ_sub`, `lintegral_mul_exp_movingZ_sub`)**:
   * Proves `0 ≤ normGrowthConst m` and `normGrowthConst m / b + 1 ≤ normGrowthConst m + 1` for `0 ≤ m`, `1 ≤ b`.
   * Proves `(d/dr) exp(μ_raw * (movingZ ν t₂ - movingZ ν r)) = -μ_raw * a(r)⁻² * exp(μ_raw * (movingZ ν t₂ - movingZ ν r))`.
   * Proves the exact Duhamel / Gronwall integrating-factor identity on `Ioc t₁ t₂`:
     `∫⁻ r in Ioc t₁ t₂, ENNReal.ofReal (μ_raw * a(r)⁻² * exp(μ_raw * (movingZ ν t₂ - movingZ ν r))) = ENNReal.ofReal (exp(μ_raw * (movingZ ν t₂ - movingZ ν t₁)) - 1)`.

4. **Conditional assembly (`shortComplPerturbDuhamel_of`)**:
   * Formulates the weak-flow perturbed Duhamel leaf `WeakFlowComplPerturbDuhamel κ`
     (`PartIII-a:T21/c3/3/1/1`, combining `FreeMovingEnergy` with the unconditional
     `AdjointLocalizedBound m` and the dual-mode bounds `MovLamDualHeatBound κ`,
     `MovLamDualEulerSubBound κ`) and assembles `ShortComplPerturbDuhamel κ` with zero sorry.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-! ## Finite-rank complement coupling profile and weak-flow perturbed Duhamel leaf -/

/-- The finite-rank coupling profile `- ∑ i : Fin 2, c_i i * F.E r i y` in the moving complement
equation (SP 2919-2925). -/
def complFiniteRankCoupling {ν c m b K : ℝ} (F : MovingFrame ν c m b K) (r : ℝ)
    (c_i : Fin 2 → ℂ) (y : ℝ × ℝ) : ℂ :=
  -∑ i : Fin 2, c_i i * F.E r i y

/-- **Analytical Leaf (`WeakFlowComplPerturbDuhamel`, `PartIII-a:T21/c3/3/1/1`,
`the November 2 reference manuscript`
lines 2919-2925, 2937-2958, 2982-2988)**:
Given `FreeMovingEnergy`, the unconditional adjoint localized interaction bound
`AdjointLocalizedBound m`, and the dual-mode heat/Euler bounds `MovLamDualHeatBound κ` and
`MovLamDualEulerSubBound κ`, testing the weak linearised flow `IsLinearisedFlow` with
`HasZeroCirculation` against the complement projection `1 - E(r) Λ(r)` and applying the moving-time
integrating factor `exp(μ_raw * (movingZ ν t₂ - movingZ ν r))` with
`μ_raw = normGrowthConst m + 1 + C_pert` yields the Duhamel inequality for `compl F w`.
Composed by task `PartIII-a:T21/c3/3/1` via `shortComplPerturbDuhamel_of`. -/
def WeakFlowComplPerturbDuhamel (κ : PlanarFrameKernels) : Prop :=
  (∀ m : ℝ, 8 < m → AdjointLocalizedBound m) →
  MovLamDualHeatBound κ →
  MovLamDualEulerSubBound κ →
  ShortComplPerturbDuhamel κ

namespace PerturbDuhamelSub

open FrameShortBlockSub ComplCouplingSub EulerErrorSub

/-! ## 1. Unconditional rescaled train, localized source, and adjoint localized interaction bounds -/

/-- **Unconditional proof of `RescaledTrainBounds m` (`Clock/WeakSmoothing/Adjoint.lean`)**:
follows directly from `EulerErrorSub.rescaledTrainBoundsBUC_uncond m`. -/
theorem rescaledTrainBounds_uncond (m : ℝ) : RescaledTrainBounds m :=
  rescaledTrainBoundsBUC_uncond m

/-- **Unconditional proof of `LocalizedSourceBounds m` (`Sub/PartIIIa_T21_2_1.lean`)** for `8 < m`. -/
theorem localizedSourceBounds_uncond {m : ℝ} (hm : 8 < m) : LocalizedSourceBounds m :=
  localizedSourceBounds m hm (rescaledTrainBounds_uncond m)

/-- **Unconditional proof of `AdjointLocalizedBound m` (`Clock/WeakSmoothing/Adjoint.lean`)** for
`8 < m`. -/
theorem adjointLocalizedBound_uncond {m : ℝ} (hm : 8 < m) : AdjointLocalizedBound m :=
  adjointLocalizedBound m hm (rescaledTrainBounds_uncond m)

/-- The `X_{-m, c}` norm is bounded by the `H^1_{-m, c}` norm:
`xNorm c (-m) φ ≤ h1Norm c m φ g`. -/
theorem xNorm_le_h1Norm (c m : ℝ) (φ : ℝ × ℝ → ℂ) (g : Fin 2 → ℝ × ℝ → ℂ) :
    xNorm c (-m) φ ≤ h1Norm c m φ g := by
  unfold h1Norm
  have h1 : xNorm c (-m) φ ^ 2 ≤ xNorm c (-m) φ ^ 2 + ∑ j, xNorm c (-m) (g j) ^ 2 :=
    le_self_add
  calc xNorm c (-m) φ
      = (xNorm c (-m) φ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
        rw [← ENNReal.rpow_mul, mul_one_div_cancel (by norm_num), ENNReal.rpow_one]
    _ = (xNorm c (-m) φ ^ 2) ^ (1 / 2 : ℝ) := by rw [ENNReal.rpow_two]
    _ ≤ (xNorm c (-m) φ ^ 2 + ∑ j, xNorm c (-m) (g j) ^ 2) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow h1 (by norm_num)

/-- **Unconditional dual-pairing `X_{m, d(r)}` bound for the localized interaction `L_{int, d(r)}`**
(SP 2953-2958, 3052-3058): for `8 < m`, there exist `b_loc ≥ 1` and for every `b ≥ b_loc`,
`C_loc ≥ 0` and `ν_loc > 0` such that for `ν ∈ Ioc 0 ν_loc`, BUC train `tr`, `0 ≤ r`,
`b ≤ clockTheta ν r`, `d = cellLen (ν ^ (-2 : ℝ)) (clockA ν r)`, and
`Φ ∈ MemLp · 2 (B0579.cellMeasure d (-m))`, the adjoint localized interaction `χ` satisfies
`xNorm d (-m) χ ≤ ENNReal.ofReal C_loc * xNorm d (-m) Φ` and for every cylinder test `ψ` with
kernel velocity `uψ = K_d ψ`,
`ENNReal.ofReal ‖∫ y in B0579.cell d, Φ y * ((uψ y 0 * B0579.pd 0 (movingTrainE tr r) y + uψ y 1 * B0579.pd 1 (movingTrainE tr r) y : ℝ) : ℂ)‖ ≤ ENNReal.ofReal C_loc * xNorm d (-m) Φ * xNorm d m (fun y => (ψ y : ℂ))`. -/
theorem adjointLocalized_xNorm_and_pairing_bound {m : ℝ} (hm : 8 < m) :
    ∃ b_loc : ℝ, 1 ≤ b_loc ∧
      ∀ b : ℝ, b_loc ≤ b →
        ∃ C_loc ν_loc : ℝ, 0 ≤ C_loc ∧ 0 < ν_loc ∧
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
  obtain ⟨b₀, hb₀⟩ := adjointLocalizedBound_uncond hm
  refine ⟨max 1 b₀, le_max_left 1 b₀, fun b hb => ?_⟩
  obtain ⟨C, ν₀, hν₀, hLoc⟩ := hb₀ b ((le_max_right 1 b₀).trans hb)
  refine ⟨max C 0, ν₀, le_max_right C 0, hν₀, fun ν hν tr hbuc r hr hθ Φ => ?_⟩
  intro d hΦ
  obtain ⟨χ, gχ, hder, hh1, hdual⟩ := hLoc ν hν tr hbuc r hr hθ Φ hΦ
  have hC_le : ENNReal.ofReal C ≤ ENNReal.ofReal (max C 0) :=
    ENNReal.ofReal_le_ofReal (le_max_left C 0)
  have hh1' : h1Norm d m χ gχ ≤ ENNReal.ofReal (max C 0) * xNorm d (-m) Φ :=
    hh1.trans (mul_le_mul_of_nonneg_right hC_le zero_le)
  have hx_le : xNorm d (-m) χ ≤ ENNReal.ofReal (max C 0) * xNorm d (-m) Φ :=
    (xNorm_le_h1Norm d m χ gχ).trans hh1'
  exact ⟨χ, gχ, hder, hh1', hx_le, hdual⟩

/-- Pairing bound for an adjoint localized interaction density `χ`: if
`xNorm d (-m) χ ≤ ENNReal.ofReal C_loc * xNorm d (-m) Φ` and `χ`, `Ψ` are `MemLp`, then
`ENNReal.ofReal ‖∫ y in B0579.cell d, χ y * Ψ y‖ ≤ ENNReal.ofReal C_loc * xNorm d (-m) Φ * xNorm d m Ψ`. -/
theorem ofReal_norm_integral_chi_le {d m C_loc : ℝ} {χ Φ Ψ : ℝ × ℝ → ℂ}
    (hχ : MemLp χ 2 (B0579.cellMeasure d (-m)))
    (hΨ : MemLp Ψ 2 (B0579.cellMeasure d m))
    (hx : xNorm d (-m) χ ≤ ENNReal.ofReal C_loc * xNorm d (-m) Φ) :
    ENNReal.ofReal ‖∫ y in B0579.cell d, χ y * Ψ y‖ ≤
      ENNReal.ofReal C_loc * xNorm d (-m) Φ * xNorm d m Ψ :=
  (xNorm_pairing_bound hχ hΨ).2.trans (mul_le_mul_of_nonneg_right hx zero_le)

/-! ## 2. Uniform `X_{m, d(r)}` bound for the finite-rank complement coupling `-E(r) H_0(r)` -/

/-- `complFiniteRankCoupling F r c_i` is `AEStronglyMeasurable` with respect to `cellMeasure`. -/
theorem aesm_complFiniteRankCoupling {ν c m b K : ℝ} (F : MovingFrame ν c m b K) {r : ℝ}
    (hr : 0 ≤ r) (hbr : b ≤ clockTheta ν r) (c_i : Fin 2 → ℂ) :
    AEStronglyMeasurable (complFiniteRankCoupling F r c_i)
      (B0579.cellMeasure (cellLen c (clockA ν r)) m) := by
  have hE : ∀ i : Fin 2, AEStronglyMeasurable (F.E r i)
      (B0579.cellMeasure (cellLen c (clockA ν r)) m) :=
    fun i => (F.E_meas r hr hbr i).mono_ac (B0579.cellMeasure_ac _ _)
  unfold complFiniteRankCoupling
  exact (aesm_sum_smul c_i (F.E r) hE).neg

/-- Uniform `X_{m, d(r)}` norm bound for `complFiniteRankCoupling F r c_i`:
`xNorm d(r) m (complFiniteRankCoupling F r c_i) ≤ (∑ i : Fin 2, ENNReal.ofReal ‖c_i i‖) * ENNReal.ofReal (max K 0)`. -/
theorem xNorm_complFiniteRankCoupling_le {ν c m b K : ℝ} (F : MovingFrame ν c m b K) {r : ℝ}
    (hr : 0 ≤ r) (hbr : b ≤ clockTheta ν r) (c_i : Fin 2 → ℂ) :
    xNorm (cellLen c (clockA ν r)) m (complFiniteRankCoupling F r c_i) ≤
      (∑ i : Fin 2, ENNReal.ofReal ‖c_i i‖) * ENNReal.ofReal (max K 0) := by
  set d := cellLen c (clockA ν r)
  set μ := B0579.cellMeasure d m
  set Kp := max K 0
  have hKle : ENNReal.ofReal K ≤ ENNReal.ofReal Kp := ENNReal.ofReal_le_ofReal (le_max_left K 0)
  have hE : ∀ i : Fin 2, AEStronglyMeasurable (F.E r i) μ :=
    fun i => (F.E_meas r hr hbr i).mono_ac (B0579.cellMeasure_ac _ _)
  have hEb : ∀ i : Fin 2, eLpNorm (F.E r i) 2 μ ≤ ENNReal.ofReal Kp :=
    fun i => (F.E_bdd r hr hbr i).trans hKle
  have h0 : complFiniteRankCoupling F r c_i =
      fun y => (0 : ℝ × ℝ → ℂ) y - ∑ i : Fin 2, c_i i * F.E r i y := by
    funext y
    simp [complFiniteRankCoupling]
  unfold xNorm
  rw [h0]
  have hsub := eLpNorm_sub_sum_le (μ := μ) (W := 0) c_i (F.E r) (ENNReal.ofReal Kp)
    aestronglyMeasurable_zero hE hEb
  simpa [eLpNorm_zero] using hsub

/-- **Bound in `X_{m, d(r)}` for the finite-rank complement coupling `-E(r) H_0(r) (compl F w r)`**
(SP 2919-2925, 2956-2958): under `MovLamDualHeatBound κ` and `MovLamDualEulerSubBound κ`, along any
weak linearised flow `IsLinearisedFlow`, the finite-rank coupling term
`complFiniteRankCoupling F r (fun i => movH0 κ tr r i (compl F w r))` is bounded in `X_{m, d(r)}` by
`ENNReal.ofReal (2 * max K 0 * (C_h + C_e) / clockTheta ν r) * xNorm d(r) m (compl F w r)`. -/
theorem xNorm_complCoupling_movH0_le {κ : PlanarFrameKernels}
    (hH : MovLamDualHeatBound κ) (hE : MovLamDualEulerSubBound κ) (hκ : IsSeedKernels κ)
    {m : ℝ} (hm : 8 < m) (K : ℝ) :
    ∃ C_H0 b_H0 : ℝ, 0 ≤ C_H0 ∧ 1 ≤ b_H0 ∧
      ∀ b : ℝ, b_H0 ≤ b →
        ∃ ν_H0 : ℝ, 0 < ν_H0 ∧
          ∀ ν (hν : ν ∈ Ioc 0 ν_H0), ∀ hF : PerFrameFacts κ ν m b K,
            ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
              PartI.IsBUCTrain tr →
              ∀ t r : ℝ, 0 ≤ t → t ≤ r → b ≤ clockTheta ν r →
                ∀ f w u, IsLinearisedFlow ν (ν ^ (-2 : ℝ)) m tr t f w u →
                  let F := periodizedFrame κ ν m b K hν.1 hF
                  let d := cellLen (ν ^ (-2 : ℝ)) (clockA ν r)
                  xNorm d m
                      (complFiniteRankCoupling F r (fun i => movH0 κ tr r i (compl F w r))) ≤
                    ENNReal.ofReal (C_H0 / clockTheta ν r) * xNorm d m (compl F w r) := by
  obtain ⟨C_h, b_h, hCh0, hbh1, hHb⟩ := hH hκ m hm
  obtain ⟨lam, C_e, b_e, hCe0, hbe1, hEb⟩ := hE hκ m hm
  set Kp := max K 0
  have hKp0 : 0 ≤ Kp := le_max_right K 0
  refine ⟨2 * Kp * (C_h + C_e), max b_h b_e, by positivity,
    le_trans hbh1 (le_max_left b_h b_e), fun b hb => ?_⟩
  obtain ⟨ν_h, hνh, hH_ν⟩ := hHb b ((le_max_left b_h b_e).trans hb)
  obtain ⟨ν_e, hνe, hE_ν⟩ := hEb b ((le_max_right b_h b_e).trans hb)
  refine ⟨min (min ν_h ν_e) 1, lt_min (lt_min hνh hνe) zero_lt_one,
    fun ν hν hF tr hbuc t r ht htr hbr f w u hflow => ?_⟩
  intro F d
  have hν_pos : 0 < ν := hν.1
  have hr : 0 ≤ r := ht.trans htr
  have hθ_pos : 0 < clockTheta ν r := theta_pos hν_pos hr
  have hν_he : ν ≤ min ν_h ν_e := hν.2.trans (min_le_left _ _)
  have hν_le_1 : ν ≤ 1 := hν.2.trans (min_le_right _ _)
  have hν_h : ν ∈ Ioc 0 ν_h := ⟨hν_pos, hν_he.trans (min_le_left _ _)⟩
  have hν_e : ν ∈ Ioc 0 ν_e := ⟨hν_pos, hν_he.trans (min_le_right _ _)⟩
  have hb1 : 1 ≤ b := (le_trans hbh1 (le_max_left b_h b_e)).trans hb
  have hd : 1 ≤ d := one_le_cellLen_of_theta hν_pos hν_le_1 hr (hb1.trans hbr)
  have hH0_bound : ∀ i : Fin 2,
      ENNReal.ofReal ‖movH0 κ tr r i (compl F w r)‖ ≤
        ENNReal.ofReal ((C_h + C_e) / clockTheta ν r) * xNorm d m (compl F w r) := by
    intro i
    obtain ⟨hHm_i, hHb_i⟩ := hH_ν ν hν_h r hr hbr i
    obtain ⟨hEm_i, hEb_i⟩ := hE_ν ν hν_e tr hbuc r hr hbr i
    have h1 := ofReal_norm_movH0_compl_le κ lam hm hν_pos ht htr hbr hd hF hflow i hHm_i hEm_i
    have hsum : xNorm d (-m) (movLamDualHeat κ ν r i) +
        xNorm d (-m) (movLamDualEulerSub κ lam tr r i) ≤
        ENNReal.ofReal ((C_h + C_e) / clockTheta ν r) := by
      calc xNorm d (-m) (movLamDualHeat κ ν r i) +
            xNorm d (-m) (movLamDualEulerSub κ lam tr r i)
          ≤ ENNReal.ofReal (C_h * (1 / clockTheta ν r)) +
              ENNReal.ofReal (C_e * (1 / clockTheta ν r)) := add_le_add hHb_i hEb_i
        _ = ENNReal.ofReal ((C_h + C_e) / clockTheta ν r) := by
            rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
            congr 1; ring
    exact h1.trans (mul_le_mul_of_nonneg_right hsum zero_le)
  have hsum_H0 :
      (∑ i : Fin 2, ENNReal.ofReal ‖movH0 κ tr r i (compl F w r)‖) ≤
        2 * (ENNReal.ofReal ((C_h + C_e) / clockTheta ν r) * xNorm d m (compl F w r)) := by
    calc (∑ i : Fin 2, ENNReal.ofReal ‖movH0 κ tr r i (compl F w r)‖)
        ≤ ∑ _i : Fin 2,
            ENNReal.ofReal ((C_h + C_e) / clockTheta ν r) * xNorm d m (compl F w r) :=
          Finset.sum_le_sum (fun i _ => hH0_bound i)
      _ = 2 * (ENNReal.ofReal ((C_h + C_e) / clockTheta ν r) * xNorm d m (compl F w r)) := by
          rw [Fin.sum_univ_two]; ring
  calc xNorm d m (complFiniteRankCoupling F r (fun i => movH0 κ tr r i (compl F w r)))
      ≤ (∑ i : Fin 2, ENNReal.ofReal ‖movH0 κ tr r i (compl F w r)‖) *
          ENNReal.ofReal Kp :=
        xNorm_complFiniteRankCoupling_le F hr hbr _
    _ ≤ (2 * (ENNReal.ofReal ((C_h + C_e) / clockTheta ν r) * xNorm d m (compl F w r))) *
          ENNReal.ofReal Kp :=
        mul_le_mul_of_nonneg_right hsum_H0 zero_le
    _ = (2 * ENNReal.ofReal Kp * ENNReal.ofReal ((C_h + C_e) / clockTheta ν r)) *
          xNorm d m (compl F w r) := by ring
    _ = ENNReal.ofReal (2 * Kp * (C_h + C_e) / clockTheta ν r) * xNorm d m (compl F w r) := by
        congr 1
        have h2 : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by norm_num
        rw [h2, ← ENNReal.ofReal_mul zero_le_two,
          ← ENNReal.ofReal_mul (mul_nonneg zero_le_two hKp0)]
        congr 1; ring

/-- Uniform constant-coefficient corollary of `xNorm_complCoupling_movH0_le`: since
`1 ≤ b ≤ clockTheta ν r` and `0 ≤ C_H0`, `C_H0 / clockTheta ν r ≤ C_H0`. -/
theorem xNorm_complCoupling_movH0_le_const {κ : PlanarFrameKernels}
    (hH : MovLamDualHeatBound κ) (hE : MovLamDualEulerSubBound κ) (hκ : IsSeedKernels κ)
    {m : ℝ} (hm : 8 < m) (K : ℝ) :
    ∃ C_H0 b_H0 : ℝ, 0 ≤ C_H0 ∧ 1 ≤ b_H0 ∧
      ∀ b : ℝ, b_H0 ≤ b →
        ∃ ν_H0 : ℝ, 0 < ν_H0 ∧
          ∀ ν (hν : ν ∈ Ioc 0 ν_H0), ∀ hF : PerFrameFacts κ ν m b K,
            ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
              PartI.IsBUCTrain tr →
              ∀ t r : ℝ, 0 ≤ t → t ≤ r → b ≤ clockTheta ν r →
                ∀ f w u, IsLinearisedFlow ν (ν ^ (-2 : ℝ)) m tr t f w u →
                  let F := periodizedFrame κ ν m b K hν.1 hF
                  let d := cellLen (ν ^ (-2 : ℝ)) (clockA ν r)
                  xNorm d m
                      (complFiniteRankCoupling F r (fun i => movH0 κ tr r i (compl F w r))) ≤
                    ENNReal.ofReal C_H0 * xNorm d m (compl F w r) := by
  obtain ⟨C_H0, b_H0, hC0, hb0, hBound⟩ := xNorm_complCoupling_movH0_le hH hE hκ hm K
  refine ⟨C_H0, b_H0, hC0, hb0, fun b hb => ?_⟩
  obtain ⟨ν_H0, hν0, hB⟩ := hBound b hb
  refine ⟨ν_H0, hν0, fun ν hν hF tr hbuc t r ht htr hbr f w u hflow => ?_⟩
  intro F d
  have h1 := hB ν hν hF tr hbuc t r ht htr hbr f w u hflow
  have hθ1 : 1 ≤ clockTheta ν r := (hb0.trans hb).trans hbr
  have hdiv : C_H0 / clockTheta ν r ≤ C_H0 := div_le_self hC0 hθ1
  exact h1.trans (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hdiv) zero_le)

/-! ## 3. Unconditional moving-time integrating factor and growth-rate calculus on `[t₁, t₂]` -/

/-- `normGrowthConst m = (m ^ 2 + 3 * m + 3) / 2` is nonnegative for `0 ≤ m`. -/
theorem normGrowthConst_nonneg {m : ℝ} (hm : 0 ≤ m) : 0 ≤ normGrowthConst m := by
  unfold normGrowthConst
  positivity

/-- For `0 ≤ m` and `1 ≤ b`, `normGrowthConst m / b + 1 ≤ normGrowthConst m + 1`. -/
theorem normGrowthConst_div_add_one_le {m b : ℝ} (hm : 0 ≤ m) (hb : 1 ≤ b) :
    normGrowthConst m / b + 1 ≤ normGrowthConst m + 1 := by
  linarith [div_le_self (normGrowthConst_nonneg hm) hb]

/-- Age derivative of the moving-time integrating factor
`r ↦ Real.exp (μ_raw * (movingZ ν t₂ - movingZ ν r))` for `0 < ν` and `0 ≤ r`:
`(d/dr) Real.exp (μ_raw * (movingZ ν t₂ - movingZ ν r)) =
  -μ_raw * (clockA ν r) ^ (-2 : ℝ) * Real.exp (μ_raw * (movingZ ν t₂ - movingZ ν r))`. -/
theorem hasDerivAt_exp_movingZ_sub {ν r : ℝ} (t₂ μ_raw : ℝ) (hν : 0 < ν) (hr : 0 ≤ r) :
    HasDerivAt (fun r' => Real.exp (μ_raw * (movingZ ν t₂ - movingZ ν r')))
      (-μ_raw * (clockA ν r) ^ (-2 : ℝ) * Real.exp (μ_raw * (movingZ ν t₂ - movingZ ν r))) r := by
  have hz : HasDerivAt (movingZ ν) ((clockA ν r) ^ (-2 : ℝ)) r := hasDerivAt_movingZ hν hr
  have hsub : HasDerivAt (fun r' => movingZ ν t₂ - movingZ ν r')
      (0 - (clockA ν r) ^ (-2 : ℝ)) r :=
    (hasDerivAt_const r (movingZ ν t₂)).sub hz
  have hmul : HasDerivAt (fun r' => μ_raw * (movingZ ν t₂ - movingZ ν r'))
      (μ_raw * (0 - (clockA ν r) ^ (-2 : ℝ))) r :=
    hsub.const_mul μ_raw
  have hexp := hmul.exp
  refine hexp.congr_deriv ?_
  ring

/-- Fundamental theorem of calculus for the moving-time integrating factor on `Ioc t₁ t₂`:
`∫ r in Ioc t₁ t₂, μ_raw * (clockA ν r) ^ (-2 : ℝ) * Real.exp (μ_raw * (movingZ ν t₂ - movingZ ν r)) =
  Real.exp (μ_raw * (movingZ ν t₂ - movingZ ν t₁)) - 1`. -/
theorem integral_mul_exp_movingZ_sub {ν t₁ t₂ : ℝ} (μ_raw : ℝ) (hν : 0 < ν)
    (ht₁ : 0 ≤ t₁) (h12 : t₁ ≤ t₂) :
    ∫ r in Ioc t₁ t₂,
        μ_raw * (clockA ν r) ^ (-2 : ℝ) * Real.exp (μ_raw * (movingZ ν t₂ - movingZ ν r)) =
      Real.exp (μ_raw * (movingZ ν t₂ - movingZ ν t₁)) - 1 := by
  rw [← intervalIntegral.integral_of_le h12]
  set F_anti : ℝ → ℝ := fun r => -Real.exp (μ_raw * (movingZ ν t₂ - movingZ ν r))
  have hderiv : ∀ r ∈ uIcc t₁ t₂,
      HasDerivAt F_anti
        (μ_raw * (clockA ν r) ^ (-2 : ℝ) * Real.exp (μ_raw * (movingZ ν t₂ - movingZ ν r))) r := by
    intro r hr
    rw [uIcc_of_le h12] at hr
    have h1 := (hasDerivAt_exp_movingZ_sub t₂ μ_raw hν (ht₁.trans hr.1)).neg
    refine h1.congr_deriv ?_
    ring
  have hint : IntervalIntegrable
      (fun r => μ_raw * (clockA ν r) ^ (-2 : ℝ) * Real.exp (μ_raw * (movingZ ν t₂ - movingZ ν r)))
      volume t₁ t₂ := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le h12]
    refine ContinuousOn.integrableOn_Icc ?_
    have hcA : ContinuousOn (clockA ν) (Icc t₁ t₂) := by
      unfold clockA
      exact continuousOn_const.add (continuousOn_const.mul continuousOn_id)
    have hca_ne : ∀ r ∈ Icc t₁ t₂, clockA ν r ≠ 0 := by
      intro r hr
      have := one_le_clockA hν.le (ht₁.trans hr.1)
      linarith
    have hcA2 : ContinuousOn (fun r => (clockA ν r) ^ (-2 : ℝ)) (Icc t₁ t₂) :=
      hcA.rpow_const (fun r hr => Or.inl (hca_ne r hr))
    have hcZ : ContinuousOn (movingZ ν) (Icc t₁ t₂) := by
      unfold movingZ
      exact continuousOn_id.div hcA hca_ne
    have hcExp : ContinuousOn (fun r => Real.exp (μ_raw * (movingZ ν t₂ - movingZ ν r)))
        (Icc t₁ t₂) :=
      Real.continuous_exp.comp_continuousOn
        (continuousOn_const.mul (continuousOn_const.sub hcZ))
    exact (continuousOn_const.mul hcA2).mul hcExp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  dsimp [F_anti]
  rw [sub_self, mul_zero, Real.exp_zero]
  ring

/-- Lebesgue integral of `ENNReal.ofReal (μ_raw * (clockA ν r) ^ (-2 : ℝ) * Real.exp (μ_raw * (movingZ ν t₂ - movingZ ν r)))`
on `Ioc t₁ t₂` for `0 ≤ μ_raw`. -/
theorem lintegral_mul_exp_movingZ_sub {ν t₁ t₂ μ_raw : ℝ} (hμ : 0 ≤ μ_raw) (hν : 0 < ν)
    (ht₁ : 0 ≤ t₁) (h12 : t₁ ≤ t₂) :
    (∫⁻ r in Ioc t₁ t₂,
        ENNReal.ofReal
          (μ_raw * (clockA ν r) ^ (-2 : ℝ) * Real.exp (μ_raw * (movingZ ν t₂ - movingZ ν r)))) =
      ENNReal.ofReal (Real.exp (μ_raw * (movingZ ν t₂ - movingZ ν t₁)) - 1) := by
  have hint : IntegrableOn
      (fun r => μ_raw * (clockA ν r) ^ (-2 : ℝ) * Real.exp (μ_raw * (movingZ ν t₂ - movingZ ν r)))
      (Ioc t₁ t₂) := by
    refine IntegrableOn.mono_set ?_ Ioc_subset_Icc_self
    refine ContinuousOn.integrableOn_Icc ?_
    have hcA : ContinuousOn (clockA ν) (Icc t₁ t₂) := by
      unfold clockA
      exact continuousOn_const.add (continuousOn_const.mul continuousOn_id)
    have hca_ne : ∀ r ∈ Icc t₁ t₂, clockA ν r ≠ 0 := by
      intro r hr
      have := one_le_clockA hν.le (ht₁.trans hr.1)
      linarith
    have hcA2 : ContinuousOn (fun r => (clockA ν r) ^ (-2 : ℝ)) (Icc t₁ t₂) :=
      hcA.rpow_const (fun r hr => Or.inl (hca_ne r hr))
    have hcZ : ContinuousOn (movingZ ν) (Icc t₁ t₂) := by
      unfold movingZ
      exact continuousOn_id.div hcA hca_ne
    have hcExp : ContinuousOn (fun r => Real.exp (μ_raw * (movingZ ν t₂ - movingZ ν r)))
        (Icc t₁ t₂) :=
      Real.continuous_exp.comp_continuousOn
        (continuousOn_const.mul (continuousOn_const.sub hcZ))
    exact (continuousOn_const.mul hcA2).mul hcExp
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioc t₁ t₂)]
      (fun r => μ_raw * (clockA ν r) ^ (-2 : ℝ) * Real.exp (μ_raw * (movingZ ν t₂ - movingZ ν r))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    have ha : 0 < clockA ν r := lt_of_lt_of_le zero_lt_one (one_le_clockA hν.le (ht₁.trans hr.1.le))
    have ha2 : 0 ≤ (clockA ν r) ^ (-2 : ℝ) := (Real.rpow_pos_of_pos ha _).le
    positivity
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnonneg,
    integral_mul_exp_movingZ_sub μ_raw hν ht₁ h12]

end PerturbDuhamelSub

open PerturbDuhamelSub

/-! ## 4. Conditional assembly of `ShortComplPerturbDuhamel` (`PartIII-a:T21/c3/3/1`) -/

/-- **Conditional assembly of `ShortComplPerturbDuhamel` (`PartIII-a:T21/c3/3/1`, SP 2919-2925,
2937-2958, 2982-2988)** from `MovLamDualHeatBound κ` (`PartIII-a:T21/c5/3/1`),
`MovLamDualEulerSubBound κ` (`PartIII-a:T21/c5/3/2`), and `WeakFlowComplPerturbDuhamel κ`
(`PartIII-a:T21/c3/3/1/1`), using our unconditional proof `adjointLocalizedBound_uncond`. -/
theorem shortComplPerturbDuhamel_of (κ : PlanarFrameKernels)
    (hH : MovLamDualHeatBound κ)
    (hE : MovLamDualEulerSubBound κ)
    (hW : WeakFlowComplPerturbDuhamel κ) :
    ShortComplPerturbDuhamel κ :=
  hW (fun _ hm => adjointLocalizedBound_uncond hm) hH hE

end UnforcedLeray.Short.IIIa
