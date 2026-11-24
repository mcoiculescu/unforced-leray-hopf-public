import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T19
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.Inequalities
import UnforcedLeray.Short.PartI.Tasks.OverlapHighNorm
import UnforcedLeray.Short.PartI.Tasks.OverlapFluctuationDecay
import UnforcedLeray.Short.PartI.Tasks.OverlapMeanPrimitive
import UnforcedLeray.Short.PartI.Tasks.OverlapMeanDecay
import UnforcedLeray.Short.PartI.Tasks.TrainOverlapProof
import UnforcedLeray.Short.PartI.Tasks.TrainStrainIntegralProof

/-!
# Part III-a, task `PartIII-a:T19/3` (sub-module): tail energy continuation across `s = H` to `(0, ∞)`

Source of record: `the November 2 reference manuscript` (SP), lines 3517-3545
(Steps P5-P6 of `prop:short-polynomial-causal`).

## Decomposition into 4 leaf tasks

To avoid trace-gluing across a rough time slice, we separate the global tail continuation into four
independent analytic leaves:

1. **`PartIII-a:T19/3/1` (`TrainAdvectionEnergyIdentity`)**:
   Distributional weighted energy inequality for any causal zero-entrance energy solution
   `IsCausalEnergySolution c ν μ (trainVel tr) F b G` around a BUC train `tr`, tested against any
   nonnegative `C¹` compactly supported weight `ψ` on `(0, ∞)` with strain rate
   `L(s) = (B0277.supNormD 1 (tr.v s)).toReal` (SP 3518-3527).
2. **`PartIII-a:T19/3/2` (`TrainTailEnergyFromAdvection`)**:
   Assuming `TrainAdvectionEnergyIdentity`, proves `TrainTailEnergyBound`: testing with
   `ψ_B(s) = exp(-2 ∫_{H-1}^s L(τ) dτ) χ_B(s)` where `χ_B` ramps up on `[H - 1, H - 1/2]` and down
   on `[B, 2B]`, applying Young's inequality (`θ = ν`), using `s^{-1/2} ≤ H s^{-3/2}` on the ramp-up
   window `[H - 1, H - 1/2]`, and letting `B → ∞` bounds the tail norms on `[H - 1/2, ∞)` by
   `exp(2 I_H) (C_trace H ‖g⁻¹b_sol‖_{𝓗(0, H)}² + C_trace ν⁻¹ ‖g⁻¹F‖_𝒯²)` (SP 3525-3537).
3. **`PartIII-a:T19/3/3` (`TrainCausalExistence`)**:
   Global existence of a causal zero-entrance energy solution `(b_sol, G_sol)` of
   `IsCausalEnergySolution (ν ^ (-2 : ℝ)) ν μ (trainVel tr) F b_sol G_sol` for `0 < ν ≤ ν_ex`,
   obtained by Picard contraction of `S_0(F - flatMult tr b)` in the exponentially weighted space
   with weight `w_0(s) = exp(-λ s / (1 + s))` using `‖trainVel tr s‖_∞ ≤ K_tr / (1 + s)` (`lateVel_of`).
4. **`PartIII-a:T19/3/4` (`CoreCausalHomogeneousZero`)**:
   Uniqueness on the core `(0, H)`: any homogeneous core solution `(d, Gd)` of
   `IsCoreCausalSolution (ν ^ (-2 : ℝ)) ν H μ (trainVel tr) 0 d Gd` has
   `hCalNormOn (ν ^ (-2 : ℝ)) H (gainConj γ ν d) = 0` and
   `tCalNormOn (ν ^ (-2 : ℝ)) H (gainConj γ ν Gd) = 0`, proved by localizing
   `T19_PolyCausal/HomogeneousZero.lean` (`θ = ν` in `cutoff_young`) to tests supported in `(0, H)`.

## What is proved unconditionally in this file

* `trainOverlap_unconditional` and `trainStrainIntegral_unconditional` (`PartI:T12..T16, T18`).
* `coreEnd_tail_arithmetic` and `tail_strain_integral_bound` (SP 3528-3533).
* `hCalNormTail`, `tCalNormTail`, `hCalNorm_le_on_add_tail`, `tCalNorm_le_on_add_tail`.
* `coreCausalSol_of_causalSol`, `coreCausalSolSub`, `hCalNormOn_eq_of_sub_zero`,
  `tCalNormOn_eq_of_sub_zero`.
* `tailEnergyContinuation_of`: assembles `TailEnergyContinuation` from the four leaves.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-! ## 1. Unconditional Part I train overlap and late strain integral (`PartI:T12..T16, T18`) -/

/-- Unconditional assembly of `PartI.TrainOverlap` (`PartI:T16`) from `PartI:T12..T15`. -/
theorem trainOverlap_unconditional : UnforcedLeray.Short.PartI.TrainOverlap := by
  have hHN : UnforcedLeray.Short.PartI.OverlapHighNormUniform :=
    UnforcedLeray.Short.PartI.overlap_highnorm_uniform
  have hFD : UnforcedLeray.Short.PartI.OverlapFluctuationDecay :=
    UnforcedLeray.Short.PartI.overlap_fluctuation_decay hHN
  have hMP : UnforcedLeray.Short.PartI.OverlapMeanPrimitive :=
    UnforcedLeray.Short.PartI.overlap_mean_primitive
  have hMD : UnforcedLeray.Short.PartI.OverlapMeanDecay :=
    UnforcedLeray.Short.PartI.overlap_mean_decay hHN hFD hMP
  exact UnforcedLeray.Short.PartI.trainOverlap_proof hFD hMD

/-- Unconditional assembly of `PartI.TrainStrainIntegral` (`PartI:T18`, SP 318-319, 425-436). -/
theorem trainStrainIntegral_unconditional : UnforcedLeray.Short.PartI.TrainStrainIntegral :=
  UnforcedLeray.Short.PartI.trainStrainIntegral_proof trainOverlap_unconditional

/-! ## 2. Core endpoint and late strain integral bound on `(H - 1, ∞)` (SP 3528-3533) -/

/-- For `b ≥ 1` and `0 < ν ≤ min (1/2) ((3b)⁻¹)`, `H = coreEnd ν b` satisfies `2 < H`,
`0 ≤ ν(H - 1)`, `1 + ν(H - 1) ≤ (ν⁻²)²`, and `(2b)⁻¹ ≤ ν(1 + ν(H - 1))`. -/
theorem coreEnd_tail_arithmetic {b ν : ℝ} (hb : 1 ≤ b) (hν0 : 0 < ν) (hν_half : ν ≤ 1 / 2)
    (hν_3b : ν ≤ (3 * b)⁻¹) :
    2 < coreEnd ν b ∧
      0 ≤ ν * (coreEnd ν b - 1) ∧
      1 + ν * (coreEnd ν b - 1) ≤ (ν ^ (-2 : ℝ)) ^ 2 ∧
      (2 * b)⁻¹ ≤ ν * (1 + ν * (coreEnd ν b - 1)) := by
  have hb0 : 0 < b := by linarith
  have hν1 : ν ≤ 1 := hν_half.trans (by norm_num)
  have hνb_le : ν * b ≤ 1 / 3 := by
    calc ν * b ≤ (3 * b)⁻¹ * b := mul_le_mul_of_nonneg_right hν_3b hb0.le
      _ = 1 / 3 := by field_simp
  have hinv_ge : 3 ≤ (ν * b)⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) (mul_pos hν0 hb0)]
    linarith
  have hνinv_ge : 2 ≤ ν⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) hν0]
    linarith
  have hH_gt : 2 < coreEnd ν b := by
    unfold coreEnd
    have : 2 * 2 ≤ ν⁻¹ * ((ν * b)⁻¹ - 1) :=
      mul_le_mul hνinv_ge (by linarith) (by norm_num) (by positivity)
    linarith
  have hσ_eq : ν * (coreEnd ν b - 1) = (ν * b)⁻¹ - 1 - ν := by
    unfold coreEnd
    have hν_ne : ν ≠ 0 := hν0.ne'
    field_simp
  have hσ_nonneg : 0 ≤ ν * (coreEnd ν b - 1) := by
    rw [hσ_eq]
    linarith
  have h1σ_eq : 1 + ν * (coreEnd ν b - 1) = (ν * b)⁻¹ - ν := by
    rw [hσ_eq]
    ring
  have hinv_le : (ν * b)⁻¹ ≤ ν⁻¹ := by
    rw [mul_inv]
    have : b⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hb
    nlinarith [inv_pos.2 hν0]
  have h1σ_le_c2 : 1 + ν * (coreEnd ν b - 1) ≤ (ν ^ (-2 : ℝ)) ^ 2 := by
    have h1 : 1 + ν * (coreEnd ν b - 1) ≤ ν⁻¹ := by linarith [h1σ_eq, hinv_le]
    have h2 : ν⁻¹ ≤ (ν ^ (-2 : ℝ)) ^ 2 := by
      rw [← Real.rpow_neg_one, ← Real.rpow_natCast, ← Real.rpow_mul hν0.le]
      exact Real.rpow_le_rpow_of_exponent_ge hν0 hν1 (by norm_num)
    exact h1.trans h2
  have h1σ_ge : (2 * b)⁻¹ ≤ ν * (1 + ν * (coreEnd ν b - 1)) := by
    have hhalf_inv : 1 / 2 * (ν * b)⁻¹ ≤ (ν * b)⁻¹ - ν := by linarith
    calc (2 * b)⁻¹ = ν * (1 / 2 * (ν * b)⁻¹) := by
          have hν_ne : ν ≠ 0 := hν0.ne'
          have hb_ne : b ≠ 0 := hb0.ne'
          field_simp
      _ ≤ ν * (1 + ν * (coreEnd ν b - 1)) := by
          rw [h1σ_eq]
          exact mul_le_mul_of_nonneg_left hhalf_inv hν0.le
  exact ⟨hH_gt, hσ_nonneg, h1σ_le_c2, h1σ_ge⟩

/-- **Late strain integral bound on `(coreEnd ν b - 1, ∞)`** (SP 3528-3533), proved unconditionally
from `trainStrainIntegral_unconditional`. For any `b ≥ 1`, there exist `C_strain ≥ 0` and
`ν_strain > 0` such that for `0 < ν ≤ ν_strain` and every BUC train `tr` at `c = ν⁻²`,
`∫_{H-1}^∞ ‖Dv(s)‖_∞ ds ≤ C_strain * b + C_strain * ν³ ≤ 2 * C_strain * b`. -/
theorem tail_strain_integral_bound (b : ℝ) (hb : 1 ≤ b) :
    ∃ (C_strain ν_strain : ℝ), 0 ≤ C_strain ∧ 0 < ν_strain ∧
      ∀ ν ∈ Ioc 0 ν_strain, ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
        UnforcedLeray.Short.PartI.IsBUCTrain tr →
        2 < coreEnd ν b ∧
          (∫⁻ s in Ioi (coreEnd ν b - 1), UnforcedLeray.B0277.supNormD 1 (tr.v s) ≤
            ENNReal.ofReal (C_strain * b + C_strain * ν ^ 3)) ∧
          C_strain * b + C_strain * ν ^ 3 ≤ 2 * C_strain * b := by
  have hb0 : 0 < b := by linarith
  obtain ⟨C₀, ν₀, hC₀, hν₀, hStrain⟩ :=
    trainStrainIntegral_unconditional 2 (by norm_num : (1 / 2 : ℝ) < 2) 0
  set C_strain : ℝ := 2 * C₀
  set ν_strain : ℝ := min ν₀ (min (1 / 2) ((3 * b)⁻¹))
  have hC_strain : 0 ≤ C_strain := by unfold C_strain; positivity
  have hν_strain : 0 < ν_strain :=
    lt_min hν₀ (lt_min (by norm_num) (inv_pos.2 (by positivity)))
  refine ⟨C_strain, ν_strain, hC_strain, hν_strain, fun ν hν tr htr => ?_⟩
  have hν0 : 0 < ν := hν.1
  have hν_le0 : ν ≤ ν₀ := hν.2.trans (min_le_left _ _)
  have hν_half : ν ≤ 1 / 2 := hν.2.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hν_3b : ν ≤ (3 * b)⁻¹ := hν.2.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hν1 : ν ≤ 1 := hν_half.trans (by norm_num)
  obtain ⟨hH2, hσ0, h1σ_c2, h1σ_ge⟩ := coreEnd_tail_arithmetic hb hν0 hν_half hν_3b
  have hper : UnforcedLeray.Short.PartI.trainPeriod 2 ν = ν ^ (-2 : ℝ) := rfl
  set σ₀ : ℝ := ν * (coreEnd ν b - 1)
  have hσ_div : σ₀ / ν = coreEnd ν b - 1 := mul_div_cancel_left₀ _ hν0.ne'
  have hEst := hStrain ν hν0 hν_le0 tr htr σ₀ hσ0 h1σ_c2
  unfold UnforcedLeray.B0278.TrainStrainEstimate at hEst
  have hIcc : (Finset.Icc 1 (0 + 1) : Finset ℕ) = {1} := rfl
  have hEst' : ∫⁻ s in Ioi (coreEnd ν b - 1), UnforcedLeray.B0277.supNormD 1 (tr.v s) ≤
      ENNReal.ofReal (C₀ / (ν * (1 + σ₀)) + C₀ / (ν * (ν ^ (-2 : ℝ)) ^ 2)) := by
    simpa [hσ_div, hIcc, hper] using hEst
  have hterm1 : C₀ / (ν * (1 + σ₀)) ≤ C_strain * b := by
    calc C₀ / (ν * (1 + σ₀))
        ≤ C₀ / (2 * b)⁻¹ := div_le_div_of_nonneg_left hC₀.le (by positivity) h1σ_ge
      _ = C_strain * b := by rw [div_inv_eq_mul]; unfold C_strain; ring
  have hterm2 : C₀ / (ν * (ν ^ (-2 : ℝ)) ^ 2) ≤ C_strain * ν ^ 3 := by
    have hdenom : ν * (ν ^ (-2 : ℝ)) ^ 2 = (ν ^ 3)⁻¹ := by
      have h1 : (ν ^ (-2 : ℝ)) ^ 2 = ν ^ (-4 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hν0.le]
        norm_num
      have h2 : ν * ν ^ (-4 : ℝ) = ν ^ (-3 : ℝ) := by
        calc ν * ν ^ (-4 : ℝ) = ν ^ (1 : ℝ) * ν ^ (-4 : ℝ) := by rw [Real.rpow_one]
          _ = ν ^ (-3 : ℝ) := by rw [← Real.rpow_add hν0]; norm_num
      rw [h1, h2, show (-3 : ℝ) = -((3 : ℕ) : ℝ) by norm_num, Real.rpow_neg hν0.le,
        Real.rpow_natCast]
    rw [hdenom, div_inv_eq_mul]
    unfold C_strain
    have : 0 ≤ C₀ * ν ^ 3 := by positivity
    linarith
  have hbd1 : ∫⁻ s in Ioi (coreEnd ν b - 1), UnforcedLeray.B0277.supNormD 1 (tr.v s) ≤
      ENNReal.ofReal (C_strain * b + C_strain * ν ^ 3) :=
    hEst'.trans (ENNReal.ofReal_le_ofReal (add_le_add hterm1 hterm2))
  have hν3_le_b : ν ^ 3 ≤ b := by
    have h1 : ν ^ 3 ≤ 1 := pow_le_one₀ hν0.le hν1
    linarith
  refine ⟨hH2, hbd1, ?_⟩
  nlinarith

/-! ## 3. Core/tail norm splitting and core solution linearity -/

/-- `‖b‖_{𝓗(t_*, ∞)}`, the `𝓗` norm restricted to ages `s ≥ t_*`. -/
def hCalNormTail (c t_star : ℝ) (b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ) : ℝ≥0∞ :=
  eLpNorm (fun p => vnorm2 (b p)) 2 ((ageμ c (-3 / 2)).restrict (Ici t_star ×ˢ univ))

/-- `‖T‖_{𝒯(t_*, ∞)}`, the `𝒯` norm restricted to ages `s ≥ t_*`. -/
def tCalNormTail (c t_star : ℝ) (T : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ) : ℝ≥0∞ :=
  eLpNorm (fun p => tnorm2 (T p)) 2 ((ageμ c (-1 / 2)).restrict (Ici t_star ×ˢ univ))

/-- General `L²` norm splitting across `s < t_*` and `s ≥ t_*`. -/
private theorem eLpNorm_two_le_restrict_Iio_add_Ici (μ : Measure (ℝ × (ℝ × ℝ))) (t_star : ℝ)
    (F : ℝ × (ℝ × ℝ) → ℝ) (hF : ∀ p, 0 ≤ F p) :
    eLpNorm F 2 μ ≤
      eLpNorm F 2 (μ.restrict (Iio t_star ×ˢ univ)) +
        eLpNorm F 2 (μ.restrict (Ici t_star ×ˢ univ)) := by
  apply le_of_sq_le_sq
  rw [eLpNorm_two_sq_eq_lintegral_nonneg μ F hF]
  have hunion : (Iio t_star ×ˢ (univ : Set (ℝ × ℝ))) ∪ (Ici t_star ×ˢ univ) = univ := by
    rw [← union_prod, Iio_union_Ici, univ_prod_univ]
  have hcov : ∫⁻ p, ENNReal.ofReal (F p ^ 2) ∂μ ≤
      (∫⁻ p in Iio t_star ×ˢ univ, ENNReal.ofReal (F p ^ 2) ∂μ) +
        ∫⁻ p in Ici t_star ×ˢ univ, ENNReal.ofReal (F p ^ 2) ∂μ := by
    rw [← setLIntegral_univ, ← hunion]
    exact lintegral_union_le _ _ _
  refine hcov.trans ?_
  rw [← eLpNorm_two_sq_eq_lintegral_nonneg (μ.restrict (Iio t_star ×ˢ univ)) F hF,
    ← eLpNorm_two_sq_eq_lintegral_nonneg (μ.restrict (Ici t_star ×ˢ univ)) F hF]
  set A := eLpNorm F 2 (μ.restrict (Iio t_star ×ˢ univ))
  set B := eLpNorm F 2 (μ.restrict (Ici t_star ×ˢ univ))
  calc A ^ 2 + B ^ 2 ≤ A ^ 2 + B ^ 2 + 2 * A * B := le_self_add
    _ = (A + B) ^ 2 := by ring

theorem hCalNorm_le_on_add_tail (c t_star : ℝ) (b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ) :
    hCalNorm c b ≤ hCalNormOn c t_star b + hCalNormTail c t_star b :=
  eLpNorm_two_le_restrict_Iio_add_Ici (ageμ c (-3 / 2)) t_star (fun p => vnorm2 (b p))
    (fun _ => Real.sqrt_nonneg _)

theorem tCalNorm_le_on_add_tail (c t_star : ℝ) (T : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ) :
    tCalNorm c T ≤ tCalNormOn c t_star T + tCalNormTail c t_star T :=
  eLpNorm_two_le_restrict_Iio_add_Ici (ageμ c (-1 / 2)) t_star (fun p => tnorm2 (T p))
    (fun _ => Real.sqrt_nonneg _)

theorem hCalNormOn_mono {c t_star H : ℝ} (htH : t_star ≤ H)
    (b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ) :
    hCalNormOn c t_star b ≤ hCalNormOn c H b := by
  unfold hCalNormOn
  refine eLpNorm_mono_measure _ (Measure.restrict_mono ?_ le_rfl)
  exact prod_mono (Iio_subset_Iio htH) Subset.rfl

theorem tCalNormOn_mono {c t_star H : ℝ} (htH : t_star ≤ H)
    (T : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ) :
    tCalNormOn c t_star T ≤ tCalNormOn c H T := by
  unfold tCalNormOn
  refine eLpNorm_mono_measure _ (Measure.restrict_mono ?_ le_rfl)
  exact prod_mono (Iio_subset_Iio htH) Subset.rfl

/-- Every global causal zero-entrance energy solution restricts to a core solution on `(0, H)`. -/
theorem coreCausalSol_of_causalSol {c ν H : ℝ} {μ : ℂ} {vel : ℝ → ℝ × ℝ → Fin 2 → ℝ}
    {F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ} {b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ}
    {G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}
    (h : IsCausalEnergySolution c ν μ vel F b G) :
    IsCoreCausalSolution c ν H μ vel F b G where
  measurable := h.measurable
  gradMeasurable := h.gradMeasurable
  energyLoc s₁ s₂ hs₁ hs₁₂ _ := h.energyLoc s₁ s₂ hs₁ hs₁₂
  zeroEntrance := h.zeroEntrance
  divFree s hs := h.divFree s hs.1
  weakGrad s hs := h.weakGrad s hs.1
  integrable Φ hΦ _ := h.integrable Φ hΦ
  weak Φ hΦ _ := h.weak Φ hΦ

/-- Linearity of `IsCoreCausalSolution` under subtraction. -/
theorem coreCausalSolSub (c ν H : ℝ) (μ : ℂ) (vel : ℝ → ℝ × ℝ → Fin 2 → ℝ)
    (F F' : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ) (b b' : ℝ × (ℝ × ℝ) → Fin 2 → ℂ)
    (G G' : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ)
    (hb : IsCoreCausalSolution c ν H μ vel F b G)
    (hb' : IsCoreCausalSolution c ν H μ vel F' b' G') :
    IsCoreCausalSolution c ν H μ vel (fun p i j => F p i j - F' p i j)
      (fun p i => b p i - b' p i) (fun p i j => G p i j - G' p i j) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact (hb.measurable i).sub (hb'.measurable i)
  · intro i j
    exact (hb.gradMeasurable i j).sub (hb'.gradMeasurable i j)
  · intro s₁ s₂ h₁ h₂ hH
    have hI := hb.energyLoc s₁ s₂ h₁ h₂ hH
    have hI' := hb'.energyLoc s₁ s₂ h₁ h₂ hH
    have hX : Measurable fun p : ℝ × (ℝ × ℝ) => vnorm2 (b p) ^ 2 + tnorm2 (G p) ^ 2 :=
      ((causalLin_measurable_vnorm2 hb.measurable).pow_const 2).add
        ((causalLin_measurable_tnorm2 hb.gradMeasurable).pow_const 2)
    have hD : ∀ p : ℝ × (ℝ × ℝ),
        vnorm2 (fun i => b p i - b' p i) ^ 2 + tnorm2 (fun i j => G p i j - G' p i j) ^ 2 ≤
          2 * (vnorm2 (b p) ^ 2 + tnorm2 (G p) ^ 2) +
            2 * (vnorm2 (b' p) ^ 2 + tnorm2 (G' p) ^ 2) := fun p => by
      linarith [causalLin_vnorm2_sub_sq_le (b p) (b' p), causalLin_tnorm2_sub_sq_le (G p) (G' p)]
    have key := causalLin_lintegral_le (volume.restrict (Icc s₁ s₂ ×ˢ B0579.cell c)) hX hD
    exact lt_of_le_of_lt key (by finiteness)
  · obtain ⟨δ₁, hδ₁, hI₁⟩ := hb.zeroEntrance
    obtain ⟨δ₂, hδ₂, hI₂⟩ := hb'.zeroEntrance
    have hpos : 0 < min δ₁ δ₂ := lt_min hδ₁ hδ₂
    refine ⟨min δ₁ δ₂, hpos, ?_⟩
    have hsub₁ : Ioo (0 : ℝ) (min δ₁ δ₂) ×ˢ (univ : Set (ℝ × ℝ)) ⊆
        Ioo (0 : ℝ) δ₁ ×ˢ (univ : Set (ℝ × ℝ)) :=
      prod_mono (Ioo_subset_Ioo_right (min_le_left _ _)) Subset.rfl
    have hsub₂ : Ioo (0 : ℝ) (min δ₁ δ₂) ×ˢ (univ : Set (ℝ × ℝ)) ⊆
        Ioo (0 : ℝ) δ₂ ×ˢ (univ : Set (ℝ × ℝ)) :=
      prod_mono (Ioo_subset_Ioo_right (min_le_right _ _)) Subset.rfl
    have hfin₁ : ∫⁻ p, ENNReal.ofReal (vnorm2 (b p) ^ 2)
        ∂((ageμ c (-3 / 2)).restrict (Ioo (0 : ℝ) (min δ₁ δ₂) ×ˢ univ)) < ⊤ :=
      lt_of_le_of_lt (lintegral_mono' (Measure.restrict_mono hsub₁ le_rfl) le_rfl) hI₁
    have hfin₂ : ∫⁻ p, ENNReal.ofReal (vnorm2 (b' p) ^ 2)
        ∂((ageμ c (-3 / 2)).restrict (Ioo (0 : ℝ) (min δ₁ δ₂) ×ˢ univ)) < ⊤ :=
      lt_of_le_of_lt (lintegral_mono' (Measure.restrict_mono hsub₂ le_rfl) le_rfl) hI₂
    have hXb : Measurable fun p : ℝ × (ℝ × ℝ) => vnorm2 (b p) ^ 2 :=
      (causalLin_measurable_vnorm2 hb.measurable).pow_const 2
    have hD0 : ∀ p : ℝ × (ℝ × ℝ),
        vnorm2 (fun i => b p i - b' p i) ^ 2 ≤ 2 * vnorm2 (b p) ^ 2 + 2 * vnorm2 (b' p) ^ 2 :=
      fun p => causalLin_vnorm2_sub_sq_le (b p) (b' p)
    have key := causalLin_lintegral_le
      ((ageμ c (-3 / 2)).restrict (Ioo (0 : ℝ) (min δ₁ δ₂) ×ˢ univ)) hXb hD0
    exact lt_of_le_of_lt key (by finiteness)
  · intro s hs ψ hψ
    have h0 := hb.divFree s hs ψ hψ
    have h0' := hb'.divFree s hs ψ hψ
    have I0 : IntegrableOn (fun x => b (s, x) 0 * (B0579.pd 0 ψ x : ℂ)) (B0579.cell c) :=
      ((hb.weakGrad s hs 0 0).1 ψ hψ).1
    have I1 : IntegrableOn (fun x => b (s, x) 1 * (B0579.pd 1 ψ x : ℂ)) (B0579.cell c) :=
      ((hb.weakGrad s hs 1 1).1 ψ hψ).1
    have J0 : IntegrableOn (fun x => b' (s, x) 0 * (B0579.pd 0 ψ x : ℂ)) (B0579.cell c) :=
      ((hb'.weakGrad s hs 0 0).1 ψ hψ).1
    have J1 : IntegrableOn (fun x => b' (s, x) 1 * (B0579.pd 1 ψ x : ℂ)) (B0579.cell c) :=
      ((hb'.weakGrad s hs 1 1).1 ψ hψ).1
    show ∫ x in B0579.cell c, ((b (s, x) 0 - b' (s, x) 0) * (B0579.pd 0 ψ x : ℂ) +
      (b (s, x) 1 - b' (s, x) 1) * (B0579.pd 1 ψ x : ℂ)) = 0
    have eqfun : (fun x => (b (s, x) 0 - b' (s, x) 0) * (B0579.pd 0 ψ x : ℂ) +
        (b (s, x) 1 - b' (s, x) 1) * (B0579.pd 1 ψ x : ℂ)) =
        fun x => (b (s, x) 0 * (B0579.pd 0 ψ x : ℂ) + b (s, x) 1 * (B0579.pd 1 ψ x : ℂ)) -
          (b' (s, x) 0 * (B0579.pd 0 ψ x : ℂ) + b' (s, x) 1 * (B0579.pd 1 ψ x : ℂ)) := by
      funext x
      ring
    have hI : IntegrableOn (fun x => b (s, x) 0 * (B0579.pd 0 ψ x : ℂ) +
        b (s, x) 1 * (B0579.pd 1 ψ x : ℂ)) (B0579.cell c) := Integrable.add I0 I1
    have hJ : IntegrableOn (fun x => b' (s, x) 0 * (B0579.pd 0 ψ x : ℂ) +
        b' (s, x) 1 * (B0579.pd 1 ψ x : ℂ)) (B0579.cell c) := Integrable.add J0 J1
    rw [eqfun, integral_sub hI hJ, h0, h0', sub_self]
  · intro s hs i j
    have hE := hb.weakGrad s hs i j
    have hE' := hb'.weakGrad s hs i j
    unfold HasWeakCellDerivC at hE hE' ⊢
    refine ⟨fun ψ hψ => ?_, fun ψ hψ => ?_⟩
    · obtain ⟨hA1, hA2⟩ := hE.1 ψ hψ
      obtain ⟨hB1, hB2⟩ := hE'.1 ψ hψ
      refine ⟨?_, ?_⟩
      · have e : (fun x => (b (s, x) i - b' (s, x) i) * (B0579.pd j ψ x : ℂ)) =
            fun x => b (s, x) i * (B0579.pd j ψ x : ℂ) - b' (s, x) i * (B0579.pd j ψ x : ℂ) := by
          funext x
          ring
        show IntegrableOn (fun x => (b (s, x) i - b' (s, x) i) * (B0579.pd j ψ x : ℂ))
          (B0579.cell c)
        rw [e]
        exact Integrable.sub hA1 hB1
      · have e : (fun x => (G (s, x) i j - G' (s, x) i j) * (ψ x : ℂ)) =
            fun x => G (s, x) i j * (ψ x : ℂ) - G' (s, x) i j * (ψ x : ℂ) := by
          funext x
          ring
        show IntegrableOn (fun x => (G (s, x) i j - G' (s, x) i j) * (ψ x : ℂ))
          (B0579.cell c)
        rw [e]
        exact Integrable.sub hA2 hB2
    · have hA1 : IntegrableOn (fun x => b (s, x) i * (B0579.pd j ψ x : ℂ)) (B0579.cell c) :=
        (hE.1 ψ hψ).1
      have hB1 : IntegrableOn (fun x => b' (s, x) i * (B0579.pd j ψ x : ℂ)) (B0579.cell c) :=
        (hE'.1 ψ hψ).1
      have hA2 : IntegrableOn (fun x => G (s, x) i j * (ψ x : ℂ)) (B0579.cell c) :=
        (hE.1 ψ hψ).2
      have hB2 : IntegrableOn (fun x => G' (s, x) i j * (ψ x : ℂ)) (B0579.cell c) :=
        (hE'.1 ψ hψ).2
      have eq1 : ∫ x in B0579.cell c, b (s, x) i * (B0579.pd j ψ x : ℂ) =
          -∫ x in B0579.cell c, G (s, x) i j * (ψ x : ℂ) := hE.2 ψ hψ
      have eq2 : ∫ x in B0579.cell c, b' (s, x) i * (B0579.pd j ψ x : ℂ) =
          -∫ x in B0579.cell c, G' (s, x) i j * (ψ x : ℂ) := hE'.2 ψ hψ
      have eA : ∫ x in B0579.cell c, (b (s, x) i - b' (s, x) i) * (B0579.pd j ψ x : ℂ) =
          (∫ x in B0579.cell c, b (s, x) i * (B0579.pd j ψ x : ℂ)) -
            ∫ x in B0579.cell c, b' (s, x) i * (B0579.pd j ψ x : ℂ) := by
        rw [← integral_sub hA1 hB1]
        congr 1
        funext x
        ring
      have eB : ∫ x in B0579.cell c, (G (s, x) i j - G' (s, x) i j) * (ψ x : ℂ) =
          (∫ x in B0579.cell c, G (s, x) i j * (ψ x : ℂ)) -
            ∫ x in B0579.cell c, G' (s, x) i j * (ψ x : ℂ) := by
        rw [← integral_sub hA2 hB2]
        congr 1
        funext x
        ring
      show ∫ x in B0579.cell c, (b (s, x) i - b' (s, x) i) * (B0579.pd j ψ x : ℂ) =
        -∫ x in B0579.cell c, (G (s, x) i j - G' (s, x) i j) * (ψ x : ℂ)
      linear_combination eA + eB + eq1 - eq2
  · intro Φ hΦ hsupp
    have hfun : flatIntegrand ν μ vel (fun p i j => F p i j - F' p i j)
        (fun p i => b p i - b' p i) Φ =
        fun p => flatIntegrand ν μ vel F b Φ p - flatIntegrand ν μ vel F' b' Φ p :=
      funext fun p => causalLin_flatIntegrand_sub ν μ vel F F' b b' Φ p
    rw [hfun]
    exact Integrable.sub (hb.integrable Φ hΦ hsupp) (hb'.integrable Φ hΦ hsupp)
  · intro Φ hΦ hsupp
    have hfun : flatIntegrand ν μ vel (fun p i j => F p i j - F' p i j)
        (fun p i => b p i - b' p i) Φ =
        fun p => flatIntegrand ν μ vel F b Φ p - flatIntegrand ν μ vel F' b' Φ p :=
      funext fun p => causalLin_flatIntegrand_sub ν μ vel F F' b b' Φ p
    rw [hfun, integral_sub (hb.integrable Φ hΦ hsupp) (hb'.integrable Φ hΦ hsupp),
      hb.weak Φ hΦ hsupp, hb'.weak Φ hΦ hsupp, sub_self]

theorem measurable_tnorm2_gainConj (γ ν : ℝ) {f : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}
    (hf : ∀ i j, Measurable fun p => f p i j) :
    Measurable fun p => tnorm2 (gainConj γ ν f p) := by
  unfold tnorm2 gainConj
  refine Measurable.sqrt (Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_)
  have hg : Measurable fun p : ℝ × (ℝ × ℝ) => (gainG γ ν p.1)⁻¹ := by
    unfold gainG
    exact (Real.measurable_exp.comp ((measurable_const.mul measurable_fst).div
      (measurable_const.add (measurable_const.mul measurable_fst)))).inv
  have h : Measurable fun p : ℝ × (ℝ × ℝ) => (gainG γ ν p.1)⁻¹ • f p i j := hg.smul (hf i j)
  simpa only [Pi.smul_apply] using h.norm.pow_const 2

theorem eq_zero_of_tnorm2_gainConj {γ ν : ℝ} {f : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}
    {p : ℝ × (ℝ × ℝ)} (h : tnorm2 (gainConj γ ν f p) = 0) : f p = 0 := by
  unfold tnorm2 at h
  have hs : ∑ i : Fin 2, ∑ j : Fin 2, ‖gainConj γ ν f p i j‖ ^ 2 = 0 :=
    (Real.sqrt_eq_zero (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _)).1 h
  have hi := (Finset.sum_eq_zero_iff_of_nonneg fun i _ =>
    Finset.sum_nonneg fun j _ => sq_nonneg ‖gainConj γ ν f p i j‖).1 hs
  funext i j
  have hj := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => sq_nonneg ‖gainConj γ ν f p i j‖).1
    (hi i (Finset.mem_univ i))
  have h0 : gainConj γ ν f p i j = 0 :=
    norm_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 (hj j (Finset.mem_univ j)))
  unfold gainConj at h0
  simp only [Pi.smul_apply] at h0
  rcases smul_eq_zero.1 h0 with h1 | h1
  · exact absurd h1 (inv_ne_zero (Real.exp_pos _).ne')
  · simpa using h1

theorem hCalNormOn_eq_of_sub_zero {c γ ν H : ℝ}
    {b₁ b₂ : ℝ × (ℝ × ℝ) → Fin 2 → ℂ}
    (hb₁ : ∀ i, Measurable fun p => b₁ p i) (hb₂ : ∀ i, Measurable fun p => b₂ p i)
    (h0 : hCalNormOn c H (gainConj γ ν (fun p i => b₁ p i - b₂ p i)) = 0) :
    hCalNormOn c H (gainConj γ ν b₁) = hCalNormOn c H (gainConj γ ν b₂) := by
  unfold hCalNormOn at h0 ⊢
  have hm : Measurable fun p : ℝ × (ℝ × ℝ) =>
      vnorm2 (gainConj γ ν (fun p i => b₁ p i - b₂ p i) p) :=
    measurable_vnorm2_gainConj γ ν fun i => (hb₁ i).sub (hb₂ i)
  have hae := (eLpNorm_eq_zero_iff hm.aestronglyMeasurable (by norm_num)).1 h0
  refine eLpNorm_congr_ae ?_
  filter_upwards [hae] with p hp
  have hp0 : (fun i => b₁ p i - b₂ p i) = 0 := eq_zero_of_vnorm2_gainConj hp
  have hp_eq : b₁ p = b₂ p := by
    funext i
    have hi := congrFun hp0 i
    simpa [sub_eq_zero] using hi
  simp only [gainConj, hp_eq]

theorem tCalNormOn_eq_of_sub_zero {c γ ν H : ℝ}
    {G₁ G₂ : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}
    (hG₁ : ∀ i j, Measurable fun p => G₁ p i j) (hG₂ : ∀ i j, Measurable fun p => G₂ p i j)
    (h0 : tCalNormOn c H (gainConj γ ν (fun p i j => G₁ p i j - G₂ p i j)) = 0) :
    tCalNormOn c H (gainConj γ ν G₁) = tCalNormOn c H (gainConj γ ν G₂) := by
  unfold tCalNormOn at h0 ⊢
  have hm : Measurable fun p : ℝ × (ℝ × ℝ) =>
      tnorm2 (gainConj γ ν (fun p i j => G₁ p i j - G₂ p i j) p) :=
    measurable_tnorm2_gainConj γ ν fun i j => (hG₁ i j).sub (hG₂ i j)
  have hae := (eLpNorm_eq_zero_iff hm.aestronglyMeasurable (by norm_num)).1 h0
  refine eLpNorm_congr_ae ?_
  filter_upwards [hae] with p hp
  have hp0 : (fun i j => G₁ p i j - G₂ p i j) = 0 := eq_zero_of_tnorm2_gainConj hp
  have hp_eq : G₁ p = G₂ p := by
    funext i j
    have hij := congrFun (congrFun hp0 i) j
    simpa [sub_eq_zero] using hij
  simp only [gainConj, hp_eq]

/-! ## 4. The four leaf statements for `PartIII-a:T19/3` (`PartIII-a:T19/3/1..4`) -/

/-- **Leaf `PartIII-a:T19/3/1` (`TrainAdvectionEnergyIdentity`)**:
Distributional weighted energy inequality for any causal zero-entrance energy solution
`IsCausalEnergySolution c ν μ (trainVel tr) F b G` around a BUC train `tr`, tested against any
nonnegative `C¹` compactly supported weight `ψ` on `(0, ∞)` (SP 3518-3527).
Obtained by reducing to the free equation with effective forcing `F - flatMult tr b` via
`causal_free_reduction`, applying `lionsMagenesCyl (flatWeakFromDensity divFreeCutoffDensity)`,
integrating the advection term `v·∇u` by parts on `B0579.cell c` (`div v = 0`) and bounding the
stretching term `u·∇v` by `(B0277.supNormD 1 (tr.v s)).toReal * ∫ |u|²`, and passing from `C^∞_c` to
`C¹_c` weights via `CoreToSmoothAux.real_core` and `smoothToC1Weighted`. -/
def TrainAdvectionEnergyIdentity : Prop :=
  ∀ (c ν γ : ℝ) (μ : ℂ), 0 < c → 0 < ν → 0 ≤ γ →
    ∀ tr : UnforcedLeray.B0140.TrainSol ν c, UnforcedLeray.Short.PartI.IsBUCTrain tr →
    ∀ (F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ) (b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ)
      (G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ),
    (∀ s₁ s₂ : ℝ, 0 < s₁ → s₁ < s₂ →
      ∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c, ENNReal.ofReal (tnorm2 (F p) ^ 2) < ⊤) →
    (∀ i j, Measurable fun p => F p i j) →
    IsCausalEnergySolution c ν μ (trainVel tr) F b G →
    ∀ ψ : ℝ → ℝ, ContDiff ℝ 1 ψ → HasCompactSupport ψ → tsupport ψ ⊆ Ioi 0 → (∀ s, 0 ≤ ψ s) →
      (∫ s in Ioi (0 : ℝ), ψ s *
          ((1 / 2 + 2 * μ.re) * s ^ (-3 / 2 : ℝ) *
              (∫ x in B0579.cell c, vnorm2 (gainConj γ ν b (s, x)) ^ 2) +
            2 * ν * s ^ (-1 / 2 : ℝ) * ∫ x in B0579.cell c, tnorm2 (gainConj γ ν G (s, x)) ^ 2))
        ≤ (∫ s in Ioi (0 : ℝ),
            (deriv ψ s + 2 * (UnforcedLeray.B0277.supNormD 1 (tr.v s)).toReal * ψ s) *
              (s ^ (-1 / 2 : ℝ) * ∫ x in B0579.cell c, vnorm2 (gainConj γ ν b (s, x)) ^ 2)) +
          2 * ∫ s in Ioi (0 : ℝ), ψ s * s ^ (-1 / 2 : ℝ) *
            ∫ x in B0579.cell c, tnorm2 (gainConj γ ν F (s, x)) * tnorm2 (gainConj γ ν G (s, x))

/-- Integrated squared tail energy bound on `[H - 1/2, ∞)` for any global causal solution
`(b_sol, G_sol)` around a BUC train `tr` with `∫_{H-1}^∞ ‖Dv(s)‖_∞ ds ≤ I_H` (SP 3525-3537). -/
def TrainTailEnergyBound : Prop :=
  ∀ P : PlanarData, IsPlanarReference P → ∀ K : Set ℂ, IsAdmissibleK K →
    ∃ C_trace : ℝ, 0 ≤ C_trace ∧
      ∀ (ν H I_H : ℝ), 0 < ν → 2 < H → 0 ≤ I_H →
        ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
          UnforcedLeray.Short.PartI.IsBUCTrain tr →
          (∫⁻ s in Ioi (H - 1), UnforcedLeray.B0277.supNormD 1 (tr.v s) ≤ ENNReal.ofReal I_H) →
          ∀ μ ∈ K,
          ∀ F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ, (∀ p i j, F p i j = F p j i) →
            (∀ i j, Measurable fun p => F p i j) →
            tCalNorm (ν ^ (-2 : ℝ)) (gainConj P.eigenvalue.re ν F) < ⊤ →
            ∀ b_sol G_sol,
              IsCausalEnergySolution (ν ^ (-2 : ℝ)) ν μ (trainVel tr) F b_sol G_sol →
              ENNReal.ofReal (2 * (⨅ μ' : K, μ'.1.re + 1 / 4)) *
                  hCalNormTail (ν ^ (-2 : ℝ)) (H - 1 / 2) (gainConj P.eigenvalue.re ν b_sol) ^ 2 +
                ENNReal.ofReal ν *
                  tCalNormTail (ν ^ (-2 : ℝ)) (H - 1 / 2) (gainConj P.eigenvalue.re ν G_sol) ^ 2 ≤
                ENNReal.ofReal (Real.exp (2 * I_H)) *
                  (ENNReal.ofReal (C_trace * H) *
                      hCalNormOn (ν ^ (-2 : ℝ)) H (gainConj P.eigenvalue.re ν b_sol) ^ 2 +
                    ENNReal.ofReal (C_trace * ν⁻¹) *
                      tCalNorm (ν ^ (-2 : ℝ)) (gainConj P.eigenvalue.re ν F) ^ 2)

/-- **Leaf `PartIII-a:T19/3/2` (`TrainTailEnergyFromAdvection`)**:
Deduces `TrainTailEnergyBound` from `TrainAdvectionEnergyIdentity` by testing with
`ψ_B(s) = exp(-2 ∫_{H-1}^s L(τ) dτ) χ_B(s)` where `χ_B` ramps up on `[H - 1, H - 1/2]` and down on
`[B, 2B]`, applying Young's inequality (`θ = ν`), bounding the ramp-up term on `[H - 1, H - 1/2]`
via `s^{-1/2} ≤ H s^{-3/2}`, and letting `B → ∞` (SP 3525-3537). -/
def TrainTailEnergyFromAdvection : Prop :=
  TrainAdvectionEnergyIdentity → TrainTailEnergyBound

/-- **Leaf `PartIII-a:T19/3/3` (`TrainCausalExistence`)**:
Global existence of a causal zero-entrance energy solution `(b_sol, G_sol)` of
`IsCausalEnergySolution (ν ^ (-2 : ℝ)) ν μ (trainVel tr) F b_sol G_sol` for `0 < ν ≤ ν_ex`,
obtained by Picard contraction of `(b_{n+1}, G_{n+1}) = S_0(F - flatMult tr b_n)` (`freeCausalExistsUnique`)
in the exponentially weighted norm with weight `w_0(s) = exp(-λ s / (1 + s))` using the uniform bound
`‖trainVel tr s‖_∞ ≤ K_tr / (1 + s)` (`lateVel_of lateFluctVel lateMeanVel` at `mZ = 0` and
`IsBUCTrain.sup_bound`) and `weightedEnergyIdentity`. -/
def TrainCausalExistence : Prop :=
  ∀ P : PlanarData, IsPlanarReference P → ∀ K : Set ℂ, IsAdmissibleK K →
    ∃ ν_ex : ℝ, 0 < ν_ex ∧
      ∀ ν ∈ Ioc 0 ν_ex, ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
        UnforcedLeray.Short.PartI.IsBUCTrain tr → ∀ μ ∈ K,
        ∀ F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ, (∀ p i j, F p i j = F p j i) →
          (∀ i j, Measurable fun p => F p i j) →
          tCalNorm (ν ^ (-2 : ℝ)) (gainConj P.eigenvalue.re ν F) < ⊤ →
          ∃ b_sol G_sol,
            IsCausalEnergySolution (ν ^ (-2 : ℝ)) ν μ (trainVel tr) F b_sol G_sol

/-- **Leaf `PartIII-a:T19/3/4` (`CoreCausalHomogeneousZero`)**:
Uniqueness on the core `(0, H)` (SP 3541-3545): any homogeneous core solution `(d, Gd)` satisfying
`IsCoreCausalSolution (ν ^ (-2 : ℝ)) ν H μ (trainVel tr) 0 d Gd` has
`hCalNormOn (ν ^ (-2 : ℝ)) H (gainConj P.eigenvalue.re ν d) = 0` and
`tCalNormOn (ν ^ (-2 : ℝ)) H (gainConj P.eigenvalue.re ν Gd) = 0`.
Proved by localizing `T19_PolyCausal/HomogeneousZero.lean` (`θ = ν` in `cutoff_young`) to `[a, 2B] ⊂ (0, H)`
using a smooth temporal cutoff supported in `(0, H)` in `lmEnergyBridge`. -/
def CoreCausalHomogeneousZero : Prop :=
  ∀ P : PlanarData, IsPlanarReference P → ∀ K : Set ℂ, IsAdmissibleK K →
    ∀ (ν H : ℝ), 0 < ν → 0 < H →
      ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
        UnforcedLeray.Short.PartI.IsBUCTrain tr → ∀ μ ∈ K,
        ∀ d Gd,
          IsCoreCausalSolution (ν ^ (-2 : ℝ)) ν H μ (trainVel tr) (fun _ _ _ => 0) d Gd →
          hCalNormOn (ν ^ (-2 : ℝ)) H (gainConj P.eigenvalue.re ν d) = 0 ∧
            tCalNormOn (ν ^ (-2 : ℝ)) H (gainConj P.eigenvalue.re ν Gd) = 0

/-! ## 5. Assembly of `TailEnergyContinuation` from the four leaves -/

/-- **Conditional assembly of `TailEnergyContinuation`** (`PartIII-a:T19/3`, SP 3517-3540) from the
four leaves `TrainAdvectionEnergyIdentity`, `TrainTailEnergyFromAdvection`, `TrainCausalExistence`,
and `CoreCausalHomogeneousZero`. -/
theorem tailEnergyContinuation_of (hAdv : TrainAdvectionEnergyIdentity)
    (hTail : TrainTailEnergyFromAdvection) (hEx : TrainCausalExistence)
    (hCore : CoreCausalHomogeneousZero) :
    TailEnergyContinuation := by
  intro P hP K hK b hb1
  obtain ⟨C_trace, hC_trace, hTail_P⟩ := (hTail hAdv) P hP K hK
  obtain ⟨ν_ex, hν_ex, hEx_P⟩ := hEx P hP K hK
  obtain ⟨C_strain, ν_strain, hC_strain, hν_strain, hStrain_b⟩ := tail_strain_integral_bound b hb1
  have hb0 : 0 < b := by linarith
  set K_tail : ℝ := Real.sqrt (2 * C_trace) * Real.exp (2 * C_strain * b)
  set C_tail : ℝ := 1 + 2 * K_tail
  set ν_tail : ℝ := min (min ν_strain ν_ex) (min (1 / 2) ((2 * b)⁻¹))
  have hK_tail : 0 ≤ K_tail := by unfold K_tail; positivity
  have hC_tail : 0 ≤ C_tail := by unfold C_tail; positivity
  have hν_tail : 0 < ν_tail :=
    lt_min (lt_min hν_strain hν_ex) (lt_min (by norm_num) (inv_pos.2 (by positivity)))
  refine ⟨C_tail, ν_tail, hC_tail, hν_tail, fun ν hν tr htr μ hμ F hsym hmeas hfin b_core G_core hCoreSol => ?_⟩
  have hν0 : 0 < ν := hν.1
  have hν_s : ν ≤ ν_strain := hν.2.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hν_e : ν ≤ ν_ex := hν.2.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hν_half : ν ≤ 1 / 2 := hν.2.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hν_2b : ν ≤ (2 * b)⁻¹ := hν.2.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hνinv_ge1 : 1 ≤ ν⁻¹ := by
    rw [le_inv_comm₀ zero_lt_one hν0]
    linarith
  obtain ⟨-, -, hsqrtH, -⟩ := coreEnd_bounds hb1 hν0 hν_half hν_2b
  obtain ⟨hH2, hStrain_int, hIH_le⟩ := hStrain_b ν ⟨hν0, hν_s⟩ tr htr
  set H : ℝ := coreEnd ν b
  have hH_pos : 0 < H := by linarith
  set I_H : ℝ := C_strain * b + C_strain * ν ^ 3
  have hIH0 : 0 ≤ I_H := by unfold I_H; positivity
  obtain ⟨b_sol, G_sol, hSol⟩ := hEx_P ν ⟨hν0, hν_e⟩ tr htr μ hμ F hsym hmeas hfin
  have hSq_sol := hTail_P ν H I_H hν0 hH2 hIH0 tr htr hStrain_int μ hμ F hsym hmeas hfin b_sol G_sol hSol
  -- Identify core norms of `(b_sol, G_sol)` with `(b_core, G_core)` via `CoreCausalHomogeneousZero`
  have hSol_core : IsCoreCausalSolution (ν ^ (-2 : ℝ)) ν H μ (trainVel tr) F b_sol G_sol :=
    coreCausalSol_of_causalSol hSol
  have hDiff_core := coreCausalSolSub (ν ^ (-2 : ℝ)) ν H μ (trainVel tr) F F
    b_sol b_core G_sol G_core hSol_core hCoreSol
  have hF0 : (fun (p : ℝ × (ℝ × ℝ)) (i j : Fin 2) => F p i j - F p i j) =
      fun _ _ _ => (0 : ℂ) := by
    funext p i j
    exact sub_self _
  rw [hF0] at hDiff_core
  obtain ⟨hb_diff0, hG_diff0⟩ := hCore P hP K hK ν H hν0 hH_pos tr htr μ hμ
    (fun p i => b_sol p i - b_core p i) (fun p i j => G_sol p i j - G_core p i j) hDiff_core
  set c : ℝ := ν ^ (-2 : ℝ)
  set γ : ℝ := P.eigenvalue.re
  set t_star : ℝ := H - 1 / 2
  have hb_eq_H : hCalNormOn c H (gainConj γ ν b_sol) = hCalNormOn c H (gainConj γ ν b_core) :=
    hCalNormOn_eq_of_sub_zero hSol.measurable hCoreSol.measurable hb_diff0
  have hG_eq_H : tCalNormOn c H (gainConj γ ν G_sol) = tCalNormOn c H (gainConj γ ν G_core) :=
    tCalNormOn_eq_of_sub_zero hSol.gradMeasurable hCoreSol.gradMeasurable hG_diff0
  have hSq :
      ENNReal.ofReal (2 * (⨅ μ' : K, μ'.1.re + 1 / 4)) *
          hCalNormTail c t_star (gainConj γ ν b_sol) ^ 2 +
        ENNReal.ofReal ν *
          tCalNormTail c t_star (gainConj γ ν G_sol) ^ 2 ≤
        ENNReal.ofReal (Real.exp (2 * I_H)) *
          (ENNReal.ofReal (C_trace * H) *
              hCalNormOn c H (gainConj γ ν b_core) ^ 2 +
            ENNReal.ofReal (C_trace * ν⁻¹) *
              tCalNorm c (gainConj γ ν F) ^ 2) := by
    rwa [hb_eq_H] at hSq_sol
  refine ⟨b_sol, G_sol, hSol, ?_⟩
  set U_core := hCalNormOn c H (gainConj γ ν b_core)
  set G_core_n := tCalNormOn c H (gainConj γ ν G_core)
  set TF := tCalNorm c (gainConj γ ν F)
  set S_rhs := U_core + ENNReal.ofReal (Real.sqrt ν) * G_core_n + TF
  set U_on := hCalNormOn c t_star (gainConj γ ν b_sol)
  set G_on := tCalNormOn c t_star (gainConj γ ν G_sol)
  set U_tail := hCalNormTail c t_star (gainConj γ ν b_sol)
  set G_tail := tCalNormTail c t_star (gainConj γ ν G_sol)
  have htH : t_star ≤ H := by unfold t_star; linarith
  have hU_on : U_on ≤ U_core :=
    (hCalNormOn_mono htH (gainConj γ ν b_sol)).trans hb_eq_H.le
  have hG_on : G_on ≤ G_core_n :=
    (tCalNormOn_mono htH (gainConj γ ν G_sol)).trans hG_eq_H.le
  have hOn_sum : U_on + ENNReal.ofReal (Real.sqrt ν) * G_on ≤
      ENNReal.ofReal (1 * ν⁻¹) * S_rhs := by
    have h1 : U_on + ENNReal.ofReal (Real.sqrt ν) * G_on ≤ S_rhs :=
      (add_le_add hU_on (mul_le_mul_of_nonneg_left hG_on bot_le)).trans le_self_add
    refine h1.trans ?_
    rw [one_mul]
    exact le_mul_of_one_le_left bot_le (ENNReal.one_le_ofReal.2 hνinv_ge1)
  have hH_le_inv_sq : H ≤ (ν⁻¹) ^ 2 := by
    have hH0 : 0 ≤ H := by linarith
    calc H = Real.sqrt H ^ 2 := (Real.sq_sqrt hH0).symm
      _ ≤ (ν⁻¹) ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hsqrtH 2
  have hνinv_le_sq : ν⁻¹ ≤ (ν⁻¹) ^ 2 := by
    rw [sq]
    exact le_mul_of_one_le_left (by positivity) hνinv_ge1
  have hexp_le : Real.exp (2 * I_H) ≤ (Real.exp (2 * C_strain * b)) ^ 2 := by
    rw [← Real.exp_nat_mul, Nat.cast_two]
    exact Real.exp_le_exp.2 (by linarith)
  have hRHS_sq :
      ENNReal.ofReal (Real.exp (2 * I_H)) *
          (ENNReal.ofReal (C_trace * H) * U_core ^ 2 +
            ENNReal.ofReal (C_trace * ν⁻¹) * TF ^ 2) ≤
        ENNReal.ofReal (1 / 2) * (ENNReal.ofReal (K_tail * ν⁻¹) * S_rhs) ^ 2 := by
    have h1 : ENNReal.ofReal (C_trace * H) ≤ ENNReal.ofReal (C_trace * (ν⁻¹) ^ 2) :=
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hH_le_inv_sq hC_trace)
    have h2 : ENNReal.ofReal (C_trace * ν⁻¹) ≤ ENNReal.ofReal (C_trace * (ν⁻¹) ^ 2) :=
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hνinv_le_sq hC_trace)
    have h3 : U_core ^ 2 + TF ^ 2 ≤ S_rhs ^ 2 := by
      have hU_le : U_core + TF ≤ S_rhs := by
        unfold S_rhs
        gcongr
        exact le_self_add
      calc U_core ^ 2 + TF ^ 2 ≤ U_core ^ 2 + TF ^ 2 + 2 * U_core * TF := le_self_add
        _ = (U_core + TF) ^ 2 := by ring
        _ ≤ S_rhs ^ 2 := pow_le_pow_left' hU_le 2
    have hcoeff :
        ENNReal.ofReal (Real.exp (2 * I_H)) * ENNReal.ofReal (C_trace * (ν⁻¹) ^ 2) ≤
          ENNReal.ofReal (1 / 2) * ENNReal.ofReal (K_tail * ν⁻¹) ^ 2 := by
      rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← ENNReal.ofReal_pow (by positivity),
        ← ENNReal.ofReal_mul (by norm_num)]
      apply ENNReal.ofReal_le_ofReal
      have hsq_K : K_tail ^ 2 = 2 * C_trace * (Real.exp (2 * C_strain * b)) ^ 2 := by
        unfold K_tail
        rw [mul_pow, Real.sq_sqrt (by positivity)]
      calc Real.exp (2 * I_H) * (C_trace * (ν⁻¹) ^ 2)
          ≤ (Real.exp (2 * C_strain * b)) ^ 2 * (C_trace * (ν⁻¹) ^ 2) :=
            mul_le_mul_of_nonneg_right hexp_le (by positivity)
        _ = 1 / 2 * (K_tail * ν⁻¹) ^ 2 := by
            rw [mul_pow, hsq_K]
            ring
    calc ENNReal.ofReal (Real.exp (2 * I_H)) *
            (ENNReal.ofReal (C_trace * H) * U_core ^ 2 +
              ENNReal.ofReal (C_trace * ν⁻¹) * TF ^ 2)
        ≤ ENNReal.ofReal (Real.exp (2 * I_H)) *
            (ENNReal.ofReal (C_trace * (ν⁻¹) ^ 2) * U_core ^ 2 +
              ENNReal.ofReal (C_trace * (ν⁻¹) ^ 2) * TF ^ 2) := by
          gcongr
      _ = (ENNReal.ofReal (Real.exp (2 * I_H)) * ENNReal.ofReal (C_trace * (ν⁻¹) ^ 2)) *
            (U_core ^ 2 + TF ^ 2) := by ring
      _ ≤ (ENNReal.ofReal (1 / 2) * ENNReal.ofReal (K_tail * ν⁻¹) ^ 2) * S_rhs ^ 2 :=
          mul_le_mul hcoeff h3 bot_le bot_le
      _ = ENNReal.ofReal (1 / 2) * (ENNReal.ofReal (K_tail * ν⁻¹) * S_rhs) ^ 2 := by
          rw [mul_pow, mul_assoc]
  have hk : (1 / 4 : ℝ) ≤ ⨅ μ' : K, μ'.1.re + 1 / 4 :=
    kStar_ge hμ (fun μ' hμ' => (hK.2 μ' hμ').1)
  have h2k : (1 / 2 : ℝ) ≤ 2 * (⨅ μ' : K, μ'.1.re + 1 / 4) := by linarith
  have hU_tail : U_tail ≤ ENNReal.ofReal (K_tail * ν⁻¹) * S_rhs := by
    apply le_of_sq_le_sq
    have h1 : ENNReal.ofReal (1 / 2) * U_tail ^ 2 ≤
        ENNReal.ofReal (1 / 2) * (ENNReal.ofReal (K_tail * ν⁻¹) * S_rhs) ^ 2 := by
      calc ENNReal.ofReal (1 / 2) * U_tail ^ 2
          ≤ ENNReal.ofReal (2 * (⨅ μ' : K, μ'.1.re + 1 / 4)) * U_tail ^ 2 :=
            mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal h2k) bot_le
        _ ≤ ENNReal.ofReal (2 * (⨅ μ' : K, μ'.1.re + 1 / 4)) * U_tail ^ 2 +
              ENNReal.ofReal ν * G_tail ^ 2 := le_self_add
        _ ≤ _ := hSq.trans hRHS_sq
    calc U_tail ^ 2
        = ENNReal.ofReal 2 * (ENNReal.ofReal (1 / 2) * U_tail ^ 2) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by norm_num),
            show (2 : ℝ) * (1 / 2) = 1 by norm_num, ENNReal.ofReal_one, one_mul]
      _ ≤ ENNReal.ofReal 2 *
            (ENNReal.ofReal (1 / 2) * (ENNReal.ofReal (K_tail * ν⁻¹) * S_rhs) ^ 2) :=
          mul_le_mul_of_nonneg_left h1 bot_le
      _ = (ENNReal.ofReal (K_tail * ν⁻¹) * S_rhs) ^ 2 := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by norm_num),
            show (2 : ℝ) * (1 / 2) = 1 by norm_num, ENNReal.ofReal_one, one_mul]
  have hG_tail : ENNReal.ofReal (Real.sqrt ν) * G_tail ≤
      ENNReal.ofReal (K_tail * ν⁻¹) * S_rhs := by
    apply le_of_sq_le_sq
    have hsq_ν : (ENNReal.ofReal (Real.sqrt ν) * G_tail) ^ 2 = ENNReal.ofReal ν * G_tail ^ 2 := by
      rw [mul_pow, ← ENNReal.ofReal_pow (Real.sqrt_nonneg _), Real.sq_sqrt hν0.le]
    rw [hsq_ν]
    calc ENNReal.ofReal ν * G_tail ^ 2
        ≤ ENNReal.ofReal (2 * (⨅ μ' : K, μ'.1.re + 1 / 4)) * U_tail ^ 2 +
            ENNReal.ofReal ν * G_tail ^ 2 := le_add_self
      _ ≤ ENNReal.ofReal (1 / 2) * (ENNReal.ofReal (K_tail * ν⁻¹) * S_rhs) ^ 2 :=
          hSq.trans hRHS_sq
      _ ≤ 1 * (ENNReal.ofReal (K_tail * ν⁻¹) * S_rhs) ^ 2 :=
          mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_one.2 (by norm_num)) bot_le
      _ = (ENNReal.ofReal (K_tail * ν⁻¹) * S_rhs) ^ 2 := one_mul _
  have hsplit_U := hCalNorm_le_on_add_tail c t_star (gainConj γ ν b_sol)
  have hsplit_G := tCalNorm_le_on_add_tail c t_star (gainConj γ ν G_sol)
  calc hCalNorm c (gainConj γ ν b_sol) +
          ENNReal.ofReal (Real.sqrt ν) * tCalNorm c (gainConj γ ν G_sol)
      ≤ (U_on + U_tail) + ENNReal.ofReal (Real.sqrt ν) * (G_on + G_tail) :=
        add_le_add hsplit_U (mul_le_mul_of_nonneg_left hsplit_G bot_le)
    _ = (U_on + ENNReal.ofReal (Real.sqrt ν) * G_on) +
          U_tail + ENNReal.ofReal (Real.sqrt ν) * G_tail := by ring
    _ ≤ ENNReal.ofReal (1 * ν⁻¹) * S_rhs +
          ENNReal.ofReal (K_tail * ν⁻¹) * S_rhs +
          ENNReal.ofReal (K_tail * ν⁻¹) * S_rhs :=
        add_le_add (add_le_add hOn_sum hU_tail) hG_tail
    _ = ENNReal.ofReal (C_tail * ν⁻¹) * S_rhs := by
        rw [← add_mul, ← add_mul,
          ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 2
        unfold C_tail
        ring

end UnforcedLeray.Short.IIIa
