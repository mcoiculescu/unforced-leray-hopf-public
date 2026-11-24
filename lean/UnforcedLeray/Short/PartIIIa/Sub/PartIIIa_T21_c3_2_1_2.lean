import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_1

/-!
# Part III-a, sub-infrastructure for `PartIII-a:T21/c3/2/1/2` (`VariationOfConstants.lean`, SP 2919-2925, 2977-2982)

Source of record: `the November 2 reference manuscript` (SP), lines 2919-2925 and
2977-2982 (`eq:short-causal-damped-complement`, `eq:short-causal-stable-moving`).

## Mathematical content and proved infrastructure

This module develops the moving-block calculus, normaliser factoring, ambient-to-cell propagator
norm bounds, and variation-of-constants norm assembly for `ComplBlockDuhamelVoC κ`
(`PartIII-a:T21/c3/2/1/2`):

1. **Moving-block age bijection `ageAt`, Jacobian `(clockA ν r) ^ (-2)`, and `clockN` factoring
   (SP 2857, 2923-2925, 2977-2982)**:
   * `nu_mul_movingZ_add_lt_one`, `movingZ_ageAt_sub`, `ageAt_mono_on_block`, `ageAt_mem_Icc`:
     order-preserving inverse properties of `ageAt ν t₁` on `[0, B]` when
     `movingZ ν t₂ - movingZ ν t₁ = B`.
   * `hasDerivAt_movingZ`, `hasDerivAt_movingZ_sub`: moving-time derivative
     `d/dr (movingZ ν r - movingZ ν t₁) = (clockA ν r) ^ (-2)`.
   * `clockN_inv_mul_clockN`: normaliser quotient identity
     `(clockN P ν t₁ r)⁻¹ * clockN P ν t₁ t₂ = clockN P ν r t₂` converting the damped variable
     `\widetilde W_\perp(z) = N(z, t₁)⁻¹ W_\perp(z)` back to `W_\perp(t₂)` (SP 2923-2925, 2980).

2. **Mode-forcing scaling, ambient-to-cell operator norm bridge, and variation-of-constants
   integral inequality**:
   * `xNorm_smul_complModeForce`: scalar homogeneity of `xNorm d m` on `complModeForce`.
   * `ofReal_norm_eq_xNorm_of_ae_cellZeroExt`, `xNorm_planeToC_smul_apply_le`: bridges `Planar.L2w m`
     operator norms `‖U_rel B σ‖` with cylinder `xNorm` via `eLpNorm_cellZeroExt_cToPlane` and
     `xNorm_planeToC_le_norm`.
   * `voc_ennreal_bound_of_split`: abstract `ENNReal` variation-of-constants assembly from a
     homogeneous + forcing integral split and pointwise-in-age integrand bounds on `Ioc t₁ t₂`.

3. **Analytical sub-leaf and conditional assembly `complBlockDuhamelVoC_of`**:
   * `ComplBlockDuhamelSplit` (`PartIII-a:T21/c3/2/1/2/1`): weak-flow Duhamel splitting of
     `xNorm d(t₂) m (compl F w t₂)` into a homogeneous term `H` and an integrated forcing term
     `∫⁻ r in Ioc t₁ t₂, G r` along `IsLinearisedFlow`.
   * `complBlockDuhamelVoC_of`: combines `ComplBlockDuhamelSplit` with `voc_ennreal_bound_of_split`
     to establish `ComplBlockDuhamelVoC κ` with zero sorry.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Metric UnforcedLeray.Blueprint.Planar
open scoped ENNReal ComplexConjugate ContDiff InnerProductSpace

namespace UnforcedLeray.Short.IIIa

open FrameShortBlockSub FrameBlockContractSub CompactDuhamelGapSub BlockPropagatorSub

namespace VariationOfConstantsSub

/-! ## 1. Moving-block age bijection `ageAt`, Jacobian, and `clockN` factoring -/

/-- On a block `[t₁, t₂]` with `movingZ ν t₂ - movingZ ν t₁ = B` and `τ ≤ B`, the shifted moving
time `movingZ ν t₁ + τ` satisfies `ν * (movingZ ν t₁ + τ) < 1`. -/
theorem nu_mul_movingZ_add_lt_one {ν t₁ t₂ B τ : ℝ}
    (hν : 0 < ν) (ht₂ : 0 ≤ t₂) (hB : movingZ ν t₂ - movingZ ν t₁ = B) (hτB : τ ≤ B) :
    ν * (movingZ ν t₁ + τ) < 1 := by
  have hz_le : movingZ ν t₁ + τ ≤ movingZ ν t₂ := by linarith
  have hlt : ν * movingZ ν t₂ < 1 := FrameStableSub.nu_mul_movingZ_lt_one hν ht₂
  nlinarith [mul_le_mul_of_nonneg_left hz_le hν.le]

/-- Right-inverse property `movingZ ν (ageAt ν t₁ τ) - movingZ ν t₁ = τ` for `τ ≤ B` on a block
`[t₁, t₂]` of moving length `B` (SP 2857). -/
theorem movingZ_ageAt_sub {ν t₁ t₂ B τ : ℝ}
    (hν : 0 < ν) (ht₂ : 0 ≤ t₂) (hB : movingZ ν t₂ - movingZ ν t₁ = B) (hτB : τ ≤ B) :
    movingZ ν (ageAt ν t₁ τ) - movingZ ν t₁ = τ := by
  unfold ageAt
  rw [FrameStableSub.movingZ_moveAgeOfZ (nu_mul_movingZ_add_lt_one hν ht₂ hB hτB)]
  ring

/-- Monotonicity of `ageAt ν t₁` on `[0, B]` when `movingZ ν t₂ - movingZ ν t₁ = B`. -/
theorem ageAt_mono_on_block {ν t₁ t₂ B σ τ : ℝ}
    (hν : 0 < ν) (ht₁ : 0 ≤ t₁) (ht₂ : 0 ≤ t₂) (hB : movingZ ν t₂ - movingZ ν t₁ = B)
    (hσ0 : 0 ≤ σ) (hστ : σ ≤ τ) (hτB : τ ≤ B) :
    ageAt ν t₁ σ ≤ ageAt ν t₁ τ := by
  unfold ageAt
  have hz₁ : 0 ≤ movingZ ν t₁ + σ :=
    add_nonneg (FrameStableSub.movingZ_nonneg hν ht₁) hσ0
  have hz₂ : ν * (movingZ ν t₁ + τ) < 1 := nu_mul_movingZ_add_lt_one hν ht₂ hB hτB
  exact FrameStableSub.moveAgeOfZ_mono hν hz₁ hz₂ (by linarith)

/-- For `τ ∈ Icc 0 B` on a block `[t₁, t₂]` with `movingZ ν t₂ - movingZ ν t₁ = B`, the age
`ageAt ν t₁ τ` lies in `Icc t₁ t₂`. -/
theorem ageAt_mem_Icc {ν t₁ t₂ B τ : ℝ}
    (hν : 0 < ν) (ht₁ : 0 ≤ t₁) (h12 : t₁ ≤ t₂) (hB : movingZ ν t₂ - movingZ ν t₁ = B)
    (hτ : τ ∈ Icc 0 B) :
    ageAt ν t₁ τ ∈ Icc t₁ t₂ := by
  have ht₂ : 0 ≤ t₂ := ht₁.trans h12
  constructor
  · exact (ageAt_zero hν ht₁).symm.trans_le
      (ageAt_mono_on_block hν ht₁ ht₂ hB le_rfl hτ.1 hτ.2)
  · exact (ageAt_mono_on_block hν ht₁ ht₂ hB hτ.1 hτ.2 le_rfl).trans_eq
      (ageAt_eq_of_movingZ_sub hν ht₂ hB)

/-- Age derivative of moving time `movingZ ν`: `(d/dr) movingZ ν r = (clockA ν r) ^ (-2 : ℝ)`
(SP 2858). -/
theorem hasDerivAt_movingZ {ν r : ℝ} (hν : 0 < ν) (hr : 0 ≤ r) :
    HasDerivAt (movingZ ν) ((clockA ν r) ^ (-2 : ℝ)) r := by
  have ha : 0 < clockA ν r := by unfold clockA; positivity
  have h1 : HasDerivAt (clockA ν) ν r := FrameAmplSub.hasDerivAt_clockA ν r
  have h2 : HasDerivAt (movingZ ν) ((1 * clockA ν r - r * ν) / (clockA ν r) ^ 2) r :=
    (hasDerivAt_id r).div h1 ha.ne'
  refine h2.congr_deriv ?_
  rw [Real.rpow_neg ha.le, Real.rpow_two, ← one_div]
  unfold clockA
  field_simp [ha.ne']
  ring

/-- Age derivative of the block moving time `r ↦ movingZ ν r - movingZ ν t₁`:
`d/dr (movingZ ν r - movingZ ν t₁) = (clockA ν r) ^ (-2 : ℝ)` (SP 2857, 2977-2982). -/
theorem hasDerivAt_movingZ_sub {ν r : ℝ} (t₁ : ℝ) (hν : 0 < ν) (hr : 0 ≤ r) :
    HasDerivAt (fun s => movingZ ν s - movingZ ν t₁) ((clockA ν r) ^ (-2 : ℝ)) r := by
  simpa using (hasDerivAt_movingZ hν hr).sub_const (movingZ ν t₁)

/-- Normaliser quotient identity: `(clockN P ν t₁ r)⁻¹ * clockN P ν t₁ t₂ = clockN P ν r t₂`
converting the damped variable `\widetilde W_\perp(r) = clockN P ν t₁ r ⁻¹ • W_\perp(r)` back to
`W_\perp(t₂) = clockN P ν t₁ t₂ • \widetilde W_\perp(t₂)` (SP 2923-2925, 2980). -/
theorem clockN_inv_mul_clockN (P : PlanarData) {ν t₁ r t₂ : ℝ}
    (hν : 0 < ν) (ht₁ : 0 ≤ t₁) (hr : 0 ≤ r) (ht₂ : 0 ≤ t₂) :
    (clockN P ν t₁ r)⁻¹ * clockN P ν t₁ t₂ = clockN P ν r t₂ := by
  have hpos : 0 < clockN P ν t₁ r := clockN_pos P hν ht₁ hr
  rw [FrameStableSub.clockN_mul P hν ht₁ hr ht₂, inv_mul_cancel_left₀ hpos.ne']

/-! ## 2. Mode-forcing scaling, ambient-to-cell operator norm bridge, and VoC assembly -/

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

/-- If `W : Planar.L2w m` represents the zero-extension `z ↦ cellZeroExt d₁ V (cToPlane z)` of a
strongly measurable cell function `V`, then `ENNReal.ofReal ‖W‖ = xNorm d₁ m V`. -/
theorem ofReal_norm_eq_xNorm_of_ae_cellZeroExt {d₁ m : ℝ} {V : ℝ × ℝ → ℂ}
    (hV : AEStronglyMeasurable V (B0579.cellMeasure d₁ m))
    (W : Planar.L2w m)
    (hW : (W : ℂ → ℂ) =ᵐ[Planar.wMeasure m] fun z => cellZeroExt d₁ V (cToPlane z)) :
    ENNReal.ofReal ‖W‖ = xNorm d₁ m V := by
  rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top W),
    eLpNorm_congr_ae hW, eLpNorm_cellZeroExt_cToPlane d₁ m hV]

/-- **Ambient-to-cell propagator norm bound** (SP 2978-2982):
For any bounded operator `T : Planar.L2w m →L[ℂ] Planar.L2w m`, scalar `c ≥ 0`, and `W : Planar.L2w m`
representing `z ↦ cellZeroExt d₁ V (cToPlane z)`, the cell `xNorm d₂ m` of the restricted output
`y ↦ (c • T W) (planeToC y)` is bounded by `ENNReal.ofReal (c * ‖T‖) * xNorm d₁ m V`. -/
theorem xNorm_planeToC_smul_apply_le {d₁ d₂ m c : ℝ} (hc : 0 ≤ c)
    (T : Planar.L2w m →L[ℂ] Planar.L2w m) {V : ℝ × ℝ → ℂ}
    (hV : AEStronglyMeasurable V (B0579.cellMeasure d₁ m))
    (W : Planar.L2w m)
    (hW : (W : ℂ → ℂ) =ᵐ[Planar.wMeasure m] fun z => cellZeroExt d₁ V (cToPlane z)) :
    xNorm d₂ m (fun y => ((c • T W : Planar.L2w m) : ℂ → ℂ) (planeToC y)) ≤
      ENNReal.ofReal (c * ‖T‖) * xNorm d₁ m V := by
  refine (xNorm_planeToC_le_norm d₂ m (c • T W)).trans ?_
  rw [← ofReal_norm_eq_xNorm_of_ae_cellZeroExt hV W hW,
    ← ENNReal.ofReal_mul (mul_nonneg hc (norm_nonneg T))]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [norm_smul, Real.norm_of_nonneg hc, mul_assoc]
  exact mul_le_mul_of_nonneg_left (T.le_opNorm W) hc

/-- **Abstract `ENNReal` variation-of-constants assembly on `[t₁, t₂]`**:
If `xNorm d₂ m V₂ ≤ H + ∫⁻ r in Ioc t₁ t₂, G r`, where `H` is bounded by the homogeneous propagator
term and `G r` is bounded a.e. on `Ioc t₁ t₂` by the mode-forcing integrand, then `V₂` satisfies
the variation-of-constants inequality of `ComplBlockDuhamelVoC`. -/
theorem voc_ennreal_bound_of_split
    {t₁ t₂ d₁ d₂ m : ℝ} {V₁ V₂ : ℝ × ℝ → ℂ}
    {H : ℝ≥0∞} {G : ℝ → ℝ≥0∞}
    {homFactor : ℝ} {forceFactor : ℝ → ℝ} {forceSum : ℝ → ℝ≥0∞}
    (hsplit : xNorm d₂ m V₂ ≤ H + ∫⁻ r in Ioc t₁ t₂, G r)
    (hH : H ≤ ENNReal.ofReal homFactor * xNorm d₁ m V₁)
    (hG : ∀ᵐ r ∂(volume.restrict (Ioc t₁ t₂)),
      G r ≤ ENNReal.ofReal (forceFactor r) * forceSum r) :
    xNorm d₂ m V₂ ≤
      ENNReal.ofReal homFactor * xNorm d₁ m V₁ +
        ∫⁻ r in Ioc t₁ t₂, ENNReal.ofReal (forceFactor r) * forceSum r :=
  hsplit.trans (add_le_add hH (lintegral_mono_ae hG))

/-! ## 3. Analytical sub-leaf and conditional assembly for `ComplBlockDuhamelVoC` -/

/-- **Sub-leaf 2a (`ComplBlockDuhamelSplit`, `PartIII-a:T21/c3/2/1/2/1`, SP 2919-2925, 2977-2982)**:
Along any weak linearised flow `IsLinearisedFlow ν (ν ^ (-2 : ℝ)) m tr t₁ f w u` with
`HasZeroCirculation (ν ^ (-2 : ℝ)) f` on a block `[t₁, t₂]` of moving length `B`, for any block
Duhamel triple `(F_rel, A_rel, U_rel)` on `Planar.L2w m` satisfying `IsPeriodizedRelFreeBlockEvol`,
`IsDampedComplBlockInt`, and `B0104.IsDuhamelEvolution`, the terminal complement norm
`xNorm d(t₂) m (compl F w t₂)` splits into a homogeneous propagator contribution `H` and an
integrated forcing contribution `∫⁻ r in Ioc t₁ t₂, G r`. -/
def ComplBlockDuhamelSplit (κ : PlanarFrameKernels) : Prop :=
  IsSeedKernels κ →
  ∀ (P : PlanarData), IsPlanarReference P →
  ∀ m : ℝ, 8 < m →
  ∀ K B b : ℝ, 0 < B → 1 ≤ b →
  ∀ ν : ℝ, ∀ (hν : 0 < ν), ∀ hF : PerFrameFacts κ ν m b K,
    ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
      UnforcedLeray.Short.PartI.IsBUCTrain tr →
      ∀ t₁ t₂ : ℝ, 0 ≤ t₁ → t₁ ≤ t₂ → b ≤ clockTheta ν t₂ →
        movingZ ν t₂ - movingZ ν t₁ = B →
        ∀ (F_rel : ℝ → ℝ → Planar.L2w m →L[ℂ] Planar.L2w m)
          (A_rel : ℝ → Planar.L2w m →L[ℂ] Planar.L2w m)
          (U_rel : ℝ → ℝ → Planar.L2w m →L[ℂ] Planar.L2w m),
          IsPeriodizedRelFreeBlockEvol P ν m tr t₁ B F_rel →
          IsDampedComplBlockInt κ P ν m tr t₁ B A_rel →
          UnforcedLeray.B0104.IsDuhamelEvolution (ι := Unit) B
            (fun _ => F_rel) (fun _ => A_rel) (fun _ => U_rel) →
          ∀ f w u, IsLinearisedFlow ν (ν ^ (-2 : ℝ)) m tr t₁ f w u →
            HasZeroCirculation (ν ^ (-2 : ℝ)) f →
            let F := periodizedFrame κ ν m b K hν hF
            ∃ (H : ℝ≥0∞) (G : ℝ → ℝ≥0∞),
              xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν t₂)) m (compl F w t₂) ≤
                H + ∫⁻ r in Ioc t₁ t₂, G r ∧
              H ≤ ENNReal.ofReal (clockN P ν t₁ t₂ * ‖U_rel B 0‖) *
                xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν t₁)) m (compl F w t₁) ∧
              ∀ r ∈ Ioc t₁ t₂,
                G r ≤
                  ENNReal.ofReal
                      ((clockA ν r) ^ (-2 : ℝ) *
                        (clockN P ν r t₂ * ‖U_rel B (movingZ ν r - movingZ ν t₁)‖)) *
                    (∑ j : Fin 2,
                      ENNReal.ofReal ‖ampl F w r j‖ *
                        xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m
                          (complModeForce κ P F tr r j))

/-- **Conditional assembly of `ComplBlockDuhamelVoC κ` (`PartIII-a:T21/c3/2/1/2`)**:
Combines `ComplBlockDuhamelSplit κ` with `voc_ennreal_bound_of_split` to establish
`ComplBlockDuhamelVoC κ` with zero sorry. -/
theorem complBlockDuhamelVoC_of (κ : PlanarFrameKernels)
    (hSplit : ComplBlockDuhamelSplit κ) :
    ComplBlockDuhamelVoC κ := by
  intro hκ P hP m hm K B b hB hb1 ν hν hF tr htr t₁ t₂ ht₁ h12 hbt₂ hB_eq
    F_rel A_rel U_rel hF_rel hA_rel hDuh f w u hFlow hCirc
  dsimp only
  obtain ⟨H, G, hsplit, hH, hG_pt⟩ :=
    hSplit hκ P hP m hm K B b hB hb1 ν hν hF tr htr t₁ t₂ ht₁ h12 hbt₂ hB_eq
      F_rel A_rel U_rel hF_rel hA_rel hDuh f w u hFlow hCirc
  refine voc_ennreal_bound_of_split hsplit hH ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
  exact hG_pt r hr

end VariationOfConstantsSub

end UnforcedLeray.Short.IIIa
