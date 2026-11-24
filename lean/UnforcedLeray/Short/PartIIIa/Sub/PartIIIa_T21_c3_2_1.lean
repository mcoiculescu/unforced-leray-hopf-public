import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2
import UnforcedLeray.Units.B0104

/-!
# Part III-a, task `PartIII-a:T21/c3/2/1` decomposition (`Sub/PartIII-a_T21_c3_2_1.lean`, SP 2919-2925, 2937-2945, 2962-2982)

Source of record: `the November 2 reference manuscript` (SP), lines 2919-2925,
2937-2945, and 2962-2982 (`eq:short-causal-damped-complement`, `eq:short-causal-free-moving`,
`eq:short-causal-stable-moving`).

## Mathematical structure and leaf decomposition

This module develops the operator, geometric, and Compact Duhamel infrastructure for
`BlockCompactDuhamelGap κ` (`PartIII-a:T21/c3/2/1`) on the ambient weighted Hilbert space
`Planar.L2w m` and reduces `BlockCompactDuhamelGap κ` to two concrete leaves:

1. **Damping rate `movBeta0`, moving-block age parameterization `ageAt`, and `clockN` identities
   (SP 2857, 2923-2925)**:
   * `hasDerivAt_clockN_movBeta0`, `movBeta0_bounds`: age derivative of `clockN P ν t₁` and
     two-sided bounds `Re λ - |Re κ| / b ≤ movBeta0 P ν r ≤ Re λ + |Re κ| / b`.
   * `ageAt`, `ageAt_zero`, `ageAt_eq_of_movingZ_sub`, `ageAt_movingZ_sub`, `ageAt_mem_Icc`:
     order-preserving bijection between block moving time `τ ∈ [0, B]` and age `r ∈ [t₁, t₂]`.

2. **Periodized extension `periodizedExt`, `cellZeroExt`, and `extDilCocycle` (SP 2937-2945)**:
   * `scaleMem_cell_iff`, `cellZeroExt_apply_of_mem`, `cellZeroExt_idem`,
     `sub_cellZeroExt_eq_zero_of_mem`, `extDilCocycle_self`, `extDilCocycle_comp`,
     `extDilCocycle_sub_cellZeroExt_eq_zero_on_cell`.
   * `periodizedExt`, `periodizedExt_apply_of_mem`, `periodizedExt_apply_of_notMem`,
     `xNorm_periodizedExt_eq`.
   * `cellLen_div_cellLen_eq_sqrt_theta`, `one_le_cellLen_div_cellLen`,
     `cellLen_div_cellLen_cube_le_exp`.

3. **Concrete damped complement generator perturbation `movDampedComplInt` (SP 2916-2925)**:
   * `movLInt`, `movL_eq_drift_add_movLInt`: localized Biot-Savart Euler interaction
     `-(K_{d(r)} W) · ∇ E_mov(r)` on `B0579.cell d(r)`.
   * `movK0`, `movLamPair`, `movM0`, `movFrameRankPert`, `movDampedComplInt`: the finite-rank frame
     terms `-E H₀ + [-K₀ + (β₀ - 1)E + E M₀] Λ` and total bounded perturbation of `𝓑` in
     `eq:short-causal-damped-complement` (SP 2920-2921), with `movFrameRankPert_of_lam_eq_zero` on
     `ker Λ(r)` and `movOscRes_add_movEulerRes_add_eigen`.
   * `planarRelTransportW`, `norm_planarRelTransportW_le`: the limiting relative free evolution
     `e^{-λ(t-s)} T(t-s)` on `Planar.L2w m`.

4. **Abstract Compact Duhamel block bounds on a Hilbert space (`B0104.compact_duhamel`,
   `B0104.IsDuhamelEvolution.norm_le`, `Infra.FiniteRankApprox`, SP 2965-2981)**:
   * `compact_duhamel_block_bound`: operator-norm bound `‖U n p t s‖ ≤ ‖U₀ p t s - F₀ p t s‖ + ‖F n p t s‖ + δ_gap`.
   * `compact_duhamel_opNorm_bound`: using finite-rank orthogonal projection approximation of a
     compact remainder `U₀ () B 0 - F₀ () B 0` (`exists_starProjection_comp_norm_sub_le`), strong
     convergence `U n → U₀` on the finite-dimensional range of the projection, and norm convergence
     of the remainders, establishes the sharp full-block bound
     `‖U n p B 0‖ ≤ ‖U₀ () B 0‖ + ‖F n p B 0‖ + δ_gap`.

5. **Two concrete analytical leaves and proved assembly `blockCompactDuhamelGap_of`**:
   * `IsPeriodizedRelFreeBlockEvol`, `IsDampedComplBlockInt`: uniquely pin down the relative
     periodized free evolution `F_rel` (via `periodizedExt` on cylinder test flows `IsFreeCylFlow`)
     and the damped complement interaction `A_rel` (via `cellZeroExt` of `movDampedComplInt` on
     smooth compactly supported fields) as continuous linear maps on `Planar.L2w m`.
   * Leaf 1 (`DampedComplBlockPropagator`, `PartIII-a:T21/c3/2/1/1`, SP 2926-2982): existence and
     Compact Duhamel full-block bound `‖U_rel B 0‖ ≤ C₀ * e^{-h B} + α_free + δ_gap` for the block
     Duhamel triple `(F_rel, A_rel, U_rel)` on `Planar.L2w m`.
   * Leaf 2 (`ComplBlockDuhamelVoC`, `PartIII-a:T21/c3/2/1/2`, SP 2919-2925, 2977-2982):
     variation-of-constants inequality for `compl F w t₂` along a weak linearised flow
     `IsLinearisedFlow` in terms of the block Duhamel evolution `U_rel` of `(F_rel, A_rel)` and
     `complModeForce κ P F tr r j`.
   * `blockCompactDuhamelGap_of`: combines `DampedComplBlockPropagator` and `ComplBlockDuhamelVoC`
     with `B0104.IsDuhamelEvolution.norm_le` (giving `C_uh = 2 * M_free * exp((2 * M_free * K_A + 1) * B)`)
     to establish `BlockCompactDuhamelGap κ` with zero sorry.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Metric UnforcedLeray.Blueprint.Planar
open scoped ENNReal ComplexConjugate ContDiff InnerProductSpace

namespace UnforcedLeray.Short.IIIa

open FrameShortBlockSub FrameBlockContractSub

/-- Coordinate bijection from `ℂ` to `ℝ × ℝ`, inverse to `planeToC`. -/
def cToPlane (z : ℂ) : ℝ × ℝ := (z.re, z.im)

@[simp] theorem planeToC_cToPlane (z : ℂ) : planeToC (cToPlane z) = z :=
  Complex.ext rfl rfl

@[simp] theorem cToPlane_planeToC (y : ℝ × ℝ) : cToPlane (planeToC y) = y :=
  Prod.ext rfl rfl

namespace CompactDuhamelGapSub

/-! ## 1. Damping rate `movBeta0`, moving-block age map `ageAt`, and `clockN` identities -/

/-- Age derivative of `clockN P ν t₁` written in terms of the instantaneous damping rate
`movBeta0 P ν r = P.eigenvalue.re + P.kappa.re / clockTheta ν r` (SP 2923-2925). -/
theorem hasDerivAt_clockN_movBeta0 (P : PlanarData) {ν t₁ r : ℝ}
    (hν : 0 < ν) (ht₁ : 0 ≤ t₁) (hr : 0 ≤ r) :
    HasDerivAt (clockN P ν t₁)
      ((clockA ν r) ^ (-2 : ℝ) * movBeta0 P ν r * clockN P ν t₁ r) r := by
  simpa [movBeta0, mul_assoc] using FrameAmplSub.hasDerivAt_clockN P hν ht₁ hr

/-- Two-sided bounds on the instantaneous damping rate `movBeta0 P ν r` when
`0 < b ≤ clockTheta ν r`. -/
theorem movBeta0_bounds (P : PlanarData) {ν r b : ℝ}
    (hν : 0 < ν) (hr : 0 ≤ r) (hb0 : 0 < b) (hbr : b ≤ clockTheta ν r) :
    P.eigenvalue.re - |P.kappa.re| / b ≤ movBeta0 P ν r ∧
      movBeta0 P ν r ≤ P.eigenvalue.re + |P.kappa.re| / b := by
  have hθr : 0 < clockTheta ν r := theta_pos hν hr
  have hdiv : |P.kappa.re / clockTheta ν r| ≤ |P.kappa.re| / b := by
    rw [abs_div, abs_of_pos hθr]
    exact div_le_div_of_nonneg_left (abs_nonneg _) hb0 hbr
  have habs := abs_le.1 hdiv
  unfold movBeta0
  constructor <;> linarith

/-- Age corresponding to block moving time `τ` starting from age `t₁` (SP 2857). -/
def ageAt (ν t₁ τ : ℝ) : ℝ :=
  FrameStableSub.moveAgeOfZ ν (movingZ ν t₁ + τ)

theorem ageAt_zero {ν t₁ : ℝ} (hν : 0 < ν) (ht₁ : 0 ≤ t₁) :
    ageAt ν t₁ 0 = t₁ := by
  unfold ageAt
  rw [add_zero]
  exact FrameStableSub.moveAgeOfZ_movingZ hν ht₁

theorem ageAt_movingZ_sub {ν t₁ r : ℝ} (hν : 0 < ν) (hr : 0 ≤ r) :
    ageAt ν t₁ (movingZ ν r - movingZ ν t₁) = r := by
  unfold ageAt
  rw [add_sub_cancel]
  exact FrameStableSub.moveAgeOfZ_movingZ hν hr

theorem ageAt_eq_of_movingZ_sub {ν t₁ t₂ B : ℝ} (hν : 0 < ν) (ht₂ : 0 ≤ t₂)
    (hB : movingZ ν t₂ - movingZ ν t₁ = B) :
    ageAt ν t₁ B = t₂ := by
  rw [← hB]
  exact ageAt_movingZ_sub hν ht₂

theorem movingZ_sub_mem_Icc {ν t₁ t₂ r : ℝ} (hν : 0 < ν) (ht₁ : 0 ≤ t₁)
    (hr : r ∈ Icc t₁ t₂) :
    movingZ ν r - movingZ ν t₁ ∈ Icc 0 (movingZ ν t₂ - movingZ ν t₁) := by
  have hr0 : 0 ≤ r := ht₁.trans hr.1
  have hz1 : movingZ ν t₁ ≤ movingZ ν r := FrameStableSub.movingZ_le_movingZ hν ht₁ hr.1
  have hz2 : movingZ ν r ≤ movingZ ν t₂ := FrameStableSub.movingZ_le_movingZ hν hr0 hr.2
  exact ⟨sub_nonneg.2 hz1, sub_le_sub_right hz2 _⟩

/-! ## 2. Periodized extension, `cellZeroExt`, and `extDilCocycle` (SP 2937-2945) -/

/-- For `0 < d_t` and `0 < d_z`, the rescaled point `((d_t / d_z) * y.1, (d_t / d_z) * y.2)` belongs
to `B0579.cell d_t` if and only if `y ∈ B0579.cell d_z`. -/
theorem scaleMem_cell_iff {d_t d_z : ℝ} (hdt : 0 < d_t) (hdz : 0 < d_z) (y : ℝ × ℝ) :
    ((d_t / d_z) * y.1, (d_t / d_z) * y.2) ∈ B0579.cell d_t ↔ y ∈ B0579.cell d_z := by
  have hratio : 0 < d_t / d_z := div_pos hdt hdz
  simp only [B0579.cell, mem_prod, mem_Ico, mem_univ, and_true]
  constructor
  · rintro ⟨h1, h2⟩
    constructor
    · have h1' : -(d_z / 2) * (d_t / d_z) ≤ y.1 * (d_t / d_z) := by
        calc -(d_z / 2) * (d_t / d_z) = -(d_t / 2) := by
              field_simp [hdz.ne']
          _ ≤ (d_t / d_z) * y.1 := h1
          _ = y.1 * (d_t / d_z) := mul_comm _ _
      exact le_of_mul_le_mul_right h1' hratio
    · have h2' : y.1 * (d_t / d_z) < (d_z / 2) * (d_t / d_z) := by
        calc y.1 * (d_t / d_z) = (d_t / d_z) * y.1 := mul_comm _ _
          _ < d_t / 2 := h2
          _ = (d_z / 2) * (d_t / d_z) := by
              field_simp [hdz.ne']
      exact lt_of_mul_lt_mul_right h2' hratio.le
  · rintro ⟨h1, h2⟩
    constructor
    · calc -(d_t / 2) = (d_t / d_z) * (-(d_z / 2)) := by
            field_simp [hdz.ne']
        _ ≤ (d_t / d_z) * y.1 := mul_le_mul_of_nonneg_left h1 hratio.le
    · calc (d_t / d_z) * y.1 < (d_t / d_z) * (d_z / 2) :=
            mul_lt_mul_of_pos_left h2 hratio
        _ = d_t / 2 := by
            field_simp [hdz.ne']

/-- `cellZeroExt d W` agrees with `W` on `B0579.cell d`. -/
theorem cellZeroExt_apply_of_mem (d : ℝ) (W : ℝ × ℝ → ℂ) {y : ℝ × ℝ}
    (hy : y ∈ B0579.cell d) :
    cellZeroExt d W y = W y :=
  indicator_of_mem hy W

/-- `cellZeroExt d` is idempotent. -/
theorem cellZeroExt_idem (d : ℝ) (W : ℝ × ℝ → ℂ) :
    cellZeroExt d (cellZeroExt d W) = cellZeroExt d W := by
  ext y
  by_cases hy : y ∈ B0579.cell d
  · rw [cellZeroExt_apply_of_mem d _ hy]
  · rw [cellZeroExt_compl_apply d _ hy, cellZeroExt_compl_apply d _ hy]

/-- The exterior projection `W - cellZeroExt d W` vanishes on `B0579.cell d`. -/
theorem sub_cellZeroExt_eq_zero_of_mem (d : ℝ) (W : ℝ × ℝ → ℂ) {y : ℝ × ℝ}
    (hy : y ∈ B0579.cell d) :
    W y - cellZeroExt d W y = 0 := by
  rw [cellZeroExt_apply_of_mem d W hy, sub_self]

/-- Identity law for the exterior dilation cocycle `extDilCocycle d d`. -/
theorem extDilCocycle_self {d : ℝ} (hd : d ≠ 0) (F : ℝ × ℝ → ℂ) (y : ℝ × ℝ) :
    extDilCocycle d d F y = F y := by
  unfold extDilCocycle
  rw [div_self hd, one_pow, Complex.ofReal_one, one_mul, one_mul, one_mul]

/-- Multiplicative cocycle law `S(z, u) (S(u, t) F) = S(z, t) F` (SP 2941). -/
theorem extDilCocycle_comp {d_t d_u d_z : ℝ} (hdu : d_u ≠ 0) (hdz : d_z ≠ 0)
    (F : ℝ × ℝ → ℂ) (y : ℝ × ℝ) :
    extDilCocycle d_u d_z (extDilCocycle d_t d_u F) y = extDilCocycle d_t d_z F y := by
  unfold extDilCocycle
  have hdiv : (d_t / d_u) * (d_u / d_z) = d_t / d_z := by
    field_simp [hdu, hdz]
  have hpow : ((d_u / d_z) ^ 4 : ℝ) * ((d_t / d_u) ^ 4 : ℝ) = (d_t / d_z) ^ 4 := by
    rw [mul_comm, ← mul_pow, hdiv]
  have h1 : (d_t / d_u) * ((d_u / d_z) * y.1) = (d_t / d_z) * y.1 := by
    rw [← mul_assoc, hdiv]
  have h2 : (d_t / d_u) * ((d_u / d_z) * y.2) = (d_t / d_z) * y.2 := by
    rw [← mul_assoc, hdiv]
  rw [h1, h2, ← mul_assoc, ← Complex.ofReal_mul, hpow]

/-- The exterior term `extDilCocycle d_t d_z (W - cellZeroExt d_t W)` vanishes on
`B0579.cell d_z` (SP 2941-2943). -/
theorem extDilCocycle_sub_cellZeroExt_eq_zero_on_cell {d_t d_z : ℝ}
    (hdt : 0 < d_t) (hdz : 0 < d_z) (W : ℝ × ℝ → ℂ) {y : ℝ × ℝ}
    (hy : y ∈ B0579.cell d_z) :
    extDilCocycle d_t d_z (fun x => W x - cellZeroExt d_t W x) y = 0 := by
  unfold extDilCocycle
  dsimp only
  have hmem : ((d_t / d_z) * y.1, (d_t / d_z) * y.2) ∈ B0579.cell d_t :=
    (scaleMem_cell_iff hdt hdz y).2 hy
  rw [sub_cellZeroExt_eq_zero_of_mem d_t W hmem, mul_zero]

/-- The periodized extension `I_z V + S(z, t)(I - Π_t) W` combining the cell zero-extension of a
cell field `V` on `B0579.cell d_z` with the exterior dilation of `W` outside `B0579.cell d_t`
(SP 2941). -/
def periodizedExt (d_t d_z : ℝ) (V W : ℝ × ℝ → ℂ) (y : ℝ × ℝ) : ℂ :=
  cellZeroExt d_z V y + extDilCocycle d_t d_z (fun x => W x - cellZeroExt d_t W x) y

/-- On `B0579.cell d_z`, `periodizedExt d_t d_z V W` agrees with `V` (`R_z \bar F(z, t) = F(z, t) R_t`,
SP 2943). -/
theorem periodizedExt_apply_of_mem {d_t d_z : ℝ} (hdt : 0 < d_t) (hdz : 0 < d_z)
    (V W : ℝ × ℝ → ℂ) {y : ℝ × ℝ} (hy : y ∈ B0579.cell d_z) :
    periodizedExt d_t d_z V W y = V y := by
  unfold periodizedExt
  rw [cellZeroExt_apply_of_mem d_z V hy,
    extDilCocycle_sub_cellZeroExt_eq_zero_on_cell hdt hdz W hy, add_zero]

/-- Outside `B0579.cell d_z`, `periodizedExt d_t d_z V W` agrees with `extDilCocycle d_t d_z W`
(SP 2941-2943). -/
theorem periodizedExt_apply_of_notMem {d_t d_z : ℝ} (hdt : 0 < d_t) (hdz : 0 < d_z)
    (V W : ℝ × ℝ → ℂ) {y : ℝ × ℝ} (hy : y ∉ B0579.cell d_z) :
    periodizedExt d_t d_z V W y = extDilCocycle d_t d_z W y := by
  unfold periodizedExt
  rw [cellZeroExt_compl_apply d_z V hy, zero_add]
  unfold extDilCocycle
  dsimp only
  have hnotMem : ((d_t / d_z) * y.1, (d_t / d_z) * y.2) ∉ B0579.cell d_t :=
    mt (scaleMem_cell_iff hdt hdz y).1 hy
  rw [cellZeroExt_compl_apply d_t W hnotMem, sub_zero]

/-- The `xNorm d_z m` of `periodizedExt d_t d_z V W` equals `xNorm d_z m V` (SP 2943). -/
theorem xNorm_periodizedExt_eq {d_t d_z : ℝ} (hdt : 0 < d_t) (hdz : 0 < d_z) (m : ℝ)
    (V W : ℝ × ℝ → ℂ) :
    xNorm d_z m (periodizedExt d_t d_z V W) = xNorm d_z m V := by
  unfold xNorm
  refine eLpNorm_congr_ae ?_
  have hae : ∀ᵐ y ∂(volume.restrict (B0579.cell d_z)),
      periodizedExt d_t d_z V W y = V y := by
    filter_upwards [ae_restrict_mem (B0579.measurableSet_cell d_z)] with y hy
    exact periodizedExt_apply_of_mem hdt hdz V W hy
  exact (B0579.cellMeasure_ac d_z m).ae_le hae

/-- Cell-length ratio identity: for `c ≠ 0`, `0 < ν`, `0 ≤ t₁`, and `0 ≤ t₂`,
`cellLen c (clockA ν t₁) / cellLen c (clockA ν t₂) = Real.sqrt (clockTheta ν t₁ / clockTheta ν t₂)`
(SP 2944). -/
theorem cellLen_div_cellLen_eq_sqrt_theta {c ν t₁ t₂ : ℝ}
    (hc : c ≠ 0) (hν : 0 < ν) (ht₁ : 0 ≤ t₁) (ht₂ : 0 ≤ t₂) :
    cellLen c (clockA ν t₁) / cellLen c (clockA ν t₂) =
      Real.sqrt (clockTheta ν t₁ / clockTheta ν t₂) := by
  have ha₁ : 0 < clockA ν t₁ := by unfold clockA; positivity
  have ha₂ : 0 < clockA ν t₂ := by unfold clockA; positivity
  have hsa₁ : 0 < Real.sqrt (clockA ν t₁) := Real.sqrt_pos.2 ha₁
  have hsa₂ : 0 < Real.sqrt (clockA ν t₂) := Real.sqrt_pos.2 ha₂
  unfold cellLen clockTheta
  have h1 : (c / Real.sqrt (clockA ν t₁)) / (c / Real.sqrt (clockA ν t₂)) =
      Real.sqrt (clockA ν t₂) / Real.sqrt (clockA ν t₁) := by
    field_simp [hc, hsa₁.ne', hsa₂.ne']
  have h2 : (ν * clockA ν t₁)⁻¹ / (ν * clockA ν t₂)⁻¹ = clockA ν t₂ / clockA ν t₁ := by
    field_simp [hν.ne', ha₁.ne', ha₂.ne']
  rw [h1, h2, Real.sqrt_div ha₂.le]

/-- On `0 ≤ t₁ ≤ t₂` with `c ≠ 0` and `0 < ν`, the cell-length ratio
`cellLen c (clockA ν t₁) / cellLen c (clockA ν t₂)` is at least `1` (SP 2944). -/
theorem one_le_cellLen_div_cellLen {c ν t₁ t₂ : ℝ}
    (hc : c ≠ 0) (hν : 0 < ν) (ht₁ : 0 ≤ t₁) (h12 : t₁ ≤ t₂) :
    1 ≤ cellLen c (clockA ν t₁) / cellLen c (clockA ν t₂) := by
  have ht₂ : 0 ≤ t₂ := ht₁.trans h12
  rw [cellLen_div_cellLen_eq_sqrt_theta hc hν ht₁ ht₂, Real.one_le_sqrt]
  exact (one_le_div (theta_pos hν ht₂)).2 (theta_anti hν ht₁ h12)

/-- Exponential upper bound on the cube of the cell-length ratio over `[t₁, t₂]` (SP 2944-2945):
`(cellLen c (clockA ν t₁) / cellLen c (clockA ν t₂)) ^ 3 ≤ Real.exp ((3 / (2 * b)) * (movingZ ν t₂ - movingZ ν t₁))`. -/
theorem cellLen_div_cellLen_cube_le_exp {c ν t₁ t₂ b : ℝ}
    (hc : c ≠ 0) (hν : 0 < ν) (ht₁ : 0 ≤ t₁) (h12 : t₁ ≤ t₂)
    (hb0 : 0 < b) (hbt₂ : b ≤ clockTheta ν t₂) :
    (cellLen c (clockA ν t₁) / cellLen c (clockA ν t₂)) ^ 3 ≤
      Real.exp ((3 / (2 * b)) * (movingZ ν t₂ - movingZ ν t₁)) := by
  have ht₂ : 0 ≤ t₂ := ht₁.trans h12
  have hθ₂ : 0 < clockTheta ν t₂ := theta_pos hν ht₂
  have hθ_le : clockTheta ν t₂ ≤ clockTheta ν t₁ := theta_anti hν ht₁ h12
  have hz_eq : clockTheta ν t₁ - clockTheta ν t₂ = movingZ ν t₂ - movingZ ν t₁ :=
    clockTheta_sub_eq_movingZ_sub hν ht₁ ht₂
  have hz_nonneg : 0 ≤ movingZ ν t₂ - movingZ ν t₁ := by linarith
  set Δz := movingZ ν t₂ - movingZ ν t₁
  set q := clockTheta ν t₁ / clockTheta ν t₂
  have hq0 : 0 ≤ q := div_nonneg (theta_pos hν ht₁).le hθ₂.le
  have hq_exp : q ≤ Real.exp (Δz / b) := by
    have hq_split : q = 1 + Δz / clockTheta ν t₂ := by
      simp only [q, ← hz_eq]
      rw [one_add_div hθ₂.ne']
      ring
    have hdiv_le : Δz / clockTheta ν t₂ ≤ Δz / b :=
      div_le_div_of_nonneg_left hz_nonneg hb0 hbt₂
    calc q = 1 + Δz / clockTheta ν t₂ := hq_split
      _ ≤ 1 + Δz / b := by linarith
      _ ≤ Real.exp (Δz / b) := by linarith [Real.add_one_le_exp (Δz / b)]
  have hsqrt_le : Real.sqrt q ≤ Real.exp (Δz / (2 * b)) := by
    rw [Real.sqrt_le_left (Real.exp_pos _).le]
    calc q ≤ Real.exp (Δz / b) := hq_exp
      _ = Real.exp (Δz / (2 * b)) ^ 2 := by
          rw [sq, ← Real.exp_add]
          congr 1
          ring
  rw [cellLen_div_cellLen_eq_sqrt_theta hc hν ht₁ ht₂]
  calc (Real.sqrt q) ^ 3 ≤ (Real.exp (Δz / (2 * b))) ^ 3 :=
        pow_le_pow_left₀ (Real.sqrt_nonneg q) hsqrt_le 3
    _ = Real.exp ((3 / (2 * b)) * Δz) := by
        rw [← Real.exp_nat_mul]
        congr 1
        push_cast
        ring

/-! ## 3. Damped complement generator perturbation `movDampedComplInt` (SP 2916-2925) -/

/-- Full unprojected moving mode residual on mode `j`:
`(θ(r)⁻¹ D(E_j) - ∂_z E_j) + L_{ν,c}(r) E_j = movOscRes κ ν r j + movEulerRes κ P tr r j + λ_j E_j`. -/
theorem movOscRes_add_movEulerRes_add_eigen (κ : PlanarFrameKernels) (P : PlanarData) {ν : ℝ}
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (r : ℝ) (j : Fin 2) (y : ℝ × ℝ) :
    movOscRes κ ν r j y + movEulerRes κ P tr r j y +
        modeEigen P j * perE κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) j y =
      ((clockTheta ν r : ℂ)⁻¹ *
          movD (perE κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) j) y -
        movEz κ ν r j y) +
      movL tr r (perE κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) j) y := by
  unfold movOscRes movEulerRes
  ring

/-- Localized nonlocal Biot-Savart Euler interaction in moving coordinates:
`L_{int, d(r)} W = -(K_{d(r)} W) · ∇ E_mov(r)` (SP 2863-2865, 2974-2976). -/
def movLInt {ν : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (r : ℝ)
    (W : ℝ × ℝ → ℂ) (y : ℝ × ℝ) : ℂ :=
  -(kerVelCx (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) W y 0 *
      ((movingTrainGradE tr r y 0 : ℝ) : ℂ) +
    kerVelCx (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) W y 1 *
      ((movingTrainGradE tr r y 1 : ℝ) : ℂ))

/-- Decomposition of `movL` into the transport drift `-V(r) · ∇ W` and the localized nonlocal
interaction `movLInt` (SP 2863-2865). -/
theorem movL_eq_drift_add_movLInt {ν : ℝ}
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (r : ℝ)
    (W : ℝ × ℝ → ℂ) (y : ℝ × ℝ) :
    movL tr r W y =
      -(((movingTrainV tr r y 0 : ℝ) : ℂ) * pdCx 0 W y +
          ((movingTrainV tr r y 1 : ℝ) : ℂ) * pdCx 1 W y) +
        movLInt tr r W y := by
  unfold movL movLInt
  ring

/-- Mode-`j` unprojected moving generator residual `K_{0, j}(r) = (G(r) E_j - ∂_z E_j)`
(SP 2916). -/
def movK0 (κ : PlanarFrameKernels) (P : PlanarData) {ν : ℝ}
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (r : ℝ) (j : Fin 2)
    (y : ℝ × ℝ) : ℂ :=
  movOscRes κ ν r j y + movEulerRes κ P tr r j y +
    modeEigen P j * perE κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) j y

/-- Moving-frame dual pairing `Λ_j(r) W = ∫_{movingCell} perLam κ d(r) j x * W x` (SP 2916-2921). -/
def movLamPair (κ : PlanarFrameKernels) (ν r : ℝ) (j : Fin 2) (W : ℝ × ℝ → ℂ) : ℂ :=
  ∫ x in movingCell ν (ν ^ (-2 : ℝ)) r,
    perLam κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) j x * W x

/-- The `2 × 2` matrix `M_{0, i, j}(r) = Λ_i(r) (K_{0, j}(r))` (SP 2918). -/
def movM0 (κ : PlanarFrameKernels) (P : PlanarData) {ν : ℝ}
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (r : ℝ) (i j : Fin 2) : ℂ :=
  movLamPair κ ν r i (movK0 κ P tr r j)

/-- The finite-rank perturbation `-E H_0 + [-K_0 + (β_0 - 1) E + E M_0] Λ` in the damped
complement generator `𝓑` (`eq:short-causal-damped-complement`, SP 2920-2921). -/
def movFrameRankPert (κ : PlanarFrameKernels) (P : PlanarData) {ν : ℝ}
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (r : ℝ)
    (W : ℝ × ℝ → ℂ) (y : ℝ × ℝ) : ℂ :=
  let d_r := cellLen (ν ^ (-2 : ℝ)) (clockA ν r)
  (-∑ i : Fin 2, movH0 κ tr r i W * perE κ d_r i y) +
    ∑ j : Fin 2,
      (-movK0 κ P tr r j y +
          (((movBeta0 P ν r - 1 : ℝ) : ℂ) * perE κ d_r j y) +
          ∑ i : Fin 2, movM0 κ P tr r i j * perE κ d_r i y) *
        movLamPair κ ν r j W

/-- On `ker Λ(r)` (`∀ j, movLamPair κ ν r j W = 0`), the finite-rank perturbation `movFrameRankPert`
reduces to `-∑ i, movH0 κ tr r i W * E_i(r)` (SP 2920-2925). -/
theorem movFrameRankPert_of_lam_eq_zero (κ : PlanarFrameKernels) (P : PlanarData) {ν : ℝ}
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (r : ℝ) (W : ℝ × ℝ → ℂ)
    (hker : ∀ j : Fin 2, movLamPair κ ν r j W = 0) (y : ℝ × ℝ) :
    movFrameRankPert κ P tr r W y =
      -∑ i : Fin 2,
        movH0 κ tr r i W * perE κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) i y := by
  unfold movFrameRankPert
  simp [hker]

/-- Total bounded perturbation `L_{int, d(r)} + movFrameRankPert` of the damped complement
generator `𝓑` relative to `G_{free} - β_0` (`eq:short-causal-damped-complement`, SP 2920-2923,
2974-2978). -/
def movDampedComplInt (κ : PlanarFrameKernels) (P : PlanarData) {ν : ℝ}
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (r : ℝ)
    (W : ℝ × ℝ → ℂ) (y : ℝ × ℝ) : ℂ :=
  movLInt tr r W y + movFrameRankPert κ P tr r W y

/-- Limiting relative free evolution `e^{-λ(t-s)} T(t-s)` on `Planar.L2w m` (SP 2964-2974). -/
def planarRelTransportW (P : PlanarData) (m : ℝ) (t s : ℝ) :
    Planar.L2w m →L[ℂ] Planar.L2w m :=
  Complex.exp (-P.eigenvalue * ((t - s : ℝ) : ℂ)) • Planar.transportGroupW m (t - s)

/-- Norm bound `‖planarRelTransportW P m t s‖ ≤ Real.exp (-P.eigenvalue.re * (t - s))`
(SP 2968: radial Euler transport `T` has norm `≤ 1` on `Planar.L2w m`). -/
theorem norm_planarRelTransportW_le (P : PlanarData) (m : ℝ) (t s : ℝ) :
    ‖planarRelTransportW P m t s‖ ≤ Real.exp (-P.eigenvalue.re * (t - s)) := by
  unfold planarRelTransportW
  rw [norm_smul, Complex.norm_exp]
  have hre : (-P.eigenvalue * ((t - s : ℝ) : ℂ)).re = -P.eigenvalue.re * (t - s) := by
    simp [Complex.mul_re]
  rw [hre]
  calc Real.exp (-P.eigenvalue.re * (t - s)) * ‖Planar.transportGroupW m (t - s)‖
      ≤ Real.exp (-P.eigenvalue.re * (t - s)) * 1 :=
        mul_le_mul_of_nonneg_left (Planar.norm_transportGroupW_le m (t - s)) (Real.exp_pos _).le
    _ = Real.exp (-P.eigenvalue.re * (t - s)) := mul_one _

/-! ## 4. Abstract Compact Duhamel block bounds from `B0104.compact_duhamel` (SP 2965-2981) -/

/-- Consequence of `UnforcedLeray.B0104.compact_duhamel`: under the hypotheses of the Compact
Duhamel theorem on blocks of length `B`, for every gap tolerance `δ_gap > 0`, eventually in `atTop`
for all `p` and `s ≤ t ≤ s + B`, the perturbed evolution `U n p t s` satisfies
`‖U n p t s‖ ≤ ‖U₀ p t s - F₀ p t s‖ + ‖F n p t s‖ + δ_gap`. -/
theorem compact_duhamel_block_bound
    {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {B δ_gap : ℝ}
    {F : ℕ → ι → ℝ → ℝ → H →L[ℂ] H} {F₀ : ι → ℝ → ℝ → H →L[ℂ] H}
    {A : ℕ → ι → ℝ → H →L[ℂ] H} {A₀ : ι → ℝ → H →L[ℂ] H}
    {U : ℕ → ι → ℝ → ℝ → H →L[ℂ] H} {U₀ : ι → ℝ → ℝ → H →L[ℂ] H}
    (hδ : 0 < δ_gap)
    (hFb : ∃ M, ∀ n p t s, s ≤ t → t ≤ s + B → ‖F n p t s‖ ≤ M ∧ ‖F₀ p t s‖ ≤ M)
    (hF : UnforcedLeray.B0104.StrongTendstoOnBlocks B F F₀)
    (hFadj : UnforcedLeray.B0104.StrongTendstoOnBlocks B
      (fun n p t s => ContinuousLinearMap.adjoint (F n p t s))
      (fun p t s => ContinuousLinearMap.adjoint (F₀ p t s)))
    (hAb : ∃ K, ∀ n p r, ‖A n p r‖ ≤ K)
    (hA : ∀ ε > 0, ∀ᶠ n in atTop, ∀ p r, ‖A n p r - A₀ p r‖ < ε)
    (hA₀c : ∀ p r, IsCompactOperator (A₀ p r))
    (hA₀p : TotallyBounded (range fun q : ι × ℝ => A₀ q.1 q.2))
    (hU : ∀ n, UnforcedLeray.B0104.IsDuhamelEvolution B (F n) (A n) (U n))
    (hU₀ : UnforcedLeray.B0104.IsDuhamelEvolution B F₀ A₀ U₀) :
    ∀ᶠ n in atTop, ∀ p t s, s ≤ t → t ≤ s + B →
      ‖U n p t s‖ ≤ ‖U₀ p t s - F₀ p t s‖ + ‖F n p t s‖ + δ_gap := by
  have hcd := (UnforcedLeray.B0104.compact_duhamel hFb hF hFadj hAb hA hA₀c hA₀p hU hU₀).2.2
    δ_gap hδ
  filter_upwards [hcd] with n hn p t s hst htsB
  have hrem : ‖(U n p t s - F n p t s) - (U₀ p t s - F₀ p t s)‖ < δ_gap :=
    hn p t s hst htsB
  have hsplit : U n p t s =
      (U₀ p t s - F₀ p t s) + F n p t s +
        ((U n p t s - F n p t s) - (U₀ p t s - F₀ p t s)) := by
    abel
  calc ‖U n p t s‖
      = ‖(U₀ p t s - F₀ p t s) + F n p t s +
          ((U n p t s - F n p t s) - (U₀ p t s - F₀ p t s))‖ := by
        rw [← hsplit]
    _ ≤ ‖(U₀ p t s - F₀ p t s) + F n p t s‖ +
          ‖(U n p t s - F n p t s) - (U₀ p t s - F₀ p t s)‖ :=
        norm_add_le _ _
    _ ≤ ‖U₀ p t s - F₀ p t s‖ + ‖F n p t s‖ + δ_gap := by
        linarith [norm_add_le (U₀ p t s - F₀ p t s) (F n p t s)]

/-- **Sharp Compact Duhamel full-block operator-norm bound** (SP 2978-2981):
If the limiting remainder `K₀ = U₀ B 0 - F₀ B 0` is compact (`IsCompactOperator K₀`), then
combining finite-rank orthogonal projection approximation (`exists_starProjection_comp_norm_sub_le`
on `K₀†`), uniform strong convergence `U n p B 0 → U₀ B 0` on the finite-dimensional range of the
projection, and norm convergence `(U n p B 0 - F n p B 0) → K₀` on its orthogonal complement yields
`‖U n p B 0‖ ≤ ‖U₀ B 0‖ + ‖F n p B 0‖ + δ_gap` eventually in `n` for all `p`. -/
theorem compact_duhamel_opNorm_bound
    {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {B δ_gap : ℝ} (hB : 0 ≤ B) (hδ : 0 < δ_gap)
    {F : ℕ → ι → ℝ → ℝ → H →L[ℂ] H} {F₀ : ℝ → ℝ → H →L[ℂ] H}
    {A : ℕ → ι → ℝ → H →L[ℂ] H} {A₀ : ℝ → H →L[ℂ] H}
    {U : ℕ → ι → ℝ → ℝ → H →L[ℂ] H} {U₀ : ℝ → ℝ → H →L[ℂ] H}
    (hFb : ∃ M, ∀ n p t s, s ≤ t → t ≤ s + B → ‖F n p t s‖ ≤ M ∧ ‖F₀ t s‖ ≤ M)
    (hF : UnforcedLeray.B0104.StrongTendstoOnBlocks B F (fun _ => F₀))
    (hFadj : UnforcedLeray.B0104.StrongTendstoOnBlocks B
      (fun n p t s => ContinuousLinearMap.adjoint (F n p t s))
      (fun _ t s => ContinuousLinearMap.adjoint (F₀ t s)))
    (hAb : ∃ K, ∀ n p r, ‖A n p r‖ ≤ K)
    (hA : ∀ ε > 0, ∀ᶠ n in atTop, ∀ p r, ‖A n p r - A₀ r‖ < ε)
    (hA₀c : ∀ r, IsCompactOperator (A₀ r))
    (hA₀p : TotallyBounded (range A₀))
    (hU : ∀ n, UnforcedLeray.B0104.IsDuhamelEvolution B (F n) (A n) (U n))
    (hU₀ : UnforcedLeray.B0104.IsDuhamelEvolution (ι := Unit) B (fun _ => F₀) (fun _ => A₀)
      (fun _ => U₀))
    (hK₀_cpt : IsCompactOperator (U₀ B 0 - F₀ B 0)) :
    ∀ᶠ n in atTop, ∀ p, ‖U n p B 0‖ ≤ ‖U₀ B 0‖ + ‖F n p B 0‖ + δ_gap := by
  have htb_p : TotallyBounded (range fun q : ι × ℝ => A₀ q.2) := by
    refine hA₀p.subset ?_
    rintro _ ⟨q, rfl⟩
    exact ⟨q.2, rfl⟩
  have hU₀_p : UnforcedLeray.B0104.IsDuhamelEvolution (ι := ι) B (fun _ => F₀) (fun _ => A₀)
      (fun _ => U₀) :=
    { integrable := fun _ s t h1 h2 x => hU₀.integrable () s t h1 h2 x
      duhamel := fun _ s t h1 h2 x => hU₀.duhamel () s t h1 h2 x
      bounded := fun _ s => hU₀.bounded () s }
  have hcd := UnforcedLeray.B0104.compact_duhamel hFb hF hFadj hAb hA
    (fun _ r => hA₀c r) htb_p hU hU₀_p
  obtain ⟨M₁, hFb'⟩ := hFb
  obtain ⟨K₁, hAb'⟩ := hAb
  set M := max M₁ 0
  set K_A := max K₁ 0
  have hFn_le : ∀ n p t s, s ≤ t → t ≤ s + B → ‖F n p t s‖ ≤ M :=
    fun n p t s h1 h2 => (hFb' n p t s h1 h2).1.trans (le_max_left _ _)
  have hAn_le : ∀ n p r, ‖A n p r‖ ≤ K_A :=
    fun n p r => (hAb' n p r).trans (le_max_left _ _)
  set CU := 2 * M * Real.exp ((2 * (M * K_A) + 1) * B)
  have hUn_le : ∀ n p, ‖U n p B 0‖ ≤ CU :=
    fun n p => (hU n).norm_le (hFn_le n) (hAn_le n) p B 0 hB (by linarith)
  set ε := δ_gap / 3
  have hε : 0 < ε := by positivity
  set K₀ : H →L[ℂ] H := U₀ B 0 - F₀ B 0
  obtain ⟨V, hVfin, hK₀_proj⟩ :=
    UnforcedLeray.Infra.FiniteRankApprox.exists_starProjection_comp_norm_sub_le
      (UnforcedLeray.B0104.isCompactOperator_adjoint hK₀_cpt) hε
  have : FiniteDimensional ℂ V := hVfin
  set P_V : H →L[ℂ] H := V.starProjection
  have hPV_self : ContinuousLinearMap.adjoint P_V = P_V :=
    V.starProjection_isSymmetric.clm_adjoint_eq
  have hK₀_sub : ‖K₀ - K₀.comp P_V‖ ≤ ε := by
    have heq : ContinuousLinearMap.adjoint (K₀ - K₀.comp P_V) =
        ContinuousLinearMap.adjoint K₀ - P_V.comp (ContinuousLinearMap.adjoint K₀) := by
      rw [ContinuousLinearMap.adjoint.map_sub, ContinuousLinearMap.adjoint_comp, hPV_self]
    rw [← UnforcedLeray.B0104.norm_adjoint_eq (K₀ - K₀.comp P_V), heq]
    exact hK₀_proj
  have hPV_finRank : P_V ∈ UnforcedLeray.Infra.FiniteRankApprox.finiteRank ℂ H H := by
    rw [UnforcedLeray.Infra.FiniteRankApprox.mem_finiteRank]
    have hle : LinearMap.range (P_V : H →ₗ[ℂ] H) ≤ V := by
      rintro _ ⟨x, rfl⟩
      exact Submodule.starProjection_apply_mem V x
    exact Submodule.finiteDimensional_of_le hle
  have hPV_cpt : IsCompactOperator P_V :=
    UnforcedLeray.Infra.FiniteRankApprox.isCompactOperator_of_mem_finiteRank hPV_finRank
  have hSV_tb : TotallyBounded (P_V '' closedBall (0 : H) 1) :=
    ((hPV_cpt : IsCompactOperator (P_V : H →ₗ[ℂ] H)).isCompact_closure_image_closedBall 1
      |>.totallyBounded).subset subset_closure
  have hU_tb := UnforcedLeray.B0104.eventually_forall_mem_of_totallyBounded
    (J := ι) (P := fun _ => True)
    (G := fun n p => U n p B 0 - U₀ B 0) (M := CU + ‖U₀ B 0‖)
    (fun n p _ => (norm_sub_le _ _).trans (add_le_add (hUn_le n p) le_rfl))
    (fun x η hη => by
      filter_upwards [hcd.1 x η hη] with n hn p _
      simpa only [sub_apply] using hn p B 0 hB (by linarith))
    hSV_tb ε hε
  filter_upwards [hU_tb, hcd.2.2 ε hε] with n hn_str hn_rem p
  refine ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity) fun x hx => ?_
  have hPV_x_norm : ‖P_V x‖ ≤ 1 :=
    (Submodule.norm_starProjection_apply_le V x).trans hx.le
  have hPV_compl_norm : ‖x - P_V x‖ ≤ 1 := by
    have horth : x - P_V x = Vᗮ.starProjection x :=
      (V.starProjection_orthogonal_val x).symm
    rw [horth]
    exact (Submodule.norm_starProjection_apply_le Vᗮ x).trans hx.le
  have hPV_mem : P_V x ∈ P_V '' closedBall (0 : H) 1 :=
    ⟨x, mem_closedBall_zero_iff.2 hx.le, rfl⟩
  have h1 : ‖U₀ B 0 (P_V x)‖ ≤ ‖U₀ B 0‖ := by
    calc ‖U₀ B 0 (P_V x)‖ ≤ ‖U₀ B 0‖ * ‖P_V x‖ := (U₀ B 0).le_opNorm _
      _ ≤ ‖U₀ B 0‖ * 1 := mul_le_mul_of_nonneg_left hPV_x_norm (norm_nonneg _)
      _ = ‖U₀ B 0‖ := mul_one _
  have h2 : ‖(U n p B 0 - U₀ B 0) (P_V x)‖ ≤ ε :=
    (hn_str p trivial (P_V x) hPV_mem).le
  have h3 : ‖F n p B 0 (x - P_V x)‖ ≤ ‖F n p B 0‖ := by
    calc ‖F n p B 0 (x - P_V x)‖ ≤ ‖F n p B 0‖ * ‖x - P_V x‖ := (F n p B 0).le_opNorm _
      _ ≤ ‖F n p B 0‖ * 1 := mul_le_mul_of_nonneg_left hPV_compl_norm (norm_nonneg _)
      _ = ‖F n p B 0‖ := mul_one _
  have h4 : ‖(K₀ - K₀.comp P_V) x‖ ≤ ε := by
    calc ‖(K₀ - K₀.comp P_V) x‖ ≤ ‖K₀ - K₀.comp P_V‖ * ‖x‖ := (K₀ - K₀.comp P_V).le_opNorm x
      _ ≤ ε * 1 := mul_le_mul hK₀_sub hx.le (norm_nonneg _) hε.le
      _ = ε := mul_one _
  have h5 : ‖((U n p B 0 - F n p B 0) - K₀) (x - P_V x)‖ ≤ ε := by
    have hrem : ‖(U n p B 0 - F n p B 0) - K₀‖ ≤ ε := (hn_rem p B 0 hB (by linarith)).le
    calc ‖((U n p B 0 - F n p B 0) - K₀) (x - P_V x)‖
        ≤ ‖(U n p B 0 - F n p B 0) - K₀‖ * ‖x - P_V x‖ :=
          ((U n p B 0 - F n p B 0) - K₀).le_opNorm _
      _ ≤ ε * 1 := mul_le_mul hrem hPV_compl_norm (norm_nonneg _) hε.le
      _ = ε := mul_one _
  have hsplit : U n p B 0 x =
      U₀ B 0 (P_V x) + (U n p B 0 - U₀ B 0) (P_V x) +
        F n p B 0 (x - P_V x) + (K₀ - K₀.comp P_V) x +
        ((U n p B 0 - F n p B 0) - K₀) (x - P_V x) := by
    simp only [K₀, sub_apply, ContinuousLinearMap.comp_apply, map_sub]
    abel
  rw [hsplit]
  have htri1 := norm_add_le
    (U₀ B 0 (P_V x) + (U n p B 0 - U₀ B 0) (P_V x) +
      F n p B 0 (x - P_V x) + (K₀ - K₀.comp P_V) x)
    (((U n p B 0 - F n p B 0) - K₀) (x - P_V x))
  have htri2 := norm_add_le
    (U₀ B 0 (P_V x) + (U n p B 0 - U₀ B 0) (P_V x) + F n p B 0 (x - P_V x))
    ((K₀ - K₀.comp P_V) x)
  have htri3 := norm_add_le
    (U₀ B 0 (P_V x) + (U n p B 0 - U₀ B 0) (P_V x))
    (F n p B 0 (x - P_V x))
  have htri4 := norm_add_le (U₀ B 0 (P_V x)) ((U n p B 0 - U₀ B 0) (P_V x))
  have hε_sum : 3 * ε = δ_gap := by unfold ε; ring
  linarith

end CompactDuhamelGapSub

open CompactDuhamelGapSub

/-! ## 5. Uniquely pinned block Duhamel predicates and analytical leaves for `BlockCompactDuhamelGap` -/

/-- `F_rel : ℝ → ℝ → Planar.L2w m →L[ℂ] Planar.L2w m` is the periodized relative free moving
evolution on the block `[t₁, t₂]` of moving length `B` (`\bar F_{\rm rel}`, SP 2941, 2960):
for every `0 ≤ σ ≤ τ ≤ B` (with ages `s = ageAt ν t₁ σ` and `t = ageAt ν t₁ τ`), every cylinder
test function `f` (`B0579.IsCylTest (ν ^ (-2 : ℝ)) f`), every free cylinder flow `ω₀`
(`IIb.IsFreeCylFlow m tr s f ω₀`), and every `W : Planar.L2w m` agreeing on `B0579.cell d(s)` with
`JscaleInv (clockA ν s) f`, `F_rel τ σ W` agrees a.e. on the plane with
`clockN P ν s t ⁻¹ • periodizedExt d(s) d(t) (JscaleInv (clockA ν t) (ω₀ t)) W`. -/
def IsPeriodizedRelFreeBlockEvol (P : PlanarData) (ν m : ℝ)
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (t₁ B : ℝ)
    (F_rel : ℝ → ℝ → Planar.L2w m →L[ℂ] Planar.L2w m) : Prop :=
  ∀ σ τ : ℝ, 0 ≤ σ → σ ≤ τ → τ ≤ B →
    let s := ageAt ν t₁ σ
    let t := ageAt ν t₁ τ
    let d_s := cellLen (ν ^ (-2 : ℝ)) (clockA ν s)
    let d_t := cellLen (ν ^ (-2 : ℝ)) (clockA ν t)
    ∀ f : B0579.Plane → ℝ, B0579.IsCylTest (ν ^ (-2 : ℝ)) f →
      ∀ ω₀ : ℝ → B0579.Plane → ℝ, UnforcedLeray.Short.IIb.IsFreeCylFlow m tr s f ω₀ →
        ∀ W : Planar.L2w m,
          (∀ᵐ z ∂volume, cToPlane z ∈ B0579.cell d_s →
            (W : ℂ → ℂ) z = JscaleInv (clockA ν s) (fun x => ((f x : ℝ) : ℂ)) (cToPlane z)) →
          ⇑(F_rel τ σ W) =ᵐ[volume] fun z : ℂ =>
            ((clockN P ν s t : ℂ)⁻¹) *
              periodizedExt d_s d_t
                (JscaleInv (clockA ν t) (fun x => ((ω₀ t x : ℝ) : ℂ)))
                (fun y => (W : ℂ → ℂ) (planeToC y))
                (cToPlane z)

/-- `A_rel : ℝ → Planar.L2w m →L[ℂ] Planar.L2w m` is the damped complement block interaction on
`[t₁, t₂]` of moving length `B` (`eq:short-causal-damped-complement`, SP 2920-2923, 2974-2978):
for every `τ ∈ Icc 0 B` (with age `r = ageAt ν t₁ τ` and cell length `d_r = cellLen (ν ^ (-2)) (clockA ν r)`),
`A_rel τ` acts on smooth compactly supported representatives `Φ` in `Planar.L2w m` as the
cell zero-extension `cellZeroExt d_r (movDampedComplInt κ P tr r Φ)`. -/
def IsDampedComplBlockInt (κ : PlanarFrameKernels) (P : PlanarData) (ν m : ℝ)
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (t₁ B : ℝ)
    (A_rel : ℝ → Planar.L2w m →L[ℂ] Planar.L2w m) : Prop :=
  ∀ τ ∈ Icc 0 B,
    let r := ageAt ν t₁ τ
    let d_r := cellLen (ν ^ (-2 : ℝ)) (clockA ν r)
    ∀ (Φ : ℝ × ℝ → ℂ), ContDiff ℝ ∞ Φ → HasCompactSupport Φ →
      ∀ W : Planar.L2w m, (⇑W =ᵐ[volume] fun z : ℂ => Φ (cToPlane z)) →
        ⇑(A_rel τ W) =ᵐ[volume] fun z : ℂ =>
          cellZeroExt d_r (movDampedComplInt κ P tr r Φ) (cToPlane z)

/-- **Leaf 1 (`DampedComplBlockPropagator`, `PartIII-a:T21/c3/2/1/1`, SP 2926-2982)**:
Given the planar damped seed-complement decay `(C₀, h)` on `B0008.XjM 0 m` and the relative free
moving energy bound `α_free` on blocks of moving length `B`, for any gap tolerance `δ_gap > 0`,
there exist uniform sub-block bounds `M_free ≥ 0`, `K_A ≥ 0`, and a threshold `b_prop ≥ 1` such
that for `b ≥ b_prop` and small `ν ∈ (0, ν_prop]`, on any block `[t₁, t₂]` of moving length `B`
with `b ≤ clockTheta ν t₂`, the periodized relative free moving evolution `F_rel`
(`IsPeriodizedRelFreeBlockEvol`) and the damped complement interaction `A_rel`
(`IsDampedComplBlockInt`) generate a `B0104.IsDuhamelEvolution` `U_rel` on `Planar.L2w m` satisfying
the uniform bounds `‖F_rel τ σ‖ ≤ M_free`, `‖A_rel τ‖ ≤ K_A`, and the full-block Compact Duhamel
contraction bound `‖U_rel B 0‖ ≤ C₀ * Real.exp (-h * B) + α_free + δ_gap` (via
`compact_duhamel_opNorm_bound` / `compact_duhamel_block_bound`).
Composed by task `PartIII-a:T21/c3/2/1` via `blockCompactDuhamelGap_of`. -/
def DampedComplBlockPropagator (κ : PlanarFrameKernels) : Prop :=
  IsSeedKernels κ →
  ∀ (P : PlanarData), IsPlanarReference P →
  ∀ m : ℝ, 8 < m →
  ∀ K : ℝ,
  ∀ C₀ h B α_free δ_gap : ℝ,
    0 < C₀ → 0 < h → h ≤ P.eigenvalue.re → 0 < B → 0 < α_free → 0 < δ_gap →
    (∃ (lam : ℂ) (h_prof : ℝ → ℂ) (hh : MemLp h_prof 2 B0010.xGMeasure) (ℓ : B0010.XG →L[ℂ] ℂ),
      PartI.IsSeedXG lam (hh.toLp h_prof) ℓ ∧
      (∀ y, κ.e 0 y = PartI.seedPlanar h_prof (planeToC y)) ∧
      (∀ y, κ.e 1 y = conj (PartI.seedPlanar h_prof (planeToC y))) ∧
      (∀ f : ℂ → ℂ, ContDiff ℝ ∞ f → HasCompactSupport f →
        ∫ y, κ.lamP 0 y * f (planeToC y) =
          PartI.seedEll h_prof (Planar.NUE.Polar.angularSector f 2) ∧
        ∫ y, κ.lamP 1 y * f (planeToC y) =
          conj (PartI.seedEll h_prof
            (fun r => conj (Planar.NUE.Polar.angularSector f (-2) r)))) ∧
      (∀ (hm1 : 1 < m) (t : ℝ), 0 ≤ t → ∀ f : B0008.XjM 0 m,
        ∃ (u : Planar.L2w m) (g : B0008.XjM 0 m),
          (⇑u =ᵐ[volume] fun y =>
            PartI.xValue f y - PartI.seedProjFun h_prof (PartI.xValue f) y) ∧
          PartI.xValue g =ᵐ[volume] ⇑(Planar.eulerGroupW hm1 t u) ∧
          Real.exp (-P.eigenvalue.re * t) * ‖g‖ ≤ C₀ * Real.exp (-h * t) * ‖f‖)) →
    (∃ b_f : ℝ, 1 ≤ b_f ∧ ∀ b : ℝ, b_f ≤ b → ∃ ν_f : ℝ, 0 < ν_f ∧
      ∀ ν ∈ Ioc 0 ν_f, ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
        UnforcedLeray.Short.PartI.IsBUCTrain tr →
        ∀ t₁ t₂ : ℝ, 0 ≤ t₁ → t₁ ≤ t₂ → b ≤ clockTheta ν t₂ →
          movingZ ν t₂ - movingZ ν t₁ = B →
          ∀ f : B0579.Plane → ℝ, B0579.IsCylTest (ν ^ (-2 : ℝ)) f →
            ∀ ω₀ : ℝ → B0579.Plane → ℝ, UnforcedLeray.Short.IIb.IsFreeCylFlow m tr t₁ f ω₀ →
              xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν t₂)) m
                  (JscaleInv (clockA ν t₂) (fun x => ((ω₀ t₂ x : ℝ) : ℂ))) ≤
                ENNReal.ofReal (clockN P ν t₁ t₂) *
                  (ENNReal.ofReal α_free *
                    xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν t₁)) m
                      (JscaleInv (clockA ν t₁) (fun x => ((f x : ℝ) : ℂ))))) →
    ∃ M_free K_A b_prop : ℝ, 0 ≤ M_free ∧ 0 ≤ K_A ∧ 1 ≤ b_prop ∧
      ∀ b : ℝ, b_prop ≤ b →
        ∃ ν_prop : ℝ, 0 < ν_prop ∧
          ∀ ν (_hν : ν ∈ Ioc 0 ν_prop), ∀ _hF : PerFrameFacts κ ν m b K,
            ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
              UnforcedLeray.Short.PartI.IsBUCTrain tr →
              ∀ t₁ t₂ : ℝ, 0 ≤ t₁ → t₁ ≤ t₂ → b ≤ clockTheta ν t₂ →
                movingZ ν t₂ - movingZ ν t₁ = B →
                ∃ (F_rel : ℝ → ℝ → Planar.L2w m →L[ℂ] Planar.L2w m)
                  (A_rel : ℝ → Planar.L2w m →L[ℂ] Planar.L2w m)
                  (U_rel : ℝ → ℝ → Planar.L2w m →L[ℂ] Planar.L2w m),
                  IsPeriodizedRelFreeBlockEvol P ν m tr t₁ B F_rel ∧
                  IsDampedComplBlockInt κ P ν m tr t₁ B A_rel ∧
                  UnforcedLeray.B0104.IsDuhamelEvolution (ι := Unit) B
                    (fun _ => F_rel) (fun _ => A_rel) (fun _ => U_rel) ∧
                  (∀ σ τ : ℝ, σ ≤ τ → τ ≤ σ + B → ‖F_rel τ σ‖ ≤ M_free) ∧
                  (∀ τ : ℝ, ‖A_rel τ‖ ≤ K_A) ∧
                  ‖U_rel B 0‖ ≤ C₀ * Real.exp (-h * B) + α_free + δ_gap

/-- **Leaf 2 (`ComplBlockDuhamelVoC`, `PartIII-a:T21/c3/2/1/2`, SP 2919-2925, 2977-2982)**:
Along any weak linearised flow `IsLinearisedFlow ν (ν ^ (-2 : ℝ)) m tr t₁ f w u` with
`HasZeroCirculation (ν ^ (-2 : ℝ)) f` on a block `[t₁, t₂]` of moving length
`movingZ ν t₂ - movingZ ν t₁ = B` with `1 ≤ b ≤ clockTheta ν t₂`, for any block Duhamel triple
`(F_rel, A_rel, U_rel)` on `Planar.L2w m` satisfying `IsPeriodizedRelFreeBlockEvol`,
`IsDampedComplBlockInt`, and `B0104.IsDuhamelEvolution`, the terminal complement `compl F w t₂`
satisfies the variation-of-constants norm inequality with homogeneous factor
`clockN P ν t₁ t₂ * ‖U_rel B 0‖` and forcing factor
`(clockA ν r) ^ (-2 : ℝ) * (clockN P ν r t₂ * ‖U_rel B (movingZ ν r - movingZ ν t₁)‖)` against
`complModeForce κ P F tr r j`.
Composed by task `PartIII-a:T21/c3/2/1` via `blockCompactDuhamelGap_of`. -/
def ComplBlockDuhamelVoC (κ : PlanarFrameKernels) : Prop :=
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
            xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν t₂)) m (compl F w t₂) ≤
              ENNReal.ofReal (clockN P ν t₁ t₂ * ‖U_rel B 0‖) *
                  xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν t₁)) m (compl F w t₁) +
                ∫⁻ r in Ioc t₁ t₂,
                  ENNReal.ofReal
                      ((clockA ν r) ^ (-2 : ℝ) *
                        (clockN P ν r t₂ * ‖U_rel B (movingZ ν r - movingZ ν t₁)‖)) *
                    (∑ j : Fin 2,
                      ENNReal.ofReal ‖ampl F w r j‖ *
                        xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m
                          (complModeForce κ P F tr r j))

/-- **Conditional assembly of `BlockCompactDuhamelGap κ` (`PartIII-a:T21/c3/2/1`)**:
Combines `DampedComplBlockPropagator κ` (`PartIII-a:T21/c3/2/1/1`), `ComplBlockDuhamelVoC κ`
(`PartIII-a:T21/c3/2/1/2`), and the Gronwall majorant `B0104.IsDuhamelEvolution.norm_le`
(`C_uh = 2 * M_free * Real.exp ((2 * (M_free * K_A) + 1) * B)`) to establish
`BlockCompactDuhamelGap κ` with zero sorry. -/
theorem blockCompactDuhamelGap_of (κ : PlanarFrameKernels)
    (hProp : DampedComplBlockPropagator κ)
    (hVoC : ComplBlockDuhamelVoC κ) :
    BlockCompactDuhamelGap κ := by
  intro hκ P hP m hm K C₀ h B α_free δ_gap hC₀ hh hh_le hB hα hδ hSeedDecay hFreeRel
  obtain ⟨M_free, K_A, b_prop, hM_free, hK_A, hb_prop, hU_b⟩ :=
    hProp hκ P hP m hm K C₀ h B α_free δ_gap hC₀ hh hh_le hB hα hδ hSeedDecay hFreeRel
  set C_uh : ℝ := 2 * M_free * Real.exp ((2 * (M_free * K_A) + 1) * B)
  have hC_uh : 0 ≤ C_uh := by positivity
  refine ⟨C_uh, b_prop, hC_uh, hb_prop, fun b hb => ?_⟩
  obtain ⟨ν_prop, hν_prop, hU_ν⟩ := hU_b b hb
  refine ⟨ν_prop, hν_prop, fun ν hν hF tr htr t₁ t₂ ht₁ h12 hbt₂ hB_eq f w u hFlow hCirc => ?_⟩
  dsimp only
  set F := periodizedFrame κ ν m b K hν.1 hF
  have hb1 : 1 ≤ b := hb_prop.trans hb
  obtain ⟨F_rel, A_rel, U_rel, hF_rel, hA_rel, hDuh, hF_bdd, hA_bdd, hU_B0⟩ :=
    hU_ν ν hν hF tr htr t₁ t₂ ht₁ h12 hbt₂ hB_eq
  have hvoc := hVoC hκ P hP m hm K B b hB hb1 ν hν.1 hF tr htr t₁ t₂ ht₁ h12 hbt₂ hB_eq
    F_rel A_rel U_rel hF_rel hA_rel hDuh f w u hFlow hCirc
  have hU_sub : ∀ σ : ℝ, 0 ≤ σ → σ ≤ B → ‖U_rel B σ‖ ≤ C_uh := by
    intro σ hσ0 hσB
    exact hDuh.norm_le (fun _ t s h1 h2 => hF_bdd s t h1 h2) (fun _ r => hA_bdd r)
      () B σ hσB (by linarith)
  have hN12_pos : 0 < clockN P ν t₁ t₂ := clockN_pos P hν.1 ht₁ (ht₁.trans h12)
  have hHom :
      ENNReal.ofReal (clockN P ν t₁ t₂ * ‖U_rel B 0‖) *
          xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν t₁)) m (compl F w t₁) ≤
        ENNReal.ofReal (clockN P ν t₁ t₂) *
          (ENNReal.ofReal (C₀ * Real.exp (-h * B) + α_free + δ_gap) *
            xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν t₁)) m (compl F w t₁)) := by
    rw [ENNReal.ofReal_mul hN12_pos.le, mul_assoc]
    refine mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hU_B0) zero_le) zero_le
  have hInt :
      (∫⁻ r in Ioc t₁ t₂,
        ENNReal.ofReal
            ((clockA ν r) ^ (-2 : ℝ) *
              (clockN P ν r t₂ * ‖U_rel B (movingZ ν r - movingZ ν t₁)‖)) *
          (∑ j : Fin 2,
            ENNReal.ofReal ‖ampl F w r j‖ *
              xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m
                (complModeForce κ P F tr r j))) ≤
      ∫⁻ r in Ioc t₁ t₂,
        ENNReal.ofReal ((clockA ν r) ^ (-2 : ℝ) * (clockN P ν r t₂ * C_uh)) *
          (∑ j : Fin 2,
            ENNReal.ofReal ‖ampl F w r j‖ *
              xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m
                (complModeForce κ P F tr r j)) := by
    refine lintegral_mono_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    have hr0 : 0 ≤ r := ht₁.trans hr.1.le
    have ha_pos : 0 < (clockA ν r) ^ (-2 : ℝ) := by
      have ha : 0 < clockA ν r := by
        have := one_le_clockA hν.1.le hr0
        linarith
      exact Real.rpow_pos_of_pos ha _
    have hN_pos : 0 < clockN P ν r t₂ := clockN_pos P hν.1 hr0 (ht₁.trans h12)
    have hz_mem := movingZ_sub_mem_Icc hν.1 ht₁ ⟨hr.1.le, hr.2⟩
    rw [hB_eq] at hz_mem
    have hU_r : ‖U_rel B (movingZ ν r - movingZ ν t₁)‖ ≤ C_uh :=
      hU_sub (movingZ ν r - movingZ ν t₁) hz_mem.1 hz_mem.2
    have hfactor :
        (clockA ν r) ^ (-2 : ℝ) * (clockN P ν r t₂ * ‖U_rel B (movingZ ν r - movingZ ν t₁)‖) ≤
          (clockA ν r) ^ (-2 : ℝ) * (clockN P ν r t₂ * C_uh) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hU_r hN_pos.le) ha_pos.le
    exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hfactor) zero_le
  exact hvoc.trans (add_le_add hHom hInt)

end UnforcedLeray.Short.IIIa
