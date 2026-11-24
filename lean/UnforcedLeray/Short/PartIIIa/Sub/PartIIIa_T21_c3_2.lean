import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3
import UnforcedLeray.Short.PartIIIa.Clock.FreeMoving
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_3
import UnforcedLeray.Infra.CompactDuhamel
import UnforcedLeray.Short.PartI.StatementsSeed
import UnforcedLeray.Short.PartI.Tasks.EulerComplementJ0

/-!
# Part III-a, task `PartIII-a:T21/c3/2` decomposition (`Sub/PartIII-a_T21_c3_2.lean`, SP 2898-2982)

Source of record: `the November 2 reference manuscript` (SP), lines 2898-2982
(`eq:short-causal-damped-complement`, `eq:short-causal-free-moving`,
`eq:short-causal-stable-moving`).

## Mathematical structure and leaf decomposition

For the periodized frame `F = periodizedFrame κ ν m b K hν.1 hF` built from a Part I seed kernel
`κ` (`IsSeedKernels κ`), we establish single-block `1/2` contraction of the normalised complement
over moving blocks `[t₁, t₂]` of length `movingZ ν t₂ - movingZ ν t₁ = B`:

1. **Unconditionally proved in `FrameBlockContractSub`**:
   * `movBeta0`, `exp_beta0_le_clockN`, `exp_free_le_clockN_mul_exp_rel`: for `0 < b ≤ clockTheta ν t₂`,
     `Real.exp ((P.eigenvalue.re - |P.kappa.re| / b) * (movingZ ν t₂ - movingZ ν t₁)) ≤ clockN P ν t₁ t₂`,
     so the unnormalised free moving growth `Real.exp ((normGrowthConst m / b + ε) * Δz)` is bounded
     by `clockN P ν t₁ t₂ * Real.exp ((-P.eigenvalue.re + (normGrowthConst m + |P.kappa.re|) / b + ε) * Δz)`.
   * `relFreeMovingEnergy`: combines `freeMovingEnergy` (`Clock/FreeMoving.lean`) with
     `exp_free_le_clockN_mul_exp_rel` to prove `eq:short-causal-free-moving` (SP 2959-2962)
     unconditionally.
   * `cellZeroExt`, `extDilCocycle`, `xNorm_cellZeroExt_eq`, `cellZeroExt_compl_apply`: the cell
     zero-extension and exterior dilation cocycle $(d(t)/d(z))^4 F((d(t)/d(z)) y)$ used in the
     periodized extension $\bar F$ (SP 2937-2945), with exact isometric property in `xNorm d m`.
   * `planarDampedComplDecay` (SP 2926-2935): proved unconditionally from
     `PartI.seedEulerComplement_zero` (`Short/PartI/Tasks/EulerComplementJ0.lean`) and
     `hP.eigenpair.re_pos : 0 < P.eigenvalue.re`, providing `C₀ > 0` and
     `h = P.eigenvalue.re / 2 > 0` with the damped planar seed-complement bound
     `Real.exp (-P.eigenvalue.re * t) * ‖g‖ ≤ C₀ * Real.exp (-h * t) * ‖f‖` on `B0008.XjM 0 m`.
   * `exists_block_length_contraction` (SP 2980-2981): given `C₀ > 0`, `h > 0`, and `γ > 0`, selects
     `B > 0` such that `C₀ * Real.exp (-h * B) + 2 * Real.exp (-γ * B) ≤ 1 / 4`.
   * `exists_b_free_rel_bound` (SP 2959-2962, 2980-2981): given `B > 0` and `0 ≤ K_num`, selects
     `ε = Real.log 2 / (2 * B) > 0` and `b_thr ≥ 1` such that for all `b ≥ b_thr`,
     `Real.exp ((-γ + K_num / b + ε) * B) ≤ 2 * Real.exp (-γ * B)`.

2. **Analytical leaves**:
   * `BlockCompactDuhamelGap` (`PartIII-a:T21/c3/2/1`, SP 2919-2925, 2962-2982,
     `Infra.CompactDuhamel.compact_duhamel`): on a block of fixed moving length
     `movingZ ν t₂ - movingZ ν t₁ = B`, given the planar damped seed-complement bound on
     `B0008.XjM 0 m` and the relative free moving bound on length `B`, the compact Duhamel
     comparison between the damped moving complement evolution and the planar seed-complement
     evolution yields homogeneous factor `≤ C₀ * e^{-h B} + α_free + δ_gap` and
     variation-of-constants forcing bound with `complModeForce κ P F tr r j`.
   * Reuses `ComplModeForceOscillator` (`PartIII-a:T21/c3/3/2`) and `ComplModeForceEulerError`
     (`PartIII-a:T21/c3/3/3`) from `Sub/PartIII-a_T21_c3_3.lean`.

3. **Proved assembly (`frameBlockContraction_of`)**:
   Combines `planarDampedComplDecay`, `relFreeMovingEnergy`, `exists_block_length_contraction`,
   `exists_b_free_rel_bound`, `BlockCompactDuhamelGap`, `ComplModeForceOscillator`, and
   `ComplModeForceEulerError` to establish `FrameBlockContraction κ` with zero sorry.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Blueprint.Planar
open scoped ENNReal ComplexConjugate ContDiff

namespace UnforcedLeray.Short.IIIa

open FrameShortBlockSub

/-! ## Damped complement rate `movBeta0` and periodized extension operators (SP 2923-2945) -/

/-- Instantaneous real damping rate `β₀(r) = Re λ + Re κ / θ(r)` subtracted from the complement
generator (SP 2923-2925). -/
def movBeta0 (P : PlanarData) (ν r : ℝ) : ℝ :=
  P.eigenvalue.re + P.kappa.re / clockTheta ν r

/-- Extension by zero outside the fundamental cell `B0579.cell d` (SP 2937-2943). -/
def cellZeroExt (d : ℝ) (W : ℝ × ℝ → ℂ) : ℝ × ℝ → ℂ :=
  (B0579.cell d).indicator W

/-- Exterior dilation cocycle `(d_t / d_z)^4 F((d_t / d_z) y)` transporting the exterior field in
the periodized extension $\bar F$ (SP 2941). -/
def extDilCocycle (d_t d_z : ℝ) (F : ℝ × ℝ → ℂ) (y : ℝ × ℝ) : ℂ :=
  (((d_t / d_z) ^ 4 : ℝ) : ℂ) * F ((d_t / d_z) * y.1, (d_t / d_z) * y.2)

/-! ## Analytical leaf for `FrameBlockContraction` -/

/-- **Leaf `PartIII-a:T21/c3/2/1` (`BlockCompactDuhamelGap`, SP 2919-2925, 2962-2982,
`Infra/CompactDuhamel.lean`)**: for a fixed moving block length `B > 0`, given the planar damped
seed-complement decay bound `(C₀, h)` on `B0008.XjM 0 m` (`planarDampedComplDecay`, SP 2926-2935)
and assuming the relative free moving energy bound with factor `α_free` on blocks of length `B`
(`relFreeMovingEnergy`, SP 2959-2962), for any gap tolerance `δ_gap > 0` there exist `C_uh ≥ 0` and
`b_gap ≥ 1` such that for `b ≥ b_gap` and small `ν`, on any block `[t₁, t₂]` of moving length
`movingZ ν t₂ - movingZ ν t₁ = B` with `b ≤ clockTheta ν t₂`, the complement `compl F w` along a
weak linearised flow satisfies the single-block Duhamel bound with homogeneous factor
`C₀ * Real.exp (-h * B) + α_free + δ_gap` and mode forcing `complModeForce`.
Composed by task `PartIII-a:T21/c3/2` via `frameBlockContraction_of`. -/
def BlockCompactDuhamelGap (κ : PlanarFrameKernels) : Prop :=
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
    ∃ C_uh b_gap : ℝ, 0 ≤ C_uh ∧ 1 ≤ b_gap ∧
      ∀ b : ℝ, b_gap ≤ b →
        ∃ ν_gap : ℝ, 0 < ν_gap ∧
          ∀ ν (hν : ν ∈ Ioc 0 ν_gap), ∀ hF : PerFrameFacts κ ν m b K,
            ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
              UnforcedLeray.Short.PartI.IsBUCTrain tr →
              ∀ t₁ t₂ : ℝ, 0 ≤ t₁ → t₁ ≤ t₂ → b ≤ clockTheta ν t₂ →
                movingZ ν t₂ - movingZ ν t₁ = B →
                ∀ f w u, IsLinearisedFlow ν (ν ^ (-2 : ℝ)) m tr t₁ f w u →
                  HasZeroCirculation (ν ^ (-2 : ℝ)) f →
                  let F := periodizedFrame κ ν m b K hν.1 hF
                  xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν t₂)) m (compl F w t₂) ≤
                    ENNReal.ofReal (clockN P ν t₁ t₂) *
                        (ENNReal.ofReal (C₀ * Real.exp (-h * B) + α_free + δ_gap) *
                          xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν t₁)) m (compl F w t₁)) +
                      ∫⁻ r in Ioc t₁ t₂,
                        ENNReal.ofReal
                            ((clockA ν r) ^ (-2 : ℝ) * (clockN P ν r t₂ * C_uh)) *
                          (∑ j : Fin 2,
                            ENNReal.ofReal ‖ampl F w r j‖ *
                              xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m
                                (complModeForce κ P F tr r j))

namespace FrameBlockContractSub

/-! ## Planar damped seed-complement decay (`eq:short-seed-complement`, SP 2926-2935) -/

/-- Unconditional planar damped seed-complement decay on `B0008.XjM 0 m` for `IsSeedKernels κ`,
`IsPlanarReference P`, and `m > 8`, proved from `PartI.seedEulerComplement_zero` with
`h = P.eigenvalue.re / 2 > 0`. -/
theorem planarDampedComplDecay {κ : PlanarFrameKernels} (hκ : IsSeedKernels κ)
    (P : PlanarData) (hP : IsPlanarReference P) {m : ℝ} (hm : 8 < m) :
    ∃ C₀ h : ℝ, 0 < C₀ ∧ 0 < h ∧ h ≤ P.eigenvalue.re ∧
      ∃ (lam : ℂ) (h_prof : ℝ → ℂ) (hh : MemLp h_prof 2 B0010.xGMeasure) (ℓ : B0010.XG →L[ℂ] ℂ),
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
            Real.exp (-P.eigenvalue.re * t) * ‖g‖ ≤ C₀ * Real.exp (-h * t) * ‖f‖) := by
  obtain ⟨lam, h_prof, hh, ℓ, hSeed, he0, he1, hlamP⟩ := hκ
  have hγ : 0 < P.eigenvalue.re := hP.eigenpair.re_pos
  have hm1_0 : 1 < m := by linarith
  set h := P.eigenvalue.re / 2
  have hh_pos : 0 < h := half_pos hγ
  have hh_le : h ≤ P.eigenvalue.re := half_le_self hγ.le
  obtain ⟨C₀, hC₀, hCompl⟩ :=
    PartI.seedEulerComplement_zero lam h_prof hh ℓ hSeed m hm1_0 h hh_pos
  refine ⟨C₀, h, hC₀, hh_pos, hh_le, lam, h_prof, hh, ℓ, hSeed, he0, he1, hlamP,
    fun hm1 t ht f => ?_⟩
  obtain ⟨u, g, hu, hg, hnorm⟩ := hCompl t ht f
  refine ⟨u, g, hu, hg, ?_⟩
  calc Real.exp (-P.eigenvalue.re * t) * ‖g‖
      ≤ Real.exp (-P.eigenvalue.re * t) * (C₀ * Real.exp (h * t) * ‖f‖) :=
        mul_le_mul_of_nonneg_left hnorm (Real.exp_pos _).le
    _ = C₀ * (Real.exp (-P.eigenvalue.re * t) * Real.exp (h * t)) * ‖f‖ := by ring
    _ = C₀ * Real.exp (-h * t) * ‖f‖ := by
        rw [← Real.exp_add]
        congr 2
        dsimp [h]
        ring

/-! ## Properties of `cellZeroExt` (SP 2937-2945) -/

/-- `cellZeroExt d W` vanishes outside `B0579.cell d`. -/
theorem cellZeroExt_compl_apply (d : ℝ) (W : ℝ × ℝ → ℂ) {y : ℝ × ℝ}
    (hy : y ∉ B0579.cell d) :
    cellZeroExt d W y = 0 :=
  indicator_of_notMem hy W

/-- `cellZeroExt d` is an exact isometry in `xNorm d m`. -/
theorem xNorm_cellZeroExt_eq (d m : ℝ) (W : ℝ × ℝ → ℂ) :
    xNorm d m (cellZeroExt d W) = xNorm d m W := by
  unfold xNorm cellZeroExt
  refine eLpNorm_congr_ae ?_
  have hae : ∀ᵐ y ∂(volume.restrict (B0579.cell d)),
      (B0579.cell d).indicator W y = W y := by
    filter_upwards [ae_restrict_mem (B0579.measurableSet_cell d)] with y hy
    exact indicator_of_mem hy W
  exact (B0579.cellMeasure_ac d m).ae_le hae

/-! ## Normalised relative free moving energy (`eq:short-causal-free-moving`, SP 2959-2962) -/

/-- Exponential lower bound on `clockN P ν u r` with explicit `1 / b` dependence on the subleading
exponent `P.kappa.re` when `0 < b ≤ clockTheta ν r`:
`Real.exp ((P.eigenvalue.re - |P.kappa.re| / b) * (movingZ ν r - movingZ ν u)) ≤ clockN P ν u r`. -/
theorem exp_beta0_le_clockN (P : PlanarData) {ν u r b : ℝ}
    (hν : 0 < ν) (hu : 0 ≤ u) (hur : u ≤ r) (hb0 : 0 < b) (hbr : b ≤ clockTheta ν r) :
    Real.exp ((P.eigenvalue.re - |P.kappa.re| / b) * (movingZ ν r - movingZ ν u)) ≤
      clockN P ν u r := by
  have hr : 0 ≤ r := hu.trans hur
  have hθu : 0 < clockTheta ν u := theta_pos hν hu
  have hθr : 0 < clockTheta ν r := theta_pos hν hr
  have hθ_le : clockTheta ν r ≤ clockTheta ν u := theta_anti hν hu hur
  have hz_eq : clockTheta ν u - clockTheta ν r = movingZ ν r - movingZ ν u :=
    clockTheta_sub_eq_movingZ_sub hν hu hr
  have hz_nonneg : 0 ≤ movingZ ν r - movingZ ν u := by linarith
  set Δz := movingZ ν r - movingZ ν u
  set q := clockTheta ν u / clockTheta ν r
  have hq1 : 1 ≤ q := (one_le_div hθr).2 hθ_le
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq1
  have hq_exp : q ≤ Real.exp (Δz / b) := by
    have hq_split : q = 1 + Δz / clockTheta ν r := by
      simp only [q, Δz, ← hz_eq]
      rw [one_add_div hθr.ne']
      ring
    have hdiv_le : Δz / clockTheta ν r ≤ Δz / b :=
      div_le_div_of_nonneg_left hz_nonneg hb0 hbr
    calc q = 1 + Δz / clockTheta ν r := hq_split
      _ ≤ 1 + Δz / b := by linarith
      _ ≤ Real.exp (Δz / b) := by linarith [Real.add_one_le_exp (Δz / b)]
  have hrpow_kap : Real.exp (-(|P.kappa.re| / b) * Δz) ≤ q ^ P.kappa.re := by
    have h1 : q ^ (-|P.kappa.re|) ≤ q ^ P.kappa.re :=
      Real.rpow_le_rpow_of_exponent_le hq1 (neg_abs_le P.kappa.re)
    have h2 : q ^ |P.kappa.re| ≤ Real.exp ((|P.kappa.re| / b) * Δz) := by
      calc q ^ |P.kappa.re| ≤ (Real.exp (Δz / b)) ^ |P.kappa.re| :=
            Real.rpow_le_rpow hq0.le hq_exp (abs_nonneg _)
        _ = Real.exp ((|P.kappa.re| / b) * Δz) := by
            rw [← Real.exp_mul]
            congr 1
            ring
    have h3 : Real.exp (-(|P.kappa.re| / b) * Δz) ≤ q ^ (-|P.kappa.re|) := by
      rw [neg_mul, Real.exp_neg, Real.rpow_neg hq0.le]
      exact inv_anti₀ (Real.rpow_pos_of_pos hq0 _) h2
    exact h3.trans h1
  unfold clockN
  rw [hz_eq]
  calc Real.exp ((P.eigenvalue.re - |P.kappa.re| / b) * Δz)
      = Real.exp (P.eigenvalue.re * Δz) * Real.exp (-(|P.kappa.re| / b) * Δz) := by
        rw [← Real.exp_add]
        congr 1
        ring
    _ ≤ Real.exp (P.eigenvalue.re * Δz) * q ^ P.kappa.re :=
        mul_le_mul_of_nonneg_left hrpow_kap (Real.exp_pos _).le

/-- Factoring `clockN P ν t₁ t₂` out of the free moving growth factor
`Real.exp ((normGrowthConst m / b + ε) * (movingZ ν t₂ - movingZ ν t₁))` (SP 2959-2962). -/
theorem exp_free_le_clockN_mul_exp_rel (P : PlanarData) {ν m b ε t₁ t₂ : ℝ}
    (hν : 0 < ν) (ht₁ : 0 ≤ t₁) (h12 : t₁ ≤ t₂) (hb0 : 0 < b) (hbs : b ≤ clockTheta ν t₂) :
    Real.exp ((normGrowthConst m / b + ε) * (movingZ ν t₂ - movingZ ν t₁)) ≤
      clockN P ν t₁ t₂ *
        Real.exp
          ((-P.eigenvalue.re + (normGrowthConst m + |P.kappa.re|) / b + ε) *
            (movingZ ν t₂ - movingZ ν t₁)) := by
  set Δz := movingZ ν t₂ - movingZ ν t₁
  have h1 := exp_beta0_le_clockN P hν ht₁ h12 hb0 hbs
  calc Real.exp ((normGrowthConst m / b + ε) * Δz)
      = Real.exp ((P.eigenvalue.re - |P.kappa.re| / b) * Δz) *
          Real.exp ((-P.eigenvalue.re + (normGrowthConst m + |P.kappa.re|) / b + ε) * Δz) := by
        rw [← Real.exp_add]
        congr 1
        ring
    _ ≤ clockN P ν t₁ t₂ *
          Real.exp ((-P.eigenvalue.re + (normGrowthConst m + |P.kappa.re|) / b + ε) * Δz) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le

/-- **Normalised relative free moving energy (`eq:short-causal-free-moving`, SP 2959-2962)**:
proved unconditionally from `freeMovingEnergy` (`Clock/FreeMoving.lean`) and
`exp_free_le_clockN_mul_exp_rel`. -/
theorem relFreeMovingEnergy (P : PlanarData) {m ε : ℝ} (hm : 8 < m) (hε : 0 < ε) :
    ∃ b₀ : ℝ, 1 ≤ b₀ ∧ ∀ b : ℝ, b₀ ≤ b → ∃ ν₀ : ℝ, 0 < ν₀ ∧
      ∀ ν ∈ Ioc 0 ν₀, ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
        UnforcedLeray.Short.PartI.IsBUCTrain tr →
        ∀ t₁ t₂ : ℝ, 0 ≤ t₁ → t₁ ≤ t₂ → b ≤ clockTheta ν t₂ →
          ∀ f : B0579.Plane → ℝ, B0579.IsCylTest (ν ^ (-2 : ℝ)) f →
            ∀ ω₀ : ℝ → B0579.Plane → ℝ, UnforcedLeray.Short.IIb.IsFreeCylFlow m tr t₁ f ω₀ →
              xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν t₂)) m
                  (JscaleInv (clockA ν t₂) (fun x => ((ω₀ t₂ x : ℝ) : ℂ))) ≤
                ENNReal.ofReal (clockN P ν t₁ t₂) *
                  (ENNReal.ofReal
                      (Real.exp
                        ((-P.eigenvalue.re + (normGrowthConst m + |P.kappa.re|) / b + ε) *
                          (movingZ ν t₂ - movingZ ν t₁))) *
                    xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν t₁)) m
                      (JscaleInv (clockA ν t₁) (fun x => ((f x : ℝ) : ℂ)))) := by
  obtain ⟨b_f, hFreeB⟩ := freeMovingEnergy m hm ε hε
  refine ⟨max 1 b_f, le_max_left 1 b_f, fun b hb => ?_⟩
  have hb1 : 1 ≤ b := (le_max_left 1 b_f).trans hb
  have hb0 : 0 < b := lt_of_lt_of_le zero_lt_one hb1
  obtain ⟨ν₀, hν₀, H⟩ := hFreeB b ((le_max_right 1 b_f).trans hb)
  refine ⟨ν₀, hν₀, fun ν hν tr htr t₁ t₂ ht₁ h12 hbs f hf ω₀ hω₀ => ?_⟩
  have hνpos : 0 < ν := hν.1
  have ht₂ : 0 ≤ t₂ := ht₁.trans h12
  have hfree := H ν hν tr htr t₁ t₂ ht₁ h12 hbs f hf ω₀ hω₀
  have hexp := exp_free_le_clockN_mul_exp_rel (m := m) (ε := ε) P hνpos ht₁ h12 hb0 hbs
  rw [← mul_assoc, ← ENNReal.ofReal_mul (clockN_pos P hνpos ht₁ ht₂).le]
  exact hfree.trans (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hexp) zero_le)

/-! ## Block-length and threshold selection lemmas (SP 2979-2982) -/

/-- Selection of the moving block length `B > 0` so that the planar seed-complement decay
`C₀ * e^{-h B}` and the relative free moving decay `2 * e^{-γ B}` sum to at most `1 / 4`
(SP 2980-2981). -/
theorem exists_block_length_contraction {C₀ h γ : ℝ} (hC₀ : 0 < C₀) (hh : 0 < h) (hγ : 0 < γ) :
    ∃ B : ℝ, 0 < B ∧ C₀ * Real.exp (-h * B) + 2 * Real.exp (-γ * B) ≤ 1 / 4 := by
  set B := max 1 (max (Real.log (8 * C₀) / h) (Real.log 16 / γ))
  have hB1 : 1 ≤ B := le_max_left _ _
  have hB_pos : 0 < B := lt_of_lt_of_le zero_lt_one hB1
  have hB_h : Real.log (8 * C₀) / h ≤ B :=
    le_trans (le_max_left _ _) (le_max_right _ _)
  have hB_γ : Real.log 16 / γ ≤ B :=
    le_trans (le_max_right _ _) (le_max_right _ _)
  have h1 : C₀ * Real.exp (-h * B) ≤ 1 / 8 := by
    have hlog : Real.log (8 * C₀) ≤ h * B := by
      have := (div_le_iff₀ hh).1 hB_h
      linarith
    have hneg : -h * B ≤ Real.log ((8 * C₀)⁻¹) := by
      rw [Real.log_inv]
      linarith
    have hexp : Real.exp (-h * B) ≤ (8 * C₀)⁻¹ := by
      calc Real.exp (-h * B) ≤ Real.exp (Real.log ((8 * C₀)⁻¹)) := Real.exp_le_exp.2 hneg
        _ = (8 * C₀)⁻¹ := Real.exp_log (by positivity)
    calc C₀ * Real.exp (-h * B) ≤ C₀ * (8 * C₀)⁻¹ :=
          mul_le_mul_of_nonneg_left hexp hC₀.le
      _ = 1 / 8 := by field_simp [hC₀.ne']
  have h2 : 2 * Real.exp (-γ * B) ≤ 1 / 8 := by
    have hlog : Real.log 16 ≤ γ * B := by
      have := (div_le_iff₀ hγ).1 hB_γ
      linarith
    have hneg : -γ * B ≤ Real.log ((16 : ℝ)⁻¹) := by
      rw [Real.log_inv]
      linarith
    have hexp : Real.exp (-γ * B) ≤ (16 : ℝ)⁻¹ := by
      calc Real.exp (-γ * B) ≤ Real.exp (Real.log ((16 : ℝ)⁻¹)) := Real.exp_le_exp.2 hneg
        _ = (16 : ℝ)⁻¹ := Real.exp_log (by norm_num)
    linarith
  exact ⟨B, hB_pos, by linarith⟩

/-- Given `B > 0` and `0 ≤ K_num`, choosing `ε = Real.log 2 / (2 * B)` and
`b_thr = max 1 (2 * B * K_num / Real.log 2)` ensures that for all `b ≥ b_thr`,
`Real.exp ((-γ + K_num / b + ε) * B) ≤ 2 * Real.exp (-γ * B)` (SP 2959-2962, 2980-2981). -/
theorem exists_b_free_rel_bound (γ : ℝ) {B K_num : ℝ} (hB : 0 < B) (_hK : 0 ≤ K_num) :
    ∃ ε b_thr : ℝ, 0 < ε ∧ 1 ≤ b_thr ∧
      ∀ b : ℝ, b_thr ≤ b →
        Real.exp ((-γ + K_num / b + ε) * B) ≤ 2 * Real.exp (-γ * B) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  set ε := Real.log 2 / (2 * B)
  have hε_pos : 0 < ε := div_pos hlog2 (by positivity)
  set b_thr := max 1 (2 * B * K_num / Real.log 2)
  refine ⟨ε, b_thr, hε_pos, le_max_left _ _, fun b hb => ?_⟩
  have hb1 : 1 ≤ b := (le_max_left _ _).trans hb
  have hb_pos : 0 < b := lt_of_lt_of_le zero_lt_one hb1
  have hb_ge : 2 * B * K_num / Real.log 2 ≤ b := (le_max_right _ _).trans hb
  have hKB_le : (K_num / b) * B ≤ Real.log 2 / 2 := by
    have hmul : 2 * B * K_num ≤ b * Real.log 2 := (div_le_iff₀ hlog2).1 hb_ge
    rw [div_mul_eq_mul_div, div_le_iff₀ hb_pos]
    linarith
  have hεB_eq : ε * B = Real.log 2 / 2 := by
    simp only [ε]
    field_simp [hB.ne']
  have hsum_le : (K_num / b + ε) * B ≤ Real.log 2 := by
    calc (K_num / b + ε) * B = (K_num / b) * B + ε * B := by ring
      _ ≤ Real.log 2 / 2 + Real.log 2 / 2 := by linarith
      _ = Real.log 2 := by ring
  calc Real.exp ((-γ + K_num / b + ε) * B)
      = Real.exp (-γ * B) * Real.exp ((K_num / b + ε) * B) := by
        rw [← Real.exp_add]
        congr 1
        ring
    _ ≤ Real.exp (-γ * B) * Real.exp (Real.log 2) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hsum_le) (Real.exp_pos _).le
    _ = 2 * Real.exp (-γ * B) := by
        rw [Real.exp_log zero_lt_two, mul_comm]

end FrameBlockContractSub

open FrameBlockContractSub

/-! ## Conditional assembly of `FrameBlockContraction` -/

/-- Assembly of `FrameBlockContraction κ` from `BlockCompactDuhamelGap` (`PartIII-a:T21/c3/2/1`),
`ComplModeForceOscillator` (`PartIII-a:T21/c3/3/2`), and `ComplModeForceEulerError`
(`PartIII-a:T21/c3/3/3`), using the unconditionally proved `planarDampedComplDecay` and
`relFreeMovingEnergy`. -/
theorem frameBlockContraction_of (κ : PlanarFrameKernels)
    (hGap : BlockCompactDuhamelGap κ)
    (hOsc : ComplModeForceOscillator κ)
    (hEul : ComplModeForceEulerError κ) :
    FrameBlockContraction κ := by
  intro hκ P hP m hm K
  -- 1. Planar seed-complement decay constants and block length B > 0
  obtain ⟨C₀, h, hC₀, hh, hh_le, hSeedDecay⟩ := planarDampedComplDecay hκ P hP hm
  have hγ : 0 < P.eigenvalue.re := lt_of_lt_of_le hh hh_le
  obtain ⟨B, hB_pos, hB_contr⟩ := exists_block_length_contraction hC₀ hh hγ
  -- 2. Relative free moving bound <= 2 * exp(-γ * B) on blocks of length B
  set K_num := normGrowthConst m + |P.kappa.re|
  have hCm_pos : 0 < normGrowthConst m := by unfold normGrowthConst; positivity
  have hK_num_nonneg : 0 ≤ K_num := by
    have := abs_nonneg P.kappa.re
    positivity
  obtain ⟨ε, b_thr, hε_pos, hb_thr1, hb_thr_exp⟩ :=
    exists_b_free_rel_bound P.eigenvalue.re hB_pos hK_num_nonneg
  obtain ⟨b_f0, hb_f0, hRelFree⟩ := relFreeMovingEnergy P hm hε_pos
  set α_free := 2 * Real.exp (-P.eigenvalue.re * B)
  have hα_free_pos : 0 < α_free := by positivity
  have hFreeHyp :
      ∃ b_f : ℝ, 1 ≤ b_f ∧ ∀ b : ℝ, b_f ≤ b → ∃ ν_f : ℝ, 0 < ν_f ∧
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
                        (JscaleInv (clockA ν t₁) (fun x => ((f x : ℝ) : ℂ)))) := by
    refine ⟨max b_thr b_f0, hb_thr1.trans (le_max_left _ _), fun b hb => ?_⟩
    have hb_t : b_thr ≤ b := (le_max_left _ _).trans hb
    have hb_0 : b_f0 ≤ b := (le_max_right _ _).trans hb
    obtain ⟨ν_f, hν_f, Hrel⟩ := hRelFree b hb_0
    refine ⟨ν_f, hν_f, fun ν hν tr htr t₁ t₂ ht₁ h12 hbs hZ f hf ω₀ hω₀ => ?_⟩
    have h1 := Hrel ν hν tr htr t₁ t₂ ht₁ h12 hbs f hf ω₀ hω₀
    rw [hZ] at h1
    refine h1.trans (mul_le_mul_of_nonneg_left ?_ zero_le)
    refine mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) zero_le
    exact hb_thr_exp b hb_t
  -- 3. Apply BlockCompactDuhamelGap with δ_gap = 1 / 4 and mode-forcing leaves
  obtain ⟨C_uh, b_gap, hC_uh, hb_gap, hGapB⟩ :=
    hGap hκ P hP m hm K C₀ h B α_free (1 / 4) hC₀ hh hh_le hB_pos hα_free_pos (by norm_num)
      hSeedDecay hFreeHyp
  obtain ⟨C₁, b_osc, hC₁, _hb_osc, hOscB⟩ := hOsc hκ m hm
  obtain ⟨C₂, b_eul, hC₂, _hb_eul, hEulB⟩ := hEul hκ P hP m hm
  set C_force := (1 + 2 * max K 0 ^ 2) * max C₁ C₂
  have hC_force_nonneg : 0 ≤ C_force := by
    have : 0 ≤ max C₁ C₂ := le_trans hC₁ (le_max_left C₁ C₂)
    positivity
  set C_B := B * C_uh * C_force
  have hC_B_nonneg : 0 ≤ C_B := by positivity
  set b₁ := max b_gap (max b_osc b_eul)
  have hb₁_ge : 1 ≤ b₁ := hb_gap.trans (le_max_left _ _)
  refine ⟨B, C_B, b₁, hB_pos, hC_B_nonneg, hb₁_ge, fun b hb => ?_⟩
  have hb_gap' : b_gap ≤ b := (le_max_left _ _).trans hb
  have hb_osc' : b_osc ≤ b :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hb
  have hb_eul' : b_eul ≤ b :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hb
  obtain ⟨ν_gap, hν_gap, HGap⟩ := hGapB b hb_gap'
  obtain ⟨ν_osc, hν_osc, HOsc⟩ := hOscB b hb_osc'
  obtain ⟨ν_eul, hν_eul, HEul⟩ := hEulB b hb_eul'
  refine ⟨min ν_gap (min ν_osc ν_eul), lt_min hν_gap (lt_min hν_osc hν_eul),
    fun ν hν hF tr htr t₁ t₂ ht₁ h12 hbs hZ f w u hw hz => ?_⟩
  have hνpos : 0 < ν := hν.1
  have hν_g : ν ∈ Ioc 0 ν_gap := ⟨hν.1, hν.2.trans (min_le_left _ _)⟩
  have hν_o : ν ∈ Ioc 0 ν_osc :=
    ⟨hν.1, hν.2.trans (le_trans (min_le_right _ _) (min_le_left _ _))⟩
  have hν_e : ν ∈ Ioc 0 ν_eul :=
    ⟨hν.1, hν.2.trans (le_trans (min_le_right _ _) (min_le_right _ _))⟩
  set F := periodizedFrame κ ν m b K hν.1 hF
  have ht₂ : 0 ≤ t₂ := ht₁.trans h12
  have hθt₂_pos : 0 < clockTheta ν t₂ := theta_pos hνpos ht₂
  -- 4. Single-block Duhamel inequality
  have hDuh := HGap ν hν_g hF tr htr t₁ t₂ ht₁ h12 hbs hZ f w u hw hz
  -- 5. Homogeneous factor C₀ * exp(-h*B) + α_free + 1/4 ≤ 1/2
  have hHom_half : C₀ * Real.exp (-h * B) + α_free + 1 / 4 ≤ 1 / 2 := by
    simp only [α_free]
    linarith [hB_contr]
  have hHom :
      ENNReal.ofReal (clockN P ν t₁ t₂) *
          (ENNReal.ofReal (C₀ * Real.exp (-h * B) + α_free + 1 / 4) *
            xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν t₁)) m (compl F w t₁)) ≤
        ENNReal.ofReal (clockN P ν t₁ t₂) *
          (ENNReal.ofReal (1 / 2) *
            xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν t₁)) m (compl F w t₁)) :=
    mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hHom_half) zero_le) zero_le
  -- 6. Forcing integral bound on Ioc t₁ t₂
  set S : ℝ≥0∞ := ⨆ r ∈ Icc t₁ t₂, amplNorm F w r / ENNReal.ofReal (clockN P ν t₁ r)
  set η_t₂ : ℝ := C_force * (1 + ν ^ 3) / clockTheta ν t₂
  have hη_t₂_nonneg : 0 ≤ η_t₂ := div_nonneg (by positivity) hθt₂_pos.le
  have hInt_pt : ∀ r ∈ Ioc t₁ t₂,
      ENNReal.ofReal ((clockA ν r) ^ (-2 : ℝ) * (clockN P ν r t₂ * C_uh)) *
        (∑ j : Fin 2,
          ENNReal.ofReal ‖ampl F w r j‖ *
            xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m (complModeForce κ P F tr r j)) ≤
      ENNReal.ofReal ((clockA ν r) ^ (-2 : ℝ)) *
        (ENNReal.ofReal (clockN P ν t₁ t₂) * (ENNReal.ofReal (C_uh * η_t₂) * S)) := by
    intro r hr
    have hr0 : 0 ≤ r := ht₁.trans hr.1.le
    have ha_pos : 0 < clockA ν r := by
      have := one_le_clockA hνpos.le hr0
      linarith
    have ha2_nonneg : 0 ≤ (clockA ν r) ^ (-2 : ℝ) := (Real.rpow_pos_of_pos ha_pos _).le
    have hθr_ge_t₂ : clockTheta ν t₂ ≤ clockTheta ν r := theta_anti hνpos hr0 hr.2
    have hbr : b ≤ clockTheta ν r := hbs.trans hθr_ge_t₂
    have hforce_r : ∀ j : Fin 2,
        xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m (complModeForce κ P F tr r j) ≤
          ENNReal.ofReal η_t₂ := by
      intro j
      obtain ⟨hOm, hOb⟩ := HOsc ν hν_o r hr0 hbr j
      obtain ⟨hEm, hEb⟩ := HEul ν hν_e tr htr r hr0 hbr j
      refine (xNorm_complModeForce_le κ P F tr j hνpos hr0 hbr hC₁ hC₂ hOm hOb hEm hEb).trans ?_
      refine ENNReal.ofReal_le_ofReal ?_
      exact div_le_div_of_nonneg_left (by positivity) hθt₂_pos hθr_ge_t₂
    have hsum_r := sum_ampl_complModeForce_le κ P F tr w hforce_r
    have hN_r : 0 < clockN P ν t₁ r := clockN_pos P hνpos ht₁ hr0
    have hN_rt₂ : 0 < clockN P ν r t₂ := clockN_pos P hνpos hr0 ht₂
    have hN_ne0 : ENNReal.ofReal (clockN P ν t₁ r) ≠ 0 :=
      (ENNReal.ofReal_pos.2 hN_r).ne'
    have hN_netop : ENNReal.ofReal (clockN P ν t₁ r) ≠ ⊤ := ENNReal.ofReal_ne_top
    have hampl_split :
        ENNReal.ofReal (clockN P ν r t₂) * amplNorm F w r ≤
          ENNReal.ofReal (clockN P ν t₁ t₂) * S := by
      have hdiv : amplNorm F w r =
          ENNReal.ofReal (clockN P ν t₁ r) *
            (amplNorm F w r / ENNReal.ofReal (clockN P ν t₁ r)) :=
        (ENNReal.mul_div_cancel hN_ne0 hN_netop).symm
      have hsup : amplNorm F w r / ENNReal.ofReal (clockN P ν t₁ r) ≤ S :=
        le_biSup (fun u => amplNorm F w u / ENNReal.ofReal (clockN P ν t₁ u)) ⟨hr.1.le, hr.2⟩
      rw [hdiv, ← mul_assoc, mul_comm (ENNReal.ofReal (clockN P ν r t₂)),
        ← FrameStableSub.ofReal_clockN_mul P hνpos ht₁ hr0 ht₂]
      exact mul_le_mul_of_nonneg_left hsup zero_le
    rw [ENNReal.ofReal_mul ha2_nonneg, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ zero_le
    calc ENNReal.ofReal (clockN P ν r t₂ * C_uh) *
          (∑ j : Fin 2,
            ENNReal.ofReal ‖ampl F w r j‖ *
              xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m (complModeForce κ P F tr r j))
        ≤ (ENNReal.ofReal (clockN P ν r t₂) * ENNReal.ofReal C_uh) *
            (ENNReal.ofReal η_t₂ * amplNorm F w r) := by
          rw [ENNReal.ofReal_mul hN_rt₂.le]
          exact mul_le_mul_of_nonneg_left hsum_r zero_le
      _ = (ENNReal.ofReal C_uh * ENNReal.ofReal η_t₂) *
            (ENNReal.ofReal (clockN P ν r t₂) * amplNorm F w r) := by
          ring
      _ ≤ (ENNReal.ofReal C_uh * ENNReal.ofReal η_t₂) *
            (ENNReal.ofReal (clockN P ν t₁ t₂) * S) :=
          mul_le_mul_of_nonneg_left hampl_split zero_le
      _ = ENNReal.ofReal (clockN P ν t₁ t₂) * (ENNReal.ofReal (C_uh * η_t₂) * S) := by
          rw [← ENNReal.ofReal_mul hC_uh]
          ring
  have hInt :
      (∫⁻ r in Ioc t₁ t₂,
        ENNReal.ofReal ((clockA ν r) ^ (-2 : ℝ) * (clockN P ν r t₂ * C_uh)) *
          (∑ j : Fin 2,
            ENNReal.ofReal ‖ampl F w r j‖ *
              xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m (complModeForce κ P F tr r j))) ≤
        ENNReal.ofReal (clockN P ν t₁ t₂) *
          (ENNReal.ofReal (C_B * (1 + ν ^ 3) / clockTheta ν t₂) * S) := by
    calc (∫⁻ r in Ioc t₁ t₂,
          ENNReal.ofReal ((clockA ν r) ^ (-2 : ℝ) * (clockN P ν r t₂ * C_uh)) *
            (∑ j : Fin 2,
              ENNReal.ofReal ‖ampl F w r j‖ *
                xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m (complModeForce κ P F tr r j)))
        ≤ ∫⁻ r in Ioc t₁ t₂,
            ENNReal.ofReal ((clockA ν r) ^ (-2 : ℝ)) *
              (ENNReal.ofReal (clockN P ν t₁ t₂) * (ENNReal.ofReal (C_uh * η_t₂) * S)) :=
          setLIntegral_mono' measurableSet_Ioc hInt_pt
      _ = (∫⁻ r in Ioc t₁ t₂, ENNReal.ofReal ((clockA ν r) ^ (-2 : ℝ))) *
            (ENNReal.ofReal (clockN P ν t₁ t₂) * (ENNReal.ofReal (C_uh * η_t₂) * S)) := by
          refine lintegral_mul_const _ ?_
          unfold clockA
          exact ENNReal.measurable_ofReal.comp
            ((measurable_const.add (measurable_const.mul measurable_id)).pow_const (-2 : ℝ))
      _ = ENNReal.ofReal B *
            (ENNReal.ofReal (clockN P ν t₁ t₂) * (ENNReal.ofReal (C_uh * η_t₂) * S)) := by
          rw [lintegral_clockA_inv_sq_eq hνpos ht₁ h12, hZ]
      _ = ENNReal.ofReal (clockN P ν t₁ t₂) *
            ((ENNReal.ofReal B * ENNReal.ofReal (C_uh * η_t₂)) * S) := by
          ring
      _ = ENNReal.ofReal (clockN P ν t₁ t₂) *
            (ENNReal.ofReal (C_B * (1 + ν ^ 3) / clockTheta ν t₂) * S) := by
          rw [← ENNReal.ofReal_mul hB_pos.le]
          congr 3
          simp only [C_B, η_t₂]
          ring
  calc xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν t₂)) m (compl F w t₂)
      ≤ ENNReal.ofReal (clockN P ν t₁ t₂) *
            (ENNReal.ofReal (1 / 2) *
              xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν t₁)) m (compl F w t₁)) +
          ENNReal.ofReal (clockN P ν t₁ t₂) *
            (ENNReal.ofReal (C_B * (1 + ν ^ 3) / clockTheta ν t₂) * S) :=
        hDuh.trans (add_le_add hHom hInt)
    _ = ENNReal.ofReal (clockN P ν t₁ t₂) *
          (ENNReal.ofReal (1 / 2) *
              xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν t₁)) m (compl F w t₁) +
            ENNReal.ofReal (C_B * (1 + ν ^ 3) / clockTheta ν t₂) * S) := by
        rw [← mul_add]

end UnforcedLeray.Short.IIIa
