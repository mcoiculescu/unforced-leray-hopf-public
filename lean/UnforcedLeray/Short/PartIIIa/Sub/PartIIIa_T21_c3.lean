import UnforcedLeray.Short.PartIIIa.Clock.Frame
import UnforcedLeray.Short.PartIIIa.Clock.LongAssemble.H2
import UnforcedLeray.Short.PartIIIa.Clock.LongAssemble.H6
import UnforcedLeray.Short.PartIIIa.Clock.Restart
import UnforcedLeray.Short.PartIIIa.Clock.ZeroCirc

/-!
# Part III-a, task `PartIII-a:T21/c3`: block-product stability of the periodized frame (`FrameStableAll`)

Source of record: `the November 2 reference manuscript` (SP), lines 2919-2990 and
2998-3006 (`eq:short-causal-damped-complement`, `eq:short-causal-free-moving`,
`eq:short-causal-stable-moving`).

## Decomposition into three analytical leaves and proved block-product assembly

For the periodized frame `F = periodizedFrame κ ν m b K hν.1 hF` of a Part I seed kernel `κ`:

* `FrameFlowMeasurable` (`PartIII-a:T21/c3/1`): along a weak linearised flow `IsLinearisedFlow`
  (`Defs.lean`), the unnormalised amplitude norm `r ↦ amplNorm F w r` and the complement norm
  `r ↦ xNorm d(r) m (compl F w r)` are `AEMeasurable` on `Icc t s` (strong continuity of `w` in
  `X_{m,c}` from `IsLinearisedFlow.strongCont` and continuous dependence of `perE`, `perLam` on
  `d(r)` once `d(r) ≥ max D₁ 1`). Proved here (`aemeasurable_div_clockN`): dividing by
  `ENNReal.ofReal (clockN P ν t r)` preserves `AEMeasurable` on `Icc t s`, discharging the first
  two conjuncts of `FrameStable`.
* `FrameBlockContraction` (`PartIII-a:T21/c3/2`, SP 2960-2982): there exist a moving block length
  `B > 0`, a forcing constant `C_B ≥ 0` and a threshold `b₁ ≥ 1` such that for `b ≥ b₁` and small
  `ν`, on every full block `[t₁, t₂]` of moving length `movingZ ν t₂ - movingZ ν t₁ = B` with
  `b ≤ clockTheta ν t₂`, the relative complement contracts by `1/2` up to the running-supremum
  amplitude coupling `C_B (1 + ν³) / θ(t₂)` (compact Duhamel comparison
  `Infra.CompactDuhamel.compact_duhamel` on a block of length `B` between the damped complement
  generator `𝓑` of SP 2919-2925, the relative free moving bound `freeMovingEnergy` of SP 2959-2962,
  and the planar seed-complement semigroup of SP 2926-2935).
* `FrameShortBlockBound` (`PartIII-a:T21/c3/3`, SP 2982-2988): for any `B > 0`, there exist
  `M_B ≥ 1`, `C_B ≥ 0` and `b₂ ≥ 1` such that for `b ≥ b₂` and small `ν`, on every short block
  `[t₁, t₂]` of moving length `0 ≤ movingZ ν t₂ - movingZ ν t₁ ≤ B` with `b ≤ clockTheta ν t₂`, the
  relative complement is bounded by `M_B` times the initial complement plus the amplitude coupling.

## Proved here (`frameStableAll_of`)

* `clockN_mul`, `ofReal_clockN_mul`: the exact multiplicative cocycle
  `clockN P ν t r = clockN P ν t u * clockN P ν u r`.
* `moveAgeOfZ_movingZ`, `movingZ_moveAgeOfZ`, `moveAgeOfZ_mono`: the order isomorphism between the
  age interval `Icc t s` and the moving-time interval `Icc (movingZ ν t) (movingZ ν s)`.
* `block_step_norm`, `block_iter_bound`: partitioning `[t, s]` at the ages
  `t_k = moveAgeOfZ ν (movingZ ν t + k * B)` for `k ≤ n = ⌊(z_s - z_t)/B⌋`, restarting the weak flow
  at each `t_k` via `IsLinearisedFlow.restart` and `zeroCirculationPreserved`, and iterating the
  `1/2`-contraction `ρ(t_{k+1}) ≤ (1/2) ρ(t_k) + δ` yields `ρ(t_n) ≤ (1/2)^n ρ(t) + 2 δ`.
* Combining with the short-block bound on `[t_n, s]`, `(1/2)^n ≤ 2 exp(-h₀(z_s - z_t))` for
  `h₀ = log 2 / B > 0`, and `frameStable_mono` (`Clock/LongAssemble/H2.lean`) proves
  `FrameStableAll κ`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Blueprint.Planar
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

/-! ## Leaf definitions -/

/-- **Leaf 1 (`FrameFlowMeasurable`, SP 2894-2902, 2975-3004)**: along any weak linearised flow,
for `m > 8`, `b` large and `ν` small (so `d(r) ≥ max D₁ 1` on `Icc t s`), the unnormalised
amplitude norm and complement norm of the periodized frame are a.e.-measurable on `Icc t s` (from
the strong continuity `IsLinearisedFlow.strongCont` on `Icc t s ⊆ Ici t` and the continuous
dependence of `perE`, `perLam` on the cell length `d(r)`). -/
def FrameFlowMeasurable (κ : PlanarFrameKernels) : Prop :=
  IsSeedKernels κ →
  ∀ m : ℝ, 8 < m → ∀ K : ℝ,
    ∃ b₀ : ℝ, 1 ≤ b₀ ∧ ∀ b : ℝ, b₀ ≤ b → ∃ ν₀ : ℝ, 0 < ν₀ ∧
      ∀ ν (hν : ν ∈ Ioc 0 ν₀), ∀ hF : PerFrameFacts κ ν m b K,
        ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
          UnforcedLeray.Short.PartI.IsBUCTrain tr →
          ∀ t s : ℝ, 0 ≤ t → t ≤ s → b ≤ clockTheta ν s → ∀ f w u,
            IsLinearisedFlow ν (ν ^ (-2 : ℝ)) m tr t f w u →
            HasZeroCirculation (ν ^ (-2 : ℝ)) f →
            AEMeasurable (fun r => amplNorm (periodizedFrame κ ν m b K hν.1 hF) w r)
              (volume.restrict (Icc t s)) ∧
            AEMeasurable (fun r => xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m
                (compl (periodizedFrame κ ν m b K hν.1 hF) w r))
              (volume.restrict (Icc t s))

/-- **Leaf 2 (`FrameBlockContraction`, SP 2960-2982)**: existence of a moving block length `B > 0`
on which each full block `movingZ ν t₂ - movingZ ν t₁ = B` contracts the relative complement by
`1/2`, up to the amplitude coupling `C_B (1 + ν³) / θ(t₂)`. -/
def FrameBlockContraction (κ : PlanarFrameKernels) : Prop :=
  IsSeedKernels κ →
  ∀ P : PlanarData, IsPlanarReference P → ∀ m : ℝ, 8 < m → ∀ K : ℝ,
    ∃ (B C_B b₁ : ℝ), 0 < B ∧ 0 ≤ C_B ∧ 1 ≤ b₁ ∧ ∀ b : ℝ, b₁ ≤ b → ∃ ν₁ : ℝ, 0 < ν₁ ∧
      ∀ ν (hν : ν ∈ Ioc 0 ν₁), ∀ hF : PerFrameFacts κ ν m b K,
        ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
          UnforcedLeray.Short.PartI.IsBUCTrain tr →
          ∀ t₁ t₂ : ℝ, 0 ≤ t₁ → t₁ ≤ t₂ → b ≤ clockTheta ν t₂ →
            movingZ ν t₂ - movingZ ν t₁ = B →
            ∀ f w u, IsLinearisedFlow ν (ν ^ (-2 : ℝ)) m tr t₁ f w u →
              HasZeroCirculation (ν ^ (-2 : ℝ)) f →
              xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν t₂)) m
                  (compl (periodizedFrame κ ν m b K hν.1 hF) w t₂) ≤
                ENNReal.ofReal (clockN P ν t₁ t₂) *
                  (ENNReal.ofReal (1 / 2) *
                      xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν t₁)) m
                        (compl (periodizedFrame κ ν m b K hν.1 hF) w t₁) +
                    ENNReal.ofReal (C_B * (1 + ν ^ 3) / clockTheta ν t₂) *
                      ⨆ r ∈ Icc t₁ t₂, amplNorm (periodizedFrame κ ν m b K hν.1 hF) w r /
                        ENNReal.ofReal (clockN P ν t₁ r))

/-- **Leaf 3 (`FrameShortBlockBound`, SP 2982-2988)**: for any moving block length `B > 0`, uniform
bound `M_B ≥ 1` on short blocks `0 ≤ movingZ ν t₂ - movingZ ν t₁ ≤ B`. -/
def FrameShortBlockBound (κ : PlanarFrameKernels) : Prop :=
  IsSeedKernels κ →
  ∀ P : PlanarData, IsPlanarReference P → ∀ m : ℝ, 8 < m → ∀ K B : ℝ, 0 < B →
    ∃ (M_B C_B b₂ : ℝ), 1 ≤ M_B ∧ 0 ≤ C_B ∧ 1 ≤ b₂ ∧ ∀ b : ℝ, b₂ ≤ b → ∃ ν₂ : ℝ, 0 < ν₂ ∧
      ∀ ν (hν : ν ∈ Ioc 0 ν₂), ∀ hF : PerFrameFacts κ ν m b K,
        ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
          UnforcedLeray.Short.PartI.IsBUCTrain tr →
          ∀ t₁ t₂ : ℝ, 0 ≤ t₁ → t₁ ≤ t₂ → b ≤ clockTheta ν t₂ →
            movingZ ν t₂ - movingZ ν t₁ ≤ B →
            ∀ f w u, IsLinearisedFlow ν (ν ^ (-2 : ℝ)) m tr t₁ f w u →
              HasZeroCirculation (ν ^ (-2 : ℝ)) f →
              xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν t₂)) m
                  (compl (periodizedFrame κ ν m b K hν.1 hF) w t₂) ≤
                ENNReal.ofReal (clockN P ν t₁ t₂) *
                  (ENNReal.ofReal M_B *
                      xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν t₁)) m
                        (compl (periodizedFrame κ ν m b K hν.1 hF) w t₁) +
                    ENNReal.ofReal (C_B * (1 + ν ^ 3) / clockTheta ν t₂) *
                      ⨆ r ∈ Icc t₁ t₂, amplNorm (periodizedFrame κ ν m b K hν.1 hF) w r /
                        ENNReal.ofReal (clockN P ν t₁ r))

namespace FrameStableSub

/-! ## Measurability and cocycle helpers -/

/-- `clockN P ν t ·` is continuous on `Icc t s`. -/
theorem continuousOn_clockN (P : PlanarData) {ν t s : ℝ} (hν : 0 < ν) (ht : 0 ≤ t) :
    ContinuousOn (fun r => clockN P ν t r) (Icc t s) := by
  have hθ : ContinuousOn (fun r => clockTheta ν r) (Icc t s) := by
    have hf : ContinuousOn (fun r => ν * clockA ν r) (Icc t s) := by
      unfold clockA
      exact continuousOn_const.mul (continuousOn_const.add (continuousOn_const.mul continuousOn_id))
    have h0 : ∀ r ∈ Icc t s, ν * clockA ν r ≠ 0 := by
      intro r hr
      have := one_le_clockA hν.le (le_trans ht hr.1)
      exact (mul_pos hν (by linarith)).ne'
    unfold clockTheta
    exact hf.inv₀ h0
  unfold clockN
  have hq : ContinuousOn (fun r => clockTheta ν t / clockTheta ν r) (Icc t s) :=
    continuousOn_const.div hθ (fun r hr => (theta_pos hν (le_trans ht hr.1)).ne')
  have hp : ContinuousOn (fun r => (clockTheta ν t / clockTheta ν r) ^ P.kappa.re) (Icc t s) :=
    hq.rpow_const (fun r hr => Or.inl (div_ne_zero (theta_pos hν ht).ne'
      (theta_pos hν (le_trans ht hr.1)).ne'))
  have he : ContinuousOn (fun r => Real.exp (P.eigenvalue.re * (clockTheta ν t - clockTheta ν r)))
      (Icc t s) :=
    (continuousOn_const.mul (continuousOn_const.sub hθ)).rexp
  exact he.mul hp

/-- Dividing an a.e.-measurable function on `Icc t s` by `ENNReal.ofReal (clockN P ν t ·)`
preserves a.e.-measurability. -/
theorem aemeasurable_div_clockN (P : PlanarData) {ν t s : ℝ} {g : ℝ → ℝ≥0∞}
    (hν : 0 < ν) (ht : 0 ≤ t)
    (hg : AEMeasurable g (volume.restrict (Icc t s))) :
    AEMeasurable (fun r => g r / ENNReal.ofReal (clockN P ν t r))
      (volume.restrict (Icc t s)) := by
  have hN : ContinuousOn (fun r => ENNReal.ofReal (clockN P ν t r)) (Icc t s) :=
    ENNReal.continuous_ofReal.comp_continuousOn (continuousOn_clockN P hν ht)
  exact hg.div (hN.aemeasurable measurableSet_Icc)

/-- Multiplicative cocycle for `clockN`: `clockN P ν t r = clockN P ν t u * clockN P ν u r`. -/
theorem clockN_mul (P : PlanarData) {ν t u r : ℝ} (hν : 0 < ν) (ht : 0 ≤ t) (hu : 0 ≤ u)
    (hr : 0 ≤ r) :
    clockN P ν t r = clockN P ν t u * clockN P ν u r := by
  unfold clockN
  have hθt : 0 < clockTheta ν t := theta_pos hν ht
  have hθu : 0 < clockTheta ν u := theta_pos hν hu
  have hθr : 0 < clockTheta ν r := theta_pos hν hr
  have hexp : Real.exp (P.eigenvalue.re * (clockTheta ν t - clockTheta ν r)) =
      Real.exp (P.eigenvalue.re * (clockTheta ν t - clockTheta ν u)) *
        Real.exp (P.eigenvalue.re * (clockTheta ν u - clockTheta ν r)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hdiv : clockTheta ν t / clockTheta ν r =
      (clockTheta ν t / clockTheta ν u) * (clockTheta ν u / clockTheta ν r) := by
    rw [div_mul_div_cancel₀ hθu.ne']
  have hrpow : (clockTheta ν t / clockTheta ν r) ^ P.kappa.re =
      (clockTheta ν t / clockTheta ν u) ^ P.kappa.re *
        (clockTheta ν u / clockTheta ν r) ^ P.kappa.re := by
    rw [hdiv, Real.mul_rpow (div_pos hθt hθu).le (div_pos hθu hθr).le]
  rw [hexp, hrpow]
  ring

theorem ofReal_clockN_mul (P : PlanarData) {ν t u r : ℝ} (hν : 0 < ν) (ht : 0 ≤ t) (hu : 0 ≤ u)
    (hr : 0 ≤ r) :
    ENNReal.ofReal (clockN P ν t r) =
      ENNReal.ofReal (clockN P ν t u) * ENNReal.ofReal (clockN P ν u r) := by
  rw [clockN_mul P hν ht hu hr, ENNReal.ofReal_mul (clockN_pos P hν ht hu).le]

/-! ## Moving-time bijection (`movingZ` and `moveAgeOfZ`) -/

/-- The age at moving time `z`: `r = z / (1 - ν z)` (SP 2857). -/
def moveAgeOfZ (ν z : ℝ) : ℝ := z / (1 - ν * z)

theorem movingZ_nonneg {ν r : ℝ} (hν : 0 < ν) (hr : 0 ≤ r) : 0 ≤ movingZ ν r := by
  unfold movingZ clockA
  exact div_nonneg hr (by positivity)

theorem nu_mul_movingZ_lt_one {ν r : ℝ} (hν : 0 < ν) (hr : 0 ≤ r) : ν * movingZ ν r < 1 := by
  have hA : 0 < 1 + ν * r := by positivity
  have e : ν * movingZ ν r = ν * r / (1 + ν * r) := by
    unfold movingZ clockA; ring
  rw [e, div_lt_one hA]
  linarith

theorem movingZ_le_movingZ {ν t s : ℝ} (hν : 0 < ν) (ht : 0 ≤ t) (hts : t ≤ s) :
    movingZ ν t ≤ movingZ ν s := by
  have hs : 0 ≤ s := ht.trans hts
  have hAt : 0 < 1 + ν * t := by positivity
  have hAs : 0 < 1 + ν * s := by positivity
  unfold movingZ clockA
  rw [div_le_div_iff₀ hAt hAs]
  nlinarith

theorem moveAgeOfZ_movingZ {ν r : ℝ} (hν : 0 < ν) (hr : 0 ≤ r) :
    moveAgeOfZ ν (movingZ ν r) = r := by
  have hA : 1 + ν * r ≠ 0 := by positivity
  unfold moveAgeOfZ movingZ clockA
  have h1 : 1 - ν * (r / (1 + ν * r)) = 1 / (1 + ν * r) := by
    field_simp; ring
  rw [h1, div_div_eq_mul_div, div_one, div_mul_cancel₀ _ hA]

theorem movingZ_moveAgeOfZ {ν z : ℝ} (hz : ν * z < 1) :
    movingZ ν (moveAgeOfZ ν z) = z := by
  have h1 : 1 - ν * z ≠ 0 := by linarith
  unfold movingZ moveAgeOfZ clockA
  have h2 : 1 + ν * (z / (1 - ν * z)) = 1 / (1 - ν * z) := by
    field_simp; ring
  rw [h2, div_div_eq_mul_div, div_one, div_mul_cancel₀ _ h1]

theorem moveAgeOfZ_mono {ν z₁ z₂ : ℝ} (hν : 0 < ν) (_hz₁ : 0 ≤ z₁) (hz₂ : ν * z₂ < 1)
    (h12 : z₁ ≤ z₂) : moveAgeOfZ ν z₁ ≤ moveAgeOfZ ν z₂ := by
  have hd2 : 0 < 1 - ν * z₂ := by linarith
  have hd1 : 0 < 1 - ν * z₁ := by nlinarith [mul_le_mul_of_nonneg_left h12 hν.le]
  unfold moveAgeOfZ
  rw [div_le_div_iff₀ hd1 hd2]
  nlinarith

theorem moveAgeOfZ_nonneg {ν z : ℝ} (hz₀ : 0 ≤ z) (hz₁ : ν * z < 1) :
    0 ≤ moveAgeOfZ ν z := by
  unfold moveAgeOfZ
  exact div_nonneg hz₀ (by linarith)

/-! ## Single-block normalisation and iteration -/

/-- Normalising a single-block complement inequality on `[t₁, t₂] ⊆ [t, s]` by `clockN P ν t t₂`. -/
theorem block_step_norm (P : PlanarData) {ν c m b K t s t₁ t₂ α C_B : ℝ}
    (F : MovingFrame ν c m b K) (w : ℝ → ℝ × ℝ → ℂ)
    (hν : 0 < ν) (ht : 0 ≤ t) (ht1 : t ≤ t₁) (h12 : t₁ ≤ t₂) (ht2s : t₂ ≤ s)
    (hC_B : 0 ≤ C_B)
    (hstep : xNorm (cellLen c (clockA ν t₂)) m (compl F w t₂) ≤
      ENNReal.ofReal (clockN P ν t₁ t₂) *
        (ENNReal.ofReal α * xNorm (cellLen c (clockA ν t₁)) m (compl F w t₁) +
          ENNReal.ofReal (C_B * (1 + ν ^ 3) / clockTheta ν t₂) *
            ⨆ r ∈ Icc t₁ t₂, amplNorm F w r / ENNReal.ofReal (clockN P ν t₁ r))) :
    xNorm (cellLen c (clockA ν t₂)) m (compl F w t₂) / ENNReal.ofReal (clockN P ν t t₂) ≤
      ENNReal.ofReal α *
          (xNorm (cellLen c (clockA ν t₁)) m (compl F w t₁) / ENNReal.ofReal (clockN P ν t t₁)) +
        ENNReal.ofReal (C_B * (1 + ν ^ 3) / clockTheta ν s) *
          ⨆ r ∈ Icc t s, amplNorm F w r / ENNReal.ofReal (clockN P ν t r) := by
  have ht₁0 : 0 ≤ t₁ := ht.trans ht1
  have ht₂0 : 0 ≤ t₂ := ht₁0.trans h12
  have hs0 : 0 ≤ s := ht₂0.trans ht2s
  set N1 := ENNReal.ofReal (clockN P ν t t₁)
  set N2 := ENNReal.ofReal (clockN P ν t₁ t₂)
  have hN1pos : N1 ≠ 0 := (ENNReal.ofReal_pos.2 (clockN_pos P hν ht ht₁0)).ne'
  have hN1top : N1 ≠ ⊤ := ENNReal.ofReal_ne_top
  have hNmul : ENNReal.ofReal (clockN P ν t t₂) = N1 * N2 :=
    ofReal_clockN_mul P hν ht ht₁0 ht₂0
  set Astar := ⨆ r ∈ Icc t s, amplNorm F w r / ENNReal.ofReal (clockN P ν t r)
  have hsup_le : (⨆ r ∈ Icc t₁ t₂, amplNorm F w r / ENNReal.ofReal (clockN P ν t₁ r)) ≤
      N1 * Astar := by
    refine iSup₂_le fun r hr => ?_
    have hr0 : 0 ≤ r := ht₁0.trans hr.1
    have hrIcc : r ∈ Icc t s := ⟨ht1.trans hr.1, hr.2.trans ht2s⟩
    have hNr : ENNReal.ofReal (clockN P ν t r) = N1 * ENNReal.ofReal (clockN P ν t₁ r) :=
      ofReal_clockN_mul P hν ht ht₁0 hr0
    have hN1r_pos : ENNReal.ofReal (clockN P ν t₁ r) ≠ 0 :=
      (ENNReal.ofReal_pos.2 (clockN_pos P hν ht₁0 hr0)).ne'
    have hN1r_top : ENNReal.ofReal (clockN P ν t₁ r) ≠ ⊤ := ENNReal.ofReal_ne_top
    have hleA : amplNorm F w r / ENNReal.ofReal (clockN P ν t r) ≤ Astar :=
      le_iSup₂ (f := fun r' (_ : r' ∈ Icc t s) =>
        amplNorm F w r' / ENNReal.ofReal (clockN P ν t r')) r hrIcc
    apply ENNReal.div_le_of_le_mul
    have h1 : (amplNorm F w r / (N1 * ENNReal.ofReal (clockN P ν t₁ r))) *
        (N1 * ENNReal.ofReal (clockN P ν t₁ r)) = amplNorm F w r :=
      ENNReal.div_mul_cancel (mul_ne_zero hN1pos hN1r_pos) (ENNReal.mul_ne_top hN1top hN1r_top)
    calc amplNorm F w r
        = (amplNorm F w r / ENNReal.ofReal (clockN P ν t r)) *
            ENNReal.ofReal (clockN P ν t r) := by rw [hNr, h1]
      _ ≤ Astar * (N1 * ENNReal.ofReal (clockN P ν t₁ r)) := by
          rw [← hNr]; exact mul_le_mul_of_nonneg_right hleA zero_le
      _ = (N1 * Astar) * ENNReal.ofReal (clockN P ν t₁ r) := by ring
  have hθ : clockTheta ν s ≤ clockTheta ν t₂ := theta_anti hν ht₂0 ht2s
  have hβ : ENNReal.ofReal (C_B * (1 + ν ^ 3) / clockTheta ν t₂) ≤
      ENNReal.ofReal (C_B * (1 + ν ^ 3) / clockTheta ν s) := by
    apply ENNReal.ofReal_le_ofReal
    exact div_le_div_of_nonneg_left (by positivity) (theta_pos hν hs0) hθ
  have hY1 : xNorm (cellLen c (clockA ν t₁)) m (compl F w t₁) =
      (xNorm (cellLen c (clockA ν t₁)) m (compl F w t₁) / N1) * N1 :=
    (ENNReal.div_mul_cancel hN1pos hN1top).symm
  apply ENNReal.div_le_of_le_mul
  rw [hNmul]
  calc xNorm (cellLen c (clockA ν t₂)) m (compl F w t₂)
      ≤ N2 * (ENNReal.ofReal α * xNorm (cellLen c (clockA ν t₁)) m (compl F w t₁) +
          ENNReal.ofReal (C_B * (1 + ν ^ 3) / clockTheta ν t₂) *
            ⨆ r ∈ Icc t₁ t₂, amplNorm F w r / ENNReal.ofReal (clockN P ν t₁ r)) := hstep
    _ ≤ N2 * (ENNReal.ofReal α *
          ((xNorm (cellLen c (clockA ν t₁)) m (compl F w t₁) / N1) * N1) +
          ENNReal.ofReal (C_B * (1 + ν ^ 3) / clockTheta ν s) * (N1 * Astar)) := by
        rw [← hY1]
        gcongr
    _ = (ENNReal.ofReal α *
          (xNorm (cellLen c (clockA ν t₁)) m (compl F w t₁) / N1) +
        ENNReal.ofReal (C_B * (1 + ν ^ 3) / clockTheta ν s) * Astar) * (N1 * N2) := by
        ring

/-- Iterating `u(k+1) ≤ (1/2) u(k) + δ` for `k < n` gives `u(n) ≤ (1/2)^n u(0) + 2 δ`. -/
theorem block_iter_bound (u : ℕ → ℝ≥0∞) (δ : ℝ≥0∞) (n : ℕ)
    (hstep : ∀ k < n, u (k + 1) ≤ ENNReal.ofReal (1 / 2) * u k + δ) :
    u n ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ n) * u 0 + ENNReal.ofReal 2 * δ := by
  induction n with
  | zero =>
    simp only [pow_zero, ENNReal.ofReal_one, one_mul]
    exact le_self_add
  | succ k ih =>
    have hk := ih (fun j hj => hstep j (Nat.lt_succ_of_lt hj))
    have h1 := hstep k (Nat.lt_succ_self k)
    have hpow : ENNReal.ofReal (1 / 2) * ENNReal.ofReal ((1 / 2 : ℝ) ^ k) =
        ENNReal.ofReal ((1 / 2 : ℝ) ^ (k + 1)) := by
      rw [← ENNReal.ofReal_mul (by norm_num), pow_succ']
    have hhalf2 : ENNReal.ofReal (1 / 2) * ENNReal.ofReal 2 = 1 := by
      rw [← ENNReal.ofReal_mul (by norm_num)]
      norm_num
    have htwo : (1 : ℝ≥0∞) * δ + δ = ENNReal.ofReal 2 * δ := by
      have e : ENNReal.ofReal 2 = (1 : ℝ≥0∞) + 1 := by
        rw [show (2 : ℝ) = 1 + 1 by norm_num, ENNReal.ofReal_add zero_le_one zero_le_one,
          ENNReal.ofReal_one]
      rw [e, add_mul, one_mul]
    calc u (k + 1) ≤ ENNReal.ofReal (1 / 2) * u k + δ := h1
      _ ≤ ENNReal.ofReal (1 / 2) *
            (ENNReal.ofReal ((1 / 2 : ℝ) ^ k) * u 0 + ENNReal.ofReal 2 * δ) + δ := by
          gcongr
      _ = (ENNReal.ofReal (1 / 2) * ENNReal.ofReal ((1 / 2 : ℝ) ^ k)) * u 0 +
            ((ENNReal.ofReal (1 / 2) * ENNReal.ofReal 2) * δ + δ) := by ring
      _ = ENNReal.ofReal ((1 / 2 : ℝ) ^ (k + 1)) * u 0 + ENNReal.ofReal 2 * δ := by
          rw [hpow, hhalf2, htwo]

/-- For `n = ⌊Δz / B⌋`, `(1/2)^n ≤ 2 * exp(-(log 2 / B) * Δz)`. -/
theorem half_pow_floor_le_exp {B Δz : ℝ} (_hB : 0 < B) (_hΔz : 0 ≤ Δz) :
    (1 / 2 : ℝ) ^ (Nat.floor (Δz / B)) ≤ 2 * Real.exp (-(Real.log 2 / B) * Δz) := by
  set n := Nat.floor (Δz / B)
  have hlt : Δz / B < (n : ℝ) + 1 := Nat.lt_floor_add_one (Δz / B)
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hexp_le : Real.exp (-(((n : ℝ) + 1) * Real.log 2)) ≤
      Real.exp (-(Real.log 2 / B) * Δz) := by
    apply Real.exp_le_exp.2
    have h1 : (Real.log 2 / B) * Δz = (Δz / B) * Real.log 2 := by ring
    have h2 : (Δz / B) * Real.log 2 ≤ ((n : ℝ) + 1) * Real.log 2 :=
      mul_le_mul_of_nonneg_right hlt.le hlog.le
    linarith
  have hexp_eq : Real.exp (-(((n : ℝ) + 1) * Real.log 2)) = (1 / 2 : ℝ) * (1 / 2 : ℝ) ^ n := by
    have e1 : -(((n : ℝ) + 1) * Real.log 2) = -Real.log 2 + (n : ℕ) * (-Real.log 2) := by
      ring
    have e2 : Real.exp (-Real.log 2) = 1 / 2 := by
      rw [Real.exp_neg, Real.exp_log (by norm_num), one_div]
    rw [e1, Real.exp_add, Real.exp_nat_mul, e2]
  linarith

end FrameStableSub

open FrameStableSub

/-! ## Conditional assembly of `FrameStableAll` -/

/-- Assembly of `FrameStableAll κ` from the three leaves (`FrameFlowMeasurable`,
`FrameBlockContraction`, `FrameShortBlockBound`). -/
theorem frameStableAll_of (κ : PlanarFrameKernels) (hκ : IsSeedKernels κ)
    (hMeas : FrameFlowMeasurable κ)
    (hFull : FrameBlockContraction κ)
    (hShort : FrameShortBlockBound κ) :
    FrameStableAll κ := by
  intro P hP m hm K
  obtain ⟨b₀, _hb₀, hBmeas⟩ := hMeas hκ m hm K
  obtain ⟨B, C_B1, b₁, hB, hCB1, _hb₁, hBfull⟩ := hFull hκ P hP m hm K
  obtain ⟨M_B, C_B2, b₂, _hMB, _hCB2, _hb₂, hBshort⟩ := hShort hκ P hP m hm K B hB
  set C_B := max C_B1 C_B2
  have hCB : 0 ≤ C_B := le_trans hCB1 (le_max_left _ _)
  set C₀ := max 1 (max (2 * M_B) ((2 * M_B + 1) * C_B))
  have hC₀_one : 1 ≤ C₀ := le_max_left _ _
  have hC₀_pos : 0 < C₀ := lt_of_lt_of_le one_pos hC₀_one
  set h₀ := Real.log 2 / B
  have hh₀ : 0 < h₀ := div_pos (Real.log_pos (by norm_num)) hB
  refine ⟨C₀, h₀, max b₀ (max b₁ b₂), hh₀, fun C hC b hb => ?_⟩
  obtain ⟨ν₀, hν₀, H0⟩ := hBmeas b (le_trans (le_max_left _ _) hb)
  obtain ⟨ν₁, hν₁, H1⟩ := hBfull b (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hb)
  obtain ⟨ν₂, hν₂, H2⟩ := hBshort b (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hb)
  refine ⟨min ν₀ (min ν₁ ν₂), lt_min hν₀ (lt_min hν₁ hν₂), fun ν hν hF => ?_⟩
  have hνpos : 0 < ν := hν.1
  have hν_0 : ν ∈ Ioc 0 ν₀ := ⟨hν.1, hν.2.trans (min_le_left _ _)⟩
  have hν_1 : ν ∈ Ioc 0 ν₁ :=
    ⟨hν.1, hν.2.trans (le_trans (min_le_right _ _) (min_le_left _ _))⟩
  have hν_2 : ν ∈ Ioc 0 ν₂ :=
    ⟨hν.1, hν.2.trans (le_trans (min_le_right _ _) (min_le_right _ _))⟩
  have hC_abs : |C₀| ≤ C := by rwa [abs_of_pos hC₀_pos]
  refine frameStable_mono P (periodizedFrame κ ν m b K hν.1 hF) hν.1 hC_abs ?_
  intro tr htr t s ht hts hbs f w u hw hz
  set F := periodizedFrame κ ν m b K hν.1 hF
  obtain ⟨hmA, hmC⟩ := H0 ν hν_0 hF tr htr t s ht hts hbs f w u hw hz
  refine ⟨aemeasurable_div_clockN P hν.1 ht hmA, aemeasurable_div_clockN P hν.1 ht hmC, ?_⟩
  -- Partition [z_t, z_s] into blocks of length B
  set zt := movingZ ν t
  set zs := movingZ ν s
  have hzt0 : 0 ≤ zt := movingZ_nonneg hν.1 ht
  have hzs1 : ν * zs < 1 := nu_mul_movingZ_lt_one hν.1 (ht.trans hts)
  have hzts : zt ≤ zs := movingZ_le_movingZ hν.1 ht hts
  have hΔz : 0 ≤ zs - zt := sub_nonneg.2 hzts
  set n := Nat.floor ((zs - zt) / B)
  let tk : ℕ → ℝ := fun k => moveAgeOfZ ν (zt + (k : ℝ) * B)
  have htk_eq0 : tk 0 = t := by
    simp only [tk, Nat.cast_zero, zero_mul, add_zero]
    exact moveAgeOfZ_movingZ hν.1 ht
  have hzk_le : ∀ k ≤ n, zt + (k : ℝ) * B ≤ zs := by
    intro k hk
    have hkR : (k : ℝ) ≤ (n : ℝ) := Nat.cast_le.2 hk
    have hnR : (n : ℝ) ≤ (zs - zt) / B := Nat.floor_le (div_nonneg hΔz hB.le)
    have hmul : (k : ℝ) * B ≤ zs - zt := by
      rw [← le_div_iff₀ hB]
      exact hkR.trans hnR
    linarith
  have htk_mem : ∀ k ≤ n, tk k ∈ Icc t s := by
    intro k hk
    have h1 : zt ≤ zt + (k : ℝ) * B := le_add_of_nonneg_right (by positivity)
    have h2 : zt + (k : ℝ) * B ≤ zs := hzk_le k hk
    constructor
    · rw [← moveAgeOfZ_movingZ hν.1 ht]
      exact moveAgeOfZ_mono hν.1 hzt0 (by linarith [mul_le_mul_of_nonneg_left h2 hν.1.le]) h1
    · rw [← moveAgeOfZ_movingZ hν.1 (ht.trans hts)]
      exact moveAgeOfZ_mono hν.1 (hzt0.trans h1) hzs1 h2
  have htk_mono : ∀ k < n, tk k ≤ tk (k + 1) := by
    intro k hk
    have h1 : zt + (k : ℝ) * B ≤ zt + ((k + 1 : ℕ) : ℝ) * B := by
      push_cast; linarith
    have h2 := hzk_le (k + 1) hk
    exact moveAgeOfZ_mono hν.1 (by positivity)
      (by linarith [mul_le_mul_of_nonneg_left h2 hν.1.le]) h1
  have htk_diff : ∀ k < n, movingZ ν (tk (k + 1)) - movingZ ν (tk k) = B := by
    intro k hk
    have h2 := hzk_le (k + 1) hk
    have h1 : zt + (k : ℝ) * B ≤ zs := hzk_le k (Nat.le_of_lt hk)
    rw [movingZ_moveAgeOfZ (by linarith [mul_le_mul_of_nonneg_left h2 hν.1.le]),
      movingZ_moveAgeOfZ (by linarith [mul_le_mul_of_nonneg_left h1 hν.1.le])]
    push_cast
    ring
  -- Iteration on the full blocks k < n
  let ρ : ℝ → ℝ≥0∞ := fun r =>
    xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m (compl F w r) /
      ENNReal.ofReal (clockN P ν t r)
  set Astar := ⨆ r ∈ Icc t s, amplNorm F w r / ENNReal.ofReal (clockN P ν t r)
  set δ := ENNReal.ofReal (C_B * (1 + ν ^ 3) / clockTheta ν s) * Astar
  have hstep_full : ∀ k < n, ρ (tk (k + 1)) ≤ ENNReal.ofReal (1 / 2) * ρ (tk k) + δ := by
    intro k hk
    have hk_mem := htk_mem k (Nat.le_of_lt hk)
    have hk1_mem := htk_mem (k + 1) hk
    have htk0 : 0 ≤ tk k := ht.trans hk_mem.1
    have hθk1 : b ≤ clockTheta ν (tk (k + 1)) :=
      hbs.trans (theta_anti hν.1 (ht.trans hk1_mem.1) hk1_mem.2)
    have hwk : IsLinearisedFlow ν (ν ^ (-2 : ℝ)) m tr (tk k) (w (tk k)) w u :=
      hw.restart hk_mem.1
    have hzk : HasZeroCirculation (ν ^ (-2 : ℝ)) (w (tk k)) :=
      zeroCirculationPreserved ν (ν ^ (-2 : ℝ)) m (Real.rpow_pos_of_pos hν.1 _)
        (by linarith) tr t f w u hw hz (tk k) hk_mem.1
    have hraw := H1 ν hν_1 hF tr htr (tk k) (tk (k + 1)) htk0 (htk_mono k hk) hθk1
      (htk_diff k hk) (w (tk k)) w u hwk hzk
    have hraw' : xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν (tk (k + 1)))) m (compl F w (tk (k + 1))) ≤
        ENNReal.ofReal (clockN P ν (tk k) (tk (k + 1))) *
          (ENNReal.ofReal (1 / 2) *
              xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν (tk k))) m (compl F w (tk k)) +
            ENNReal.ofReal (C_B * (1 + ν ^ 3) / clockTheta ν (tk (k + 1))) *
              ⨆ r ∈ Icc (tk k) (tk (k + 1)),
                amplNorm F w r / ENNReal.ofReal (clockN P ν (tk k) r)) := by
      have hC_le : ENNReal.ofReal (C_B1 * (1 + ν ^ 3) / clockTheta ν (tk (k + 1))) ≤
          ENNReal.ofReal (C_B * (1 + ν ^ 3) / clockTheta ν (tk (k + 1))) := by
        apply ENNReal.ofReal_le_ofReal
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
          (theta_pos hν.1 (ht.trans hk1_mem.1)).le
      refine hraw.trans ?_
      gcongr
    exact block_step_norm P F w hν.1 ht hk_mem.1 (htk_mono k hk) hk1_mem.2 hCB hraw'
  have hiter := block_iter_bound (fun k => ρ (tk k)) δ n hstep_full
  rw [htk_eq0] at hiter
  -- Short block [tk n, s]
  have hn_mem := htk_mem n le_rfl
  have htn0 : 0 ≤ tk n := ht.trans hn_mem.1
  have hwn : IsLinearisedFlow ν (ν ^ (-2 : ℝ)) m tr (tk n) (w (tk n)) w u :=
    hw.restart hn_mem.1
  have hzn : HasZeroCirculation (ν ^ (-2 : ℝ)) (w (tk n)) :=
    zeroCirculationPreserved ν (ν ^ (-2 : ℝ)) m (Real.rpow_pos_of_pos hν.1 _)
      (by linarith) tr t f w u hw hz (tk n) hn_mem.1
  have hshort_len : movingZ ν s - movingZ ν (tk n) ≤ B := by
    have h1 := hzk_le n le_rfl
    rw [movingZ_moveAgeOfZ (by linarith [mul_le_mul_of_nonneg_left h1 hν.1.le])]
    have hlt : (zs - zt) / B < (n : ℝ) + 1 := Nat.lt_floor_add_one ((zs - zt) / B)
    have hmul : zs - zt < ((n : ℝ) + 1) * B := (div_lt_iff₀ hB).1 hlt
    linarith
  have hraw_s := H2 ν hν_2 hF tr htr (tk n) s htn0 hn_mem.2 hbs hshort_len (w (tk n)) w u hwn hzn
  have hraw_s' : xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)) m (compl F w s) ≤
      ENNReal.ofReal (clockN P ν (tk n) s) *
        (ENNReal.ofReal M_B *
            xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν (tk n))) m (compl F w (tk n)) +
          ENNReal.ofReal (C_B * (1 + ν ^ 3) / clockTheta ν s) *
            ⨆ r ∈ Icc (tk n) s,
              amplNorm F w r / ENNReal.ofReal (clockN P ν (tk n) r)) := by
    have hC_le : ENNReal.ofReal (C_B2 * (1 + ν ^ 3) / clockTheta ν s) ≤
        ENNReal.ofReal (C_B * (1 + ν ^ 3) / clockTheta ν s) := by
      apply ENNReal.ofReal_le_ofReal
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
        (theta_pos hν.1 (ht.trans hts)).le
    refine hraw_s.trans ?_
    gcongr
  have hstep_s := block_step_norm P F w hν.1 ht hn_mem.1 hn_mem.2 le_rfl hCB hraw_s'
  -- Combine ρ(s) ≤ M_B ρ(tk n) + δ with ρ(tk n) ≤ (1/2)^n ρ(t) + 2 δ
  have hρt : ρ t = xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν t)) m (compl F w t) := by
    simp only [ρ, clockN_self P hν.1 ht, ENNReal.ofReal_one, div_one]
  have hMB0 : 0 ≤ M_B := by linarith
  have hρs_bound : ρ s ≤
      ENNReal.ofReal (C₀ * Real.exp (-h₀ * (zs - zt))) *
          xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν t)) m (compl F w t) +
        ENNReal.ofReal (C₀ * (C₀ * (1 + ν ^ 3) / clockTheta ν s)) * Astar := by
    have hstep_s' : ρ s ≤ ENNReal.ofReal M_B * ρ (tk n) + δ := hstep_s
    have h1 : ρ s ≤ ENNReal.ofReal M_B *
          (ENNReal.ofReal ((1 / 2 : ℝ) ^ n) * ρ t + ENNReal.ofReal 2 * δ) + δ := by
      refine hstep_s'.trans ?_
      gcongr
    have hpow_exp : ENNReal.ofReal M_B * ENNReal.ofReal ((1 / 2 : ℝ) ^ n) ≤
        ENNReal.ofReal (C₀ * Real.exp (-h₀ * (zs - zt))) := by
      rw [← ENNReal.ofReal_mul hMB0]
      apply ENNReal.ofReal_le_ofReal
      have hexp := half_pow_floor_le_exp hB hΔz
      have hMC : 2 * M_B ≤ C₀ := le_trans (le_max_left _ _) (le_max_right _ _)
      calc M_B * (1 / 2 : ℝ) ^ n ≤ M_B * (2 * Real.exp (-h₀ * (zs - zt))) :=
            mul_le_mul_of_nonneg_left hexp hMB0
        _ = (2 * M_B) * Real.exp (-h₀ * (zs - zt)) := by ring
        _ ≤ C₀ * Real.exp (-h₀ * (zs - zt)) :=
            mul_le_mul_of_nonneg_right hMC (Real.exp_pos _).le
    have hδ_coeff : (ENNReal.ofReal M_B * ENNReal.ofReal 2 + 1) *
          ENNReal.ofReal (C_B * (1 + ν ^ 3) / clockTheta ν s) ≤
        ENNReal.ofReal (C₀ * (C₀ * (1 + ν ^ 3) / clockTheta ν s)) := by
      have e1 : ENNReal.ofReal M_B * ENNReal.ofReal 2 + 1 = ENNReal.ofReal (2 * M_B + 1) := by
        rw [← ENNReal.ofReal_mul hMB0, ← ENNReal.ofReal_one,
          ← ENNReal.ofReal_add (by positivity) zero_le_one]
        ring_nf
      rw [e1, ← ENNReal.ofReal_mul (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      have hMCB : (2 * M_B + 1) * C_B ≤ C₀ := le_trans (le_max_right _ _) (le_max_right _ _)
      have hC₀_sq : C₀ ≤ C₀ * C₀ := by nlinarith
      have hY : 0 ≤ (1 + ν ^ 3) / clockTheta ν s :=
        div_nonneg (by positivity) (theta_pos hν.1 (ht.trans hts)).le
      calc (2 * M_B + 1) * (C_B * (1 + ν ^ 3) / clockTheta ν s)
          = ((2 * M_B + 1) * C_B) * ((1 + ν ^ 3) / clockTheta ν s) := by ring
        _ ≤ (C₀ * C₀) * ((1 + ν ^ 3) / clockTheta ν s) :=
            mul_le_mul_of_nonneg_right (hMCB.trans hC₀_sq) hY
        _ = C₀ * (C₀ * (1 + ν ^ 3) / clockTheta ν s) := by ring
    calc ρ s ≤ ENNReal.ofReal M_B *
            (ENNReal.ofReal ((1 / 2 : ℝ) ^ n) * ρ t + ENNReal.ofReal 2 * δ) + δ := h1
      _ = (ENNReal.ofReal M_B * ENNReal.ofReal ((1 / 2 : ℝ) ^ n)) * ρ t +
            ((ENNReal.ofReal M_B * ENNReal.ofReal 2 + 1) *
              ENNReal.ofReal (C_B * (1 + ν ^ 3) / clockTheta ν s)) * Astar := by
          simp only [δ]; ring
      _ ≤ ENNReal.ofReal (C₀ * Real.exp (-h₀ * (zs - zt))) *
            xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν t)) m (compl F w t) +
          ENNReal.ofReal (C₀ * (C₀ * (1 + ν ^ 3) / clockTheta ν s)) * Astar := by
          rw [← hρt]
          exact add_le_add (mul_le_mul_of_nonneg_right hpow_exp zero_le)
            (mul_le_mul_of_nonneg_right hδ_coeff zero_le)
  -- Multiply by clockN P ν t s
  have hNs_pos : ENNReal.ofReal (clockN P ν t s) ≠ 0 :=
    (ENNReal.ofReal_pos.2 (clockN_pos P hν.1 ht (ht.trans hts))).ne'
  have hNs_top : ENNReal.ofReal (clockN P ν t s) ≠ ⊤ := ENNReal.ofReal_ne_top
  calc xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)) m (compl F w s)
      = ENNReal.ofReal (clockN P ν t s) * ρ s := by
        rw [mul_comm]
        exact (ENNReal.div_mul_cancel hNs_pos hNs_top).symm
    _ ≤ ENNReal.ofReal (clockN P ν t s) *
          (ENNReal.ofReal (C₀ * Real.exp (-h₀ * (zs - zt))) *
              xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν t)) m (compl F w t) +
            ENNReal.ofReal (C₀ * (C₀ * (1 + ν ^ 3) / clockTheta ν s)) * Astar) :=
        mul_le_mul_of_nonneg_left hρs_bound zero_le

end UnforcedLeray.Short.IIIa
