import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_3
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PhaseGradient.Assembly
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PhaseGradient.L5_WardGradXPhase
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PhaseGradient.L7_WardGradYPhase
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PhaseGradient.L8_RepairSepBridge

/-!
# Audit decomposition of `PartIII-b:C/rep/3/1` (`RepAgeSurf`)

Source of record: `the November 2 reference manuscript` (73 pages), lines
5203-5210 (age-surface `L²_τ L^∞_y` bound on `DX` and `DY` for `0 < s ≤ 1/ν`),
5236-5244 (`q = ∞` endpoint `L^∞_τ L^∞_y` bound on `DX` and `D²X`, 5267),
3603-3647 (`sep:kernel`, `sep:resolvent`), and 4161-4200 (Ward fields and stream cutoff).

`RepAgeSurfAt Pl K L μ C k` has two clauses for every `w : LVel Pl L`:
1. For `0 < s` with `L.ν * s ≤ 1`,
   `ageSurfL2 P L.ε⁻¹ s (‖fderiv (repX ...)‖) + ageSurfL2 P L.ε⁻¹ s (‖fderiv (repY ...)‖) ≤ ENNReal.ofReal (C * L.ν⁻¹ ^ k * L.ε ^ (101/22) * s ^ (101/44)) * F_r`.
2. For all `(τ, y)`,
   `ENNReal.ofReal (gradSize (repX ... τ) y + hessSize (repX ... τ) y) ≤ ENNReal.ofReal (C * L.ν⁻¹ ^ k * L.ε ^ (101/22)) * F_r`.

By Hölder's inequality in `z` with `(22/3, 22/19)` (`-4 - j + 3/(22/3) = -4 - j + 9/22`, which is
`-101/22` at `j = 1`) and `periodicDilationSum_proved` on `l ∈ (0, 1)`, the separated resolvent
jets `wgxJet j`, `wgyWJet j` and outward primitives `wgxPsi`, `wgyWPsi` satisfy uniform pointwise
(`q = ∞`) bounds in `(τ, y)` bounded by `IIIa.ltauLq P (22/19) (IIIa.srcNorm T)`.

The decomposition splits into three independent leaves:
* `SepJetPointwiseSup` (`PartIII-b:C/rep/3/1/1`): pointwise `L^∞_{τ,y}` bounds on `wgxJet j` (`j ≤ 2`)
  and `wgyWJet j` (`j ≤ 1`) across any radial gap `0 ≤ rOut < rIn` with exponent `-4 - j + 9/22`.
* `OutPrimPointwiseSup` (`PartIII-b:C/rep/3/1/2`): pointwise `L^∞_{τ,y}` bounds on `wgyWPsi` and
  `wgxPsi` on the transition annulus with scale `(R√ν)^{-35/22}`.
* `SepWXWYPointwiseDecomp` (`PartIII-b:C/rep/3/1/3`):
  (i) beyond the transition annulus (`R√(5ν/4) < ϱ y`), `χ_y(ν·age) = 1` near `y`, so
  `‖fderiv (sepWX ...) y‖ₑ ≤ wgxJet 1 ν μ (ϱ y) T τ y` and
  `‖fderiv (sepWY ...) y‖ₑ ≤ wgyWJet 1 ν μ (ϱ y) T τ y`;
  (ii) globally at every `(τ, y)` (including on and near the axis where `sepWX` vanishes),
  `gradSize (sepWX ...) y + hessSize (sepWX ...) y` is bounded by `wgxJet 0, 1, 2` and `wgxPsi` at
  `L = R√ν`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Blueprint.Planar (PlanarData)

/-- **Leaf 1 (`PartIII-b:C/rep/3/1/1`): pointwise `L^∞_{τ,y}` bounds on the separated resolvent jets**
(source 3603-3629, 5203-5210, 5238-5244).  For `j ≤ 2` (`wgxJet j` of `sepX0`) and `j ≤ 1`
(`wgyWJet j` of `sepWre`), across any radial gap `0 ≤ rOut < rIn`, Hölder's inequality in `z` with
exponents `(22/3, 22/19)` (`DomPointwise.kernelNorm`, exponent `-4 - j + 9/22`) and
`periodicDilationSum_proved` over `l ∈ (0, 1)` yield a uniform pointwise bound in `(τ, y)`. -/
def SepJetPointwiseSup : Prop :=
  ∀ (σ₁ σ₂ : ℝ), -(1 / 4 : ℝ) < σ₁ → ∀ (j : ℕ), j ≤ 2 →
    ∃ (C : ℝ), 0 ≤ C ∧
      ∀ (ν μ rOut rIn P : ℝ), 0 < ν → μ ∈ Icc σ₁ σ₂ →
        0 ≤ rOut → rOut < rIn → 0 < P → P ≤ 1 →
        ∀ T, IIIa.IsSepSource P rOut T → SepMoment P T →
          ∀ (τ : ℝ) (y : Space),
            wgxJet j ν μ rIn T τ y ≤
              ENNReal.ofReal (C * (rIn - rOut) ^ (-4 - (j : ℝ) + 9 / 22)) *
                IIIa.ltauLq P (22 / 19) (IIIa.srcNorm T) ∧
            (j ≤ 1 →
              wgyWJet j ν μ rIn T τ y ≤
                ENNReal.ofReal (C * (rIn - rOut) ^ (-4 - (j : ℝ) + 9 / 22)) *
                  IIIa.ltauLq P (22 / 19) (IIIa.srcNorm T))

/-- **Leaf 2 (`PartIII-b:C/rep/3/1/2`): pointwise `L^∞_{τ,y}` bounds on the outward primitives**
(source 3687-3713, 4178-4186, 5238-5244).  On the transition annulus `streamAnn ν R`,
`outPrimPointwise_of` and `outMajReduce` bound `wgyWPsi` and `wgxPsi` by `outMaj`, and 1D Hölder
(`(22/3, 22/19)`) with `vertKernLb`, `vertDil`, `vprofHolder` and `periodicDilationSum_proved`
gives the uniform bound `(R√ν)^{-2 + 3/22 + 3/11} = (R√ν)^{-35/22}`. -/
def OutPrimPointwiseSup : Prop :=
  ∀ (σ₁ σ₂ : ℝ), -(1 / 4 : ℝ) < σ₁ →
    ∃ (C : ℝ), 0 ≤ C ∧
      ∀ (ν μ R P : ℝ), 0 < ν → 0 < R → 0 < P → P ≤ 1 → μ ∈ Icc σ₁ σ₂ →
        ∀ T, IIIa.IsSepSource P (R * Real.sqrt (5 * ν / 6)) T → SepMoment P T →
          ∀ (τ : ℝ) (y : Space),
            wgyWPsi ν μ R T τ y ≤
              ENNReal.ofReal (C * (R * Real.sqrt ν) ^ (-(35 / 22 : ℝ))) *
                IIIa.ltauLq P (22 / 19) (IIIa.srcNorm T) ∧
            wgxPsi ν μ R T τ y ≤
              ENNReal.ofReal (C * (R * Real.sqrt ν) ^ (-(35 / 22 : ℝ))) *
                IIIa.ltauLq P (22 / 19) (IIIa.srcNorm T)

/-- **Leaf 3 (`PartIII-b:C/rep/3/1/3`): pointwise cutoff decomposition for `sepWX` and `sepWY`**
(source 4181-4200, 5203-5210, 5238-5244, 5267).
* (i) Beyond the transition annulus (`R√(5ν/4) < ϱ y`), `ν · age R < 4/5` near `y`, so `χ_y = 1` and
  `χ_y' = χ_y'' = 0` near `y`; hence `sepWX = sepX0` and `sepWY = sepWre` near `y`, so their
  derivatives are bounded by `wgxJet 1 ν μ (ϱ y)` and `wgyWJet 1 ν μ (ϱ y)`.
* (ii) At every `(τ, y)` (for `ϱ y < R√ν`, including `y ∈ axis`, `physPd (sepWX ...)` vanishes on the
  open cylinder `{z | ϱ z < R√ν}`; for `ϱ y ≥ R√ν`, by `wgxPointwise`, `streamCutHess` and rotation
  invariance), `gradSize (sepWX ...) y + hessSize (sepWX ...) y` is bounded by `wgxJet 0, 1, 2` and
  `wgxPsi` at `L = R√ν`. -/
def SepWXWYPointwiseDecomp : Prop :=
  ∀ (σ₁ σ₂ : ℝ), -(1 / 4 : ℝ) < σ₁ → ∀ (χy : ℝ → ℝ), IsStreamCutoff χy →
    ∃ (C : ℝ), 0 ≤ C ∧
      ∀ (ν μ R P : ℝ), 0 < ν → ν ≤ 1 → 1 ≤ R → 0 < P → P ≤ 1 → μ ∈ Icc σ₁ σ₂ →
        ∀ T, IIIa.IsSepSource P (R * Real.sqrt (5 * ν / 6)) T → SepMoment P T → IsAxiSource T →
          ∀ (τ : ℝ) (y : Space),
            (R * Real.sqrt (5 * ν / 4) < ϱ y →
              ENNReal.ofReal ‖fderiv ℝ (sepWX ν μ R χy T τ) y‖ ≤
                  wgxJet 1 ν μ (ϱ y) T τ y ∧
                ENNReal.ofReal ‖fderiv ℝ (sepWY ν μ R χy T τ) y‖ ≤
                  wgyWJet 1 ν μ (ϱ y) T τ y) ∧
            ENNReal.ofReal (gradSize (sepWX ν μ R χy T τ) y + hessSize (sepWX ν μ R χy T τ) y) ≤
              ENNReal.ofReal C *
                (wgxJet 2 ν μ (R * Real.sqrt ν) T τ y +
                  wgxJet 1 ν μ (R * Real.sqrt ν) T τ y +
                  ENNReal.ofReal (R * Real.sqrt ν)⁻¹ *
                    wgxJet 1 ν μ (R * Real.sqrt ν) T τ y +
                  ENNReal.ofReal (R * Real.sqrt ν)⁻¹ *
                    wgxJet 0 ν μ (R * Real.sqrt ν) T τ y +
                  ENNReal.ofReal ((R * Real.sqrt ν)⁻¹ ^ 2) *
                    wgxJet 0 ν μ (R * Real.sqrt ν) T τ y +
                  ENNReal.ofReal ((R * Real.sqrt ν)⁻¹ ^ 3) *
                    wgxPsi ν μ R T τ y +
                  ENNReal.ofReal ((R * Real.sqrt ν)⁻¹ ^ 4) *
                    wgxPsi ν μ R T τ y)

/-- A uniform pointwise bound on the age surface `age R y = s` bounds `ageSurfL2 P R s`. -/
theorem ageSurfL2_le_of_pointwise {P R s : ℝ} (hP : 0 < P) (f : ℝ → Space → ℝ) (B : ℝ≥0∞)
    (h : ∀ (τ : ℝ) (y : Space), age R y = s → ENNReal.ofReal (f τ y) ≤ B) :
    ageSurfL2 P R s f ≤ B := by
  unfold ageSurfL2
  have hsup : ∀ τ : ℝ, ageSurfSup R s (f τ) ^ (2 : ℝ) ≤ B ^ (2 : ℝ) := fun τ =>
    ENNReal.rpow_le_rpow (iSup₂_le fun y hy => h τ y hy) (by norm_num)
  have hint : ∫⁻ τ in Ioc (0 : ℝ) P, ageSurfSup R s (f τ) ^ (2 : ℝ) ≤
      ENNReal.ofReal P * B ^ (2 : ℝ) := by
    calc ∫⁻ τ in Ioc (0 : ℝ) P, ageSurfSup R s (f τ) ^ (2 : ℝ)
        ≤ ∫⁻ _ in Ioc (0 : ℝ) P, B ^ (2 : ℝ) := lintegral_mono fun τ => hsup τ
      _ = B ^ (2 : ℝ) * volume (Ioc (0 : ℝ) P) := setLIntegral_const (Ioc (0 : ℝ) P) (B ^ (2 : ℝ))
      _ = ENNReal.ofReal P * B ^ (2 : ℝ) := by rw [Real.volume_Ioc, sub_zero, mul_comm]
  have hmul : ENNReal.ofReal P⁻¹ * (ENNReal.ofReal P * B ^ (2 : ℝ)) = B ^ (2 : ℝ) := by
    rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.2 hP.le), inv_mul_cancel₀ hP.ne',
      ENNReal.ofReal_one, one_mul]
  calc (ENNReal.ofReal P⁻¹ * ∫⁻ τ in Ioc (0 : ℝ) P, ageSurfSup R s (f τ) ^ (2 : ℝ)) ^ (1 / 2 : ℝ)
      ≤ (ENNReal.ofReal P⁻¹ * (ENNReal.ofReal P * B ^ (2 : ℝ))) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow (mul_le_mul_of_nonneg_left hint zero_le) (by norm_num)
    _ = (B ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by rw [hmul]
    _ = B := by rw [← ENNReal.rpow_mul, show (2 : ℝ) * (1 / 2) = 1 by norm_num, ENNReal.rpow_one]

private lemma as_L_inv_le_nu_inv {ν R : ℝ} (hν : 0 < ν) (hν1 : ν ≤ 1) (hR1 : 1 ≤ R) :
    (R * Real.sqrt ν)⁻¹ ≤ ν⁻¹ := by
  refine inv_anti₀ hν ?_
  have h1 : ν ≤ Real.sqrt ν := by
    nlinarith [Real.sq_sqrt hν.le, Real.sqrt_le_one.2 hν1, Real.sqrt_nonneg ν]
  nlinarith [Real.sqrt_pos.2 hν]

private lemma as_scale_global {ν ε : ℝ} (hν : 0 < ν) (hν1 : ν ≤ 1) (hε : 0 < ε) :
    (ε⁻¹ * Real.sqrt ν) ^ (-(101 / 22 : ℝ)) ≤ ν⁻¹ ^ 3 * ε ^ (101 / 22 : ℝ) := by
  have hs : 0 < Real.sqrt ν := Real.sqrt_pos.2 hν
  have e1 : (ε⁻¹) ^ (-(101 / 22 : ℝ)) = ε ^ (101 / 22 : ℝ) := by
    rw [Real.inv_rpow hε.le, Real.rpow_neg hε.le, inv_inv]
  have e2 : Real.sqrt ν ^ (-(101 / 22 : ℝ)) = ν⁻¹ ^ (101 / 44 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hν.le, Real.inv_rpow hν.le, ← Real.rpow_neg hν.le]
    norm_num
  have hν' : 1 ≤ ν⁻¹ := (one_le_inv₀ hν).2 hν1
  have e3 : ν⁻¹ ^ (101 / 44 : ℝ) ≤ ν⁻¹ ^ 3 := by
    have := Real.rpow_le_rpow_of_exponent_le hν' (show (101 / 44 : ℝ) ≤ (3 : ℕ) by norm_num)
    rwa [Real.rpow_natCast] at this
  rw [Real.mul_rpow (inv_pos.2 hε).le hs.le, e1, e2, mul_comm]
  exact mul_le_mul_of_nonneg_right e3 (Real.rpow_nonneg hε.le _)

private lemma as_scale_surf {ε s : ℝ} (hε : 0 < ε) (hs : 0 < s) :
    (ε⁻¹ / Real.sqrt s) ^ (-(101 / 22 : ℝ)) = ε ^ (101 / 22 : ℝ) * s ^ (101 / 44 : ℝ) := by
  have hss : 0 < Real.sqrt s := Real.sqrt_pos.2 hs
  have e1 : (ε⁻¹) ^ (-(101 / 22 : ℝ)) = ε ^ (101 / 22 : ℝ) := by
    rw [Real.inv_rpow hε.le, Real.rpow_neg hε.le, inv_inv]
  have e2 : (Real.sqrt s)⁻¹ ^ (-(101 / 22 : ℝ)) = s ^ (101 / 44 : ℝ) := by
    rw [Real.inv_rpow hss.le, Real.rpow_neg hss.le, inv_inv, Real.sqrt_eq_rpow,
      ← Real.rpow_mul hs.le]
    norm_num
  rw [div_eq_mul_inv, Real.mul_rpow (inv_pos.2 hε).le (inv_pos.2 hss).le, e1, e2]

private lemma as_varrho_of_age {R s : ℝ} (hR : 0 < R) (hs : 0 < s) {y : Space}
    (hy : age R y = s) : ϱ y = R / Real.sqrt s := by
  have hρ2 : ϱ y ^ 2 ≠ 0 := by
    intro h0
    have : age R y = 0 := by unfold age; rw [h0, div_zero]
    linarith
  have h1 : ϱ y ^ 2 = (R / Real.sqrt s) ^ 2 := by
    unfold age at hy
    rw [div_pow, Real.sq_sqrt hs.le, eq_div_iff (ne_of_gt hs)]
    have := (div_eq_iff hρ2).1 hy
    linarith
  have hss : 0 < R / Real.sqrt s := div_pos hR (Real.sqrt_pos.2 hs)
  exact (sq_eq_sq₀ (Real.sqrt_nonneg _) hss.le).1 h1

private lemma as_L_le_surf {ν R s : ℝ} (hν : 0 < ν) (hR : 0 < R) (hs : 0 < s)
    (hνs : ν * s ≤ 1) : R * Real.sqrt ν ≤ R / Real.sqrt s := by
  have hss : 0 < Real.sqrt s := Real.sqrt_pos.2 hs
  rw [le_div_iff₀ hss, mul_assoc, ← Real.sqrt_mul hν.le]
  have h1 : Real.sqrt (ν * s) ≤ 1 := Real.sqrt_le_one.2 hνs
  nlinarith

private lemma as_ann_rpow_le {ν R s : ℝ} (hν : 0 < ν) (hR : 0 < R) (hs : 0 < s)
    (hle : R / Real.sqrt s ≤ R * Real.sqrt (5 * ν / 4)) :
    (R * Real.sqrt ν) ^ (-(101 / 22 : ℝ)) ≤
      (Real.sqrt (5 / 4)) ^ (101 / 22 : ℝ) * (R / Real.sqrt s) ^ (-(101 / 22 : ℝ)) := by
  have hL : 0 < R * Real.sqrt ν := mul_pos hR (Real.sqrt_pos.2 hν)
  have hRs : 0 < R / Real.sqrt s := div_pos hR (Real.sqrt_pos.2 hs)
  have h54 : 0 < Real.sqrt (5 / 4) := Real.sqrt_pos.2 (by norm_num)
  have heq : R * Real.sqrt (5 * ν / 4) = Real.sqrt (5 / 4) * (R * Real.sqrt ν) := by
    rw [show 5 * ν / 4 = (5 / 4) * ν by ring, Real.sqrt_mul (by norm_num)]; ring
  rw [heq] at hle
  have hinv : (R * Real.sqrt ν)⁻¹ ≤ Real.sqrt (5 / 4) * (R / Real.sqrt s)⁻¹ := by
    rw [inv_le_iff_one_le_mul₀' hL]
    calc (1 : ℝ) = (R / Real.sqrt s) / (R / Real.sqrt s) := (div_self hRs.ne').symm
      _ ≤ (Real.sqrt (5 / 4) * (R * Real.sqrt ν)) / (R / Real.sqrt s) :=
          div_le_div_of_nonneg_right hle hRs.le
      _ = R * Real.sqrt ν * (Real.sqrt (5 / 4) * (R / Real.sqrt s)⁻¹) := by ring
  have hrp := Real.rpow_le_rpow (inv_nonneg.2 hL.le) hinv (by norm_num : (0 : ℝ) ≤ 101 / 22)
  rw [Real.inv_rpow hL.le, ← Real.rpow_neg hL.le,
    Real.mul_rpow h54.le (inv_nonneg.2 hRs.le), Real.inv_rpow hRs.le, ← Real.rpow_neg hRs.le] at hrp
  exact hrp

private lemma as_term_le {κ C D e Y : ℝ} {F g : ℝ≥0∞} (hκ : 0 ≤ κ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hY : 0 ≤ Y) (h : κ * (C * D ^ e) ≤ Y)
    (hg : g ≤ ENNReal.ofReal (C * D ^ e) * F) :
    ENNReal.ofReal κ * g ≤ ENNReal.ofReal Y * F := by
  calc ENNReal.ofReal κ * g
      ≤ ENNReal.ofReal κ * (ENNReal.ofReal (C * D ^ e) * F) :=
        mul_le_mul_of_nonneg_left hg zero_le
    _ = ENNReal.ofReal (κ * (C * D ^ e)) * F := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hκ]
    _ ≤ ENNReal.ofReal Y * F := by
        have := hD; have := hC; have := hY
        gcongr

private lemma as_sumX (K1 Cx K0 Co Y : ℝ) (F : ℝ≥0∞)
    (h1 : 0 ≤ K1) (hCx : 0 ≤ Cx) (h0 : 0 ≤ K0) (hCo : 0 ≤ Co) (hY : 0 ≤ Y) :
    ENNReal.ofReal (K1 * Y) * F + ENNReal.ofReal (Cx * (K0 * Y)) * F +
        ENNReal.ofReal (Cx * (Co * Y)) * F =
      ENNReal.ofReal ((K1 + Cx * K0 + Cx * Co) * Y) * F := by
  have e : (K1 + Cx * K0 + Cx * Co) * Y = (K1 * Y + Cx * (K0 * Y)) + Cx * (Co * Y) := by ring
  rw [e, ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_add (by positivity) (by positivity)]
  simp only [add_mul]

private lemma as_sum5 (K0 K1 K2 Co Y : ℝ) (F : ℝ≥0∞)
    (h0 : 0 ≤ K0) (h1 : 0 ≤ K1) (h2 : 0 ≤ K2) (hCo : 0 ≤ Co) (hY : 0 ≤ Y) :
    ENNReal.ofReal (K0 * Y) * F + ENNReal.ofReal (K1 * Y) * F +
        ENNReal.ofReal (K2 * Y) * F + ENNReal.ofReal (K1 * Y) * F +
        ENNReal.ofReal (Co * Y) * F =
      ENNReal.ofReal ((K0 + K1 + K2 + K1 + Co) * Y) * F := by
  have e : (K0 + K1 + K2 + K1 + Co) * Y =
      (((K0 * Y + K1 * Y) + K2 * Y) + K1 * Y) + Co * Y := by ring
  rw [e, ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_add (by positivity) (by positivity)]
  simp only [add_mul]

private lemma as_sumY (K1 Cy1 K0 Co Cy2 S Y : ℝ) (F : ℝ≥0∞)
    (h1 : 0 ≤ K1) (hCy1 : 0 ≤ Cy1) (h0 : 0 ≤ K0) (hCo : 0 ≤ Co) (hCy2 : 0 ≤ Cy2)
    (hS : 0 ≤ S) (hY : 0 ≤ Y) :
    (ENNReal.ofReal (K1 * Y) * F + ENNReal.ofReal (Cy1 * (K0 * Y)) * F +
        ENNReal.ofReal (Cy1 * (Co * Y)) * F) +
      ENNReal.ofReal Cy2 * (ENNReal.ofReal (S * Y) * F) =
      ENNReal.ofReal ((K1 + Cy1 * K0 + Cy1 * Co + Cy2 * S) * Y) * F := by
  have e : (K1 + Cy1 * K0 + Cy1 * Co + Cy2 * S) * Y =
      ((K1 * Y + Cy1 * (K0 * Y)) + Cy1 * (Co * Y)) + Cy2 * (S * Y) := by ring
  rw [e, ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_mul hCy2]
  simp only [add_mul, mul_assoc]

private lemma as_sum6 (K2 K1 K0 Co Y : ℝ) (F : ℝ≥0∞)
    (h2 : 0 ≤ K2) (h1 : 0 ≤ K1) (h0 : 0 ≤ K0) (hCo : 0 ≤ Co) (hY : 0 ≤ Y) :
    ENNReal.ofReal (K2 * Y) * F + ENNReal.ofReal (K1 * Y) * F +
        ENNReal.ofReal (K1 * Y) * F + ENNReal.ofReal (K0 * Y) * F +
        ENNReal.ofReal (K0 * Y) * F + ENNReal.ofReal (Co * Y) * F +
        ENNReal.ofReal (Co * Y) * F =
      ENNReal.ofReal ((K2 + K1 + K1 + K0 + K0 + Co + Co) * Y) * F := by
  have e : (K2 + K1 + K1 + K0 + K0 + Co + Co) * Y =
      (((((K2 * Y + K1 * Y) + K1 * Y) + K0 * Y) + K0 * Y) + Co * Y) + Co * Y := by ring
  rw [e, ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_add (by positivity) (by positivity)]
  simp only [add_mul]

private lemma as_ofReal_mul_le {a b : ℝ} {F : ℝ≥0∞} (hab : a ≤ b) :
    ENNReal.ofReal a * F ≤ ENNReal.ofReal b * F :=
  mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hab) zero_le

private lemma as_MX_le {MX MY A54 K1 MGH Y Ys : ℝ}
    (hMX : 0 ≤ MX) (hMY : 0 ≤ MY) (hA : 0 ≤ A54) (hK1 : 0 ≤ K1) (hMGH : 0 ≤ MGH) (hYs : 0 ≤ Ys)
    (hY : Y ≤ A54 * Ys) :
    MX * Y ≤ ((MX + MY) * A54 + K1 + MGH) * Ys := by
  have h1 : MX * Y ≤ MX * (A54 * Ys) := mul_le_mul_of_nonneg_left hY hMX
  nlinarith [mul_nonneg hMY (mul_nonneg hA hYs), mul_nonneg hK1 hYs, mul_nonneg hMGH hYs]

private lemma as_MY_le {MX MY A54 K1 MGH Y Ys : ℝ}
    (hMX : 0 ≤ MX) (hMY : 0 ≤ MY) (hA : 0 ≤ A54) (hK1 : 0 ≤ K1) (hMGH : 0 ≤ MGH) (hYs : 0 ≤ Ys)
    (hY : Y ≤ A54 * Ys) :
    MY * Y ≤ ((MX + MY) * A54 + K1 + MGH) * Ys := by
  have h1 : MY * Y ≤ MY * (A54 * Ys) := mul_le_mul_of_nonneg_left hY hMY
  nlinarith [mul_nonneg hMX (mul_nonneg hA hYs), mul_nonneg hK1 hYs, mul_nonneg hMGH hYs]

private lemma as_K1_le {MX MY A54 K1 MGH Ys : ℝ}
    (hMX : 0 ≤ MX) (hMY : 0 ≤ MY) (hA : 0 ≤ A54) (hMGH : 0 ≤ MGH) (hYs : 0 ≤ Ys) :
    K1 * Ys ≤ ((MX + MY) * A54 + K1 + MGH) * Ys := by
  nlinarith [mul_nonneg (mul_nonneg (add_nonneg hMX hMY) hA) hYs, mul_nonneg hMGH hYs]

private lemma as_MGH_le {MX MY A54 K1 MGH Y : ℝ}
    (hMX : 0 ≤ MX) (hMY : 0 ≤ MY) (hA : 0 ≤ A54) (hK1 : 0 ≤ K1) (hY : 0 ≤ Y) :
    MGH * Y ≤ ((MX + MY) * A54 + K1 + MGH) * Y := by
  nlinarith [mul_nonneg (add_nonneg (mul_nonneg (add_nonneg hMX hMY) hA) hK1) hY]

private lemma as_gap_le {c0 A L : ℝ} (hc0 : c0 = 1 - Real.sqrt (5 / 6)) (hL : L ≤ A) :
    c0 * A ≤ A - Real.sqrt (5 / 6) * L := by
  rw [hc0]
  have hs : 0 ≤ Real.sqrt (5 / 6) := Real.sqrt_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left hL hs]

private lemma as_scale_term {C a b K Y : ℝ} {Z F : ℝ≥0∞} (hC : 0 ≤ C) (ha : a = b)
    (hb : ENNReal.ofReal b * Z ≤ ENNReal.ofReal (K * Y) * F) :
    ENNReal.ofReal (C * a) * Z ≤ ENNReal.ofReal (C * (K * Y)) * F := by
  rw [ha, ENNReal.ofReal_mul hC, mul_assoc]
  calc ENNReal.ofReal C * (ENNReal.ofReal b * Z)
      ≤ ENNReal.ofReal C * (ENNReal.ofReal (K * Y) * F) := mul_le_mul_of_nonneg_left hb zero_le
    _ = ENNReal.ofReal (C * (K * Y)) * F := by rw [← mul_assoc, ← ENNReal.ofReal_mul hC]

private lemma as_bJ_at_L {D0 D1 D2 Co ν μ R c0 K0 K1 K2 L Y : ℝ}
    {T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ} {τ : ℝ} {y : Space} {F : ℝ≥0∞}
    (hν : 0 < ν) (hν1 : ν ≤ 1) (hR1 : 1 ≤ R)
    (hD0 : 0 ≤ D0) (hD1 : 0 ≤ D1) (hD2 : 0 ≤ D2) (hCo : 0 ≤ Co)
    (hc0 : c0 = 1 - Real.sqrt (5 / 6))
    (hK0_eq : K0 = D0 * c0 ^ (-4 - ((0 : ℕ) : ℝ) + 9 / 22))
    (hK1_eq : K1 = D1 * c0 ^ (-4 - ((1 : ℕ) : ℝ) + 9 / 22))
    (hK2_eq : K2 = D2 * c0 ^ (-4 - ((2 : ℕ) : ℝ) + 9 / 22))
    (hL : L = R * Real.sqrt ν)
    (hY : Y = ν⁻¹ * L ^ (-(101 / 22 : ℝ)))
    (j0x : wgxJet 0 ν μ L T τ y ≤
      ENNReal.ofReal (D0 * (L - R * Real.sqrt (5 * ν / 6)) ^
        (-4 - ((0 : ℕ) : ℝ) + 9 / 22)) * F)
    (j0w : wgyWJet 0 ν μ L T τ y ≤
      ENNReal.ofReal (D0 * (L - R * Real.sqrt (5 * ν / 6)) ^
        (-4 - ((0 : ℕ) : ℝ) + 9 / 22)) * F)
    (j1x : wgxJet 1 ν μ L T τ y ≤
      ENNReal.ofReal (D1 * (L - R * Real.sqrt (5 * ν / 6)) ^
        (-4 - ((1 : ℕ) : ℝ) + 9 / 22)) * F)
    (j1w : wgyWJet 1 ν μ L T τ y ≤
      ENNReal.ofReal (D1 * (L - R * Real.sqrt (5 * ν / 6)) ^
        (-4 - ((1 : ℕ) : ℝ) + 9 / 22)) * F)
    (j2x : wgxJet 2 ν μ L T τ y ≤
      ENNReal.ofReal (D2 * (L - R * Real.sqrt (5 * ν / 6)) ^
        (-4 - ((2 : ℕ) : ℝ) + 9 / 22)) * F)
    (ow : wgyWPsi ν μ R T τ y ≤
      ENNReal.ofReal (Co * L ^ (-(35 / 22 : ℝ))) * F)
    (ox : wgxPsi ν μ R T τ y ≤
      ENNReal.ofReal (Co * L ^ (-(35 / 22 : ℝ))) * F) :
    wgxJet 1 ν μ L T τ y ≤ ENNReal.ofReal (K1 * Y) * F ∧
    wgyWJet 1 ν μ L T τ y ≤ ENNReal.ofReal (K1 * Y) * F ∧
    ENNReal.ofReal L⁻¹ * wgxJet 0 ν μ L T τ y ≤ ENNReal.ofReal (K0 * Y) * F ∧
    ENNReal.ofReal L⁻¹ * wgyWJet 0 ν μ L T τ y ≤ ENNReal.ofReal (K0 * Y) * F ∧
    wgxJet 2 ν μ L T τ y ≤ ENNReal.ofReal (K2 * Y) * F ∧
    ENNReal.ofReal L⁻¹ * wgxJet 2 ν μ L T τ y ≤ ENNReal.ofReal (K2 * Y) * F ∧
    ENNReal.ofReal L⁻¹ * wgxJet 1 ν μ L T τ y ≤ ENNReal.ofReal (K1 * Y) * F ∧
    ENNReal.ofReal (L⁻¹ ^ 2) * wgxJet 1 ν μ L T τ y ≤ ENNReal.ofReal (K1 * Y) * F ∧
    ENNReal.ofReal (L⁻¹ ^ 2) * wgxJet 0 ν μ L T τ y ≤ ENNReal.ofReal (K0 * Y) * F ∧
    ENNReal.ofReal (L⁻¹ ^ 3) * wgxPsi ν μ R T τ y ≤ ENNReal.ofReal (Co * Y) * F ∧
    ENNReal.ofReal (L⁻¹ ^ 3) * wgyWPsi ν μ R T τ y ≤ ENNReal.ofReal (Co * Y) * F ∧
    ENNReal.ofReal (L⁻¹ ^ 4) * wgxPsi ν μ R T τ y ≤ ENNReal.ofReal (Co * Y) * F := by
  have hR : 0 < R := by linarith
  have hLpos : 0 < L := by rw [hL]; exact mul_pos hR (Real.sqrt_pos.2 hν)
  have hLsq : ν * R ^ 2 = L ^ 2 := by rw [hL, mul_pow, Real.sq_sqrt hν.le]; ring
  have hs56 : Real.sqrt (5 / 6) < 1 := by rw [Real.sqrt_lt' one_pos]; norm_num
  have hc0pos : 0 < c0 := by rw [hc0]; exact sub_pos.2 hs56
  have hc0n : 0 ≤ c0 := hc0pos.le
  have hrO : R * Real.sqrt (5 * ν / 6) = Real.sqrt (5 / 6) * L := by
    rw [hL, show 5 * ν / 6 = 5 / 6 * ν by ring, Real.sqrt_mul (by norm_num)]; ring
  have hD : L - R * Real.sqrt (5 * ν / 6) = c0 * L := by
    rw [hrO, hc0]; ring
  have hK0 : 0 ≤ K0 := by rw [hK0_eq]; exact mul_nonneg hD0 (Real.rpow_nonneg hc0n _)
  have hK1 : 0 ≤ K1 := by rw [hK1_eq]; exact mul_nonneg hD1 (Real.rpow_nonneg hc0n _)
  have hK2 : 0 ≤ K2 := by rw [hK2_eq]; exact mul_nonneg hD2 (Real.rpow_nonneg hc0n _)
  have hX0 : 0 ≤ L ^ (-(101 / 22 : ℝ)) := Real.rpow_nonneg hLpos.le _
  have hν1' : 1 ≤ ν⁻¹ := (one_le_inv₀ hν).2 hν1
  have hY0 : 0 ≤ Y := by rw [hY]; exact mul_nonneg (inv_nonneg.2 hν.le) hX0
  have hXY : L ^ (-(101 / 22 : ℝ)) ≤ Y := by
    rw [hY]
    calc L ^ (-(101 / 22 : ℝ)) = 1 * L ^ (-(101 / 22 : ℝ)) := (one_mul _).symm
      _ ≤ ν⁻¹ * L ^ (-(101 / 22 : ℝ)) := mul_le_mul_of_nonneg_right hν1' hX0
  have hLinv_le : L⁻¹ ≤ ν⁻¹ := by rw [hL]; exact as_L_inv_le_nu_inv hν hν1 hR1
  have hY123 : L ^ (-(123 / 22 : ℝ)) ≤ Y := by
    have h1 : L ^ (-(123 / 22 : ℝ)) = L⁻¹ * L ^ (-(101 / 22 : ℝ)) := by
      rw [← Real.rpow_neg_one L, ← Real.rpow_add hLpos]; congr 1; norm_num
    rw [h1, hY]; exact mul_le_mul_of_nonneg_right hLinv_le hX0
  have hY145 : L ^ (-(145 / 22 : ℝ)) ≤ Y := by
    have h2 : L ^ (-(145 / 22 : ℝ)) = L ^ (-2 : ℝ) * L ^ (-(101 / 22 : ℝ)) := by
      rw [← Real.rpow_add hLpos]; congr 1; norm_num
    have h3 : L ^ (-2 : ℝ) ≤ ν⁻¹ := by
      have : L ^ (-2 : ℝ) = (L ^ 2)⁻¹ := by rw [Real.rpow_neg hLpos.le]; norm_cast
      rw [this, ← hLsq]
      refine inv_anti₀ hν ?_
      nlinarith [mul_pos hν (pow_pos hR 2), sq_nonneg R, mul_nonneg hν.le (sq_nonneg (R - 1)),
        mul_nonneg hν.le (sq_nonneg R)]
    rw [h2, hY]; exact mul_le_mul_of_nonneg_right h3 hX0
  have hLinv : L⁻¹ = L ^ (-1 : ℝ) := (Real.rpow_neg_one L).symm
  have hLinv2 : L⁻¹ ^ 2 = L ^ (-2 : ℝ) := by rw [Real.rpow_neg hLpos.le, inv_pow]; norm_cast
  have hLinv3 : L⁻¹ ^ 3 = L ^ (-3 : ℝ) := by rw [Real.rpow_neg hLpos.le, inv_pow]; norm_cast
  have hLinv4 : L⁻¹ ^ 4 = L ^ (-4 : ℝ) := by rw [Real.rpow_neg hLpos.le, inv_pow]; norm_cast
  have hmul : ∀ a b c : ℝ, a + b = c → L ^ a * L ^ b = L ^ c := fun a b c h => by
    rw [← Real.rpow_add hLpos, h]
  have xp1 : (c0 * L) ^ (-4 - ((1 : ℕ) : ℝ) + 9 / 22) =
      c0 ^ (-4 - ((1 : ℕ) : ℝ) + 9 / 22) * L ^ (-(101 / 22 : ℝ)) := by
    rw [Real.mul_rpow hc0n hLpos.le]; congr 2; norm_num
  have xp0 : L ^ (-1 : ℝ) * (c0 * L) ^ (-4 - ((0 : ℕ) : ℝ) + 9 / 22) =
      c0 ^ (-4 - ((0 : ℕ) : ℝ) + 9 / 22) * L ^ (-(101 / 22 : ℝ)) := by
    rw [Real.mul_rpow hc0n hLpos.le, mul_left_comm, hmul _ _ (-(101 / 22)) (by norm_num)]
  have xp2 : (c0 * L) ^ (-4 - ((2 : ℕ) : ℝ) + 9 / 22) =
      c0 ^ (-4 - ((2 : ℕ) : ℝ) + 9 / 22) * L ^ (-(123 / 22 : ℝ)) := by
    rw [Real.mul_rpow hc0n hLpos.le]; congr 2; norm_num
  have xp2_1 : L ^ (-1 : ℝ) * (c0 * L) ^ (-4 - ((2 : ℕ) : ℝ) + 9 / 22) =
      c0 ^ (-4 - ((2 : ℕ) : ℝ) + 9 / 22) * L ^ (-(145 / 22 : ℝ)) := by
    rw [Real.mul_rpow hc0n hLpos.le, mul_left_comm, hmul _ _ (-(145 / 22)) (by norm_num)]
  have xp1_1 : L ^ (-1 : ℝ) * (c0 * L) ^ (-4 - ((1 : ℕ) : ℝ) + 9 / 22) =
      c0 ^ (-4 - ((1 : ℕ) : ℝ) + 9 / 22) * L ^ (-(123 / 22 : ℝ)) := by
    rw [Real.mul_rpow hc0n hLpos.le, mul_left_comm, hmul _ _ (-(123 / 22)) (by norm_num)]
  have xp1_2 : L ^ (-2 : ℝ) * (c0 * L) ^ (-4 - ((1 : ℕ) : ℝ) + 9 / 22) =
      c0 ^ (-4 - ((1 : ℕ) : ℝ) + 9 / 22) * L ^ (-(145 / 22 : ℝ)) := by
    rw [Real.mul_rpow hc0n hLpos.le, mul_left_comm, hmul _ _ (-(145 / 22)) (by norm_num)]
  have xp0_2 : L ^ (-2 : ℝ) * (c0 * L) ^ (-4 - ((0 : ℕ) : ℝ) + 9 / 22) =
      c0 ^ (-4 - ((0 : ℕ) : ℝ) + 9 / 22) * L ^ (-(123 / 22 : ℝ)) := by
    rw [Real.mul_rpow hc0n hLpos.le, mul_left_comm, hmul _ _ (-(123 / 22)) (by norm_num)]
  have xpPsi : L ^ (-3 : ℝ) * L ^ (-(35 / 22 : ℝ)) = L ^ (-(101 / 22 : ℝ)) :=
    hmul _ _ (-(101 / 22)) (by norm_num)
  have xpPsi4 : L ^ (-4 : ℝ) * L ^ (-(35 / 22 : ℝ)) = L ^ (-(123 / 22 : ℝ)) :=
    hmul _ _ (-(123 / 22)) (by norm_num)
  rw [hD] at j0x j0w j1x j1w j2x
  have hcL : 0 ≤ c0 * L := mul_nonneg hc0n hLpos.le
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using as_term_le zero_le_one hD1 hcL (mul_nonneg hK1 hY0)
      (by rw [one_mul, xp1, ← mul_assoc, ← hK1_eq]; exact mul_le_mul_of_nonneg_left hXY hK1) j1x
  · simpa using as_term_le zero_le_one hD1 hcL (mul_nonneg hK1 hY0)
      (by rw [one_mul, xp1, ← mul_assoc, ← hK1_eq]; exact mul_le_mul_of_nonneg_left hXY hK1) j1w
  · exact as_term_le (inv_nonneg.2 hLpos.le) hD0 hcL (mul_nonneg hK0 hY0)
      (by rw [hLinv, ← mul_left_comm, xp0, ← mul_assoc, ← hK0_eq]; exact mul_le_mul_of_nonneg_left hXY hK0) j0x
  · exact as_term_le (inv_nonneg.2 hLpos.le) hD0 hcL (mul_nonneg hK0 hY0)
      (by rw [hLinv, ← mul_left_comm, xp0, ← mul_assoc, ← hK0_eq]; exact mul_le_mul_of_nonneg_left hXY hK0) j0w
  · simpa using as_term_le zero_le_one hD2 hcL (mul_nonneg hK2 hY0)
      (by rw [one_mul, xp2, ← mul_assoc, ← hK2_eq]; exact mul_le_mul_of_nonneg_left hY123 hK2) j2x
  · exact as_term_le (inv_nonneg.2 hLpos.le) hD2 hcL (mul_nonneg hK2 hY0)
      (by rw [hLinv, ← mul_left_comm, xp2_1, ← mul_assoc, ← hK2_eq]
          exact mul_le_mul_of_nonneg_left hY145 hK2) j2x
  · exact as_term_le (inv_nonneg.2 hLpos.le) hD1 hcL (mul_nonneg hK1 hY0)
      (by rw [hLinv, ← mul_left_comm, xp1_1, ← mul_assoc, ← hK1_eq]
          exact mul_le_mul_of_nonneg_left hY123 hK1) j1x
  · exact as_term_le (by positivity) hD1 hcL (mul_nonneg hK1 hY0)
      (by rw [hLinv2, ← mul_left_comm, xp1_2, ← mul_assoc, ← hK1_eq]
          exact mul_le_mul_of_nonneg_left hY145 hK1) j1x
  · exact as_term_le (by positivity) hD0 hcL (mul_nonneg hK0 hY0)
      (by rw [hLinv2, ← mul_left_comm, xp0_2, ← mul_assoc, ← hK0_eq]
          exact mul_le_mul_of_nonneg_left hY123 hK0) j0x
  · exact as_term_le (by positivity) hCo hLpos.le (mul_nonneg hCo hY0)
      (by rw [hLinv3, ← mul_left_comm, xpPsi]; exact mul_le_mul_of_nonneg_left hXY hCo) ox
  · exact as_term_le (by positivity) hCo hLpos.le (mul_nonneg hCo hY0)
      (by rw [hLinv3, ← mul_left_comm, xpPsi]; exact mul_le_mul_of_nonneg_left hXY hCo) ow
  · exact as_term_le (by positivity) hCo hLpos.le (mul_nonneg hCo hY0)
      (by rw [hLinv4, ← mul_left_comm, xpPsi4]; exact mul_le_mul_of_nonneg_left hY123 hCo) ox

/-- Pointwise bounds at `L = R√ν` on `‖fderiv (sepWX ...) y‖`, `‖fderiv (sepWY ...) y‖` (`0 < ϱ y`),
and `gradSize (sepWX ...) y + hessSize (sepWX ...) y` (all `y`), together with the age-surface bound
for `0 < s ≤ 1/ν`. -/
theorem sepAgeSurfBounds_of (hJet : SepJetPointwiseSup) (hOut : OutPrimPointwiseSup)
    (hDec : SepWXWYPointwiseDecomp) (σ₁ σ₂ : ℝ) (hσ : -(1 / 4 : ℝ) < σ₁)
    (χy : ℝ → ℝ) (hχ : IsStreamCutoff χy) :
    ∃ (C : ℝ), 0 ≤ C ∧
      ∀ (ν μ R P : ℝ), 0 < ν → ν ≤ 1 → 1 ≤ R → 0 < P → P ≤ 1 → μ ∈ Icc σ₁ σ₂ →
        ∀ T, IIIa.IsSepSource P (R * Real.sqrt (5 * ν / 6)) T → SepMoment P T → IsAxiSource T →
          (∀ (s : ℝ), 0 < s → ν * s ≤ 1 → ∀ (τ : ℝ) (y : Space), age R y = s →
            ENNReal.ofReal ‖fderiv ℝ (sepWX ν μ R χy T τ) y‖ ≤
                ENNReal.ofReal (C * ν⁻¹ * (R / Real.sqrt s) ^ (-(101 / 22 : ℝ))) *
                  IIIa.ltauLq P (22 / 19) (IIIa.srcNorm T) ∧
              ENNReal.ofReal ‖fderiv ℝ (sepWY ν μ R χy T τ) y‖ ≤
                ENNReal.ofReal (C * ν⁻¹ * (R / Real.sqrt s) ^ (-(101 / 22 : ℝ))) *
                  IIIa.ltauLq P (22 / 19) (IIIa.srcNorm T)) ∧
          (∀ (τ : ℝ) (y : Space),
            ENNReal.ofReal (gradSize (sepWX ν μ R χy T τ) y + hessSize (sepWX ν μ R χy T τ) y) ≤
              ENNReal.ofReal (C * ν⁻¹ * (R * Real.sqrt ν) ^ (-(101 / 22 : ℝ))) *
                IIIa.ltauLq P (22 / 19) (IIIa.srcNorm T)) := by
  obtain ⟨Cx, hCx, hPtX⟩ := wgxPointwise σ₁ σ₂ hσ χy hχ
  obtain ⟨Cy1, Cy2, hCy1, hCy2, hPtY⟩ := wgyPointwise σ₁ σ₂ hσ χy hχ
  obtain ⟨Cd, hCd, hPtD⟩ := hDec σ₁ σ₂ hσ χy hχ
  obtain ⟨D0, hD0, H0⟩ := hJet σ₁ σ₂ hσ 0 (by norm_num)
  obtain ⟨D1, hD1, H1⟩ := hJet σ₁ σ₂ hσ 1 (by norm_num)
  obtain ⟨D2, hD2, H2⟩ := hJet σ₁ σ₂ hσ 2 (by norm_num)
  obtain ⟨Co, hCo, Ho⟩ := hOut σ₁ σ₂ hσ
  obtain ⟨c0, hc0⟩ : ∃ x : ℝ, x = 1 - Real.sqrt (5 / 6) := ⟨_, rfl⟩
  have hs56 : Real.sqrt (5 / 6) < 1 := by rw [Real.sqrt_lt' one_pos]; norm_num
  have hc0pos : 0 < c0 := by rw [hc0]; linarith
  have hc0n : 0 ≤ c0 := hc0pos.le
  obtain ⟨K0, hK0_eq⟩ : ∃ x : ℝ, x = D0 * c0 ^ (-4 - ((0 : ℕ) : ℝ) + 9 / 22) := ⟨_, rfl⟩
  obtain ⟨K1, hK1_eq⟩ : ∃ x : ℝ, x = D1 * c0 ^ (-4 - ((1 : ℕ) : ℝ) + 9 / 22) := ⟨_, rfl⟩
  obtain ⟨K2, hK2_eq⟩ : ∃ x : ℝ, x = D2 * c0 ^ (-4 - ((2 : ℕ) : ℝ) + 9 / 22) := ⟨_, rfl⟩
  have hK0 : 0 ≤ K0 := by rw [hK0_eq]; exact mul_nonneg hD0 (Real.rpow_nonneg hc0n _)
  have hK1 : 0 ≤ K1 := by rw [hK1_eq]; exact mul_nonneg hD1 (Real.rpow_nonneg hc0n _)
  have hK2 : 0 ≤ K2 := by rw [hK2_eq]; exact mul_nonneg hD2 (Real.rpow_nonneg hc0n _)
  obtain ⟨MX, hMX_eq⟩ : ∃ x : ℝ, x = K1 + Cx * K0 + Cx * Co := ⟨_, rfl⟩
  obtain ⟨MY, hMY_eq⟩ :
      ∃ x : ℝ, x = K1 + Cy1 * K0 + Cy1 * Co + Cy2 * (K0 + K1 + K2 + K1 + Co) := ⟨_, rfl⟩
  obtain ⟨MGH, hMGH_eq⟩ : ∃ x : ℝ, x = Cd * (K2 + K1 + K1 + K0 + K0 + Co + Co) := ⟨_, rfl⟩
  have hMX0 : 0 ≤ MX := by
    rw [hMX_eq]; exact add_nonneg (add_nonneg hK1 (mul_nonneg hCx hK0)) (mul_nonneg hCx hCo)
  have hKsum5 : 0 ≤ K0 + K1 + K2 + K1 + Co :=
    add_nonneg (add_nonneg (add_nonneg (add_nonneg hK0 hK1) hK2) hK1) hCo
  have hKsum6 : 0 ≤ K2 + K1 + K1 + K0 + K0 + Co + Co :=
    add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg hK2 hK1) hK1) hK0) hK0) hCo) hCo
  have hMY0 : 0 ≤ MY := by
    rw [hMY_eq]
    exact add_nonneg (add_nonneg (add_nonneg hK1 (mul_nonneg hCy1 hK0)) (mul_nonneg hCy1 hCo))
      (mul_nonneg hCy2 hKsum5)
  have hMGH0 : 0 ≤ MGH := by rw [hMGH_eq]; exact mul_nonneg hCd hKsum6
  obtain ⟨A54, hA54_eq⟩ : ∃ x : ℝ, x = (Real.sqrt (5 / 4)) ^ (101 / 22 : ℝ) := ⟨_, rfl⟩
  have hA54 : 0 ≤ A54 := by rw [hA54_eq]; exact Real.rpow_nonneg (Real.sqrt_nonneg _) _
  obtain ⟨C, hC_eq⟩ : ∃ x : ℝ, x = (MX + MY) * A54 + K1 + MGH := ⟨_, rfl⟩
  have hC0 : 0 ≤ C := by
    rw [hC_eq]; exact add_nonneg (add_nonneg (mul_nonneg (add_nonneg hMX0 hMY0) hA54) hK1) hMGH0
  refine ⟨C, hC0, ?_⟩
  intro ν μ R P hν hν1 hR1 hP0 hP1 hμ T hT hSM hAx
  have hR : 0 < R := lt_of_lt_of_le zero_lt_one hR1
  obtain ⟨L, hL⟩ : ∃ x : ℝ, x = R * Real.sqrt ν := ⟨_, rfl⟩
  have hLpos : 0 < L := by rw [hL]; exact mul_pos hR (Real.sqrt_pos.2 hν)
  have hrO : R * Real.sqrt (5 * ν / 6) = Real.sqrt (5 / 6) * L := by
    rw [hL, show 5 * ν / 6 = 5 / 6 * ν by ring, Real.sqrt_mul (by norm_num)]; ring
  have hrOnn : 0 ≤ R * Real.sqrt (5 * ν / 6) := mul_nonneg hR.le (Real.sqrt_nonneg _)
  have hlt : R * Real.sqrt (5 * ν / 6) < L := by
    have hD : L - R * Real.sqrt (5 * ν / 6) = c0 * L := by rw [hrO, hc0]; ring
    exact sub_pos.1 (hD.symm ▸ mul_pos hc0pos hLpos)
  obtain ⟨F, hF⟩ : ∃ x : ℝ≥0∞, x = IIIa.ltauLq P (22 / 19) (IIIa.srcNorm T) := ⟨_, rfl⟩
  rw [← hF]
  obtain ⟨X, hX⟩ : ∃ x : ℝ, x = L ^ (-(101 / 22 : ℝ)) := ⟨_, rfl⟩
  obtain ⟨Y, hY⟩ : ∃ x : ℝ, x = ν⁻¹ * X := ⟨_, rfl⟩
  have hX0 : 0 ≤ X := by rw [hX]; exact Real.rpow_nonneg hLpos.le _
  have hν1' : 1 ≤ ν⁻¹ := (one_le_inv₀ hν).2 hν1
  have hY0 : 0 ≤ Y := by rw [hY]; exact mul_nonneg (inv_nonneg.2 hν.le) hX0
  have hLinv : L ^ (-1 : ℝ) = L⁻¹ := Real.rpow_neg_one L
  have hLinv3 : L ^ (-3 : ℝ) = L⁻¹ ^ 3 := by rw [Real.rpow_neg hLpos.le, inv_pow]; norm_cast
  have bJ (τ : ℝ) (y : Space) :
      wgxJet 1 ν μ L T τ y ≤ ENNReal.ofReal (K1 * Y) * F ∧
      wgyWJet 1 ν μ L T τ y ≤ ENNReal.ofReal (K1 * Y) * F ∧
      ENNReal.ofReal L⁻¹ * wgxJet 0 ν μ L T τ y ≤ ENNReal.ofReal (K0 * Y) * F ∧
      ENNReal.ofReal L⁻¹ * wgyWJet 0 ν μ L T τ y ≤ ENNReal.ofReal (K0 * Y) * F ∧
      wgxJet 2 ν μ L T τ y ≤ ENNReal.ofReal (K2 * Y) * F ∧
      ENNReal.ofReal L⁻¹ * wgxJet 2 ν μ L T τ y ≤ ENNReal.ofReal (K2 * Y) * F ∧
      ENNReal.ofReal L⁻¹ * wgxJet 1 ν μ L T τ y ≤ ENNReal.ofReal (K1 * Y) * F ∧
      ENNReal.ofReal (L⁻¹ ^ 2) * wgxJet 1 ν μ L T τ y ≤ ENNReal.ofReal (K1 * Y) * F ∧
      ENNReal.ofReal (L⁻¹ ^ 2) * wgxJet 0 ν μ L T τ y ≤ ENNReal.ofReal (K0 * Y) * F ∧
      ENNReal.ofReal (L⁻¹ ^ 3) * wgxPsi ν μ R T τ y ≤ ENNReal.ofReal (Co * Y) * F ∧
      ENNReal.ofReal (L⁻¹ ^ 3) * wgyWPsi ν μ R T τ y ≤ ENNReal.ofReal (Co * Y) * F ∧
      ENNReal.ofReal (L⁻¹ ^ 4) * wgxPsi ν μ R T τ y ≤ ENNReal.ofReal (Co * Y) * F := by
    have j0 := H0 ν μ _ L P hν hμ hrOnn hlt hP0 hP1 T hT hSM τ y
    have j1 := H1 ν μ _ L P hν hμ hrOnn hlt hP0 hP1 T hT hSM τ y
    have j2 := H2 ν μ _ L P hν hμ hrOnn hlt hP0 hP1 T hT hSM τ y
    have ho := Ho ν μ R P hν hR hP0 hP1 hμ T hT hSM τ y
    rw [← hF] at j0 j1 j2 ho
    rw [← hL] at ho
    exact as_bJ_at_L hν hν1 hR1 hD0 hD1 hD2 hCo hc0 hK0_eq hK1_eq hK2_eq hL (by rw [hY, hX])
      j0.1 (j0.2 (by norm_num)) j1.1 (j1.2 (by norm_num)) j2.1 ho.1 ho.2
  refine ⟨fun s hs hνs τ y hy => ?_, fun τ y => ?_⟩
  · -- Clause 1: age surface `age R y = s`
    have hρeq : ϱ y = R / Real.sqrt s := as_varrho_of_age hR hs hy
    have hL_le : L ≤ R / Real.sqrt s := by rw [hL]; exact as_L_le_surf hν hR hs hνs
    have hy0 : 0 < ϱ y := by rw [hρeq]; exact div_pos hR (Real.sqrt_pos.2 hs)
    obtain ⟨Xs, hXs⟩ : ∃ x : ℝ, x = (R / Real.sqrt s) ^ (-(101 / 22 : ℝ)) := ⟨_, rfl⟩
    have hXs0 : 0 ≤ Xs := by rw [hXs]; exact Real.rpow_nonneg (div_pos hR (Real.sqrt_pos.2 hs)).le _
    obtain ⟨Ys, hYs⟩ : ∃ x : ℝ, x = ν⁻¹ * Xs := ⟨_, rfl⟩
    have hYs0 : 0 ≤ Ys := by rw [hYs]; exact mul_nonneg (inv_nonneg.2 hν.le) hXs0
    by_cases hann : ϱ y ≤ R * Real.sqrt (5 * ν / 4)
    · -- Inside transition annulus: `X ≤ A54 * Xs`, so `Y ≤ A54 * Ys`
      have hX_le : X ≤ A54 * Xs := by
        rw [hX, hL, hA54_eq, hXs]
        exact as_ann_rpow_le hν hR hs (by rwa [← hρeq])
      have hY_le : Y ≤ A54 * Ys := by
        rw [hY, hYs]
        calc ν⁻¹ * X ≤ ν⁻¹ * (A54 * Xs) := mul_le_mul_of_nonneg_left hX_le (inv_nonneg.2 hν.le)
          _ = A54 * (ν⁻¹ * Xs) := mul_left_comm _ _ _
      obtain ⟨b1x, b1w, b0x, b0w, b2x, b2x1, b1x1, b1x2, b0x2, bPx, bPw, -⟩ := bJ τ y
      have pX := hPtX ν μ R P hν hν1 hR1 hP0 hP1 hμ T hT hSM hAx τ y hy0
      have pY := hPtY ν μ R P hν hν1 hR1 hP0 hP1 hμ T hT hSM hAx τ y hy0
      rw [← hL] at pX pY
      have eCx1 := as_scale_term hCx hLinv b0x
      have eCx3 := as_scale_term hCx hLinv3 bPx
      have eCy1 := as_scale_term hCy1 hLinv b0w
      have eCy3 := as_scale_term hCy1 hLinv3 bPw
      have hX_tot : ENNReal.ofReal ‖fderiv ℝ (sepWX ν μ R χy T τ) y‖ ≤
          ENNReal.ofReal (C * Ys) * F := by
        calc ENNReal.ofReal ‖fderiv ℝ (sepWX ν μ R χy T τ) y‖
            ≤ ENNReal.ofReal (K1 * Y) * F + ENNReal.ofReal (Cx * (K0 * Y)) * F +
                ENNReal.ofReal (Cx * (Co * Y)) * F :=
              pX.trans (add_le_add (add_le_add b1x eCx1) eCx3)
          _ = ENNReal.ofReal (MX * Y) * F := by
              rw [hMX_eq]
              exact as_sumX K1 Cx K0 Co Y F hK1 hCx hK0 hCo hY0
          _ ≤ ENNReal.ofReal (C * Ys) * F := by
              rw [hC_eq]
              exact as_ofReal_mul_le (as_MX_le hMX0 hMY0 hA54 hK1 hMGH0 hYs0 hY_le)
      have hY_tot : ENNReal.ofReal ‖fderiv ℝ (sepWY ν μ R χy T τ) y‖ ≤
          ENNReal.ofReal (C * Ys) * F := by
        have bComm : ENNReal.ofReal L⁻¹ * wgxJet 0 ν μ L T τ y + wgxJet 1 ν μ L T τ y +
            ENNReal.ofReal L⁻¹ * wgxJet 2 ν μ L T τ y +
            ENNReal.ofReal (L⁻¹ ^ 2) * wgxJet 1 ν μ L T τ y +
            ENNReal.ofReal (L⁻¹ ^ 3) * wgxPsi ν μ R T τ y ≤
            ENNReal.ofReal ((K0 + K1 + K2 + K1 + Co) * Y) * F :=
          (add_le_add (add_le_add (add_le_add (add_le_add b0x b1x) b2x1) b1x2) bPx).trans
            (as_sum5 K0 K1 K2 Co Y F hK0 hK1 hK2 hCo hY0).le
        calc ENNReal.ofReal ‖fderiv ℝ (sepWY ν μ R χy T τ) y‖
            ≤ (ENNReal.ofReal (K1 * Y) * F + ENNReal.ofReal (Cy1 * (K0 * Y)) * F +
                ENNReal.ofReal (Cy1 * (Co * Y)) * F) +
              ENNReal.ofReal Cy2 * (ENNReal.ofReal ((K0 + K1 + K2 + K1 + Co) * Y) * F) :=
              pY.trans (add_le_add (add_le_add (add_le_add b1w eCy1) eCy3)
                (mul_le_mul_of_nonneg_left bComm zero_le))
          _ = ENNReal.ofReal (MY * Y) * F := by
              rw [hMY_eq]
              exact as_sumY K1 Cy1 K0 Co Cy2 (K0 + K1 + K2 + K1 + Co) Y F hK1 hCy1 hK0 hCo hCy2
                hKsum5 hY0
          _ ≤ ENNReal.ofReal (C * Ys) * F := by
              rw [hC_eq]
              exact as_ofReal_mul_le (as_MY_le hMX0 hMY0 hA54 hK1 hMGH0 hYs0 hY_le)
      have heqY : C * ν⁻¹ * (R / Real.sqrt s) ^ (-(101 / 22 : ℝ)) = C * Ys := by
        rw [hYs, hXs, mul_assoc]
      rw [heqY]
      exact ⟨hX_tot, hY_tot⟩
    · -- Beyond transition annulus: `R * √(5ν/4) < ϱ y`
      have hgt : R * Real.sqrt (5 * ν / 4) < ϱ y := not_le.1 hann
      obtain ⟨pXY_gt, -⟩ := hPtD ν μ R P hν hν1 hR1 hP0 hP1 hμ T hT hSM hAx τ y
      obtain ⟨pX_gt, pY_gt⟩ := pXY_gt hgt
      have hlt_s : R * Real.sqrt (5 * ν / 6) < ϱ y := by
        rw [hρeq]; exact lt_of_lt_of_le hlt hL_le
      obtain ⟨j1x_s, j1w_s⟩ := H1 ν μ _ (ϱ y) P hν hμ hrOnn hlt_s hP0 hP1 T hT hSM τ y
      have j1w_s' := j1w_s (by norm_num)
      rw [← hF] at j1x_s j1w_s'
      have hgap : c0 * (R / Real.sqrt s) ≤ ϱ y - R * Real.sqrt (5 * ν / 6) := by
        rw [hρeq, hrO]; exact as_gap_le hc0 hL_le
      have hgap_pos : 0 < c0 * (R / Real.sqrt s) :=
        mul_pos hc0pos (div_pos hR (Real.sqrt_pos.2 hs))
      have hD1_le : D1 * (ϱ y - R * Real.sqrt (5 * ν / 6)) ^ (-4 - ((1 : ℕ) : ℝ) + 9 / 22) ≤
          C * Ys := by
        have h1 : D1 * (ϱ y - R * Real.sqrt (5 * ν / 6)) ^ (-4 - ((1 : ℕ) : ℝ) + 9 / 22) ≤
            K1 * Xs := by
          have := Real.rpow_le_rpow_of_nonpos hgap_pos hgap
            (show (-4 - ((1 : ℕ) : ℝ) + 9 / 22) ≤ 0 by norm_num)
          rw [Real.mul_rpow hc0n (div_pos hR (Real.sqrt_pos.2 hs)).le] at this
          have hm := mul_le_mul_of_nonneg_left this hD1
          have hp1_eq : (R / Real.sqrt s) ^ (-4 - ((1 : ℕ) : ℝ) + 9 / 22) = Xs := by
            rw [hXs]; congr 1; norm_num
          rw [hp1_eq, ← mul_assoc, ← hK1_eq] at hm
          exact hm
        have h2 : K1 * Xs ≤ K1 * Ys := by
          rw [hYs]
          calc K1 * Xs = K1 * (1 * Xs) := by rw [one_mul]
            _ ≤ K1 * (ν⁻¹ * Xs) :=
                mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hν1' hXs0) hK1
        have h3 : K1 * Ys ≤ C * Ys := by
          rw [hC_eq]; exact as_K1_le hMX0 hMY0 hA54 hMGH0 hYs0
        exact h1.trans (h2.trans h3)
      have heqY : C * ν⁻¹ * (R / Real.sqrt s) ^ (-(101 / 22 : ℝ)) = C * Ys := by
        rw [hYs, hXs, mul_assoc]
      rw [heqY]
      exact ⟨pX_gt.trans (j1x_s.trans (as_ofReal_mul_le hD1_le)),
        pY_gt.trans (j1w_s'.trans (as_ofReal_mul_le hD1_le))⟩
  · -- Clause 2: global `(τ, y)` bound on `gradSize + hessSize`
    obtain ⟨-, pGH⟩ := hPtD ν μ R P hν hν1 hR1 hP0 hP1 hμ T hT hSM hAx τ y
    rw [← hL] at pGH ⊢
    obtain ⟨b1x, -, b0x, -, b2x, -, b1x1, -, b0x2, bPx, -, bPx4⟩ := bJ τ y
    have bIn : wgxJet 2 ν μ L T τ y + wgxJet 1 ν μ L T τ y +
        ENNReal.ofReal L⁻¹ * wgxJet 1 ν μ L T τ y +
        ENNReal.ofReal L⁻¹ * wgxJet 0 ν μ L T τ y +
        ENNReal.ofReal (L⁻¹ ^ 2) * wgxJet 0 ν μ L T τ y +
        ENNReal.ofReal (L⁻¹ ^ 3) * wgxPsi ν μ R T τ y +
        ENNReal.ofReal (L⁻¹ ^ 4) * wgxPsi ν μ R T τ y ≤
        ENNReal.ofReal ((K2 + K1 + K1 + K0 + K0 + Co + Co) * Y) * F :=
      (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add b2x b1x) b1x1) b0x) b0x2) bPx) bPx4).trans
        (as_sum6 K2 K1 K0 Co Y F hK2 hK1 hK0 hCo hY0).le
    calc ENNReal.ofReal (gradSize (sepWX ν μ R χy T τ) y + hessSize (sepWX ν μ R χy T τ) y)
        ≤ ENNReal.ofReal Cd * (ENNReal.ofReal ((K2 + K1 + K1 + K0 + K0 + Co + Co) * Y) * F) :=
          pGH.trans (mul_le_mul_of_nonneg_left bIn zero_le)
      _ = ENNReal.ofReal (MGH * Y) * F := by
          have e : MGH * Y = Cd * ((K2 + K1 + K1 + K0 + K0 + Co + Co) * Y) := by
            rw [hMGH_eq, mul_assoc]
          rw [e, ENNReal.ofReal_mul hCd, mul_assoc]
      _ ≤ ENNReal.ofReal (C * ν⁻¹ * L ^ (-(101 / 22 : ℝ))) * F := by
          have e : C * ν⁻¹ * L ^ (-(101 / 22 : ℝ)) = C * Y := by
            rw [hY, hX, mul_assoc]
          rw [e, hC_eq]
          exact as_ofReal_mul_le (as_MGH_le hMX0 hMY0 hA54 hK1 hY0)

/-- `RepAgeSurfAt` at one regime from the separated bounds and `RepairSepBridge`. -/
theorem repAgeSurfAt_of (hB : RepairSepBridge) (Pl : PlanarData) (K : ReturnConsts)
    (L : ReturnLevel) (μ : ℝ) {σ₁ σ₂ C : ℝ} (hC : 0 ≤ C)
    (hSb : ∀ (ν μ R P : ℝ), 0 < ν → ν ≤ 1 → 1 ≤ R → 0 < P → P ≤ 1 → μ ∈ Icc σ₁ σ₂ →
      ∀ T, IIIa.IsSepSource P (R * Real.sqrt (5 * ν / 6)) T → SepMoment P T → IsAxiSource T →
        (∀ (s : ℝ), 0 < s → ν * s ≤ 1 → ∀ (τ : ℝ) (y : Space), age R y = s →
          ENNReal.ofReal ‖fderiv ℝ (sepWX ν μ R K.χy T τ) y‖ ≤
              ENNReal.ofReal (C * ν⁻¹ * (R / Real.sqrt s) ^ (-(101 / 22 : ℝ))) *
                IIIa.ltauLq P (22 / 19) (IIIa.srcNorm T) ∧
            ENNReal.ofReal ‖fderiv ℝ (sepWY ν μ R K.χy T τ) y‖ ≤
              ENNReal.ofReal (C * ν⁻¹ * (R / Real.sqrt s) ^ (-(101 / 22 : ℝ))) *
                IIIa.ltauLq P (22 / 19) (IIIa.srcNorm T)) ∧
        (∀ (τ : ℝ) (y : Space),
          ENNReal.ofReal (gradSize (sepWX ν μ R K.χy T τ) y + hessSize (sepWX ν μ R K.χy T τ) y) ≤
            ENNReal.ofReal (C * ν⁻¹ * (R * Real.sqrt ν) ^ (-(101 / 22 : ℝ))) *
              IIIa.ltauLq P (22 / 19) (IIIa.srcNorm T)))
    (hμ : μ ∈ Icc σ₁ σ₂) (hν1 : L.ν ≤ 1) (hε1 : L.ε ≤ 1) (hP : 2 * L.ε * cOf L.ν ≤ 1)
    (_hC0 : 0 < K.C0) (hmZ : 0 ≤ K.mZ) :
    RepAgeSurfAt Pl K L μ (2 * C) 4 := by
  intro w
  have hν := L.ν_pos
  have hε := L.ε_pos
  have hc := cOf_pos hν
  have hρ : 0 < L.ρb Pl K := by
    unfold ReturnLevel.ρb UnforcedLeray.Short.IIb.rhoB
    have h1 := (L.params Pl).ν_pos
    have h2 := (L.params Pl).ε_pos
    positivity
  obtain ⟨T, hS, hM, hA, hW, hN⟩ := hB (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν L.ε K.χo K.hχo
    hc hρ hmZ hν hε (multOp Pl K L w)
  have hX0 : wardX0 L.ν μ L.ε⁻¹ (cOf L.ν) (repSrcTen Pl K L w) = sepX0 L.ν μ T := by
    rw [wardX0_eq_sepX0]; exact sepX0_congr hW
  have hX : repX Pl K L μ w = sepWX L.ν μ L.ε⁻¹ K.χy T := by
    show wardStreamCut L.ν L.ε⁻¹ K.χy (wardX0 L.ν μ L.ε⁻¹ (cOf L.ν) (repSrcTen Pl K L w)) = _
    rw [hX0]; rfl
  have hY : repY Pl K L μ w = sepWY L.ν μ L.ε⁻¹ K.χy T := by
    show physDmu L.ν (μ + 1) (repX Pl K L μ w) = _
    rw [hX]; rfl
  have hR1 : 1 ≤ L.ε⁻¹ := (one_le_inv₀ hε).2 hε1
  have hP0 : 0 < 2 * L.ε * cOf L.ν := by positivity
  obtain ⟨hSurf, hGlob⟩ := hSb L.ν μ L.ε⁻¹ _ hν hν1 hR1 hP0 hP hμ T hS hM hA
  set F := IIIa.ltauLq (2 * L.ε * cOf L.ν) (22 / 19) (IIIa.srcNorm T)
  have hν' : 1 ≤ L.ν⁻¹ := (one_le_inv₀ hν).2 hν1
  have hp14 : L.ν⁻¹ ≤ L.ν⁻¹ ^ 4 := by
    have := pow_le_pow_right₀ hν' (show 1 ≤ 4 by norm_num)
    rwa [pow_one] at this
  refine ⟨fun s hs hνs => ?_, fun τ y => ?_⟩
  · rw [hX, hY]
    set Bs : ℝ≥0∞ :=
      ENNReal.ofReal (C * L.ν⁻¹ * (L.ε⁻¹ / Real.sqrt s) ^ (-(101 / 22 : ℝ))) * F
    have bX : ageSurfL2 (2 * L.ε * cOf L.ν) L.ε⁻¹ s
        (fun τ y => ‖fderiv ℝ (sepWX L.ν μ L.ε⁻¹ K.χy T τ) y‖) ≤ Bs :=
      ageSurfL2_le_of_pointwise hP0 _ Bs (fun τ y hy => (hSurf s hs hνs τ y hy).1)
    have bY : ageSurfL2 (2 * L.ε * cOf L.ν) L.ε⁻¹ s
        (fun τ y => ‖fderiv ℝ (sepWY L.ν μ L.ε⁻¹ K.χy T τ) y‖) ≤ Bs :=
      ageSurfL2_le_of_pointwise hP0 _ Bs (fun τ y hy => (hSurf s hs hνs τ y hy).2)
    have hsc : 2 * (C * L.ν⁻¹ * (L.ε⁻¹ / Real.sqrt s) ^ (-(101 / 22 : ℝ))) ≤
        2 * C * L.ν⁻¹ ^ 4 * L.ε ^ (101 / 22 : ℝ) * s ^ (101 / 44 : ℝ) := by
      rw [as_scale_surf hε hs]
      have h1 : C * L.ν⁻¹ ≤ C * L.ν⁻¹ ^ 4 := mul_le_mul_of_nonneg_left hp14 hC
      have h2 : 0 ≤ L.ε ^ (101 / 22 : ℝ) * s ^ (101 / 44 : ℝ) := by positivity
      nlinarith [mul_le_mul_of_nonneg_right h1 h2]
    calc ageSurfL2 (2 * L.ε * cOf L.ν) L.ε⁻¹ s
            (fun τ y => ‖fderiv ℝ (sepWX L.ν μ L.ε⁻¹ K.χy T τ) y‖) +
          ageSurfL2 (2 * L.ε * cOf L.ν) L.ε⁻¹ s
            (fun τ y => ‖fderiv ℝ (sepWY L.ν μ L.ε⁻¹ K.χy T τ) y‖)
        ≤ Bs + Bs := add_le_add bX bY
      _ = ENNReal.ofReal (2 * (C * L.ν⁻¹ * (L.ε⁻¹ / Real.sqrt s) ^ (-(101 / 22 : ℝ)))) * F := by
          unfold Bs
          have hnn : 0 ≤ C * L.ν⁻¹ * (L.ε⁻¹ / Real.sqrt s) ^ (-(101 / 22 : ℝ)) := by positivity
          rw [← add_mul, ← ENNReal.ofReal_add hnn hnn, ← two_mul]
      _ ≤ ENNReal.ofReal (2 * C * L.ν⁻¹ ^ 4 * L.ε ^ (101 / 22 : ℝ) * s ^ (101 / 44 : ℝ)) *
            phaseL2Lr (2 * L.ε * cOf L.ν) (22 / 19) (repStressPhys Pl K L w) :=
          mul_le_mul' (ENNReal.ofReal_le_ofReal hsc) hN
  · rw [hX]
    change ENNReal.ofReal (gradSize (sepWX L.ν μ L.ε⁻¹ K.χy T τ) y +
        hessSize (sepWX L.ν μ L.ε⁻¹ K.χy T τ) y) ≤ _
    refine (hGlob τ y).trans ?_
    have hsc : C * L.ν⁻¹ * (L.ε⁻¹ * Real.sqrt L.ν) ^ (-(101 / 22 : ℝ)) ≤
        2 * C * L.ν⁻¹ ^ 4 * L.ε ^ (101 / 22 : ℝ) := by
      have h := as_scale_global hν hν1 hε
      have h1 : C * L.ν⁻¹ * (L.ε⁻¹ * Real.sqrt L.ν) ^ (-(101 / 22 : ℝ)) ≤
          C * L.ν⁻¹ * (L.ν⁻¹ ^ 3 * L.ε ^ (101 / 22 : ℝ)) :=
        mul_le_mul_of_nonneg_left h (by positivity)
      have h2 : C * L.ν⁻¹ * (L.ν⁻¹ ^ 3 * L.ε ^ (101 / 22 : ℝ)) =
          C * L.ν⁻¹ ^ 4 * L.ε ^ (101 / 22 : ℝ) := by ring
      have h3 : 0 ≤ C * L.ν⁻¹ ^ 4 * L.ε ^ (101 / 22 : ℝ) := by positivity
      linarith
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal hsc) hN

/-- **`RepAgeSurf` along the concrete sequence from the three leaves**
(source 5203-5210, 5236-5244). -/
theorem repAgeSurf_of (hJet : SepJetPointwiseSup) (hOut : OutPrimPointwiseSup)
    (hDec : SepWXWYPointwiseDecomp) (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp) :
    RepAgeSurf D := by
  have hσ : -(1 / 4 : ℝ) < D.σ₀ / 2 := by linarith [hst.sigma_pos]
  obtain ⟨C, hC, hSb⟩ := sepAgeSurfBounds_of hJet hOut hDec (D.σ₀ / 2) ((D.σ₀ + 1 / 4) / 2) hσ
    D.K.χy hst.chiY
  refine ⟨2 * C, 4, ?_⟩
  have hev1 := mu_eventually_mem D hst.omega_ne hst.sigma_pos hst.sigma_lt
  have hev2 := retNu_retEps_eventually_le_one hst.omega_ne hst.gamma_pos D.coeff_ne
  have hev3 : ∀ᶠ n : ℕ in atTop, retNu D.Pl D.σ₀ n ≤ dm ^ 3 / 12 :=
    (retNu_tendsto D.σ₀ hst.omega_ne).eventually_le_const (by have := hst.dm_pos; positivity)
  filter_upwards [hev1, hev2, hev3, hst.actual] with n h1 h2 h3 h4 z hz
  have hP : 2 * (D.level n).ε * cOf (D.level n).ν ≤ 1 :=
    UnforcedLeray.Short.IIIa.period_le_one_of_small h4.regime h3
  exact repAgeSurfAt_of repairSepBridge D.Pl D.K (D.level n) (D.mu n z) hC hSb (h1 z hz)
    h2.1 h2.2 hP hst.C0_pos (by linarith [hst.mZ_gt])

end UnforcedLeray.Short.PartIIIb.Concrete

end
