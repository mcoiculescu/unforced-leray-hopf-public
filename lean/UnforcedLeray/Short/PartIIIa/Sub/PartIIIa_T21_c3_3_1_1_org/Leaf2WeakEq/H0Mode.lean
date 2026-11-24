import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_3_1_1_org.Leaf2WeakEq.Needed
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_3_1_1_org.Leaf2WeakEq.FramePairing1.PhysCol
import UnforcedLeray.Short.PartIIIa.Clock.FrameAmplitudeProof.DirectError.HeatError.HeatDecomp
import UnforcedLeray.Short.PartIIIa.Clock.FrameAmplitudeProof.DirectError.HeatError.OscGramApprox
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c5_3_2
import UnforcedLeray.Short.PartIIIa.Clock.FrameAmplitudeProof.DirectError.EulerSubBound.Pullback
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2.E0.Train
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2.E0.DivZero
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_3_6_1_1_3.AdjFubini0

/-!
# Leaf (`PartIII-a:T21/c3/3/1/1/2/2/3/d`): `H0ModeIdentity` (`M₀ = H₀ E = Λ K₀`, SP 2905–2918)

Source of record: `the November 2 reference manuscript` (SP), lines 2863–2865,
2891–2897, and 2905–2918.

## Missing-hypothesis diagnosis on `Leaf2WeakEqNeeded.H0ModeIdentity` (`Leaf2WeakEq/Needed.lean:57`)

`Leaf2WeakEqNeeded.H0ModeIdentity κ P ν b tr` quantifies over completely arbitrary
`κ : PlanarFrameKernels`, `ν b : ℝ`, and `tr : B0140.TrainSol ν (ν ^ (-2 : ℝ))` with zero
regularity, positivity, Gram-invertibility, or cylinder-decay hypotheses. As stated without
hypotheses, it is strictly false:
1. **Missing `IsSeedKernels κ`**: `PlanarFrameKernels` only assumes continuity of `κ.e` and
   `κ.lamP`. For smooth `κ.lamP` and piecewise-affine tent `κ.e` supported on `[-1/4, 1/4]²` with
   `∫ lamP_i * e_j = δ_{ij}`, `ladLapCx (perE κ d 0) = 0` everywhere (`fderiv = 0` at corners),
   whereas `movH0` integrates `ν * ladLapCx (physFrameLam) * e_0 ≠ 0`.
2. **Missing `0 < ν`**: for `ν ≤ 0` (e.g. `ν = -1, r = 1, b = -10`), `clockA ν r = 0` and
   `dd ν r = 0`.
3. **Missing `PerFrameFacts κ ν m b K` (or `IsUnit (perGram κ (dd ν r))`)**: at an isolated zero of
   `r' ↦ (perGram κ (dd ν r')).det`, `(perGram κ (dd ν r))⁻¹ = 0` (`Ring.inverse 0 = 0`), making
   `perLam = 0` on the RHS while the right-hand time derivative `ladDt` of `physFrameLam` is
   nonzero.
4. **Missing `LadTrainBdd`**: `B0140.IsTrain` imposes no vertical growth bound on `tr.v` or `∇Ec`
   on `B0579.cell (ν ^ (-2 : ℝ))`, which is needed for integrability, transport IBP, and Biot–Savart
   Fubini (already noted in `Leaf2WeakEq/Needed.lean:18-19` and included on `LinFreeAdjPairing`,
   but accidentally omitted from `H0ModeIdentity`).

Every one of these hypotheses (`IsSeedKernels κ`, `8 < m`, `0 < ν`, `PerFrameFacts κ ν m b K`, and
`∀ S : ℝ, 0 ≤ S → ∃ C : ℝ, LadTrainBdd tr m S C`) is already in scope in the sole consumer
`ComplWeakEq` (`DuhamelSplit.lean:109-115`). Below we prove the complete identity in full
from those exact hypotheses (`h0ModeIdentity_of`, and pointwise-in-`r` version
`h0ModeIdentity_of_isUnit`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff Matrix

namespace UnforcedLeray.Short.IIIa

open FrameShortBlockSub ComplCouplingSub PerturbDuhamelSub
open ComplFreeRateSub.Leaf2WeakEqFrame

namespace ComplFreeRateSub

namespace Leaf2WeakEqNeeded

/-! ## 1. Periodized seed regularity, vertical Gaussian decay, and Gram-inverse orthogonality -/

/-- For any `d > 0` and `LamJetInf.Good L`, `perSum d L` is `C^∞` on `ℝ × ℝ`. -/
private lemma contDiff_perSum_of_good {d : ℝ} (hd : 0 < d) {L : ℝ × ℝ → ℂ}
    (hL : LamJetInf.Good L) : ContDiff ℝ ∞ (perSum d L) := by
  have ha0 : (0 : ℝ) < clockA 1 0 := by unfold clockA; norm_num
  have hP : ContDiffOn ℝ ∞ (LamJetInf.perPhys 1 d L) (LamJetInf.physU 1) :=
    LamJetInf.contDiffOn_perPhys zero_lt_one hd.ne' hL
  have heq : perSum d L = fun y : ℝ × ℝ => LamJetInf.perPhys 1 d L (0, y) := by
    funext y
    unfold LamJetInf.perPhys physAdj clockA
    simp
  rw [heq]
  exact hP.comp_contDiff (contDiff_const.prodMk contDiff_id) fun _ => ha0

/-- Termwise first partial derivative `pdCx k (perSum d L) = perSum d (pdCx k L)` for `d > 0` and
`LamJetInf.Good L`. -/
private lemma pdCx_perSum_of_good {d : ℝ} (hd : 0 < d) {L : ℝ × ℝ → ℂ}
    (hL : LamJetInf.Good L) (k : Fin 2) (y : ℝ × ℝ) :
    pdCx k (perSum d L) y = perSum d (pdCx k L) y := by
  have ha0 : (0 : ℝ) < clockA 1 0 := by unfold clockA; norm_num
  have hF := (LamJetInf.hasFDerivAt_perPhys zero_lt_one hd.ne' hL (p₀ := (0, y)) ha0).1
  have hcomp := hF.comp y ((hasFDerivAt_const (0 : ℝ) y).prodMk (hasFDerivAt_id y))
  have heq : perSum d L = fun z : ℝ × ℝ => LamJetInf.perPhys 1 d L (0, z) := by
    funext z
    unfold LamJetInf.perPhys physAdj clockA
    simp
  rw [heq]
  unfold pdCx
  change fderiv ℝ (LamJetInf.perPhys 1 d L ∘ Prod.mk (0 : ℝ)) y (B0579.dir k) = _
  rw [hcomp.fderiv, ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    zero_apply, ContinuousLinearMap.id_apply, ← hF.fderiv]
  have happ := LamJetInf.fderiv_perPhys_apply zero_lt_one hd.ne' hL (p := (0, y)) ha0
    (0, B0579.dir k)
  have hca : clockA 1 0 = 1 := by unfold clockA; ring
  have hpa1 : ∀ f : ℝ × ℝ → ℂ, physAdj 1 f = f := fun f => funext fun z => by
    unfold physAdj; simp
  simpa [LamJetInf.perPhys, hpa1, hca, pdCx] using happ

/-- Every horizontal coordinate shifts by an integer multiple of `d > 0` into `[-d/2, d/2)`. -/
private lemma exists_int_shift_mem_cell {d : ℝ} (hd : 0 < d) (y : ℝ × ℝ) :
    ∃ m : ℤ, (y.1 + (m : ℝ) * d, y.2) ∈ B0579.cell d := by
  set n₀ : ℤ := ⌊y.1 / d + 1 / 2⌋
  refine ⟨-n₀, ?_⟩
  simp only [B0579.cell, mem_prod, mem_Ico, mem_univ, and_true, Int.cast_neg]
  have h1 : (n₀ : ℝ) ≤ y.1 / d + 1 / 2 := Int.floor_le _
  have h2 : y.1 / d + 1 / 2 < (n₀ : ℝ) + 1 := Int.lt_floor_add_one _
  have hm1 := mul_le_mul_of_nonneg_right h1 hd.le
  have hm2 := mul_lt_mul_of_pos_right h2 hd
  have hdiv : (y.1 / d + 1 / 2) * d = y.1 + d / 2 := by field_simp [hd.ne']
  rw [hdiv] at hm1 hm2
  constructor <;> linarith

/-- Global supremum bound on `perSum d L` for any `d > 0` when `‖L z‖ ≤ C * (1 + |z.1|) ^ (-2)`. -/
private lemma perSum_sup_of_inv_sq {d C : ℝ} (hd : 0 < d) (hC0 : 0 ≤ C) {L : ℝ × ℝ → ℂ}
    (hL : ∀ z : ℝ × ℝ, ‖L z‖ ≤ C * (1 + |z.1|) ^ (-(2 : ℝ))) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ y : ℝ × ℝ, ‖perSum d L y‖ ≤ B := by
  set s : ℝ := min d 1
  have hs_pos : 0 < s := lt_min hd zero_lt_one
  have hs_le_d : s ≤ d := min_le_left d 1
  have hs_le_one : s ≤ 1 := min_le_right d 1
  have hsum0 : Summable (fun n : ℤ => (1 + |(n : ℝ)|) ^ (-(2 : ℝ))) :=
    Gaussian.summable_one_add_abs_int_rpow (by norm_num)
  set K : ℝ := 4 * C / s ^ 2
  have hK0 : 0 ≤ K := by positivity
  have hhasSum : HasSum (fun n : ℤ => K * (1 + |(n : ℝ)|) ^ (-(2 : ℝ)))
      (K * ∑' n : ℤ, (1 + |(n : ℝ)|) ^ (-(2 : ℝ))) := hsum0.hasSum.mul_left K
  have hS_nn : 0 ≤ ∑' n : ℤ, (1 + |(n : ℝ)|) ^ (-(2 : ℝ)) :=
    tsum_nonneg fun _ => by positivity
  have hcell : ∀ w ∈ B0579.cell d,
      ‖perSum d L w‖ ≤ K * ∑' n : ℤ, (1 + |(n : ℝ)|) ^ (-(2 : ℝ)) := by
    intro w hw
    have hw1 : |w.1| ≤ d / 2 := by
      rw [abs_le]; constructor <;> linarith [hw.1.1, hw.1.2]
    unfold perSum
    refine tsum_of_norm_bounded hhasSum fun n => ?_
    refine (hL _).trans ?_
    have hlow : s * (1 + |(n : ℝ)|) / 2 ≤ 1 + |w.1 + n * d| := by
      by_cases hn : n = 0
      · subst hn; simp; linarith [abs_nonneg w.1]
      · have hn1 : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs hn
        have htri : |(n : ℝ) * d| ≤ |w.1 + n * d| + |w.1| := by
          calc |(n : ℝ) * d| = |(w.1 + n * d) - w.1| := by congr 1; ring
            _ ≤ |w.1 + n * d| + |w.1| := abs_sub _ _
        rw [abs_mul, abs_of_pos hd] at htri
        have hnd : s * |(n : ℝ)| ≤ |(n : ℝ)| * d := by
          nlinarith [mul_le_mul_of_nonneg_left hs_le_d (abs_nonneg (n : ℝ))]
        have hnd2 : |(n : ℝ)| * d / 2 ≤ |w.1 + n * d| := by
          nlinarith [mul_le_mul_of_nonneg_right hn1 hd.le]
        linarith [abs_nonneg (w.1 + n * d)]
    have hpos : 0 < s * (1 + |(n : ℝ)|) / 2 := by positivity
    have h5 : (1 + |w.1 + n * d|) ^ (-(2 : ℝ)) ≤ (s * (1 + |(n : ℝ)|) / 2) ^ (-(2 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hpos hlow (by norm_num)
    have h6 : (s * (1 + |(n : ℝ)|) / 2) ^ (-(2 : ℝ)) =
        (4 / s ^ 2) * (1 + |(n : ℝ)|) ^ (-(2 : ℝ)) := by
      rw [Real.div_rpow (by positivity) (by norm_num),
        Real.mul_rpow hs_pos.le (by positivity),
        Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
        Real.rpow_neg hs_pos.le, Real.rpow_neg (by positivity), Real.rpow_two, Real.rpow_two]
      field_simp [hs_pos.ne']
      norm_num
    calc C * (1 + |w.1 + n * d|) ^ (-(2 : ℝ))
        ≤ C * ((4 / s ^ 2) * (1 + |(n : ℝ)|) ^ (-(2 : ℝ))) := by
          rw [← h6]; exact mul_le_mul_of_nonneg_left h5 hC0
      _ = K * (1 + |(n : ℝ)|) ^ (-(2 : ℝ)) := by simp only [K]; ring
  refine ⟨K * ∑' n : ℤ, (1 + |(n : ℝ)|) ^ (-(2 : ℝ)), mul_nonneg hK0 hS_nn, fun y => ?_⟩
  obtain ⟨m, hm⟩ := exists_int_shift_mem_cell hd y
  rw [← perSum_int_period d L m y]
  exact hcell _ hm

/-- Global supremum bound on `perSum d L` for any `d > 0` and `LamJetInf.Good L`. -/
private lemma perSum_sup_of_good {d : ℝ} (hd : 0 < d) {L : ℝ × ℝ → ℂ} (hL : LamJetInf.Good L) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ y : ℝ × ℝ, ‖perSum d L y‖ ≤ B := by
  obtain ⟨C, hC0, hC⟩ := hL.norm_le
  refine perSum_sup_of_inv_sq hd hC0 fun z => ?_
  have hz1 : 1 + |z.1| ≤ 1 + ‖z‖ := by
    have : |z.1| ≤ ‖z‖ := by rw [← Real.norm_eq_abs]; exact norm_fst_le z
    linarith
  have hp1 : 0 < (1 + |z.1|) ^ 2 := by positivity
  have hp2 : (1 + |z.1|) ^ 2 ≤ (1 + ‖z‖) ^ 2 := pow_le_pow_left₀ (by positivity) hz1 2
  rw [Real.rpow_neg (by positivity), Real.rpow_two, ← div_eq_mul_inv, le_div_iff₀ hp1]
  have hmul : ‖L z‖ * (1 + |z.1|) ^ 2 ≤ ‖L z‖ * (1 + ‖z‖) ^ 2 :=
    mul_le_mul_of_nonneg_left hp2 (norm_nonneg _)
  exact hmul.trans (hC z)

/-- Global vertical Gaussian bound `‖perSum d g y‖ ≤ M * exp(-y.2² / 8)` for `d > 0` when
`‖g z‖ ≤ C * exp(-(z.1² + z.2²) / 8)`. -/
private lemma perSum_vert_gauss_bound {d C : ℝ} (hd : 0 < d) (hC0 : 0 ≤ C) {g : ℝ × ℝ → ℂ}
    (hg : ∀ z : ℝ × ℝ, ‖g z‖ ≤ C * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ y : ℝ × ℝ, ‖perSum d g y‖ ≤ M * Real.exp (-y.2 ^ 2 / 8) := by
  obtain ⟨B, hB0, hB⟩ := perSum_sup_of_inv_sq (d := d) (C := 1) hd zero_le_one
    (L := fun z => (((1 + |z.1|) ^ (-(2 : ℝ)) : ℝ) : ℂ)) (fun z => by
      rw [Complex.norm_of_nonneg (by positivity), one_mul])
  refine ⟨16 * C * B, by positivity, fun y => ?_⟩
  have hsum_one : Summable (fun n : ℤ => (1 + |y.1 + n * d|) ^ (-(2 : ℝ))) := by
    have hs := LamJetInf.summable_inv_sq_shift hd.ne' y.1
    refine hs.congr fun n => ?_
    rw [Real.rpow_neg (by positivity), Real.rpow_two]
  have hterm : ∀ n : ℤ, ‖g (y.1 + n * d, y.2)‖ ≤
      (16 * C * Real.exp (-y.2 ^ 2 / 8)) * (1 + |y.1 + n * d|) ^ (-(2 : ℝ)) := by
    intro n
    have h1 := hg (y.1 + n * d, y.2)
    have hexp : Real.exp (-((y.1 + n * d) ^ 2 + y.2 ^ 2) / 8) =
        Real.exp (-((y.1 + n * d) ^ 2 + 0 ^ 2) / 8) * Real.exp (-y.2 ^ 2 / 8) := by
      rw [← Real.exp_add]; congr 1; ring
    have htw := FrameCont.exp_le_translate_weight (y.1 + n * d) 0
    calc ‖g (y.1 + n * d, y.2)‖
        ≤ C * (Real.exp (-((y.1 + n * d) ^ 2 + 0 ^ 2) / 8) * Real.exp (-y.2 ^ 2 / 8)) := by
          rwa [hexp] at h1
      _ ≤ C * ((16 * (1 + |y.1 + n * d|) ^ (-(2 : ℝ))) * Real.exp (-y.2 ^ 2 / 8)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right htw (Real.exp_pos _).le) hC0
      _ = (16 * C * Real.exp (-y.2 ^ 2 / 8)) * (1 + |y.1 + n * d|) ^ (-(2 : ℝ)) := by ring
  have htsum_eq : ∑' n : ℤ, (1 + |y.1 + n * d|) ^ (-(2 : ℝ)) ≤ B := by
    have hnn : 0 ≤ ∑' n : ℤ, (1 + |y.1 + n * d|) ^ (-(2 : ℝ)) :=
      tsum_nonneg fun _ => by positivity
    have hcast : perSum d (fun z : ℝ × ℝ => (((1 + |z.1|) ^ (-(2 : ℝ)) : ℝ) : ℂ)) y =
        ((∑' n : ℤ, (1 + |y.1 + n * d|) ^ (-(2 : ℝ)) : ℝ) : ℂ) := by
      unfold perSum
      exact (Complex.ofReal_tsum _).symm
    have hb := hB y
    rw [hcast, Complex.norm_of_nonneg hnn] at hb
    exact hb
  unfold perSum
  calc ‖∑' n : ℤ, g (y.1 + n * d, y.2)‖
      ≤ (16 * C * Real.exp (-y.2 ^ 2 / 8)) * ∑' n : ℤ, (1 + |y.1 + n * d|) ^ (-(2 : ℝ)) :=
        tsum_of_norm_bounded (hsum_one.hasSum.mul_left _) hterm
    _ ≤ (16 * C * Real.exp (-y.2 ^ 2 / 8)) * B :=
        mul_le_mul_of_nonneg_left htsum_eq (by positivity)
    _ = (16 * C * B) * Real.exp (-y.2 ^ 2 / 8) := by ring

/-- The vertical Gaussian `y ↦ exp(-y.2² / 8)` is integrable on `B0579.cell d` for every `d : ℝ`. -/
private lemma integrableOn_vert_gauss_cell (d : ℝ) :
    IntegrableOn (fun y : ℝ × ℝ => Real.exp (-y.2 ^ 2 / 8)) (B0579.cell d) := by
  have hg0 : IntegrableOn (fun y : ℝ × ℝ =>
      Real.exp (d ^ 2 / 32) * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8)) (B0579.cell d) := by
    have h := (integrable_jb_gauss (m := 0) le_rfl).const_mul (Real.exp (d ^ 2 / 32))
    refine h.integrableOn.congr_fun (fun y _ => ?_) (B0579.measurableSet_cell d)
    simp
  have hcont : Continuous (fun y : ℝ × ℝ => Real.exp (-y.2 ^ 2 / 8)) := by fun_prop
  refine hg0.mono' hcont.aestronglyMeasurable
    ((ae_restrict_mem (B0579.measurableSet_cell d)).mono fun y hy => ?_)
  rw [Real.norm_of_nonneg (Real.exp_pos _).le, ← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  have hy1 : |y.1| ≤ |d| / 2 := by
    have h1 := hy.1.1
    have h2 := hy.1.2
    have hd_le : d ≤ |d| := le_abs_self d
    rw [abs_le]; constructor <;> linarith
  have hsq : y.1 ^ 2 ≤ d ^ 2 / 4 := by
    have h := pow_le_pow_left₀ (abs_nonneg y.1) hy1 2
    rw [sq_abs, div_pow, sq_abs] at h
    linarith
  linarith

/-- Any continuous complex field bounded by `M * exp(-y.2² / 8)` on `B0579.cell d` is integrable on
`B0579.cell d`. -/
private lemma integrableOn_of_vert_gauss {d M : ℝ} {f : ℝ × ℝ → ℂ} (hf : Continuous f)
    (hbd : ∀ y ∈ B0579.cell d, ‖f y‖ ≤ M * Real.exp (-y.2 ^ 2 / 8)) :
    IntegrableOn f (B0579.cell d) := by
  refine ((integrableOn_vert_gauss_cell d).const_mul M).mono' hf.aestronglyMeasurable
    ((ae_restrict_mem (B0579.measurableSet_cell d)).mono hbd)

/-- For every `d > 0`, `perLam0 κ d k * perE κ d j` is integrable on `B0579.cell d`. -/
private lemma integrableOn_perLam0_mul_perE_pos (κ : PlanarFrameKernels) {d : ℝ} (hd : 0 < d)
    (k j : Fin 2) :
    IntegrableOn (fun y => perLam0 κ d k y * perE κ d j y) (B0579.cell d) := by
  obtain ⟨C_l, hCl0, hCl⟩ := Lam0B.lamP_translate_bound κ
  obtain ⟨B_l, hBl0, hBl⟩ := perSum_sup_of_inv_sq hd hCl0 (hCl k)
  obtain ⟨C_e, hCe⟩ := κ.e_decay
  obtain ⟨M_e, _, hMe⟩ := perSum_vert_gauss_bound hd (abs_nonneg C_e) (g := κ.e j) fun z =>
    (hCe j z).trans (mul_le_mul_of_nonneg_right (le_abs_self C_e) (Real.exp_pos _).le)
  have hc : Continuous (fun y => perLam0 κ d k y * perE κ d j y) :=
    (Lam0B.perLam0_continuous κ hd k).mul (FrameCont.perE_continuous κ hd j)
  refine integrableOn_of_vert_gauss (M := B_l * M_e) hc fun y _ => ?_
  rw [norm_mul]
  calc ‖perLam0 κ d k y‖ * ‖perE κ d j y‖
      ≤ B_l * (M_e * Real.exp (-y.2 ^ 2 / 8)) :=
        mul_le_mul (hBl y) (hMe y) (norm_nonneg _) hBl0
    _ = (B_l * M_e) * Real.exp (-y.2 ^ 2 / 8) := by ring

/-- `PerFrameFacts κ ν m b K` implies `IsUnit (perGram κ (dd ν r))` whenever `0 < ν`, `0 ≤ r`, and
`b ≤ clockTheta ν r`. -/
private lemma isUnit_perGram_of_perFrameFacts (κ : PlanarFrameKernels) {ν m b K r : ℝ}
    (hν : 0 < ν) (hr : 0 ≤ r) (hbr : b ≤ clockTheta ν r) (hF : PerFrameFacts κ ν m b K) :
    IsUnit (perGram κ (dd ν r)) := by
  set d := dd ν r
  have ha : 0 < clockA ν r := lt_of_lt_of_le zero_lt_one (one_le_clockA hν.le hr)
  have hd : 0 < d := div_pos (Real.rpow_pos_of_pos hν _) (Real.sqrt_pos.2 ha)
  have hmul : (perGram κ d)⁻¹ * perGram κ d = 1 := by
    ext i j
    rw [Matrix.mul_apply, Matrix.one_apply]
    have hdual := hF.1 r hr hbr i j
    have hcell : movingCell ν (ν ^ (-2 : ℝ)) r = B0579.cell d := rfl
    have hd_eq : cellLen (ν ^ (-2 : ℝ)) (clockA ν r) = d := rfl
    rw [hcell, hd_eq] at hdual
    rw [← hdual]
    have hfun : (fun x => perLam κ d i x * perE κ d j x) =
        fun x => ∑ k : Fin 2, (perGram κ d)⁻¹ i k * (perLam0 κ d k x * perE κ d j x) := by
      funext x
      unfold perLam
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [hfun, integral_finsetSum _ fun k _ =>
      (integrableOn_perLam0_mul_perE_pos κ hd k j).const_mul _]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_const_mul]
    rfl
  have hdet1 : ((perGram κ d)⁻¹).det * (perGram κ d).det = 1 := by
    rw [← Matrix.det_mul, hmul, Matrix.det_one]
  have hdet_ne : (perGram κ d).det ≠ 0 := right_ne_zero_of_mul_eq_one hdet1
  exact (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hdet_ne)

/-- Entrywise `HasDerivAt` of `d' ↦ (perGram κ d')⁻¹ i k` at any `d > 0` where `perGram κ d` is a
unit, together with the product-rule identity `(G⁻¹)' G + G⁻¹ G' = 0` from `(G⁻¹ G) = I₂`. -/
private lemma hasDerivAt_perGram_inv_and_orth {κ : PlanarFrameKernels} (hκ : IsSeedKernels κ)
    {d : ℝ} (hd : 0 < d) (hU : IsUnit (perGram κ d)) :
    ∃ G_inv' : Matrix (Fin 2) (Fin 2) ℂ,
      (∀ i k : Fin 2, HasDerivAt (fun d' => (perGram κ d')⁻¹ i k) (G_inv' i k) d) ∧
      (∀ i j : Fin 2,
        ∑ k : Fin 2,
          (G_inv' i k * perGram κ d k j +
            (perGram κ d)⁻¹ i k * ComplCouplingHeat.perGramDeriv κ d k j) = 0) := by
  obtain ⟨hCD, _, _, _, h1, _⟩ :=
    ComplCouplingHeat.seedLamP_jet2_bounds_of κ (seedLamPJet2Decay_all κ) hκ
  obtain ⟨_, _, hG_all⟩ := ComplCouplingHeat.hasDerivAt_perGram_and_bound κ hCD h1
  have hder : ∀ a b : Fin 2,
      HasDerivAt (fun d' => perGram κ d' a b) (ComplCouplingHeat.perGramDeriv κ d a b) d :=
    fun a b => (hG_all hd a b).1
  have hdet_ne : (perGram κ d).det ≠ 0 :=
    isUnit_iff_ne_zero.1 ((Matrix.isUnit_iff_isUnit_det _).1 hU)
  set det' : ℂ :=
    (ComplCouplingHeat.perGramDeriv κ d 0 0 * perGram κ d 1 1 +
      perGram κ d 0 0 * ComplCouplingHeat.perGramDeriv κ d 1 1) -
      (ComplCouplingHeat.perGramDeriv κ d 0 1 * perGram κ d 1 0 +
        perGram κ d 0 1 * ComplCouplingHeat.perGramDeriv κ d 1 0)
  have hdet_der : HasDerivAt (fun d' => (perGram κ d').det) det' d := by
    have hfun : (fun d' => (perGram κ d').det) =
        fun d' => perGram κ d' 0 0 * perGram κ d' 1 1 - perGram κ d' 0 1 * perGram κ d' 1 0 :=
      funext fun d' => Matrix.det_fin_two (perGram κ d')
    rw [hfun]
    exact ((hder 0 0).mul (hder 1 1)).sub ((hder 0 1).mul (hder 1 0))
  have hinv_det : HasDerivAt (fun d' => ((perGram κ d').det)⁻¹)
      (-det' / ((perGram κ d).det) ^ 2) d :=
    hdet_der.inv hdet_ne
  have hprod : ∀ {u : ℝ → ℂ} {u' : ℂ}, HasDerivAt u u' d →
      ∃ g' : ℂ, HasDerivAt (fun d' => ((perGram κ d').det)⁻¹ * u d') g' d :=
    fun {u} {u'} hu =>
      ⟨(-det' / ((perGram κ d).det) ^ 2) * u d + ((perGram κ d).det)⁻¹ * u', hinv_det.mul hu⟩
  have hentry : ∀ i k : Fin 2, ∃ g' : ℂ,
      HasDerivAt (fun d' => (perGram κ d')⁻¹ i k) g' d := by
    intro i k
    fin_cases i <;> fin_cases k <;> dsimp only [Fin.zero_eta, Fin.mk_one, Fin.isValue]
    · have hfun : (fun d' => (perGram κ d')⁻¹ 0 0) =
          fun d' => ((perGram κ d').det)⁻¹ * perGram κ d' 1 1 := by
        funext d'; rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.adjugate_fin_two]; simp
      rw [hfun]; exact hprod (hder 1 1)
    · have hfun : (fun d' => (perGram κ d')⁻¹ 0 1) =
          fun d' => ((perGram κ d').det)⁻¹ * (-perGram κ d' 0 1) := by
        funext d'; rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.adjugate_fin_two]; simp
      rw [hfun]; exact hprod (hder 0 1).neg
    · have hfun : (fun d' => (perGram κ d')⁻¹ 1 0) =
          fun d' => ((perGram κ d').det)⁻¹ * (-perGram κ d' 1 0) := by
        funext d'; rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.adjugate_fin_two]; simp
      rw [hfun]; exact hprod (hder 1 0).neg
    · have hfun : (fun d' => (perGram κ d')⁻¹ 1 1) =
          fun d' => ((perGram κ d').det)⁻¹ * perGram κ d' 0 0 := by
        funext d'; rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.adjugate_fin_two]; simp
      rw [hfun]; exact hprod (hder 0 0)
  choose G_inv' hG_inv' using fun p : Fin 2 × Fin 2 => hentry p.1 p.2
  refine ⟨Matrix.of (fun i k => G_inv' (i, k)), fun i k => hG_inv' (i, k), fun i j => ?_⟩
  have hev_ne : ∀ᶠ d' in 𝓝 d, (perGram κ d').det ≠ 0 :=
    hdet_der.continuousAt.eventually_ne hdet_ne
  have hev_one : (fun d' => ∑ k : Fin 2, (perGram κ d')⁻¹ i k * perGram κ d' k j) =ᶠ[𝓝 d]
      fun _ => (1 : Matrix (Fin 2) (Fin 2) ℂ) i j := by
    filter_upwards [hev_ne] with d' hd'
    have hmul := Matrix.nonsing_inv_mul (perGram κ d') (isUnit_iff_ne_zero.2 hd')
    have := congrFun (congrFun hmul i) j
    rwa [Matrix.mul_apply] at this
  have hterm_der : ∀ k : Fin 2,
      HasDerivAt (fun d' => (perGram κ d')⁻¹ i k * perGram κ d' k j)
        (G_inv' (i, k) * perGram κ d k j +
          (perGram κ d)⁻¹ i k * ComplCouplingHeat.perGramDeriv κ d k j) d :=
    fun k => (hG_inv' (i, k)).mul (hder k j)
  have hsum_der : HasDerivAt (fun d' => ∑ k : Fin 2, (perGram κ d')⁻¹ i k * perGram κ d' k j)
      (∑ k : Fin 2,
        (G_inv' (i, k) * perGram κ d k j +
          (perGram κ d)⁻¹ i k * ComplCouplingHeat.perGramDeriv κ d k j)) d :=
    HasDerivAt.fun_sum fun k _ => hterm_der k
  have hconst : HasDerivAt (fun _ : ℝ => (1 : Matrix (Fin 2) (Fin 2) ℂ) i j) 0 d :=
    hasDerivAt_const d _
  exact hsum_der.unique (hconst.congr_of_eventuallyEq hev_one)

/-! ## 2. Step 2 (`task.issues`): moving pullback of `movH0` into heat and Euler parts -/

/-- **Step 2** (SP 2905–2918): change of variables via `movingPhi` / `physAdj` expresses `movH0` on
`perE κ (dd ν r) j` as the moving-cell integral of `movLamDualHeat` plus `movEulerAdj` against
`perE κ (dd ν r) j`. -/
private lemma step2_movH0_pullback_split (κ : PlanarFrameKernels) {ν r : ℝ}
    (hν : 0 < ν) (hr : 0 ≤ r)
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (i j : Fin 2) :
    movH0 κ tr r i (perE κ (dd ν r) j) =
      ∫ y in B0579.cell (dd ν r),
        (movLamDualHeat κ ν r i y +
          ComplCouplingEuler.movEulerAdj (dd ν r)
            (movingTrainV tr r) (movingTrainE tr r) (perLam κ (dd ν r) i) y) *
          perE κ (dd ν r) j y := by
  rw [ComplCouplingSub.movH0_eq_integral_movLamDual]
  have hcell : movingCell ν (ν ^ (-2 : ℝ)) r = B0579.cell (dd ν r) := rfl
  rw [hcell]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  dsimp only
  rw [ComplCouplingSub.movLamDual_eq_heat_add_euler,
    ComplCouplingEuler.movPullback_physLamDualEuler_eq κ tr hν hr i y]

/-! ## 3. Step 3 (`task.issues`): Euler `ladTransport` IBP and `kerAdj` Fubini against `perE` -/

/-- **Step 3a** (SP 2912–2918): periodic integration by parts of the rescaled divergence-free train
drift `movingTrainV tr r` on `B0579.cell (dd ν r)` transfers `E0.transCx` from `perLam` to
`-perE`. -/
private lemma step3a_euler_transport_ibp {κ : PlanarFrameKernels} (hκ : IsSeedKernels κ)
    {ν m r C_tr : ℝ} (hν : 0 < ν) (hr : 0 ≤ r)
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)))
    (hBdd : LadTrainBdd tr m r C_tr) (i j : Fin 2) :
    let d := dd ν r
    let V := movingTrainV tr r
    IntegrableOn (fun y => E0.transCx V (perLam κ d i) y * perE κ d j y) (B0579.cell d) ∧
    IntegrableOn (fun y => perLam κ d i y * E0.transCx V (perE κ d j) y) (B0579.cell d) ∧
    (∫ y in B0579.cell d, E0.transCx V (perLam κ d i) y * perE κ d j y =
      -∫ y in B0579.cell d, perLam κ d i y * E0.transCx V (perE κ d j) y) := by
  intro d V
  have hc : 0 < ν ^ (-2 : ℝ) := Real.rpow_pos_of_pos hν _
  have ha1 : 1 ≤ clockA ν r := one_le_clockA hν.le hr
  have ha0 : 0 < clockA ν r := lt_of_lt_of_le zero_lt_one ha1
  have hsa0 : 0 < Real.sqrt (clockA ν r) := Real.sqrt_pos.2 ha0
  have hd : 0 < d := div_pos hc hsa0
  obtain ⟨hV_sm, hV_per, hV_div⟩ := E0.movingTrainReg ν (ν ^ (-2 : ℝ)) hν hc tr r hr
  have hVk_sm : ∀ k : Fin 2, ContDiff ℝ 1 (fun y => V y k) := fun k =>
    (ContinuousLinearMap.proj k : (Fin 2 → ℝ) →L[ℝ] ℝ).contDiff.comp hV_sm
  set Λ : ℝ × ℝ → ℂ := perLam κ d i
  set E : ℝ × ℝ → ℂ := perE κ d j
  have hlam0_sm : ∀ k : Fin 2, ContDiff ℝ ∞ (perLam0 κ d k) := fun k =>
    contDiff_perSum_of_good hd (LamJetInf.good_lamP hκ k)
  have hΛ_sm : ContDiff ℝ ∞ Λ := by
    have heq : Λ = fun y => ∑ k : Fin 2, (perGram κ d)⁻¹ i k * perLam0 κ d k y := rfl
    rw [heq]
    exact ContDiff.sum fun k _ => contDiff_const.mul (hlam0_sm k)
  have hE_sm : ContDiff ℝ ∞ E := contDiff_perSum_of_good hd (FramePairing1Aux.good_e hκ j)
  have hΛ_per : ∀ y : ℝ × ℝ, Λ (y.1 + d, y.2) = Λ y := by
    intro y
    unfold Λ perLam perLam0
    refine Finset.sum_congr rfl fun k _ => ?_
    have hp := perSum_int_period d (κ.lamP k) 1 y
    simp only [Int.cast_one, one_mul] at hp
    rw [hp]
  have hE_per : ∀ y : ℝ × ℝ, E (y.1 + d, y.2) = E y := by
    intro y
    have hp := perSum_int_period d (κ.e j) 1 y
    simp only [Int.cast_one, one_mul] at hp
    exact hp
  set CV : ℝ := (clockA ν r) ^ (3 / 2 : ℝ) * max C_tr 0
  have hCV0 : 0 ≤ CV := by positivity
  have hV_bd : ∀ y ∈ B0579.cell d, ∀ k : Fin 2, |V y k| ≤ CV := by
    intro y hy k
    set z : ℝ × ℝ := (Real.sqrt (clockA ν r) * y.1, Real.sqrt (clockA ν r) * y.2)
    have hz_cell : z ∈ B0579.cell (ν ^ (-2 : ℝ)) := by
      simp only [B0579.cell, mem_prod, mem_Ico, mem_univ, and_true, z]
      have hmul : Real.sqrt (clockA ν r) * (d / 2) = ν ^ (-2 : ℝ) / 2 := by
        dsimp [d, dd, cellLen]
        field_simp [hsa0.ne']
      exact ⟨by linarith [mul_le_mul_of_nonneg_left hy.1.1 hsa0.le, hmul],
        by linarith [mul_lt_mul_of_pos_left hy.1.2 hsa0, hmul]⟩
    have hvz : |tr.v r z k| ≤ max C_tr 0 :=
      ((hBdd r ⟨hr, le_rfl⟩ z hz_cell).1 k).trans (le_max_left _ _)
    unfold V movingTrainV
    rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos ha0 _)]
    exact mul_le_mul_of_nonneg_left hvz (Real.rpow_nonneg ha0.le _)
  obtain ⟨B_l0, _, hb_l0⟩ := perSum_sup_of_good hd (LamJetInf.good_lamP hκ 0)
  obtain ⟨B_l1, _, hb_l1⟩ := perSum_sup_of_good hd (LamJetInf.good_lamP hκ 1)
  set B_Λ : ℝ := ‖(perGram κ d)⁻¹ i 0‖ * B_l0 + ‖(perGram κ d)⁻¹ i 1‖ * B_l1
  have hBΛ0 : 0 ≤ B_Λ := by positivity
  have hΛ_bd : ∀ y : ℝ × ℝ, ‖Λ y‖ ≤ B_Λ := by
    intro y
    change ‖∑ k : Fin 2, (perGram κ d)⁻¹ i k * perLam0 κ d k y‖ ≤ B_Λ
    rw [Fin.sum_univ_two]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    exact add_le_add
      (mul_le_mul_of_nonneg_left (hb_l0 y) (norm_nonneg _))
      (mul_le_mul_of_nonneg_left (hb_l1 y) (norm_nonneg _))
  have hpdΛ_bd : ∃ B_dΛ : ℝ, 0 ≤ B_dΛ ∧ ∀ (k : Fin 2) (y : ℝ × ℝ), ‖pdCx k Λ y‖ ≤ B_dΛ := by
    have hk_bd : ∀ k : Fin 2, ∃ Bk : ℝ, 0 ≤ Bk ∧ ∀ y : ℝ × ℝ, ‖pdCx k Λ y‖ ≤ Bk := by
      intro k
      obtain ⟨D0, _, hd0_b⟩ :=
        perSum_sup_of_good hd ((LamJetInf.good_lamP hκ 0).fderiv_apply (B0579.dir k))
      obtain ⟨D1, _, hd1_b⟩ :=
        perSum_sup_of_good hd ((LamJetInf.good_lamP hκ 1).fderiv_apply (B0579.dir k))
      refine ⟨‖(perGram κ d)⁻¹ i 0‖ * D0 + ‖(perGram κ d)⁻¹ i 1‖ * D1, by positivity, fun y => ?_⟩
      have heq : pdCx k Λ y =
          (perGram κ d)⁻¹ i 0 * perSum d (pdCx k (κ.lamP 0)) y +
            (perGram κ d)⁻¹ i 1 * perSum d (pdCx k (κ.lamP 1)) y := by
        set g0 : ℝ × ℝ → ℂ := fun z => (perGram κ d)⁻¹ i 0 * perSum d (κ.lamP 0) z
        set g1 : ℝ × ℝ → ℂ := fun z => (perGram κ d)⁻¹ i 1 * perSum d (κ.lamP 1) z
        have hΛ2 : Λ = g0 + g1 := by
          funext z; unfold Λ perLam perLam0; rw [Fin.sum_univ_two]; rfl
        have hf0 : DifferentiableAt ℝ (perSum d (κ.lamP 0)) y :=
          ((hlam0_sm 0).differentiable (by simp)) y
        have hf1 : DifferentiableAt ℝ (perSum d (κ.lamP 1)) y :=
          ((hlam0_sm 1).differentiable (by simp)) y
        have hg0 : DifferentiableAt ℝ g0 y :=
          (differentiableAt_const ((perGram κ d)⁻¹ i 0)).mul hf0
        have hg1 : DifferentiableAt ℝ g1 y :=
          (differentiableAt_const ((perGram κ d)⁻¹ i 1)).mul hf1
        rw [hΛ2]
        unfold pdCx
        have hd_add := (hg0.hasFDerivAt.add hg1.hasFDerivAt).fderiv
        rw [hd_add]
        simp only [add_apply]
        have hm0 := RateSplitAux.pdCx_mul k (differentiableAt_const ((perGram κ d)⁻¹ i 0)) hf0
        have hm1 := RateSplitAux.pdCx_mul k (differentiableAt_const ((perGram κ d)⁻¹ i 1)) hf1
        have hc0 : pdCx k (fun _ : ℝ × ℝ => (perGram κ d)⁻¹ i 0) y = 0 := by unfold pdCx; simp
        have hc1 : pdCx k (fun _ : ℝ × ℝ => (perGram κ d)⁻¹ i 1) y = 0 := by unfold pdCx; simp
        change pdCx k g0 y + pdCx k g1 y = _
        rw [hm0, hm1, hc0, hc1, zero_mul, zero_mul, zero_add, zero_add,
          pdCx_perSum_of_good hd (LamJetInf.good_lamP hκ 0) k y,
          pdCx_perSum_of_good hd (LamJetInf.good_lamP hκ 1) k y]
        rfl
      rw [heq]
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, norm_mul]
      exact add_le_add
        (mul_le_mul_of_nonneg_left (hd0_b y) (norm_nonneg _))
        (mul_le_mul_of_nonneg_left (hd1_b y) (norm_nonneg _))
    obtain ⟨B0, hB0_pos, hb0⟩ := hk_bd 0
    obtain ⟨B1, _, hb1⟩ := hk_bd 1
    refine ⟨max B0 B1, le_trans hB0_pos (le_max_left _ _), fun k y => ?_⟩
    fin_cases k
    · exact (hb0 y).trans (le_max_left _ _)
    · exact (hb1 y).trans (le_max_right _ _)
  obtain ⟨B_dΛ, hBdΛ0, hBdΛ⟩ := hpdΛ_bd
  obtain ⟨C_e, hCe0, hseed_e⟩ := EulerErrorTail.seed_bounds hκ
  obtain ⟨M_E, hME0, hME⟩ := perSum_vert_gauss_bound hd hCe0 (g := κ.e j) fun z => (hseed_e j z).1
  obtain ⟨M_E0, hME0_pos, hME0_bd⟩ :=
    perSum_vert_gauss_bound hd hCe0 (g := pdCx 0 (κ.e j)) fun z => (hseed_e j z).2 0
  obtain ⟨M_E1, hME1_pos, hME1_bd⟩ :=
    perSum_vert_gauss_bound hd hCe0 (g := pdCx 1 (κ.e j)) fun z => (hseed_e j z).2 1
  have hVk_cont : ∀ k : Fin 2, Continuous (fun y => (V y k : ℂ)) :=
    fun k => Complex.continuous_ofReal.comp (hVk_sm k).continuous
  have hpdΛ_cont : ∀ k : Fin 2, Continuous (pdCx k Λ) :=
    fun k => (RateSplitAux.contDiff_pdCx hΛ_sm k).continuous
  have hpdE_cont : ∀ k : Fin 2, Continuous (pdCx k E) :=
    fun k => (RateSplitAux.contDiff_pdCx hE_sm k).continuous
  have hint_lhs : IntegrableOn (fun y => E0.transCx V Λ y * E y) (B0579.cell d) := by
    have hc_lhs : Continuous (fun y => E0.transCx V Λ y * E y) := by
      unfold E0.transCx
      exact (((hVk_cont 0).mul (hpdΛ_cont 0)).add ((hVk_cont 1).mul (hpdΛ_cont 1))).mul
        hE_sm.continuous
    refine integrableOn_of_vert_gauss (M := (2 * CV * B_dΛ) * M_E) hc_lhs fun y hy => ?_
    rw [norm_mul]
    have ht := E0.norm_transCx_le V Λ CV hCV0 y (hV_bd y hy 0) (hV_bd y hy 1)
    have ht' : ‖E0.transCx V Λ y‖ ≤ 2 * CV * B_dΛ := by
      have h0 := hBdΛ 0 y
      have h1 := hBdΛ 1 y
      nlinarith
    calc ‖E0.transCx V Λ y‖ * ‖E y‖
        ≤ (2 * CV * B_dΛ) * (M_E * Real.exp (-y.2 ^ 2 / 8)) :=
          mul_le_mul ht' (hME y) (norm_nonneg _) (by positivity)
      _ = ((2 * CV * B_dΛ) * M_E) * Real.exp (-y.2 ^ 2 / 8) := by ring
  have hint_rhs : IntegrableOn (fun y => Λ y * E0.transCx V E y) (B0579.cell d) := by
    have hc_rhs : Continuous (fun y => Λ y * E0.transCx V E y) := by
      unfold E0.transCx
      exact hΛ_sm.continuous.mul
        (((hVk_cont 0).mul (hpdE_cont 0)).add ((hVk_cont 1).mul (hpdE_cont 1)))
    refine integrableOn_of_vert_gauss (M := B_Λ * (CV * (M_E0 + M_E1))) hc_rhs fun y hy => ?_
    rw [norm_mul]
    have ht := E0.norm_transCx_le V E CV hCV0 y (hV_bd y hy 0) (hV_bd y hy 1)
    have hpd0_eq : pdCx 0 E y = perSum d (pdCx 0 (κ.e j)) y :=
      pdCx_perSum_of_good hd (FramePairing1Aux.good_e hκ j) 0 y
    have hpd1_eq : pdCx 1 E y = perSum d (pdCx 1 (κ.e j)) y :=
      pdCx_perSum_of_good hd (FramePairing1Aux.good_e hκ j) 1 y
    have ht' : ‖E0.transCx V E y‖ ≤ (CV * (M_E0 + M_E1)) * Real.exp (-y.2 ^ 2 / 8) := by
      rw [hpd0_eq, hpd1_eq] at ht
      have h0 := hME0_bd y
      have h1 := hME1_bd y
      nlinarith [Real.exp_pos (-y.2 ^ 2 / 8)]
    calc ‖Λ y‖ * ‖E0.transCx V E y‖
        ≤ B_Λ * ((CV * (M_E0 + M_E1)) * Real.exp (-y.2 ^ 2 / 8)) :=
          mul_le_mul (hΛ_bd y) ht' (norm_nonneg _) hBΛ0
      _ = (B_Λ * (CV * (M_E0 + M_E1))) * Real.exp (-y.2 ^ 2 / 8) := by ring
  refine ⟨hint_lhs, hint_rhs, ?_⟩
  set P : ℝ × ℝ → ℂ := fun y => Λ y * E y
  have hP_sm : ContDiff ℝ 1 P := (hΛ_sm.mul hE_sm).of_le (by simp)
  have hP_per : ∀ y : ℝ × ℝ, P (y.1 + d, y.2) = P y := fun y => by
    show Λ (y.1 + d, y.2) * E (y.1 + d, y.2) = Λ y * E y
    rw [hΛ_per y, hE_per y]
  have hP_int : IntegrableOn (fun y => (V y 1 : ℂ) * P y) (B0579.cell d) := by
    refine integrableOn_of_vert_gauss (M := CV * B_Λ * M_E)
      ((hVk_cont 1).mul hP_sm.continuous) fun y hy => ?_
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc |V y 1| * (‖Λ y‖ * ‖E y‖)
        ≤ CV * (B_Λ * (M_E * Real.exp (-y.2 ^ 2 / 8))) :=
          mul_le_mul (hV_bd y hy 1)
            (mul_le_mul (hΛ_bd y) (hME y) (norm_nonneg _) hBΛ0)
            (by positivity) hCV0
      _ = (CV * B_Λ * M_E) * Real.exp (-y.2 ^ 2 / 8) := by ring
  have hdiv_cx : ∀ y : ℝ × ℝ,
      pdCx 0 (fun x => (V x 0 : ℂ) * P x) y + pdCx 1 (fun x => (V x 1 : ℂ) * P x) y =
        E0.transCx V Λ y * E y + Λ y * E0.transCx V E y := by
    intro y
    have hV0d : DifferentiableAt ℝ (fun x => (V x 0 : ℂ)) y :=
      Complex.ofRealCLM.differentiableAt.comp y ((hVk_sm 0).differentiable one_ne_zero y)
    have hV1d : DifferentiableAt ℝ (fun x => (V x 1 : ℂ)) y :=
      Complex.ofRealCLM.differentiableAt.comp y ((hVk_sm 1).differentiable one_ne_zero y)
    have hΛd : DifferentiableAt ℝ Λ y := (hΛ_sm.differentiable (by simp)) y
    have hEd : DifferentiableAt ℝ E y := (hE_sm.differentiable (by simp)) y
    have hPd : DifferentiableAt ℝ P y := hΛd.mul hEd
    have hpdV : ∀ k : Fin 2,
        pdCx k (fun x => (V x k : ℂ)) y = (B0579.pd k (fun x => V x k) y : ℂ) := by
      intro k
      have hk_d : DifferentiableAt ℝ (fun x => V x k) y := (hVk_sm k).differentiable one_ne_zero y
      unfold pdCx B0579.pd
      have hc_f := (Complex.ofRealCLM.hasFDerivAt.comp y hk_d.hasFDerivAt).fderiv
      change fderiv ℝ (Complex.ofRealCLM ∘ fun x => V x k) y (B0579.dir k) = _
      rw [hc_f]
      rfl
    rw [RateSplitAux.pdCx_mul 0 hV0d hPd, RateSplitAux.pdCx_mul 1 hV1d hPd,
      hpdV 0, hpdV 1,
      RateSplitAux.pdCx_mul 0 hΛd hEd, RateSplitAux.pdCx_mul 1 hΛd hEd]
    unfold E0.transCx P
    have hdivC :
        ((B0579.pd 0 (fun x => V x 0) y : ℂ) + (B0579.pd 1 (fun x => V x 1) y : ℂ)) = 0 := by
      exact_mod_cast hV_div y
    linear_combination (Λ y * E y) * hdivC
  have pd_re : ∀ (k : Fin 2) (G : ℝ × ℝ → ℂ), Differentiable ℝ G → ∀ y : ℝ × ℝ,
      B0579.pd k (fun x => (G x).re) y = (pdCx k G y).re := by
    intro k G hGd y
    unfold B0579.pd pdCx
    change fderiv ℝ (Complex.reCLM ∘ G) y (B0579.dir k) = _
    rw [(Complex.reCLM.hasFDerivAt.comp y (hGd y).hasFDerivAt).fderiv]
    rfl
  have pd_im : ∀ (k : Fin 2) (G : ℝ × ℝ → ℂ), Differentiable ℝ G → ∀ y : ℝ × ℝ,
      B0579.pd k (fun x => (G x).im) y = (pdCx k G y).im := by
    intro k G hGd y
    unfold B0579.pd pdCx
    change fderiv ℝ (Complex.imCLM ∘ G) y (B0579.dir k) = _
    rw [(Complex.imCLM.hasFDerivAt.comp y (hGd y).hasFDerivAt).fderiv]
    rfl
  set G0 : ℝ × ℝ → ℂ := fun x => (V x 0 : ℂ) * P x
  set G1 : ℝ × ℝ → ℂ := fun x => (V x 1 : ℂ) * P x
  have hG0_sm : ContDiff ℝ 1 G0 := (Complex.ofRealCLM.contDiff.comp (hVk_sm 0)).mul hP_sm
  have hG1_sm : ContDiff ℝ 1 G1 := (Complex.ofRealCLM.contDiff.comp (hVk_sm 1)).mul hP_sm
  have hG0_d : Differentiable ℝ G0 := hG0_sm.differentiable one_ne_zero
  have hG1_d : Differentiable ℝ G1 := hG1_sm.differentiable one_ne_zero
  have hG0_per : ∀ y : ℝ × ℝ, G0 (y.1 + d, y.2) = G0 y := fun y => by
    have hv0 : V (y.1 + d, y.2) 0 = V y 0 := congrFun (hV_per y) 0
    show (V (y.1 + d, y.2) 0 : ℂ) * P (y.1 + d, y.2) = (V y 0 : ℂ) * P y
    rw [hv0, hP_per y]
  have hsum_int : IntegrableOn (fun y => E0.transCx V Λ y * E y + Λ y * E0.transCx V E y)
      (B0579.cell d) := hint_lhs.add hint_rhs
  have hre_eq : (fun y => B0579.pd 0 (fun x => (G0 x).re) y + B0579.pd 1 (fun x => (G1 x).re) y) =
      fun y => (E0.transCx V Λ y * E y + Λ y * E0.transCx V E y).re := by
    funext y
    rw [pd_re 0 G0 hG0_d y, pd_re 1 G1 hG1_d y, ← Complex.add_re, hdiv_cx y]
  have him_eq : (fun y => B0579.pd 0 (fun x => (G0 x).im) y + B0579.pd 1 (fun x => (G1 x).im) y) =
      fun y => (E0.transCx V Λ y * E y + Λ y * E0.transCx V E y).im := by
    funext y
    rw [pd_im 0 G0 hG0_d y, pd_im 1 G1 hG1_d y, ← Complex.add_im, hdiv_cx y]
  have hre_zero : ∫ y in B0579.cell d,
      (E0.transCx V Λ y * E y + Λ y * E0.transCx V E y).re = 0 := by
    rw [← hre_eq]
    exact E0.cellDivZero d hd (fun x => (G0 x).re) (fun x => (G1 x).re)
      (Complex.reCLM.contDiff.comp hG0_sm) (Complex.reCLM.contDiff.comp hG1_sm)
      (fun y => congrArg Complex.re (hG0_per y))
      (Complex.reCLM.integrable_comp hP_int)
      (by rw [hre_eq]; exact Complex.reCLM.integrable_comp hsum_int)
  have him_zero : ∫ y in B0579.cell d,
      (E0.transCx V Λ y * E y + Λ y * E0.transCx V E y).im = 0 := by
    rw [← him_eq]
    exact E0.cellDivZero d hd (fun x => (G0 x).im) (fun x => (G1 x).im)
      (Complex.imCLM.contDiff.comp hG0_sm) (Complex.imCLM.contDiff.comp hG1_sm)
      (fun y => congrArg Complex.im (hG0_per y))
      (Complex.imCLM.integrable_comp hP_int)
      (by rw [him_eq]; exact Complex.imCLM.integrable_comp hsum_int)
  have hsum_zero : ∫ y in B0579.cell d,
      (E0.transCx V Λ y * E y + Λ y * E0.transCx V E y) = 0 := by
    apply Complex.ext
    · change Complex.reCLM
        (∫ y in B0579.cell d, (E0.transCx V Λ y * E y + Λ y * E0.transCx V E y)) = 0
      rw [← Complex.reCLM.integral_comp_comm hsum_int]
      exact hre_zero
    · change Complex.imCLM
        (∫ y in B0579.cell d, (E0.transCx V Λ y * E y + Λ y * E0.transCx V E y)) = 0
      rw [← Complex.imCLM.integral_comp_comm hsum_int]
      exact him_zero
  rw [integral_add hint_lhs hint_rhs] at hsum_zero
  exact eq_neg_of_add_eq_zero_left hsum_zero

/-- Complex periodic Fubini duality between `kerAdj d` and `kerVelCx d` for any `d > 0` and any
continuous, `d`-periodic, globally bounded, cell-integrable complex field `W` (adapting
`kerAdjFubini0` from `AdjFubini0.lean`). -/
private lemma kerAdj_fubini_complex {d B : ℝ} (hd0 : 0 < d) (_hB0 : 0 ≤ B)
    {F : Fin 2 → ℝ × ℝ → ℂ} (hF : ∀ l : Fin 2, IntegrableOn (F l) (B0579.cell d))
    {W : ℝ × ℝ → ℂ} (hWc : Continuous W) (hWper : ∀ y : ℝ × ℝ, W (y.1 + d, y.2) = W y)
    (hWbd : ∀ y : ℝ × ℝ, ‖W y‖ ≤ B) (hWint : IntegrableOn W (B0579.cell d)) :
    IntegrableOn (fun y => kerAdj d F y * W y) (B0579.cell d) ∧
    IntegrableOn (fun x => ∑ l : Fin 2, F l x * kerVelCx d W x l) (B0579.cell d) ∧
    (∫ y in B0579.cell d, kerAdj d F y * W y =
      ∫ x in B0579.cell d, ∑ l : Fin 2, F l x * kerVelCx d W x l) := by
  obtain ⟨C, hC0, hmeas, hper, -, hnear, hfar⟩ := kerNearFar0 d hd0
  have hL : (∫⁻ y in UnforcedLeray.Cyl.cell d, ‖W y‖ₑ) < ⊤ := by
    rw [← AdjFubiniAux.cell_eq]
    exact hWint.hasFiniteIntegral
  set M : ℝ≥0∞ := ENNReal.ofReal B * ENNReal.ofReal C +
    ENNReal.ofReal C * ∫⁻ y in UnforcedLeray.Cyl.cell d, ‖W y‖ₑ with hM
  have hMtop : M ≠ ⊤ := by
    rw [hM]
    exact (ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top,
      ENNReal.mul_lt_top ENNReal.ofReal_lt_top hL⟩).ne
  have hbound : ∀ (l : Fin 2) (x : ℝ × ℝ),
      ∫⁻ y in B0579.cell d, ‖kerD d (x - y) l‖ₑ * ‖W y‖ₑ ≤ M := by
    intro l x
    rw [AdjFubiniAux.cell_eq] at hnear hfar ⊢
    have hW_cyl : UnforcedLeray.Cyl.IsPeriodic d W := hWper
    have hGper : UnforcedLeray.Cyl.IsPeriodic d
        (fun w : ℝ × ℝ => ‖kerD d w l‖ₑ * ‖W (x - w)‖ₑ) := by
      intro w
      have h1 : W (x - (w.1 + d, w.2)) = W (x - w) := by
        have := hW_cyl.sub_eq (x - w)
        rw [← this]
        congr 1
        ext <;> simp; ring
      simp only [h1, hper w l]
    have hWper' : UnforcedLeray.Cyl.IsPeriodic d (fun y : ℝ × ℝ => ‖W y‖ₑ) :=
      fun z => by simp only [hW_cyl z]
    have e1 : ∫⁻ y in UnforcedLeray.Cyl.cell d, ‖kerD d (x - y) l‖ₑ * ‖W y‖ₑ =
        ∫⁻ w in UnforcedLeray.Cyl.cell d, ‖kerD d w l‖ₑ * ‖W (x - w)‖ₑ := by
      have := UnforcedLeray.Cyl.lintegral_cell_comp_sub_left hd0 hGper x
      rw [← this]
      exact lintegral_congr fun y => by simp
    rw [e1]
    have hmb : MeasurableSet (Metric.ball (0 : ℝ × ℝ) 1) := Metric.isOpen_ball.measurableSet
    rw [← lintegral_inter_add_sdiff _ _ hmb, hM]
    gcongr
    · calc ∫⁻ w in UnforcedLeray.Cyl.cell d ∩ Metric.ball (0 : ℝ × ℝ) 1,
            ‖kerD d w l‖ₑ * ‖W (x - w)‖ₑ
          ≤ ∫⁻ w in UnforcedLeray.Cyl.cell d ∩ Metric.ball (0 : ℝ × ℝ) 1,
              ENNReal.ofReal B * ∑ i, ‖kerD d w i‖ₑ := by
            refine setLIntegral_mono' ((UnforcedLeray.Cyl.measurableSet_cell d).inter hmb)
              fun w _ => ?_
            rw [mul_comm (ENNReal.ofReal B)]
            refine mul_le_mul'
              (Finset.single_le_sum (f := fun i => ‖kerD d w i‖ₑ)
                (fun _ _ => bot_le) (Finset.mem_univ l)) ?_
            rw [← ofReal_norm]
            exact ENNReal.ofReal_le_ofReal (hWbd _)
        _ = ENNReal.ofReal B *
              ∫⁻ w in UnforcedLeray.Cyl.cell d ∩ Metric.ball (0 : ℝ × ℝ) 1, ∑ i, ‖kerD d w i‖ₑ :=
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
        _ ≤ _ := by gcongr
    · calc ∫⁻ w in UnforcedLeray.Cyl.cell d \ Metric.ball (0 : ℝ × ℝ) 1,
            ‖kerD d w l‖ₑ * ‖W (x - w)‖ₑ
          ≤ ∫⁻ w in UnforcedLeray.Cyl.cell d \ Metric.ball (0 : ℝ × ℝ) 1,
              ENNReal.ofReal C * ‖W (x - w)‖ₑ := by
            refine setLIntegral_mono' ((UnforcedLeray.Cyl.measurableSet_cell d).diff hmb)
              fun w hw => ?_
            gcongr
            rw [← ofReal_norm, Real.norm_eq_abs]
            exact ENNReal.ofReal_le_ofReal (hfar w hw.1 hw.2 l)
        _ ≤ ∫⁻ w in UnforcedLeray.Cyl.cell d, ENNReal.ofReal C * ‖W (x - w)‖ₑ :=
            lintegral_mono_set sdiff_subset
        _ = ENNReal.ofReal C * ∫⁻ w in UnforcedLeray.Cyl.cell d, ‖W (x - w)‖ₑ :=
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
        _ = _ := by
            rw [UnforcedLeray.Cyl.lintegral_cell_comp_sub_left hd0 (G := fun y => ‖W y‖ₑ) hWper' x]
  set μ : Measure (ℝ × ℝ) := volume.restrict (B0579.cell d)
  have hkm : ∀ l : Fin 2, Measurable fun p : (ℝ × ℝ) × (ℝ × ℝ) => kerD d (p.1 - p.2) l :=
    fun l => (hmeas l).comp (measurable_fst.sub measurable_snd)
  have hHl : ∀ l : Fin 2, Integrable (fun p : (ℝ × ℝ) × (ℝ × ℝ) =>
      F l p.1 * ((kerD d (p.1 - p.2) l : ℝ) : ℂ) * W p.2) (μ.prod μ) := by
    intro l
    have hF1 : AEStronglyMeasurable (fun p : (ℝ × ℝ) × (ℝ × ℝ) => F l p.1) (μ.prod μ) :=
      (hF l).aestronglyMeasurable.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst
    have hF2 : AEStronglyMeasurable
        (fun p : (ℝ × ℝ) × (ℝ × ℝ) => ((kerD d (p.1 - p.2) l : ℝ) : ℂ)) (μ.prod μ) :=
      (Complex.measurable_ofReal.comp (hkm l)).aestronglyMeasurable
    have hF3 : AEStronglyMeasurable (fun p : (ℝ × ℝ) × (ℝ × ℝ) => W p.2) (μ.prod μ) :=
      (hWc.comp continuous_snd).aestronglyMeasurable
    have hsm : AEStronglyMeasurable
        (fun p : (ℝ × ℝ) × (ℝ × ℝ) => F l p.1 * ((kerD d (p.1 - p.2) l : ℝ) : ℂ) * W p.2)
        (μ.prod μ) := (hF1.mul hF2).mul hF3
    refine ⟨hsm, ?_⟩
    show ∫⁻ p, ‖F l p.1 * ((kerD d (p.1 - p.2) l : ℝ) : ℂ) * W p.2‖ₑ ∂(μ.prod μ) < ⊤
    rw [lintegral_prod _ hsm.enorm]
    have hin : ∀ x : ℝ × ℝ, ∫⁻ y, ‖F l x * ((kerD d (x - y) l : ℝ) : ℂ) * W y‖ₑ ∂μ ≤
        ‖F l x‖ₑ * M := by
      intro x
      calc ∫⁻ y, ‖F l x * ((kerD d (x - y) l : ℝ) : ℂ) * W y‖ₑ ∂μ
          = ∫⁻ y, ‖F l x‖ₑ * (‖kerD d (x - y) l‖ₑ * ‖W y‖ₑ) ∂μ := by
            refine lintegral_congr fun y => ?_
            simp only [enorm_mul, AdjFubiniAux.enorm_ofReal_complex, mul_assoc]
        _ = ‖F l x‖ₑ * ∫⁻ y, ‖kerD d (x - y) l‖ₑ * ‖W y‖ₑ ∂μ := by
            refine lintegral_const_mul'' _ ?_
            exact (((hmeas l).comp (measurable_const.sub measurable_id)).enorm.mul
              hWc.measurable.enorm).aemeasurable
        _ ≤ ‖F l x‖ₑ * M := by gcongr; exact hbound l x
    calc ∫⁻ x, ∫⁻ y, ‖F l x * ((kerD d (x - y) l : ℝ) : ℂ) * W y‖ₑ ∂μ ∂μ
        ≤ ∫⁻ x, ‖F l x‖ₑ * M ∂μ := lintegral_mono hin
      _ = (∫⁻ x, ‖F l x‖ₑ ∂μ) * M := lintegral_mul_const' _ _ hMtop
      _ < ⊤ := ENNReal.mul_lt_top (hF l).hasFiniteIntegral hMtop.lt_top
  set Hs : (ℝ × ℝ) → (ℝ × ℝ) → ℂ := fun x y =>
    ∑ l : Fin 2, F l x * ((kerD d (x - y) l : ℝ) : ℂ) * W y with hHs
  have hHsI : Integrable (Function.uncurry Hs) (μ.prod μ) :=
    integrable_finsetSum _ fun l _ => hHl l
  have hkey : ∀ y : ℝ × ℝ, kerAdj d F y * W y = ∫ x, Hs x y ∂μ := by
    intro y
    unfold kerAdj
    rw [← integral_mul_const]
    exact integral_congr_ae (Eventually.of_forall fun x => by simp only [hHs, Finset.sum_mul])
  have hinner : ∀ x : ℝ × ℝ, ∫ y, Hs x y ∂μ = ∑ l : Fin 2, F l x * kerVelCx d W x l := by
    intro x
    have hIy : ∀ l : Fin 2, Integrable (fun y => W y * ((kerD d (x - y) l : ℝ) : ℂ)) μ := by
      intro l
      refine ⟨(hWc.aestronglyMeasurable.mul
          (Complex.measurable_ofReal.comp
            ((hmeas l).comp (measurable_const.sub measurable_id))).aestronglyMeasurable), ?_⟩
      show ∫⁻ y, ‖W y * ((kerD d (x - y) l : ℝ) : ℂ)‖ₑ ∂μ < ⊤
      calc ∫⁻ y, ‖W y * ((kerD d (x - y) l : ℝ) : ℂ)‖ₑ ∂μ
          = ∫⁻ y, ‖kerD d (x - y) l‖ₑ * ‖W y‖ₑ ∂μ := by
            refine lintegral_congr fun y => ?_
            simp only [enorm_mul, AdjFubiniAux.enorm_ofReal_complex, mul_comm]
        _ ≤ M := hbound l x
        _ < ⊤ := hMtop.lt_top
    have e : ∀ y : ℝ × ℝ, Hs x y = ∑ l : Fin 2, F l x * (W y * ((kerD d (x - y) l : ℝ) : ℂ)) :=
      fun y => Finset.sum_congr rfl fun l _ => by ring
    simp_rw [e]
    rw [integral_finsetSum _ fun l _ => (hIy l).const_mul (F l x)]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [integral_const_mul]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · show Integrable (fun y => kerAdj d F y * W y) μ
    simp_rw [hkey]
    exact hHsI.integral_prod_right
  · show Integrable (fun x => ∑ l : Fin 2, F l x * kerVelCx d W x l) μ
    simp_rw [← hinner]
    exact hHsI.integral_prod_left
  · calc ∫ y in B0579.cell d, kerAdj d F y * W y = ∫ y, ∫ x, Hs x y ∂μ ∂μ := by
          simp_rw [hkey]; rfl
      _ = ∫ x, ∫ y, Hs x y ∂μ ∂μ := (integral_integral_swap hHsI).symm
      _ = ∫ x in B0579.cell d, ∑ l : Fin 2, F l x * kerVelCx d W x l := by
          simp_rw [hinner]; rfl

/-- **Step 3b** (SP 2912–2918): periodic Biot–Savart duality (`kerAdj` vs `kerVelCx`) on
`B0579.cell (dd ν r)` against `perE κ (dd ν r) j`. -/
private lemma step3b_euler_kerAdj_fubini (κ : PlanarFrameKernels)
    {ν m r C_tr : ℝ} (hm : 8 < m) (hν : 0 < ν) (hr : 0 ≤ r)
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)))
    (hBdd : LadTrainBdd tr m r C_tr) (i j : Fin 2) :
    let d := dd ν r
    IntegrableOn
      (fun y =>
        kerAdj d (fun l w => perLam κ d i w * (B0579.pd l (movingTrainE tr r) w : ℂ)) y *
          perE κ d j y)
      (B0579.cell d) ∧
    IntegrableOn
      (fun y =>
        perLam κ d i y *
          (kerVelCx d (perE κ d j) y 0 * (movingTrainGradE tr r y 0 : ℂ) +
            kerVelCx d (perE κ d j) y 1 * (movingTrainGradE tr r y 1 : ℂ)))
      (B0579.cell d) ∧
    (∫ y in B0579.cell d,
        kerAdj d (fun l w => perLam κ d i w * (B0579.pd l (movingTrainE tr r) w : ℂ)) y *
          perE κ d j y =
      ∫ y in B0579.cell d,
        perLam κ d i y *
          (kerVelCx d (perE κ d j) y 0 * (movingTrainGradE tr r y 0 : ℂ) +
            kerVelCx d (perE κ d j) y 1 * (movingTrainGradE tr r y 1 : ℂ))) := by
  intro d
  have ha1 : 1 ≤ clockA ν r := one_le_clockA hν.le hr
  have ha0 : 0 < clockA ν r := lt_of_lt_of_le zero_lt_one ha1
  have hsa0 : 0 < Real.sqrt (clockA ν r) := Real.sqrt_pos.2 ha0
  have hd : 0 < d := div_pos (Real.rpow_pos_of_pos hν _) hsa0
  -- Global sup bound on `perLam κ d i`
  obtain ⟨C_l, hCl0, hCl⟩ := Lam0B.lamP_translate_bound κ
  obtain ⟨B_l0, _, hBl0⟩ := perSum_sup_of_inv_sq hd hCl0 (hCl 0)
  obtain ⟨B_l1, _, hBl1⟩ := perSum_sup_of_inv_sq hd hCl0 (hCl 1)
  set B_Λ : ℝ := ‖(perGram κ d)⁻¹ i 0‖ * B_l0 + ‖(perGram κ d)⁻¹ i 1‖ * B_l1
  have hBΛ0 : 0 ≤ B_Λ := by positivity
  have hΛ_bd : ∀ w : ℝ × ℝ, ‖perLam κ d i w‖ ≤ B_Λ := by
    intro w
    unfold perLam perLam0
    rw [Fin.sum_univ_two]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    exact add_le_add
      (mul_le_mul_of_nonneg_left (hBl0 w) (norm_nonneg _))
      (mul_le_mul_of_nonneg_left (hBl1 w) (norm_nonneg _))
  -- Cell integrability of `F l w := perLam κ d i w * (pd l (movingTrainE tr r) w : ℂ)`
  set F : Fin 2 → ℝ × ℝ → ℂ :=
    fun l w => perLam κ d i w * (B0579.pd l (movingTrainE tr r) w : ℂ)
  have hF_int : ∀ l : Fin 2, IntegrableOn (F l) (B0579.cell d) := by
    intro l
    have hcont : Continuous (F l) := by
      have h1 : Continuous (perLam κ d i) := FrameCont.perLam_continuous κ hd i
      have heq : (fun w => (B0579.pd l (movingTrainE tr r) w : ℂ)) =
          fun w => (movingTrainGradE tr r w l : ℂ) :=
        funext fun w =>
          congrArg Complex.ofReal (DirectEulerSub.pd_movingTrainE_eq_movingTrainGradE tr hν hr l w)
      have h2 : Continuous (fun w => (B0579.pd l (movingTrainE tr r) w : ℂ)) := by
        rw [heq]
        exact Complex.continuous_ofReal.comp (EulerErrorSub.continuous_movingTrainGradE tr hr l)
      exact h1.mul h2
    set M_F : ℝ := B_Λ * ((clockA ν r) ^ ((5 : ℝ) / 2) * max C_tr 0)
    have hMF0 : 0 ≤ M_F := by positivity
    have hjb_bd : ∀ w ∈ B0579.cell d, B0579.jb w ^ 2 * ‖F l w‖ ≤ M_F := by
      intro w hw
      set z : ℝ × ℝ := (Real.sqrt (clockA ν r) * w.1, Real.sqrt (clockA ν r) * w.2)
      have hz_cell : z ∈ B0579.cell (ν ^ (-2 : ℝ)) := by
        simp only [B0579.cell, mem_prod, mem_Ico, mem_univ, and_true, z]
        have hmul : Real.sqrt (clockA ν r) * (d / 2) = ν ^ (-2 : ℝ) / 2 := by
          dsimp [d, dd, cellLen]
          field_simp [hsa0.ne']
        exact ⟨by linarith [mul_le_mul_of_nonneg_left hw.1.1 hsa0.le, hmul],
          by linarith [mul_lt_mul_of_pos_left hw.1.2 hsa0, hmul]⟩
      have hjb_le : B0579.jb w ≤ B0579.jb z := by
        unfold B0579.jb
        dsimp [z]
        have h1 : w.1 ^ 2 ≤ (Real.sqrt (clockA ν r) * w.1) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt ha0.le]
          exact le_mul_of_one_le_left (sq_nonneg w.1) ha1
        have h2 : w.2 ^ 2 ≤ (Real.sqrt (clockA ν r) * w.2) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt ha0.le]
          exact le_mul_of_one_le_left (sq_nonneg w.2) ha1
        linarith
      have hjb_m : B0579.jb w ^ 2 ≤ B0579.jb z ^ ((m + 2) / 2) := by
        calc B0579.jb w ^ 2 ≤ B0579.jb z ^ 2 :=
              pow_le_pow_left₀ (B0579.jb_pos w).le hjb_le 2
          _ = B0579.jb z ^ (2 : ℝ) := (Real.rpow_two _).symm
          _ ≤ B0579.jb z ^ ((m + 2) / 2) :=
              Real.rpow_le_rpow_of_exponent_le (Lam0B.jb_ge_one z) (by linarith)
      have hEc_bd : B0579.jb z ^ ((m + 2) / 2) *
          |B0579.pd l (UnforcedLeray.B0238.Ec tr r) z| ≤ max C_tr 0 :=
        ((hBdd r ⟨hr, le_rfl⟩ z hz_cell).2 l).trans (le_max_left _ _)
      have hgrad_bd : B0579.jb w ^ 2 * |B0579.pd l (movingTrainE tr r) w| ≤
          (clockA ν r) ^ ((5 : ℝ) / 2) * max C_tr 0 := by
        rw [DirectEulerSub.pd_movingTrainE_eq_movingTrainGradE tr hν hr l w]
        unfold movingTrainGradE
        rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos ha0 _), ← mul_left_comm]
        refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg ha0.le _)
        exact (mul_le_mul_of_nonneg_right hjb_m (abs_nonneg _)).trans hEc_bd
      simp only [F, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      calc B0579.jb w ^ 2 * (‖perLam κ d i w‖ * |B0579.pd l (movingTrainE tr r) w|)
          = ‖perLam κ d i w‖ * (B0579.jb w ^ 2 * |B0579.pd l (movingTrainE tr r) w|) := by ring
        _ ≤ B_Λ * ((clockA ν r) ^ ((5 : ℝ) / 2) * max C_tr 0) :=
            mul_le_mul (hΛ_bd w) hgrad_bd (by positivity) hBΛ0
    have hfin := lt_of_le_of_lt
      (DirectEulerSub.lintegral_cell_le_of_jb_sq hMF0 hjb_bd) ENNReal.ofReal_lt_top
    exact ⟨hcont.aestronglyMeasurable, hfin⟩
  -- Regularity, periodicity, bound, and cell integrability of `perE κ d j`
  obtain ⟨C_e, hCe⟩ := κ.e_decay
  obtain ⟨M_E, hME0, hME⟩ := perSum_vert_gauss_bound hd (abs_nonneg C_e) (g := κ.e j) fun z =>
    (hCe j z).trans (mul_le_mul_of_nonneg_right (le_abs_self C_e) (Real.exp_pos _).le)
  have hEc : Continuous (perE κ d j) := FrameCont.perE_continuous κ hd j
  have hEper : ∀ y : ℝ × ℝ, perE κ d j (y.1 + d, y.2) = perE κ d j y := by
    intro y
    have hp := perSum_int_period d (κ.e j) 1 y
    simp only [Int.cast_one, one_mul] at hp
    exact hp
  have hEbd : ∀ y : ℝ × ℝ, ‖perE κ d j y‖ ≤ M_E := fun y =>
    (hME y).trans (mul_le_of_le_one_right hME0
      (Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg y.2])))
  have hEint : IntegrableOn (perE κ d j) (B0579.cell d) :=
    integrableOn_of_vert_gauss hEc fun y _ => hME y
  obtain ⟨hi1, hi2, hfub⟩ := kerAdj_fubini_complex hd hME0 hF_int hEc hEper hEbd hEint
  have hrhs_eq : (fun x : ℝ × ℝ => ∑ l : Fin 2, F l x * kerVelCx d (perE κ d j) x l) =
      fun y : ℝ × ℝ =>
        perLam κ d i y *
          (kerVelCx d (perE κ d j) y 0 * (movingTrainGradE tr r y 0 : ℂ) +
            kerVelCx d (perE κ d j) y 1 * (movingTrainGradE tr r y 1 : ℂ)) := by
    funext y
    rw [Fin.sum_univ_two]
    simp only [F, DirectEulerSub.pd_movingTrainE_eq_movingTrainGradE tr hν hr _ y]
    ring
  rw [hrhs_eq] at hi2 hfub
  exact ⟨hi1, hi2, hfub⟩

/-- **Step 3 combined** (SP 2912–2918): on `B0579.cell (dd ν r)`, the Euler adjoint pairing
`∫ movEulerAdj(perLam_i) * perE_j` equals `∫ perLam_i * movL(perE_j)`. -/
private lemma step3_euler_part_eq {κ : PlanarFrameKernels} (hκ : IsSeedKernels κ)
    {ν m r C_tr : ℝ} (hm : 8 < m) (hν : 0 < ν) (hr : 0 ≤ r)
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)))
    (hBdd : LadTrainBdd tr m r C_tr) (i j : Fin 2) :
    let d := dd ν r
    IntegrableOn
      (fun y =>
        ComplCouplingEuler.movEulerAdj d (movingTrainV tr r) (movingTrainE tr r)
          (perLam κ d i) y * perE κ d j y)
      (B0579.cell d) ∧
    IntegrableOn (fun y => perLam κ d i y * movL tr r (perE κ d j) y) (B0579.cell d) ∧
    (∫ y in B0579.cell d,
        ComplCouplingEuler.movEulerAdj d (movingTrainV tr r) (movingTrainE tr r)
          (perLam κ d i) y * perE κ d j y =
      ∫ y in B0579.cell d, perLam κ d i y * movL tr r (perE κ d j) y) := by
  intro d
  obtain ⟨ht_lhs, ht_rhs, ht_eq⟩ := step3a_euler_transport_ibp hκ hν hr tr hBdd i j
  obtain ⟨hk_lhs, hk_rhs, hk_eq⟩ := step3b_euler_kerAdj_fubini κ hm hν hr tr hBdd i j
  have hlhs_eq : (fun y =>
      ComplCouplingEuler.movEulerAdj d (movingTrainV tr r) (movingTrainE tr r)
        (perLam κ d i) y * perE κ d j y) =
      fun y =>
        E0.transCx (movingTrainV tr r) (perLam κ d i) y * perE κ d j y -
          kerAdj d (fun l w => perLam κ d i w * (B0579.pd l (movingTrainE tr r) w : ℂ)) y *
            perE κ d j y := by
    funext y
    unfold ComplCouplingEuler.movEulerAdj
    ring
  have hrhs_eq : (fun y => perLam κ d i y * movL tr r (perE κ d j) y) =
      fun y =>
        -(perLam κ d i y * E0.transCx (movingTrainV tr r) (perE κ d j) y) -
          perLam κ d i y *
            (kerVelCx d (perE κ d j) y 0 * (movingTrainGradE tr r y 0 : ℂ) +
              kerVelCx d (perE κ d j) y 1 * (movingTrainGradE tr r y 1 : ℂ)) := by
    funext y
    dsimp only [d, dd]
    unfold movL E0.transCx
    ring
  have ht_neg : IntegrableOn
      (fun y => -(perLam κ d i y * E0.transCx (movingTrainV tr r) (perE κ d j) y))
      (B0579.cell d) := ht_rhs.neg
  refine ⟨by rw [hlhs_eq]; exact ht_lhs.sub hk_lhs,
    by rw [hrhs_eq]; exact ht_neg.sub hk_rhs, ?_⟩
  have hneg_int : ∫ y in B0579.cell d,
      -(perLam κ d i y * E0.transCx (movingTrainV tr r) (perE κ d j) y) =
      -∫ y in B0579.cell d, perLam κ d i y * E0.transCx (movingTrainV tr r) (perE κ d j) y :=
    integral_neg _
  rw [hlhs_eq, hrhs_eq, integral_sub ht_lhs hk_lhs, integral_sub ht_neg hk_rhs, hneg_int]
  exact congrArg₂ (· - ·) ht_eq hk_eq

/-! ## 4. Steps 4 & 5 (`task.issues`): chain rule on `physFrameLam`, planar `D^#` IBP, and
`(G⁻¹ G)' = 0` collapse -/

/-- Shifted planar `D^#` cross-integral identity: translating `y = z - (n d, 0)` expresses
`∫ (D^# λ_k)(y) e_j(y₁ + n d, y₂) dy` as `oscGramTerm κ d k j n - (d / 2) • gramTermDeriv κ d k j n`
via `OscGramIBP.integral_dualGen_mul` and `ComplCouplingHeat.gramTermDeriv_eq_shift_lamP`. -/
private lemma shifted_dualGen_cross_eq {κ : PlanarFrameKernels} (hκ : IsSeedKernels κ)
    (d : ℝ) (k j : Fin 2) (n : ℤ) :
    ∫ y : ℝ × ℝ, Gaussian.dualGen (κ.lamP k) y * κ.e j (y.1 + (n : ℝ) * d, y.2) =
      oscGramTerm κ d k j n + (-(d / 2) : ℝ) • ComplCouplingHeat.gramTermDeriv κ d k j n := by
  obtain ⟨hCD, C, hC0, h0, h1, h2⟩ :=
    ComplCouplingHeat.seedLamP_jet2_bounds_of κ (seedLamPJet2Decay_all κ) hκ
  obtain ⟨hsm_e, hdec_e⟩ := OscillatorForceSub.seed_e_smooth_decay hκ
  obtain ⟨Ce, hCe⟩ := κ.e_decay
  set a : ℝ := (n : ℝ) * d
  set c₀ : ℝ × ℝ := (a, 0)
  set L : ℝ × ℝ → ℂ := κ.lamP k
  set L_a : ℝ × ℝ → ℂ := fun z => L (z - c₀)
  have hLa_sm : ContDiff ℝ 2 L_a := (hCD k).comp (contDiff_id.sub contDiff_const)
  have hfderiv_La : ∀ z : ℝ × ℝ, fderiv ℝ L_a z = fderiv ℝ L (z - c₀) := by
    intro z
    have hL_d : DifferentiableAt ℝ L (z - c₀) := ((hCD k).differentiable (by norm_num)) (z - c₀)
    exact (hL_d.hasFDerivAt.comp z ((hasFDerivAt_id z).sub_const c₀)).fderiv
  have hiter2_La : ∀ z : ℝ × ℝ, iteratedFDeriv ℝ 2 L_a z = iteratedFDeriv ℝ 2 L (z - c₀) :=
    fun z => iteratedFDeriv_comp_sub (𝕜 := ℝ) (f := L) 2 c₀ z
  have hw1 : ∀ w : ℝ × ℝ, ((1 + |w.1| + |w.2|)⁻¹) ^ 2 ≤ 1 := fun w => by
    have h1w : 1 ≤ 1 + |w.1| + |w.2| := by linarith [abs_nonneg w.1, abs_nonneg w.2]
    have hi : (1 + |w.1| + |w.2|)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h1w
    have hi0 : 0 ≤ (1 + |w.1| + |w.2|)⁻¹ := by positivity
    nlinarith
  set Ca : ℝ := (1 + ‖c₀‖) * C
  have hLa0 : ∀ z : ℝ × ℝ, ‖L_a z‖ ≤ Ca := fun z => by
    have hb : ‖L (z - c₀)‖ ≤ C := (h0 k (z - c₀)).trans (mul_le_of_le_one_right hC0 (hw1 _))
    calc ‖L (z - c₀)‖ ≤ C := hb
      _ ≤ (1 + ‖c₀‖) * C := le_mul_of_one_le_left hC0 (by linarith [norm_nonneg c₀])
  have hLa1 : ∀ z : ℝ × ℝ, (1 + ‖z‖) * ‖fderiv ℝ L_a z‖ ≤ Ca := fun z => by
    rw [hfderiv_La z]
    have hzn : 1 + ‖z‖ ≤ (1 + ‖c₀‖) * (1 + ‖z - c₀‖) := by
      have htri : ‖z‖ ≤ ‖z - c₀‖ + ‖c₀‖ := by
        simpa [sub_add_cancel] using norm_add_le (z - c₀) c₀
      nlinarith [norm_nonneg (z - c₀), norm_nonneg c₀]
    have hb : (1 + ‖z - c₀‖) * ‖fderiv ℝ L (z - c₀)‖ ≤ C :=
      (h1 k (z - c₀)).trans (mul_le_of_le_one_right hC0 (hw1 _))
    calc (1 + ‖z‖) * ‖fderiv ℝ L (z - c₀)‖
        ≤ ((1 + ‖c₀‖) * (1 + ‖z - c₀‖)) * ‖fderiv ℝ L (z - c₀)‖ :=
          mul_le_mul_of_nonneg_right hzn (norm_nonneg _)
      _ = (1 + ‖c₀‖) * ((1 + ‖z - c₀‖) * ‖fderiv ℝ L (z - c₀)‖) := by ring
      _ ≤ (1 + ‖c₀‖) * C := mul_le_mul_of_nonneg_left hb (by positivity)
  have hLa2 : ∀ z : ℝ × ℝ, ‖iteratedFDeriv ℝ 2 L_a z‖ ≤ Ca := fun z => by
    rw [hiter2_La z]
    have hb : ‖iteratedFDeriv ℝ 2 L (z - c₀)‖ ≤ C :=
      (h2 k (z - c₀)).trans (mul_le_of_le_one_right hC0 (hw1 _))
    exact hb.trans (le_mul_of_one_le_left hC0 (by linarith [norm_nonneg c₀]))
  obtain ⟨B0, hB0, hb0⟩ := hdec_e j 0
  obtain ⟨B1, hB1, hb1⟩ := hdec_e j 1
  obtain ⟨B2, hB2, hb2⟩ := hdec_e j 2
  have he_sm2 : ContDiff ℝ 2 (κ.e j) := (hsm_e j).of_le (by simp)
  have hibp := OscGramIBP.integral_dualGen_mul (L := L_a) (e := κ.e j)
    hLa_sm he_sm2 hLa0 hLa1 hLa2
    (B := B0 + B1 + B2)
    (fun y => by
      have h := hb0 y; rw [norm_iteratedFDeriv_zero] at h
      exact h.trans (mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le))
    (fun y => by
      have h := hb1 y; rw [norm_iteratedFDeriv_one] at h
      exact h.trans (mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le))
    (fun y => (le_mul_of_one_le_left (norm_nonneg _) (by linarith [norm_nonneg y])).trans
      ((hb2 y).trans (mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le)))
  -- Pointwise relation between `Gaussian.dualGen L (z - c₀)` and `Gaussian.dualGen L_a z`
  have hdual_pt : ∀ z : ℝ × ℝ,
      Gaussian.dualGen L (z - c₀) =
        Gaussian.dualGen L_a z + (a / 2 : ℝ) • pdCx 0 L (z - c₀) := by
    intro z
    have hlap : Cyl.laplacian L_a z = Cyl.laplacian L (z - c₀) := by
      rw [Gaussian.laplacian_eq_iteratedFDeriv hLa_sm,
        Gaussian.laplacian_eq_iteratedFDeriv (hCD k), hiter2_La z]
    have hc0_dir : c₀ = a • B0579.dir 0 := by ext <;> simp [c₀, B0579.dir]
    have hfd : fderiv ℝ L (z - c₀) (z - c₀) =
        fderiv ℝ L_a z z - a • pdCx 0 L (z - c₀) := by
      rw [map_sub, hfderiv_La z, hc0_dir, map_smul]
      rfl
    unfold Gaussian.dualGen
    rw [hlap, hfd]
    dsimp only [L_a]
    rw [smul_sub, smul_smul]
    simp only [Complex.real_smul]
    push_cast
    ring
  -- Integrability of `z ↦ Gaussian.dualGen L (z - c₀) * κ.e j z` and the shift-derivative piece
  have hΨc : Continuous (Gaussian.dualGen L) := ComplCouplingHeat.continuous_dualGen (hCD k)
  have hΨb : ∀ y : ℝ × ℝ,
      ‖Gaussian.dualGen L y‖ ≤ (7 / 2 * C) * (1 + |y.1| + |y.2|)⁻¹ ^ 2 :=
    fun y => ComplCouplingHeat.norm_dualGen_le_inv_sq (hCD k) (h0 k) (h1 k) (h2 k) y
  have hint_orig : Integrable (fun y : ℝ × ℝ => Gaussian.dualGen L y * κ.e j (y.1 + a, y.2)) :=
    (OscGramDual.cross_int hΨc (κ.e_cont j) hΨb (hCe j) a).1
  have hint_shift : Integrable (fun z : ℝ × ℝ => Gaussian.dualGen L (z - c₀) * κ.e j z) := by
    have h := hint_orig.comp_sub_right c₀
    refine h.congr (Eventually.of_forall fun z => ?_)
    dsimp only
    have h1' : (z - c₀).1 + a = z.1 := by simp [c₀, sub_add_cancel]
    have h2' : (z - c₀).2 = z.2 := by simp [c₀]
    rw [show ((z - c₀).1 + a, (z - c₀).2) = z from Prod.ext h1' h2']
  have hint_pd : Integrable (fun z : ℝ × ℝ => ((a / 2 : ℝ) • pdCx 0 L (z - c₀)) * κ.e j z) := by
    have hpd_c : Continuous (fun z : ℝ × ℝ => pdCx 0 L (z - c₀)) := by
      have heq : pdCx 0 L = fun w => fderiv ℝ L w (B0579.dir 0) := rfl
      rw [heq]
      exact (((hCD k).continuous_fderiv (by norm_num)).clm_apply continuous_const).comp
        (continuous_id.sub continuous_const)
    have hc_prod : Continuous (fun z : ℝ × ℝ => ((a / 2 : ℝ) • pdCx 0 L (z - c₀)) * κ.e j z) :=
      (hpd_c.const_smul (a / 2 : ℝ)).mul (κ.e_cont j)
    refine ((OscGramIBP.integrable_gw).const_mul (|(a / 2 : ℝ)| * C * |Ce|)).mono'
      hc_prod.aestronglyMeasurable (Eventually.of_forall fun z => ?_)
    have hpd_le : ‖pdCx 0 L (z - c₀)‖ ≤ C := by
      have hn_dir : ‖B0579.dir 0‖ ≤ 1 := by simp [B0579.dir]
      have hle1 : ‖pdCx 0 L (z - c₀)‖ ≤ ‖fderiv ℝ L (z - c₀)‖ := by
        calc ‖fderiv ℝ L (z - c₀) (B0579.dir 0)‖
            ≤ ‖fderiv ℝ L (z - c₀)‖ * ‖B0579.dir 0‖ := ContinuousLinearMap.le_opNorm _ _
          _ ≤ ‖fderiv ℝ L (z - c₀)‖ * 1 := mul_le_mul_of_nonneg_left hn_dir (norm_nonneg _)
          _ = ‖fderiv ℝ L (z - c₀)‖ := mul_one _
      have hle2 : ‖fderiv ℝ L (z - c₀)‖ ≤ (1 + ‖z - c₀‖) * ‖fderiv ℝ L (z - c₀)‖ :=
        le_mul_of_one_le_left (norm_nonneg _) (by linarith [norm_nonneg (z - c₀)])
      exact (hle1.trans hle2).trans
        ((h1 k (z - c₀)).trans (mul_le_of_le_one_right hC0 (hw1 _)))
    have he_le : ‖κ.e j z‖ ≤ |Ce| * OscGramIBP.gw z :=
      (hCe j z).trans (mul_le_mul_of_nonneg_right (le_abs_self Ce) (Real.exp_pos _).le)
    rw [norm_mul, norm_smul, Real.norm_eq_abs]
    calc |a / 2| * ‖pdCx 0 L (z - c₀)‖ * ‖κ.e j z‖
        ≤ (|a / 2| * C) * (|Ce| * OscGramIBP.gw z) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hpd_le (abs_nonneg _)) he_le
            (norm_nonneg _) (by positivity)
      _ = (|a / 2| * C * |Ce|) * OscGramIBP.gw z := by ring
  have hint_La : Integrable (fun z : ℝ × ℝ => Gaussian.dualGen L_a z * κ.e j z) := by
    have heq : (fun z : ℝ × ℝ => Gaussian.dualGen L_a z * κ.e j z) =
        fun z => Gaussian.dualGen L (z - c₀) * κ.e j z -
          ((a / 2 : ℝ) • pdCx 0 L (z - c₀)) * κ.e j z := by
      funext z
      rw [hdual_pt z, add_mul, add_sub_cancel_right]
    rw [heq]
    exact hint_shift.sub hint_pd
  -- Translate the LHS integral and split
  have hshift_lhs :
      ∫ y : ℝ × ℝ, Gaussian.dualGen L y * κ.e j (y.1 + a, y.2) =
        ∫ z : ℝ × ℝ, Gaussian.dualGen L (z - c₀) * κ.e j z := by
    have h := integral_sub_right_eq_self (μ := (volume : Measure (ℝ × ℝ)))
      (fun y : ℝ × ℝ => Gaussian.dualGen L y * κ.e j (y.1 + a, y.2)) c₀
    rw [← h]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    dsimp only
    have h1' : (z - c₀).1 + a = z.1 := by simp [c₀, sub_add_cancel]
    have h2' : (z - c₀).2 = z.2 := by simp [c₀]
    rw [show ((z - c₀).1 + a, (z - c₀).2) = z from Prod.ext h1' h2']
  have hshift_osc :
      ∫ z : ℝ × ℝ, L_a z * movD (κ.e j) z = oscGramTerm κ d k j n := by
    unfold oscGramTerm
    have h := integral_sub_right_eq_self (μ := (volume : Measure (ℝ × ℝ)))
      (fun y : ℝ × ℝ => L y * movD (κ.e j) (y.1 + a, y.2)) c₀
    rw [← h]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    dsimp only [L_a, L, a]
    have h1' : (z - c₀).1 + (n : ℝ) * d = z.1 := by simp [c₀, a, sub_add_cancel]
    have h2' : (z - c₀).2 = z.2 := by simp [c₀]
    rw [show ((z - c₀).1 + (n : ℝ) * d, (z - c₀).2) = z from Prod.ext h1' h2']
  have hshift_gram :
      ∫ z : ℝ × ℝ, ((a / 2 : ℝ) • pdCx 0 L (z - c₀)) * κ.e j z =
        (-(d / 2) : ℝ) • ComplCouplingHeat.gramTermDeriv κ d k j n := by
    rw [ComplCouplingHeat.gramTermDeriv_eq_shift_lamP κ d k j n, ← integral_smul]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    have hzc : z - c₀ = (z.1 - (n : ℝ) * d, z.2) := by ext <;> simp [c₀, a]
    dsimp only [L, a]
    rw [hzc, Complex.real_smul, Complex.real_smul, Complex.real_smul]
    push_cast
    ring
  calc ∫ y : ℝ × ℝ, Gaussian.dualGen L y * κ.e j (y.1 + a, y.2)
      = ∫ z : ℝ × ℝ, Gaussian.dualGen L (z - c₀) * κ.e j z := hshift_lhs
    _ = ∫ z : ℝ × ℝ,
          (Gaussian.dualGen L_a z * κ.e j z +
            ((a / 2 : ℝ) • pdCx 0 L (z - c₀)) * κ.e j z) := by
        refine integral_congr_ae (Eventually.of_forall fun z => ?_)
        dsimp only
        rw [hdual_pt z, add_mul]
    _ = (∫ z : ℝ × ℝ, Gaussian.dualGen L_a z * κ.e j z) +
          ∫ z : ℝ × ℝ, ((a / 2 : ℝ) • pdCx 0 L (z - c₀)) * κ.e j z :=
        integral_add hint_La hint_pd
    _ = oscGramTerm κ d k j n +
          (-(d / 2) : ℝ) • ComplCouplingHeat.gramTermDeriv κ d k j n := by
        rw [hibp, hshift_osc, hshift_gram]

/-- **Steps 4 & 5** (SP 2891–2897, 2905–2918): chain rule on `physFrameLam`, periodized `D^#` IBP,
and `(G⁻¹ G)' = 0` collapse yield
`∫_{cell d} movLamDualHeat κ ν r i * perE κ d j = ∫_{cell d} perLam κ d i * movOscRes κ ν r j`. -/
private lemma step4_5_heat_part_eq {κ : PlanarFrameKernels} (hκ : IsSeedKernels κ)
    {ν r : ℝ} (hν : 0 < ν) (hr : 0 ≤ r) (hU : IsUnit (perGram κ (dd ν r))) (i j : Fin 2) :
    let d := dd ν r
    IntegrableOn (fun y => movLamDualHeat κ ν r i y * perE κ d j y) (B0579.cell d) ∧
    IntegrableOn (fun y => perLam κ d i y * movOscRes κ ν r j y) (B0579.cell d) ∧
    (∫ y in B0579.cell d, movLamDualHeat κ ν r i y * perE κ d j y =
      ∫ y in B0579.cell d, perLam κ d i y * movOscRes κ ν r j y) := by
  intro d
  have ha1 : 1 ≤ clockA ν r := one_le_clockA hν.le hr
  have ha0 : 0 < clockA ν r := lt_of_lt_of_le zero_lt_one ha1
  have hd : 0 < d := div_pos (Real.rpow_pos_of_pos hν _) (Real.sqrt_pos.2 ha0)
  obtain ⟨hCD, C, _, h0, h1, h2⟩ :=
    ComplCouplingHeat.seedLamP_jet2_bounds_of κ (seedLamPJet2Decay_all κ) hκ
  obtain ⟨ht0_0, ht1_0, ht2_0⟩ := ComplCouplingHeat.translate_jet2_bounds (h0 0) (h1 0) (h2 0)
  obtain ⟨ht0_1, ht1_1, ht2_1⟩ := ComplCouplingHeat.translate_jet2_bounds (h0 1) (h1 1) (h2 1)
  have ht0 : ∀ (k : Fin 2) (z : ℝ × ℝ), ‖κ.lamP k z‖ ≤ |C| * (1 + |z.1|) ^ (-(2 : ℝ)) := by
    intro k; fin_cases k
    · exact ht0_0
    · exact ht0_1
  have ht1 : ∀ (k : Fin 2) (z : ℝ × ℝ),
      (1 + ‖z‖) * ‖fderiv ℝ (κ.lamP k) z‖ ≤ |C| * (1 + |z.1|) ^ (-(2 : ℝ)) := by
    intro k; fin_cases k
    · exact ht1_0
    · exact ht1_1
  have ht2 : ∀ (k : Fin 2) (z : ℝ × ℝ),
      ‖iteratedFDeriv ℝ 2 (κ.lamP k) z‖ ≤ |C| * (1 + |z.1|) ^ (-(2 : ℝ)) := by
    intro k; fin_cases k
    · exact ht2_0
    · exact ht2_1
  obtain ⟨G_inv', hG_der, hG_orth⟩ := hasDerivAt_perGram_inv_and_orth hκ hd hU
  -- Differentiability of `s ↦ (perGram κ (cellLen (ν⁻²) (clockA ν s)))⁻¹ i k` on `Ici r` at `r`
  have hG_diffW : ∀ k : Fin 2,
      DifferentiableWithinAt ℝ
        (fun s => (perGram κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)))⁻¹ i k) (Ici r) r :=
    fun k => (DirectHeatDecomp.hasDerivAt_perGram_inv_comp_cellLen κ hν hr i k
      (hG_der i k)).differentiableAt.differentiableWithinAt
  have hpt_heat : ∀ y : ℝ × ℝ,
      movLamDualHeat κ ν r i y =
        (∑ k : Fin 2, (perGram κ d)⁻¹ i k * movLam0DualHeat κ ν r k y) +
        (∑ k : Fin 2, movGramInvDeriv κ ν r i k * perLam0 κ d k y) :=
    fun y => DirectHeatDecomp.movLamDualHeat_eq_sum_of_diff κ hν hr hCD ht0 ht1 ht2 i hG_diffW y
  have hid0 : ∀ (k : Fin 2) (y : ℝ × ℝ),
      movLam0DualHeat κ ν r k y =
        (clockTheta ν r : ℂ)⁻¹ * perSum d (Gaussian.dualGen (κ.lamP k)) y :=
    fun k y => ComplCouplingHeat.movLam0DualHeat_eq_inv_clockTheta_mul_perSum_dualGen κ hν hr k
      (hCD k) (ht0 k) (ht1 k) (ht2 k) y
  -- Integrability and exact evaluation of `∫_{cell d} movLam0DualHeat κ ν r k * perE κ d j`
  obtain ⟨Ce, hCe⟩ := κ.e_decay
  have hint0_and_eval : ∀ k : Fin 2,
      IntegrableOn (fun y => movLam0DualHeat κ ν r k y * perE κ d j y) (B0579.cell d) ∧
      (∫ y in B0579.cell d, movLam0DualHeat κ ν r k y * perE κ d j y =
        (clockTheta ν r : ℂ)⁻¹ * oscGram κ d k j +
          (-(1 / 2) * (clockTheta ν r)⁻¹ * d : ℝ) • ComplCouplingHeat.perGramDeriv κ d k j) := by
    intro k
    have hΨc : Continuous (Gaussian.dualGen (κ.lamP k)) :=
      ComplCouplingHeat.continuous_dualGen (hCD k)
    have hΨb : ∀ y : ℝ × ℝ,
        ‖Gaussian.dualGen (κ.lamP k) y‖ ≤ (7 / 2 * C) * (1 + |y.1| + |y.2|)⁻¹ ^ 2 :=
      fun y => ComplCouplingHeat.norm_dualGen_le_inv_sq (hCD k) (h0 k) (h1 k) (h2 k) y
    have hΨt : ∀ z : ℝ × ℝ,
        ‖Gaussian.dualGen (κ.lamP k) z‖ ≤ |7 / 2 * C| * (1 + |z.1|) ^ (-(2 : ℝ)) := by
      intro z
      have h1z : 1 + |z.1| ≤ 1 + |z.1| + |z.2| := by linarith [abs_nonneg z.2]
      have hinv : (1 + |z.1| + |z.2|)⁻¹ ≤ (1 + |z.1|)⁻¹ :=
        inv_anti₀ (by positivity) h1z
      have hsq : ((1 + |z.1| + |z.2|)⁻¹) ^ 2 ≤ (1 + |z.1|) ^ (-(2 : ℝ)) := by
        rw [Real.rpow_neg (by positivity), Real.rpow_two, ← inv_pow]
        exact pow_le_pow_left₀ (by positivity) hinv 2
      exact (hΨb z).trans (mul_le_mul (le_abs_self _) hsq (by positivity) (abs_nonneg _))
    obtain ⟨B_Ψ, hBΨ0, hb_Ψ⟩ := perSum_sup_of_inv_sq hd (abs_nonneg _) hΨt
    obtain ⟨M_E, _, hME⟩ := perSum_vert_gauss_bound hd (abs_nonneg Ce) (g := κ.e j) fun z =>
      (hCe j z).trans (mul_le_mul_of_nonneg_right (le_abs_self Ce) (Real.exp_pos _).le)
    have hperΨ_c : Continuous (perSum d (Gaussian.dualGen (κ.lamP k))) :=
      FrameCont.perSum_continuous hΨc hΨt hd.ne'
    have hint_perΨ : IntegrableOn
        (fun y => perSum d (Gaussian.dualGen (κ.lamP k)) y * perE κ d j y) (B0579.cell d) := by
      refine integrableOn_of_vert_gauss (M := B_Ψ * M_E)
        (hperΨ_c.mul (FrameCont.perE_continuous κ hd j)) fun y _ => ?_
      rw [norm_mul]
      calc ‖perSum d (Gaussian.dualGen (κ.lamP k)) y‖ * ‖perE κ d j y‖
          ≤ B_Ψ * (M_E * Real.exp (-y.2 ^ 2 / 8)) :=
            mul_le_mul (hb_Ψ y) (hME y) (norm_nonneg _) hBΨ0
        _ = (B_Ψ * M_E) * Real.exp (-y.2 ^ 2 / 8) := by ring
    have hfeq : (fun y => movLam0DualHeat κ ν r k y * perE κ d j y) =
        fun y => (clockTheta ν r : ℂ)⁻¹ *
          (perSum d (Gaussian.dualGen (κ.lamP k)) y * perE κ d j y) := by
      funext y
      rw [hid0 k y]
      ring
    have hint_k : IntegrableOn (fun y => movLam0DualHeat κ ν r k y * perE κ d j y) (B0579.cell d) := by
      rw [hfeq]
      exact hint_perΨ.const_mul _
    refine ⟨hint_k, ?_⟩
    obtain ⟨hsum_dual, hunf_dual⟩ := OscGramDual.unfold hΨc (κ.e_cont j) hΨb (hCe j) hd
    obtain ⟨hsum_osc, hunf_osc⟩ := OscGramSub.oscGram_unfold hκ hd k j
    have hterm_eq : ∀ n : ℤ,
        ∫ y : ℝ × ℝ, Gaussian.dualGen (κ.lamP k) y * κ.e j (y.1 + (n : ℝ) * d, y.2) =
          oscGramTerm κ d k j n +
            (-(d / 2) : ℝ) • ComplCouplingHeat.gramTermDeriv κ d k j n :=
      fun n => shifted_dualGen_cross_eq hκ d k j n
    have hsum_smul : Summable
        (fun n : ℤ => (-(d / 2) : ℝ) • ComplCouplingHeat.gramTermDeriv κ d k j n) := by
      have heq_s : (fun n : ℤ => (-(d / 2) : ℝ) • ComplCouplingHeat.gramTermDeriv κ d k j n) =
          fun n : ℤ =>
            (∫ y : ℝ × ℝ, Gaussian.dualGen (κ.lamP k) y * κ.e j (y.1 + (n : ℝ) * d, y.2)) -
              oscGramTerm κ d k j n := by
        funext n
        rw [hterm_eq n, add_sub_cancel_left]
      rw [heq_s]
      exact hsum_dual.sub hsum_osc
    have hpair_eq : ∫ y in B0579.cell d, perSum d (Gaussian.dualGen (κ.lamP k)) y * perE κ d j y =
        oscGram κ d k j + (-(d / 2) : ℝ) • ComplCouplingHeat.perGramDeriv κ d k j := by
      change ∫ x in B0579.cell d, perSum d (Gaussian.dualGen (κ.lamP k)) x * perSum d (κ.e j) x = _
      rw [hunf_dual, show (fun n : ℤ => ∫ y : ℝ × ℝ,
          Gaussian.dualGen (κ.lamP k) y * κ.e j (y.1 + (n : ℝ) * d, y.2)) =
          fun n : ℤ => oscGramTerm κ d k j n +
            (-(d / 2) : ℝ) • ComplCouplingHeat.gramTermDeriv κ d k j n from funext hterm_eq,
        hsum_osc.tsum_add hsum_smul, tsum_const_smul'' (-(d / 2) : ℝ), ← hunf_osc]
      rfl
    rw [hfeq, integral_const_mul, hpair_eq, mul_add]
    congr 1
    rw [Complex.real_smul, Complex.real_smul, ← Complex.ofReal_inv]
    push_cast
    ring
  -- Integrability of `perLam0 κ d k * movOscRes κ ν r j` on `B0579.cell d`
  obtain ⟨hcontD, C_D, hCD0, hCD_dec⟩ := OscGramSub.movD_seed_uniform_decay hκ
  obtain ⟨C_l, hCl0, hCl⟩ := Lam0B.lamP_translate_bound κ
  have hint_osc0 : ∀ k : Fin 2,
      IntegrableOn (fun y => perLam0 κ d k y * movOscRes κ ν r j y) (B0579.cell d) := by
    intro k
    obtain ⟨B_lk, hBlk0, hBlk⟩ := perSum_sup_of_inv_sq hd hCl0 (hCl k)
    obtain ⟨M_D, _, hMD⟩ := perSum_vert_gauss_bound hd hCD0 (g := movD (κ.e j)) (hCD_dec j)
    have hperD_c : Continuous (perSum d (movD (κ.e j))) :=
      FrameCont.perSum_continuous (hcontD j)
        (fun z => (hCD_dec j z).trans (by
          have htw := FrameCont.exp_le_translate_weight z.1 z.2
          calc C_D * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8)
              ≤ C_D * (16 * (1 + |z.1|) ^ (-(2 : ℝ))) := mul_le_mul_of_nonneg_left htw hCD0
            _ = (16 * C_D) * (1 + |z.1|) ^ (-(2 : ℝ)) := by ring)) hd.ne'
    have hosc_eq : movOscRes κ ν r j =
        fun y => (clockTheta ν r : ℂ)⁻¹ * perSum d (movD (κ.e j)) y :=
      funext (OscillatorForceSub.movOscRes_eq_perSum_movD hκ hν hr j)
    have hint_D : IntegrableOn (fun y => perLam0 κ d k y * perSum d (movD (κ.e j)) y)
        (B0579.cell d) := by
      refine integrableOn_of_vert_gauss (M := B_lk * M_D)
        ((Lam0B.perLam0_continuous κ hd k).mul hperD_c) fun y _ => ?_
      rw [norm_mul]
      calc ‖perLam0 κ d k y‖ * ‖perSum d (movD (κ.e j)) y‖
          ≤ B_lk * (M_D * Real.exp (-y.2 ^ 2 / 8)) :=
            mul_le_mul (hBlk y) (hMD y) (norm_nonneg _) hBlk0
        _ = (B_lk * M_D) * Real.exp (-y.2 ^ 2 / 8) := by ring
    have hfeq : (fun y => perLam0 κ d k y * movOscRes κ ν r j y) =
        fun y => (clockTheta ν r : ℂ)⁻¹ * (perLam0 κ d k y * perSum d (movD (κ.e j)) y) := by
      funext y
      rw [hosc_eq]
      ring
    rw [hfeq]
    exact hint_D.const_mul _
  -- Integrability and decomposition of LHS and RHS
  have hlhs_decomp : (fun y => movLamDualHeat κ ν r i y * perE κ d j y) =
      fun y =>
        (∑ k : Fin 2, (perGram κ d)⁻¹ i k * (movLam0DualHeat κ ν r k y * perE κ d j y)) +
        (∑ k : Fin 2, movGramInvDeriv κ ν r i k * (perLam0 κ d k y * perE κ d j y)) := by
    funext y
    rw [hpt_heat y, add_mul, Finset.sum_mul, Finset.sum_mul]
    congr 1 <;> exact Finset.sum_congr rfl fun k _ => by ring
  have hint_a : IntegrableOn
      (fun y => ∑ k : Fin 2, (perGram κ d)⁻¹ i k * (movLam0DualHeat κ ν r k y * perE κ d j y))
      (B0579.cell d) :=
    integrable_finsetSum _ fun k _ => ((hint0_and_eval k).1).const_mul _
  have hint_b : IntegrableOn
      (fun y => ∑ k : Fin 2, movGramInvDeriv κ ν r i k * (perLam0 κ d k y * perE κ d j y))
      (B0579.cell d) :=
    integrable_finsetSum _ fun k _ => (integrableOn_perLam0_mul_perE_pos κ hd k j).const_mul _
  have hrhs_decomp : (fun y => perLam κ d i y * movOscRes κ ν r j y) =
      fun y => ∑ k : Fin 2, (perGram κ d)⁻¹ i k * (perLam0 κ d k y * movOscRes κ ν r j y) := by
    funext y
    unfold perLam
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hint_rhs : IntegrableOn (fun y => perLam κ d i y * movOscRes κ ν r j y) (B0579.cell d) := by
    rw [hrhs_decomp]
    exact integrable_finsetSum _ fun k _ => (hint_osc0 k).const_mul _
  refine ⟨by rw [hlhs_decomp]; exact hint_a.add hint_b, hint_rhs, ?_⟩
  -- Collapse via `(G⁻¹ G)' = 0` (`hG_orth i j`) and `OscGramSub.integral_perLam0_mul_movOscRes_eq`
  rw [hlhs_decomp, integral_add hint_a hint_b,
    integral_finsetSum _ fun k _ => ((hint0_and_eval k).1).const_mul _,
    integral_finsetSum _ fun k _ => (integrableOn_perLam0_mul_perE_pos κ hd k j).const_mul _,
    hrhs_decomp,
    integral_finsetSum _ fun k _ => (hint_osc0 k).const_mul _]
  have h1_sum : (∑ k : Fin 2, (perGram κ d)⁻¹ i k *
      ∫ y in B0579.cell d, (movLam0DualHeat κ ν r k y * perE κ d j y)) =
      (∑ k : Fin 2, (perGram κ d)⁻¹ i k *
        ((clockTheta ν r : ℂ)⁻¹ * oscGram κ d k j)) +
      ∑ k : Fin 2, (-(1 / 2) * (clockTheta ν r)⁻¹ * d : ℝ) •
        ((perGram κ d)⁻¹ i k * ComplCouplingHeat.perGramDeriv κ d k j) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [(hint0_and_eval k).2, mul_add, Complex.real_smul, Complex.real_smul]
    ring
  have h2_sum : (∑ k : Fin 2, movGramInvDeriv κ ν r i k *
      ∫ y in B0579.cell d, (perLam0 κ d k y * perE κ d j y)) =
      ∑ k : Fin 2, (-(1 / 2) * (clockTheta ν r)⁻¹ * d : ℝ) •
        (G_inv' i k * perGram κ d k j) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    have hmv := DirectHeatDecomp.movGramInvDeriv_eq_of_hasDerivAt κ hν hr i k (hG_der i k)
    change movGramInvDeriv κ ν r i k * perGram κ d k j = _
    rw [hmv, show cellLen (ν ^ (-2 : ℝ)) (clockA ν r) = d from rfl,
      Complex.real_smul, Complex.real_smul]
    ring
  have hcancel :
      (∑ k : Fin 2, (-(1 / 2) * (clockTheta ν r)⁻¹ * d : ℝ) •
        ((perGram κ d)⁻¹ i k * ComplCouplingHeat.perGramDeriv κ d k j)) +
      (∑ k : Fin 2, (-(1 / 2) * (clockTheta ν r)⁻¹ * d : ℝ) •
        (G_inv' i k * perGram κ d k j)) = 0 := by
    have horth := hG_orth i j
    simp only [Fin.sum_univ_two, Complex.real_smul] at horth ⊢
    linear_combination (((-(1 / 2) * (clockTheta ν r)⁻¹ * d : ℝ) : ℂ)) * horth
  have hosc_sum :
      (∑ k : Fin 2, (perGram κ d)⁻¹ i k *
        ((clockTheta ν r : ℂ)⁻¹ * oscGram κ d k j)) =
      ∑ k : Fin 2, ∫ y in B0579.cell d,
        (perGram κ d)⁻¹ i k * (perLam0 κ d k y * movOscRes κ ν r j y) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_const_mul]
    congr 1
    exact (OscGramSub.integral_perLam0_mul_movOscRes_eq hκ hν hr k j).symm
  simp_rw [integral_const_mul] at hosc_sum ⊢
  rw [h1_sum, h2_sum, add_assoc, hcancel, add_zero, hosc_sum]

/-! ## 5. Main mode-identity theorems (`SP 2915–2918`) -/

/-- **Pointwise-in-`r` `H₀ E = Λ K₀` identity** (SP 2915–2918): for any Part I seed kernel `κ`,
planar data `P`, `m > 8`, `ν > 0`, `r ≥ 0` with `IsUnit (perGram κ (dd ν r))` and
`LadTrainBdd tr m r C_tr`, `movH0 κ tr r i (perE κ (dd ν r) j)` equals the moving-cell pairing of
`perLam κ (dd ν r) i` with `movOscRes + movEulerRes + modeEigen * perE`. -/
theorem h0ModeIdentity_of_isUnit (κ : PlanarFrameKernels) (P : PlanarData)
    {ν m r C_tr : ℝ} (hκ : IsSeedKernels κ) (hm : 8 < m) (hν : 0 < ν) (hr : 0 ≤ r)
    (hU : IsUnit (perGram κ (dd ν r)))
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)))
    (hBdd : LadTrainBdd tr m r C_tr) (i j : Fin 2) :
    movH0 κ tr r i (perE κ (dd ν r) j) =
      ∫ y in movingCell ν (ν ^ (-2 : ℝ)) r, perLam κ (dd ν r) i y *
        (movOscRes κ ν r j y + movEulerRes κ P tr r j y + modeEigen P j * perE κ (dd ν r) j y) := by
  rw [step2_movH0_pullback_split κ hν hr tr i j]
  obtain ⟨hH_lhs, hH_rhs, hH_eq⟩ := step4_5_heat_part_eq hκ hν hr hU i j
  obtain ⟨hE_lhs, hE_rhs, hE_eq⟩ := step3_euler_part_eq hκ hm hν hr tr hBdd i j
  have hlhs_add : (fun y =>
      (movLamDualHeat κ ν r i y +
        ComplCouplingEuler.movEulerAdj (dd ν r)
          (movingTrainV tr r) (movingTrainE tr r) (perLam κ (dd ν r) i) y) *
        perE κ (dd ν r) j y) =
      fun y =>
        movLamDualHeat κ ν r i y * perE κ (dd ν r) j y +
          ComplCouplingEuler.movEulerAdj (dd ν r)
            (movingTrainV tr r) (movingTrainE tr r) (perLam κ (dd ν r) i) y *
            perE κ (dd ν r) j y :=
    funext fun _ => add_mul _ _ _
  have hrhs_add : (fun y => perLam κ (dd ν r) i y *
      (movOscRes κ ν r j y + movEulerRes κ P tr r j y + modeEigen P j * perE κ (dd ν r) j y)) =
      fun y =>
        perLam κ (dd ν r) i y * movOscRes κ ν r j y +
          perLam κ (dd ν r) i y * movL tr r (perE κ (dd ν r) j) y := by
    funext y
    unfold movEulerRes dd
    ring
  have hcell : movingCell ν (ν ^ (-2 : ℝ)) r = B0579.cell (dd ν r) := rfl
  rw [hcell, hlhs_add, hrhs_add, integral_add hH_lhs hE_lhs, integral_add hH_rhs hE_rhs,
    hH_eq, hE_eq]

/-- **Complete `H₀ E = Λ K₀` identity (`PartIII-a:T21/c3/3/1/1/2/2/3/d`, SP 2915–2918)** under the
exact hypotheses already present in `ComplWeakEq` (`DuhamelSplit.lean:109-115`):
`IsSeedKernels κ`, `8 < m`, `0 < ν`, `PerFrameFacts κ ν m b K`, and
`∀ S : ℝ, 0 ≤ S → ∃ C : ℝ, LadTrainBdd tr m S C`. -/
theorem h0ModeIdentity_of (κ : PlanarFrameKernels) (P : PlanarData)
    {ν m b K : ℝ} (hκ : IsSeedKernels κ) (hm : 8 < m) (hν : 0 < ν)
    (hF : PerFrameFacts κ ν m b K)
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)))
    (hBdd : ∀ S : ℝ, 0 ≤ S → ∃ C : ℝ, LadTrainBdd tr m S C) :
    H0ModeIdentity κ P ν b tr := by
  intro r hr hbr i j
  obtain ⟨C_tr, hCtr⟩ := hBdd r hr
  exact h0ModeIdentity_of_isUnit κ P hκ hm hν hr
    (isUnit_perGram_of_perFrameFacts κ hν hr hbr hF) tr hCtr i j

end Leaf2WeakEqNeeded

end ComplFreeRateSub

end UnforcedLeray.Short.IIIa

end
