import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg

/-!
# `truncBddTendsto`: the bounded commutator `EBdd n` tends to zero in `Y_2`

Source: `the November 2 reference manuscript` lines 1334-1337, 1351-1362,
1470-1480.  `EBdd n ν D = (½ y·∇χₙ - νΔχₙ) Φ - 2ν ∑ₖ ∂ₖχₙ ∂ₖΦ - 2ν ∑ₖ ∇∂ₖχₙ × ∂ₖψ`.

All coefficients are bounded uniformly in `n` and `y` (`CutBounds`), so
`‖EBdd n x‖ ≤ K (‖Φ x‖ + ∑ₖ‖∂ₖΦ x‖ + ∑ₖ‖∂ₖψ x‖)` with `K = 4C(1 + |ν|)`.  The squared majorant is
integrable (`IsInYr`), and `EBdd n x = 0` once `n + 1 > |y|` (the coefficients vanish on the ball
`|y| < n+1`), so dominated convergence on the phase measure finishes.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest)

/-- The constant of the bounded-commutator estimate. -/
def trbK (C ν : ℝ) : ℝ := 4 * C * (1 + |ν|)

theorem trbK_nonneg {C : ℝ} (hC0 : 0 ≤ C) (ν : ℝ) : 0 ≤ trbK C ν := by
  unfold trbK
  have : (0 : ℝ) ≤ 1 + |ν| := by positivity
  exact mul_nonneg (mul_nonneg (by norm_num) hC0) this

theorem trb_cross_zero (b : CVec3) : crossC 0 b = 0 := by
  unfold crossC
  ext i
  fin_cases i <;> simp

theorem trb_pair_sq (x1 x2 y1 y2 : ℂ) :
    ‖x1 * y2 - x2 * y1‖ ^ 2 ≤ (‖x1‖ ^ 2 + ‖x2‖ ^ 2) * (‖y1‖ ^ 2 + ‖y2‖ ^ 2) := by
  have h1 : ‖x1 * y2 - x2 * y1‖ ≤ ‖x1‖ * ‖y2‖ + ‖x2‖ * ‖y1‖ := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul, norm_mul]
  have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  nlinarith [sq_nonneg (‖x1‖ * ‖y1‖ - ‖x2‖ * ‖y2‖)]

theorem trb_cross_sq (a b : CVec3) : ‖crossC a b‖ ^ 2 ≤ 4 * (‖a‖ ^ 2 * ‖b‖ ^ 2) := by
  have c0 : crossC a b 0 = a 1 * b 2 - a 2 * b 1 := by simp [crossC]
  have c1 : crossC a b 1 = a 2 * b 0 - a 0 * b 2 := by simp [crossC]
  have c2 : crossC a b 2 = a 0 * b 1 - a 1 * b 0 := by simp [crossC]
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  rw [Fin.sum_univ_three, Fin.sum_univ_three, Fin.sum_univ_three, c0, c1, c2]
  have e1 := trb_pair_sq (a 1) (a 2) (b 1) (b 2)
  have e2 := trb_pair_sq (a 2) (a 0) (b 2) (b 0)
  have e3 := trb_pair_sq (a 0) (a 1) (b 0) (b 1)
  have hA0 : 0 ≤ ‖a 0‖ ^ 2 + ‖a 1‖ ^ 2 + ‖a 2‖ ^ 2 := by positivity
  have hB0 : 0 ≤ ‖b 0‖ ^ 2 + ‖b 1‖ ^ 2 + ‖b 2‖ ^ 2 := by positivity
  have m1 : (‖a 1‖ ^ 2 + ‖a 2‖ ^ 2) * (‖b 1‖ ^ 2 + ‖b 2‖ ^ 2)
      ≤ (‖a 0‖ ^ 2 + ‖a 1‖ ^ 2 + ‖a 2‖ ^ 2) * (‖b 0‖ ^ 2 + ‖b 1‖ ^ 2 + ‖b 2‖ ^ 2) :=
    mul_le_mul (by linarith [sq_nonneg ‖a 0‖]) (by linarith [sq_nonneg ‖b 0‖])
      (by positivity) hA0
  have m2 : (‖a 2‖ ^ 2 + ‖a 0‖ ^ 2) * (‖b 2‖ ^ 2 + ‖b 0‖ ^ 2)
      ≤ (‖a 0‖ ^ 2 + ‖a 1‖ ^ 2 + ‖a 2‖ ^ 2) * (‖b 0‖ ^ 2 + ‖b 1‖ ^ 2 + ‖b 2‖ ^ 2) :=
    mul_le_mul (by linarith [sq_nonneg ‖a 1‖]) (by linarith [sq_nonneg ‖b 1‖])
      (by positivity) hA0
  have m3 : (‖a 0‖ ^ 2 + ‖a 1‖ ^ 2) * (‖b 0‖ ^ 2 + ‖b 1‖ ^ 2)
      ≤ (‖a 0‖ ^ 2 + ‖a 1‖ ^ 2 + ‖a 2‖ ^ 2) * (‖b 0‖ ^ 2 + ‖b 1‖ ^ 2 + ‖b 2‖ ^ 2) :=
    mul_le_mul (by linarith [sq_nonneg ‖a 2‖]) (by linarith [sq_nonneg ‖b 2‖])
      (by positivity) hA0
  nlinarith [mul_nonneg hA0 hB0]

theorem trb_cross_norm (a b : CVec3) : ‖crossC a b‖ ≤ 2 * (‖a‖ * ‖b‖) := by
  have h := trb_cross_sq a b
  nlinarith [norm_nonneg (crossC a b), mul_nonneg (norm_nonneg a) (norm_nonneg b)]

theorem trb_grad_cont (a : Space → ℝ) (ha : ContDiff ℝ ∞ a) :
    Continuous fun y : Space => gradC a y := by
  unfold gradC
  have hc : Continuous fun y : Space => fun j : Fin 3 => ((sd j a y : ℝ) : ℂ) :=
    continuous_pi fun j => Complex.continuous_ofReal.comp (contDiff_sd ha j).continuous
  exact (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℂ)).comp hc

theorem trb_cross_cont : Continuous fun p : CVec3 × CVec3 => crossC p.1 p.2 := by
  have c : ∀ i : Fin 3, Continuous fun p : CVec3 × CVec3 => p.1 i := fun i => by
    first
      | exact (PiLp.continuous_apply i).comp continuous_fst
      | fun_prop
  have d : ∀ i : Fin 3, Continuous fun p : CVec3 × CVec3 => p.2 i := fun i => by
    first
      | exact (PiLp.continuous_apply i).comp continuous_snd
      | fun_prop
  unfold crossC
  refine (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℂ)).comp ?_
  refine continuous_pi fun i => ?_
  fin_cases i
  · exact ((c 1).mul (d 2)).sub ((c 2).mul (d 1))
  · exact ((c 2).mul (d 0)).sub ((c 0).mul (d 2))
  · exact ((c 0).mul (d 1)).sub ((c 1).mul (d 0))

theorem trb_radS_cd (n : ℕ) : ContDiff ℝ ∞ (radS (cutχ n)) := by
  unfold radS
  apply ContDiff.sum
  intro j _
  exact ((EuclideanSpace.proj j : Space →L[ℝ] ℝ).contDiff).mul (contDiff_sd (contDiff_cutχ n) j)

theorem trb_lapS_cd (n : ℕ) : ContDiff ℝ ∞ (lapS (cutχ n)) := by
  unfold lapS
  apply ContDiff.sum
  intro j _
  exact contDiff_sd (contDiff_sd (contDiff_cutχ n) j) j

theorem trb_enorm_sq (v : CVec3) : ‖v‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (‖v‖ ^ 2) := by
  rw [← ofReal_norm_eq_enorm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num),
    Real.rpow_two]

/-- Vector-level bound: the three terms of `EBdd` with coefficients bounded by `C`. -/
theorem trb_pointwise (C : ℝ) (hC0 : 0 ≤ C) (ν a b : ℝ) (Φ : CVec3) (c : Fin 3 → ℝ)
    (DΦ Dψ gc : Fin 3 → CVec3)
    (ha : |a| ≤ C) (hb : |b| ≤ C) (hc : ∀ k, |c k| ≤ C) (hgc : ∀ k, ‖gc k‖ ≤ C) :
    ‖((1 / 2 : ℝ) * a - ν * b) • Φ - (2 * ν) • (∑ k, c k • DΦ k)
        - (2 * ν) • (∑ k, crossC (gc k) (Dψ k))‖
      ≤ trbK C ν * (‖Φ‖ + ∑ k, ‖DΦ k‖ + ∑ k, ‖Dψ k‖) := by
  have hν0 := abs_nonneg ν
  have hS0 : 0 ≤ ∑ k, ‖DΦ k‖ := Finset.sum_nonneg fun k _ => norm_nonneg _
  have hS1 : 0 ≤ ∑ k, ‖Dψ k‖ := Finset.sum_nonneg fun k _ => norm_nonneg _
  have hKe : trbK C ν = 4 * C * (1 + |ν|) := rfl
  have hνb : |ν * b| ≤ |ν| * C := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hb hν0
  have hcoef : |(1 / 2 : ℝ) * a - ν * b| ≤ trbK C ν := by
    rw [hKe]
    have h1 := abs_le.1 ha
    have h2 := abs_le.1 hνb
    rw [abs_le]
    constructor
    · nlinarith [h1.1, h1.2, h2.1, h2.2, mul_nonneg hC0 hν0]
    · nlinarith [h1.1, h1.2, h2.1, h2.2, mul_nonneg hC0 hν0]
  have hA : ‖((1 / 2 : ℝ) * a - ν * b) • Φ‖ ≤ trbK C ν * ‖Φ‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right hcoef (norm_nonneg _)
  have hsμ : |2 * ν| = 2 * |ν| := by
    rw [abs_mul]
    norm_num
  have hB : ‖(2 * ν) • (∑ k, c k • DΦ k)‖ ≤ trbK C ν * ∑ k, ‖DΦ k‖ := by
    rw [norm_smul, Real.norm_eq_abs, hsμ]
    have hs : ‖∑ k, c k • DΦ k‖ ≤ C * ∑ k, ‖DΦ k‖ := by
      refine (norm_sum_le _ _).trans ?_
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun k _ => ?_
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hc k) (norm_nonneg _)
    have hcst : 2 * |ν| * ‖∑ k, c k • DΦ k‖ ≤ 2 * |ν| * (C * ∑ k, ‖DΦ k‖) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    have hfin : 2 * |ν| * (C * ∑ k, ‖DΦ k‖) ≤ trbK C ν * ∑ k, ‖DΦ k‖ := by
      rw [hKe]
      nlinarith [mul_nonneg hC0 hS0, mul_nonneg (mul_nonneg hC0 hS0) hν0]
    linarith
  have hD : ‖(2 * ν) • (∑ k, crossC (gc k) (Dψ k))‖ ≤ trbK C ν * ∑ k, ‖Dψ k‖ := by
    rw [norm_smul, Real.norm_eq_abs, hsμ]
    have hs : ‖∑ k, crossC (gc k) (Dψ k)‖ ≤ (2 * C) * ∑ k, ‖Dψ k‖ := by
      refine (norm_sum_le _ _).trans ?_
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun k _ => ?_
      refine (trb_cross_norm _ _).trans ?_
      have := mul_le_mul_of_nonneg_right (hgc k) (norm_nonneg (Dψ k))
      linarith
    have hcst : 2 * |ν| * ‖∑ k, crossC (gc k) (Dψ k)‖ ≤ 2 * |ν| * ((2 * C) * ∑ k, ‖Dψ k‖) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    have hfin : 2 * |ν| * ((2 * C) * ∑ k, ‖Dψ k‖) ≤ trbK C ν * ∑ k, ‖Dψ k‖ := by
      rw [hKe]
      nlinarith [mul_nonneg hC0 hS1, mul_nonneg (mul_nonneg hC0 hS1) hν0]
    linarith
  have t1 := norm_sub_le
    (((1 / 2 : ℝ) * a - ν * b) • Φ - (2 * ν) • (∑ k, c k • DΦ k))
    ((2 * ν) • (∑ k, crossC (gc k) (Dψ k)))
  have t2 := norm_sub_le (((1 / 2 : ℝ) * a - ν * b) • Φ) ((2 * ν) • (∑ k, c k • DΦ k))
  rw [mul_add, mul_add]
  linarith

theorem trb_sq7 (x1 x2 x3 x4 x5 x6 x7 : ℝ) :
    (x1 + x2 + x3 + x4 + x5 + x6 + x7) ^ 2
      ≤ 7 * (x1 ^ 2 + x2 ^ 2 + x3 ^ 2 + x4 ^ 2 + x5 ^ 2 + x6 ^ 2 + x7 ^ 2) := by
  nlinarith [sq_nonneg (x1 - x2), sq_nonneg (x1 - x3), sq_nonneg (x1 - x4),
    sq_nonneg (x1 - x5), sq_nonneg (x1 - x6), sq_nonneg (x1 - x7), sq_nonneg (x2 - x3),
    sq_nonneg (x2 - x4), sq_nonneg (x2 - x5), sq_nonneg (x2 - x6), sq_nonneg (x2 - x7),
    sq_nonneg (x3 - x4), sq_nonneg (x3 - x5), sq_nonneg (x3 - x6), sq_nonneg (x3 - x7),
    sq_nonneg (x4 - x5), sq_nonneg (x4 - x6), sq_nonneg (x4 - x7), sq_nonneg (x5 - x6),
    sq_nonneg (x5 - x7), sq_nonneg (x6 - x7)]

theorem trb_ofReal_sq7 (x1 x2 x3 x4 x5 x6 x7 : ℝ) :
    ENNReal.ofReal (x1 ^ 2 + x2 ^ 2 + x3 ^ 2 + x4 ^ 2 + x5 ^ 2 + x6 ^ 2 + x7 ^ 2)
      = ENNReal.ofReal (x1 ^ 2) + ENNReal.ofReal (x2 ^ 2) + ENNReal.ofReal (x3 ^ 2)
        + ENNReal.ofReal (x4 ^ 2) + ENNReal.ofReal (x5 ^ 2) + ENNReal.ofReal (x6 ^ 2)
        + ENNReal.ofReal (x7 ^ 2) := by
  rw [ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_add (by positivity) (by positivity)]

theorem trb_lint_add {α : Type*} [MeasurableSpace α] {μ : Measure α} (g h : α → ℝ≥0∞)
    (hg : AEMeasurable g μ) (h1 : ∫⁻ a, g a ∂μ ≠ ⊤) (h2 : ∫⁻ a, h a ∂μ ≠ ⊤) :
    ∫⁻ a, (g a + h a) ∂μ ≠ ⊤ := by
  rw [lintegral_add_left' hg]
  exact ENNReal.add_ne_top.2 ⟨h1, h2⟩

/-- The seven squared norms of the majorant. -/
def trbS (D : TruncData) (z : ℝ × Space) : ℝ≥0∞ :=
  ‖D.Φ z‖ₑ ^ (2 : ℝ) + ‖D.DΦ 0 z‖ₑ ^ (2 : ℝ) + ‖D.DΦ 1 z‖ₑ ^ (2 : ℝ) + ‖D.DΦ 2 z‖ₑ ^ (2 : ℝ)
    + ‖D.Dψ 0 z‖ₑ ^ (2 : ℝ) + ‖D.Dψ 1 z‖ₑ ^ (2 : ℝ) + ‖D.Dψ 2 z‖ₑ ^ (2 : ℝ)

theorem trbS_lint (P : ℝ) (hP : 0 < P) (D : TruncData)
    (hΦ : UnforcedLeray.Short.IIb.IsInYr P 2 D.Φ)
    (hDΦ : ∀ j, UnforcedLeray.Short.IIb.IsInYr P 2 (D.DΦ j))
    (hDψ : ∀ j, UnforcedLeray.Short.IIb.IsInYr P 2 (D.Dψ j)) :
    ∫⁻ z, trbS D z ∂(muP P) ≠ ⊤ := by
  have m : ∀ F : ℝ × Space → CVec3, UnforcedLeray.Short.IIb.IsInYr P 2 F →
      AEMeasurable (fun z => ‖F z‖ₑ ^ (2 : ℝ)) (muP P) := fun F hF =>
    ((aesm_muP hF.meas).enorm).pow_const 2
  have f : ∀ F : ℝ × Space → CVec3, UnforcedLeray.Short.IIb.IsInYr P 2 F →
      ∫⁻ z, ‖F z‖ₑ ^ (2 : ℝ) ∂(muP P) ≠ ⊤ := fun F hF =>
    (lint_lt_top_of_phaseLpNorm hP hF.meas hF.finite).ne
  have a0 := m _ hΦ
  have a1 := m _ (hDΦ 0)
  have a2 := m _ (hDΦ 1)
  have a3 := m _ (hDΦ 2)
  have a4 := m _ (hDψ 0)
  have a5 := m _ (hDψ 1)
  have a6 := m _ (hDψ 2)
  have g1 := trb_lint_add _ _ a0 (f _ hΦ) (f _ (hDΦ 0))
  have g2 := trb_lint_add _ _ (a0.add a1) g1 (f _ (hDΦ 1))
  have g3 := trb_lint_add _ _ ((a0.add a1).add a2) g2 (f _ (hDΦ 2))
  have g4 := trb_lint_add _ _ (((a0.add a1).add a2).add a3) g3 (f _ (hDψ 0))
  have g5 := trb_lint_add _ _ ((((a0.add a1).add a2).add a3).add a4) g4 (f _ (hDψ 1))
  have g6 := trb_lint_add _ _ (((((a0.add a1).add a2).add a3).add a4).add a5) g5 (f _ (hDψ 2))
  unfold trbS
  exact g6

set_option maxHeartbeats 1000000 in
theorem trb_cross_meas (n : ℕ) (D : TruncData) (k : Fin 3)
    (hgk : Continuous fun x : ℝ × Space => gradC (sd k (cutχ n)) x.2)
    (hψ : AEStronglyMeasurable (fun x : ℝ × Space => D.Dψ k x) volume) :
    AEStronglyMeasurable (fun x : ℝ × Space => crossC (gradC (sd k (cutχ n)) x.2) (D.Dψ k x))
      volume := by
  have h := trb_cross_cont.comp_aestronglyMeasurable (hgk.aestronglyMeasurable.prodMk hψ)
  exact h

set_option maxHeartbeats 1000000 in
theorem trb_smul_meas (n : ℕ) (F : ℝ × Space → CVec3) (k : Fin 3)
    (hk : Continuous fun x : ℝ × Space => sd k (cutχ n) x.2)
    (hF : AEStronglyMeasurable F volume) :
    AEStronglyMeasurable (fun x : ℝ × Space => sd k (cutχ n) x.2 • F x) volume :=
  hk.aestronglyMeasurable.smul hF

set_option maxHeartbeats 1000000 in
theorem truncBddTendsto : TruncBddTendsto := by
  unfold TruncBddTendsto
  intro hCut P ν hP D hΦ hDΦ hDψ
  obtain ⟨C, hC0, hall⟩ := hCut
  have hbd : ∀ n : ℕ, ∀ y : Space, |radS (cutχ n) y| ≤ C ∧ |lapS (cutχ n) y| ≤ C ∧
      ∀ k : Fin 3, |sd k (cutχ n) y| ≤ C ∧ ‖gradC (sd k (cutχ n)) y‖ ≤ C := by
    intro n y
    obtain ⟨-, -, -, -, h1, h2, h3⟩ := hall n y
    exact ⟨h1, h2, h3⟩
  have hzero : ∀ n : ℕ, ∀ y : Space, ‖y‖ < (n : ℝ) + 1 →
      radS (cutχ n) y = 0 ∧ lapS (cutχ n) y = 0 ∧
        ∀ k : Fin 3, sd k (cutχ n) y = 0 ∧ gradC (sd k (cutχ n)) y = 0 := by
    intro n y h
    obtain ⟨-, -, -, h1, h2, h3⟩ := (hall n y).1 (Or.inl h)
    exact ⟨h1, h2, h3⟩
  have hmeas : ∀ n : ℕ, AEStronglyMeasurable (EBdd n ν D) volume := by
    intro n
    have hc1 : Continuous fun x : ℝ × Space =>
        (1 / 2 : ℝ) * radS (cutχ n) x.2 - ν * lapS (cutχ n) x.2 :=
      (continuous_const.mul ((trb_radS_cd n).continuous.comp continuous_snd)).sub
        (continuous_const.mul ((trb_lapS_cd n).continuous.comp continuous_snd))
    have hk : ∀ k : Fin 3, Continuous fun x : ℝ × Space => sd k (cutχ n) x.2 := fun k =>
      (contDiff_sd (contDiff_cutχ n) k).continuous.comp continuous_snd
    have hgk : ∀ k : Fin 3, Continuous fun x : ℝ × Space => gradC (sd k (cutχ n)) x.2 :=
      fun k => (trb_grad_cont _ (contDiff_sd (contDiff_cutχ n) k)).comp continuous_snd
    have T1 : AEStronglyMeasurable
        (fun x : ℝ × Space => ((1 / 2 : ℝ) * radS (cutχ n) x.2 - ν * lapS (cutχ n) x.2) • D.Φ x)
        volume := hc1.aestronglyMeasurable.smul hΦ.meas
    have T2 : AEStronglyMeasurable
        (fun x : ℝ × Space => ∑ k : Fin 3, sd k (cutχ n) x.2 • D.DΦ k x) volume := by
      have e : (fun x : ℝ × Space => ∑ k : Fin 3, sd k (cutχ n) x.2 • D.DΦ k x)
          = fun x => sd 0 (cutχ n) x.2 • D.DΦ 0 x + sd 1 (cutχ n) x.2 • D.DΦ 1 x
            + sd 2 (cutχ n) x.2 • D.DΦ 2 x := by
        funext x
        rw [Fin.sum_univ_three]
      rw [e]
      exact ((trb_smul_meas n (D.DΦ 0) 0 (hk 0) (hDΦ 0).meas).add
        (trb_smul_meas n (D.DΦ 1) 1 (hk 1) (hDΦ 1).meas)).add
        (trb_smul_meas n (D.DΦ 2) 2 (hk 2) (hDΦ 2).meas)
    have T3 : AEStronglyMeasurable
        (fun x : ℝ × Space => ∑ k : Fin 3, crossC (gradC (sd k (cutχ n)) x.2) (D.Dψ k x)) volume := by
      have e : (fun x : ℝ × Space => ∑ k : Fin 3, crossC (gradC (sd k (cutχ n)) x.2) (D.Dψ k x))
          = fun x => crossC (gradC (sd 0 (cutχ n)) x.2) (D.Dψ 0 x)
            + crossC (gradC (sd 1 (cutχ n)) x.2) (D.Dψ 1 x)
            + crossC (gradC (sd 2 (cutχ n)) x.2) (D.Dψ 2 x) := by
        funext x
        rw [Fin.sum_univ_three]
      rw [e]
      exact ((trb_cross_meas n D 0 (hgk 0) (hDψ 0).meas).add
        (trb_cross_meas n D 1 (hgk 1) (hDψ 1).meas)).add
        (trb_cross_meas n D 2 (hgk 2) (hDψ 2).meas)
    have hT2 : AEStronglyMeasurable
        (fun x : ℝ × Space => (2 * ν) • ∑ k : Fin 3, sd k (cutχ n) x.2 • D.DΦ k x) volume :=
      T2.const_smul (2 * ν)
    have hT3 : AEStronglyMeasurable
        (fun x : ℝ × Space => (2 * ν) • ∑ k : Fin 3, crossC (gradC (sd k (cutχ n)) x.2) (D.Dψ k x))
        volume :=
      T3.const_smul (2 * ν)
    have hfin : AEStronglyMeasurable
        (fun x : ℝ × Space => ((1 / 2 : ℝ) * radS (cutχ n) x.2 - ν * lapS (cutχ n) x.2) • D.Φ x
          - (2 * ν) • ∑ k : Fin 3, sd k (cutχ n) x.2 • D.DΦ k x
          - (2 * ν) • ∑ k : Fin 3, crossC (gradC (sd k (cutχ n)) x.2) (D.Dψ k x)) volume :=
      (T1.sub hT2).sub hT3
    exact hfin
  have hbound : ∀ n : ℕ, ∀ z : ℝ × Space,
      ‖EBdd n ν D z‖ₑ ^ (2 : ℝ) ≤ ENNReal.ofReal (7 * (trbK C ν) ^ 2) * trbS D z := by
    intro n z
    have hE : ‖EBdd n ν D z‖ ≤ trbK C ν *
        (‖D.Φ z‖ + ∑ k, ‖D.DΦ k z‖ + ∑ k, ‖D.Dψ k z‖) :=
      trb_pointwise C hC0 ν (radS (cutχ n) z.2) (lapS (cutχ n) z.2) (D.Φ z)
        (fun k => sd k (cutχ n) z.2) (fun k => D.DΦ k z) (fun k => D.Dψ k z)
        (fun k => gradC (sd k (cutχ n)) z.2) (hbd n z.2).1 (hbd n z.2).2.1
        (fun k => ((hbd n z.2).2.2 k).1) (fun k => ((hbd n z.2).2.2 k).2)
    have hsum : ‖D.Φ z‖ + ∑ k, ‖D.DΦ k z‖ + ∑ k, ‖D.Dψ k z‖
        = ‖D.Φ z‖ + ‖D.DΦ 0 z‖ + ‖D.DΦ 1 z‖ + ‖D.DΦ 2 z‖
          + ‖D.Dψ 0 z‖ + ‖D.Dψ 1 z‖ + ‖D.Dψ 2 z‖ := by
      simp only [Fin.sum_univ_three]
      ring
    have hsq : ‖EBdd n ν D z‖ ^ 2 ≤ 7 * (trbK C ν) ^ 2 *
        (‖D.Φ z‖ ^ 2 + ‖D.DΦ 0 z‖ ^ 2 + ‖D.DΦ 1 z‖ ^ 2 + ‖D.DΦ 2 z‖ ^ 2
          + ‖D.Dψ 0 z‖ ^ 2 + ‖D.Dψ 1 z‖ ^ 2 + ‖D.Dψ 2 z‖ ^ 2) := by
      have h0 : 0 ≤ ‖EBdd n ν D z‖ := norm_nonneg _
      have h1 := pow_le_pow_left₀ h0 hE 2
      rw [mul_pow, hsum] at h1
      have h2 := trb_sq7 (‖D.Φ z‖) (‖D.DΦ 0 z‖) (‖D.DΦ 1 z‖) (‖D.DΦ 2 z‖)
        (‖D.Dψ 0 z‖) (‖D.Dψ 1 z‖) (‖D.Dψ 2 z‖)
      have h3 := mul_le_mul_of_nonneg_left h2 (sq_nonneg (trbK C ν))
      nlinarith [h1, h3]
    rw [trb_enorm_sq]
    unfold trbS
    simp only [trb_enorm_sq]
    rw [← trb_ofReal_sq7, ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 7 * (trbK C ν) ^ 2)]
    exact ENNReal.ofReal_le_ofReal hsq
  have hpt : ∀ z : ℝ × Space, Tendsto (fun n : ℕ => ‖EBdd n ν D z‖ₑ ^ (2 : ℝ)) atTop (𝓝 0) := by
    intro z
    obtain ⟨N, hN⟩ := exists_nat_gt ‖z.2‖
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop N] with n hn
    have hlt : ‖z.2‖ < (n : ℝ) + 1 := by
      have : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    obtain ⟨h1, h2, h3⟩ := hzero n z.2 hlt
    have hs1 : ∀ k : Fin 3, sd k (cutχ n) z.2 = 0 := fun k => (h3 k).1
    have hs2 : ∀ k : Fin 3, gradC (sd k (cutχ n)) z.2 = 0 := fun k => (h3 k).2
    have hE : EBdd n ν D z = 0 := by
      unfold EBdd
      simp [h1, h2, hs1, hs2, trb_cross_zero]
    rw [hE, enorm_zero, ENNReal.zero_rpow_of_pos (by norm_num)]
  have hbfin : ∫⁻ z, ENNReal.ofReal (7 * (trbK C ν) ^ 2) * trbS D z ∂(muP P) ≠ ⊤ := by
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (trbS_lint P hP D hΦ hDΦ hDψ)
  have key := tendsto_lintegral_of_dominated_convergence'
    (μ := muP P)
    (F := fun n z => ‖EBdd n ν D z‖ₑ ^ (2 : ℝ))
    (f := fun _ => (0 : ℝ≥0∞))
    (fun z => ENNReal.ofReal (7 * (trbK C ν) ^ 2) * trbS D z)
    (fun n => ((aesm_muP (hmeas n)).enorm).pow_const 2)
    (fun n => Filter.Eventually.of_forall (fun z => hbound n z))
    hbfin
    (Filter.Eventually.of_forall (fun z => hpt z))
  have hJ : Tendsto (fun n : ℕ => ∫⁻ z, ‖EBdd n ν D z‖ₑ ^ (2 : ℝ) ∂(muP P)) atTop (𝓝 0) := by
    simpa using key
  have hfun : (fun n : ℕ => UnforcedLeray.Short.IIb.phaseLpNorm P 2 (EBdd n ν D)) =
      fun n : ℕ => (ENNReal.ofReal P⁻¹ * ∫⁻ z, ‖EBdd n ν D z‖ₑ ^ (2 : ℝ) ∂(muP P)) ^ (1 / 2 : ℝ) :=
    funext fun n => phaseLpNorm_eq P _ (hmeas n)
  refine ⟨hmeas, ?_⟩
  rw [hfun]
  have h8 := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal P⁻¹) hJ (Or.inr ENNReal.ofReal_ne_top)
  have h9 := ((ENNReal.continuous_rpow_const (y := 1 / 2)).tendsto
    (ENNReal.ofReal P⁻¹ * 0)).comp h8
  have h10 : (ENNReal.ofReal P⁻¹ * 0) ^ (1 / 2 : ℝ) = 0 := by
    rw [mul_zero]
    exact ENNReal.zero_rpow_of_pos (by norm_num)
  rw [h10] at h9
  exact h9
