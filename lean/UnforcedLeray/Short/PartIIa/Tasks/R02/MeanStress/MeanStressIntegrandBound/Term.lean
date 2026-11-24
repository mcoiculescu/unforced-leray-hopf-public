import UnforcedLeray.Short.PartIIa.Sub.R02_6

/-!
# Part II-a, helper for `PartII-a:R02/MeanStress/MeanStressIntegrandBound`: the Leibniz term bound

Source of record: `the November 2 reference manuscript`, lines 397-404 and 439-446.

Helper file for `Short/PartII-a/Tasks/R02/MeanStress/MeanStressIntegrandBound.lean`. It defines

* `MeanIdx ρ`: the instance index `⟨ν, tr, q, (η, s)⟩` with `tr : TrainSol ν (ν^{-ρ})`;
* `meanPairs a k`: the finite Leibniz index set `range (a+1) × range (k+1)`;
* `termVal`: one Leibniz summand's weight-and-slice factor
  `(1+η²/s)^m |η|^i s^k |∂_η^{i'}∂_s^{l'} ṽ₁| |∂_η^{i+a-i'}∂_s^{k-l'} ṽ₂|`;

and proves `termVal_bound`: each summand has a bound `polyConst C N ν c · exp(-κνs/c²)`
for `s ≥ 1`, from `FluctVelSliceBound` (two slice bounds, weights `m' = m+i` and `m' = 0`) and
`ExpPowAbsorb` (absorbing `s^k`). The real-number core is `term_core`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIa

/-- The instance index: `ν`, a train solution at `c = ν^{-ρ}` in the BUC class, and a point
`(q, (η, s))`. -/
abbrev MeanIdx (ρ : ℝ) : Type :=
  Σ ν : ℝ, {tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-ρ)) // UnforcedLeray.Short.PartI.IsBUCTrain tr} × (ℝ × ℝ × ℝ)

/-- The finite Leibniz index set `{0, …, a} × {0, …, k}`. -/
def meanPairs (a k : ℕ) : Finset (ℕ × ℕ) :=
  Finset.range (a + 1) ×ˢ Finset.range (k + 1)

/-- One Leibniz summand's weight and slice factor: `(1+η²/s)^m |η|^i s^k` times the product of the
absolute values of the two slice derivatives of `ṽ₁` (component `0`) and `ṽ₂` (component `1`)
at the indices `(p.1, p.2)` and `(i+a-p.1, k-p.2)`. -/
def termVal (ρ : ℝ) (m i a k : ℕ) (p : ℕ × ℕ) (ν : ℝ)
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-ρ))) (q η s : ℝ) : ℝ :=
  (1 + η ^ 2 / s) ^ m * (|η| ^ i * s ^ k) *
    (|iteratedDeriv p.1 (fun e => iteratedDeriv p.2
        (fun r => UnforcedLeray.Short.PartI.hfluct (ν ^ (-ρ)) (fun w => tr.v r w 0) (q, e)) s) η| *
      |iteratedDeriv (i + a - p.1) (fun e => iteratedDeriv (k - p.2)
        (fun r => UnforcedLeray.Short.PartI.hfluct (ν ^ (-ρ)) (fun w => tr.v r w 1) (q, e)) s) η|)

/-- **Real-number core of one Leibniz term.** The weight `(1+η²/s)^m |η|^i ≤ (1+η²)^{m+i}` is spent
on the first factor (which carries the weight `(1+η²)^{m+i}`), the second factor is bounded
unweighted, the two exponentials multiply, and `s^k` is absorbed by `hk`. -/
theorem term_core (ν c s η : ℝ) (m i k : ℕ) (C1 C2 CA : ℝ) (N1 N2 NA : ℕ)
    (E1 E2 EA P1 P2 : ℝ) (hE1 : 0 < E1) (hE2 : 0 < E2) (hs0 : 0 ≤ s)
    (hwt : (1 + η ^ 2 / s) ^ m * |η| ^ i ≤ (1 + η ^ 2) ^ (m + i))
    (h1 : (1 + η ^ 2) ^ (m + i) * |P1| ≤ polyConst C1 N1 ν c * E1)
    (h2 : |P2| ≤ polyConst C2 N2 ν c * E2)
    (hk : s ^ k * (E1 * E2) ≤ polyConst CA NA ν c * EA) :
    (1 + η ^ 2 / s) ^ m * (|η| ^ i * s ^ k) * (|P1| * |P2|) ≤
      polyConst (C1 * C2 * CA) (N1 + N2 + NA) ν c * EA := by
  have hsk : 0 ≤ s ^ k := pow_nonneg hs0 k
  have hW0 : 0 ≤ (1 + η ^ 2) ^ (m + i) * |P1| := by positivity
  have hX1 : 0 ≤ polyConst C1 N1 ν c * E1 := le_trans hW0 h1
  have hP1 : 0 ≤ polyConst C1 N1 ν c := (mul_nonneg_iff_of_pos_right hE1).mp hX1
  have hX2 : 0 ≤ polyConst C2 N2 ν c * E2 := le_trans (abs_nonneg _) h2
  have hP2 : 0 ≤ polyConst C2 N2 ν c := (mul_nonneg_iff_of_pos_right hE2).mp hX2
  calc (1 + η ^ 2 / s) ^ m * (|η| ^ i * s ^ k) * (|P1| * |P2|)
      = ((1 + η ^ 2 / s) ^ m * |η| ^ i) * (s ^ k * (|P1| * |P2|)) := by ring
    _ ≤ (1 + η ^ 2) ^ (m + i) * (s ^ k * (|P1| * |P2|)) :=
        mul_le_mul_of_nonneg_right hwt (mul_nonneg hsk (mul_nonneg (abs_nonneg _) (abs_nonneg _)))
    _ = s ^ k * (((1 + η ^ 2) ^ (m + i) * |P1|) * |P2|) := by ring
    _ ≤ s ^ k * ((polyConst C1 N1 ν c * E1) * |P2|) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h1 (abs_nonneg _)) hsk
    _ ≤ s ^ k * ((polyConst C1 N1 ν c * E1) * (polyConst C2 N2 ν c * E2)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hX1) hsk
    _ = (polyConst C1 N1 ν c * polyConst C2 N2 ν c) * (s ^ k * (E1 * E2)) := by ring
    _ ≤ (polyConst C1 N1 ν c * polyConst C2 N2 ν c) * (polyConst CA NA ν c * EA) :=
        mul_le_mul_of_nonneg_left hk (mul_nonneg hP1 hP2)
    _ = polyConst (C1 * C2 * CA) (N1 + N2 + NA) ν c * EA := by
        unfold polyConst
        rw [pow_add, pow_add]
        ring

/-- **Term bound** (`s ≥ 1`). For each Leibniz index `p`, the summand `termVal` is bounded by
`polyConst C N ν c · exp(-κνs/c²)` uniformly in the instance, with `c = ν^{-ρ}`.  The two slice
factors come from `FluctVelSliceBound` (`hS`, with `m' = m+i` for the first and `m' = 0` for the
second), and `s^k` is absorbed by `ExpPowAbsorb` (`hA`) at the rate `κ₁ + κ₂`, halved. -/
theorem termVal_bound (ρ : ℝ) (hρ : 1 / 2 < ρ) (hS : FluctVelSliceBound) (hA : ExpPowAbsorb)
    (m i a k : ℕ) (p : ℕ × ℕ) :
    ∃ (C : ℝ) (N : ℕ) (κ ν₀ : ℝ), 0 < κ ∧ 0 < ν₀ ∧
      ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ → ∀ (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-ρ))),
        UnforcedLeray.Short.PartI.IsBUCTrain tr → ∀ (q η s : ℝ), 1 ≤ s →
        termVal ρ m i a k p ν tr q η s ≤
          polyConst C N ν (ν ^ (-ρ)) * Real.exp (-(κ * ν * s / (ν ^ (-ρ)) ^ 2)) := by
  obtain ⟨C1, N1, κ1, ν1, hκ1, hν1, H1⟩ := hS ρ (m + i) p.1 p.2 hρ
  obtain ⟨C2, N2, κ2, ν2, hκ2, hν2, H2⟩ := hS ρ 0 (i + a - p.1) (k - p.2) hρ
  obtain ⟨CA, NA, _, HA⟩ := hA (κ1 + κ2) k (by linarith)
  refine ⟨C1 * C2 * CA, N1 + N2 + NA, (κ1 + κ2) / 2, min ν1 ν2, by linarith,
    lt_min hν1 hν2, ?_⟩
  intro ν hν hνν tr hb q η s hs
  have hν1' : ν ≤ ν1 := hνν.trans (min_le_left _ _)
  have hν2' : ν ≤ ν2 := hνν.trans (min_le_right _ _)
  have hs0 : 0 < s := by linarith
  have hc : 0 < ν ^ (-ρ) := Real.rpow_pos_of_pos hν _
  have h1 := H1 ν hν hν1' tr hb 0 q η s hs0
  have h2 := H2 ν hν hν2' tr hb 1 q η s hs0
  rw [pow_zero, one_mul] at h2
  have hE12 : Real.exp (-(κ1 * ν * s / (ν ^ (-ρ)) ^ 2)) *
      Real.exp (-(κ2 * ν * s / (ν ^ (-ρ)) ^ 2)) =
        Real.exp (-((κ1 + κ2) * ν * s / (ν ^ (-ρ)) ^ 2)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hk := HA ν (ν ^ (-ρ)) s hν hc hs0.le
  rw [← hE12] at hk
  exact term_core ν (ν ^ (-ρ)) s η m i k C1 C2 CA N1 N2 NA
    (Real.exp (-(κ1 * ν * s / (ν ^ (-ρ)) ^ 2)))
    (Real.exp (-(κ2 * ν * s / (ν ^ (-ρ)) ^ 2)))
    (Real.exp (-((κ1 + κ2) / 2 * ν * s / (ν ^ (-ρ)) ^ 2)))
    _ _ (Real.exp_pos _) (Real.exp_pos _) hs0.le (weight_le m i hs) h1 h2 hk

end UnforcedLeray.Short.PartIIa
