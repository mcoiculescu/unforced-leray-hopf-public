import UnforcedLeray.Short.PartIIa.Tasks.R02.MeanStress.MeanStressIntegrandBound.Leib

/-!
# Part II-a, task `PartII-a:R02/MeanStress/MeanStressIntegrandBound`: the integrand bound

Source of record: `the November 2 reference manuscript`, lines 397-404 (`g = \overline{v₁v₂}`,
`\bar v₂ = 0`) and 439-446 (`sct:fluctuation`, the slice bound and the absorption of `s^k`).

Target: `MeanStressIntegrandBound` (`Sub/R02_6.lean`): for `ρ > 1/2` and `m a i k`, the weighted
`η`-derivatives `(1+η²/s)^m |η|^i s^k |∂_η^{i+a} ∂_s^k (ṽ₁ṽ₂)(q, ·)|` are bounded by
`polyConst C N ν c · e^{-κνs/c²}` for `s ≥ 1`, `c = ν^{-ρ}`, uniformly in `q`.

Route (the helpers live in `MeanStressIntegrandBound/`):
1. `leib_abs_le` (`Leib.lean`): the Leibniz rule `MixedLeibniz` expands `∂_η^{i+a} ∂_s^k (ṽ₁ṽ₂)` into
   the finite sum over `meanPairs (i+a) k` of `C(i+a,i') C(k,l') ∂_η^{i'}∂_s^{l'}ṽ₁ · ∂_η^{i+a-i'}∂_s^{k-l'}ṽ₂`,
   with the smoothness of `ṽ_j` from `MeanStressSmooth`; the weighted absolute value is bounded by
   `∑ |C C| · termVal`.
2. `termVal_bound` (`Term.lean`): each summand is bounded by `polyConst · e^{-κνs/c²}` by
   `FluctVelSliceBound` (weight `(1+η²)^{m+i}` on the first factor, `1` on the second) and
   `ExpPowAbsorb` (absorbing `s^k`).
3. `finite_uniform` (`Sub/R02_2.lean`) combines the finitely many summands into one bound with a common
   `(C, N, κ, ν₀)`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIa

/-- **`PartII-a:R02/MeanStress/MeanStressIntegrandBound`**: the integrand bound for the mean stress
(`MeanStressIntegrandBound`), from the Leibniz rule, the slice bound, the smoothness of the mean
stress, and the absorption of `s^k`. -/
theorem meanStressIntegrandBound_of (hL : UnforcedLeray.Short.PartIIa.MixedLeibniz)
    (hS : UnforcedLeray.Short.PartIIa.FluctVelSliceBound)
    (hSm : UnforcedLeray.Short.PartIIa.MeanStressSmooth)
    (hA : UnforcedLeray.Short.PartIIa.ExpPowAbsorb) :
    UnforcedLeray.Short.PartIIa.MeanStressIntegrandBound := by
  intro ρ m a i k hρ
  have hterm : ∀ p ∈ meanPairs (i + a) k, ∃ (C : ℝ) (N : ℕ) (κ ν₀ : ℝ), 0 < κ ∧ 0 < ν₀ ∧
      ∀ j : MeanIdx ρ, (0 < j.1 ∧ 1 ≤ j.2.2.2.2) → j.1 ≤ ν₀ →
        termVal ρ m i a k p j.1 j.2.1.1 j.2.2.1 j.2.2.2.1 j.2.2.2.2 ≤
          polyConst C N j.1 (j.1 ^ (-ρ)) * Real.exp (-(κ * j.1 * j.2.2.2.2 / (j.1 ^ (-ρ)) ^ 2)) := by
    intro p _
    obtain ⟨C, N, κ, ν₀, hκ, hν₀, H⟩ := termVal_bound ρ hρ hS hA m i a k p
    refine ⟨C, N, κ, ν₀, hκ, hν₀, ?_⟩
    rintro ⟨ν, ⟨tr, hb⟩, q, η, s⟩ ⟨hν, hs⟩ hνν
    exact H ν hν hνν tr hb q η s hs
  have hD0 : ∀ (κ : ℝ) (j : MeanIdx ρ), (0 < j.1 ∧ 1 ≤ j.2.2.2.2) →
      0 ≤ Real.exp (-(κ * j.1 * j.2.2.2.2 / (j.1 ^ (-ρ)) ^ 2)) :=
    fun κ j _ => (Real.exp_pos _).le
  have hDm : ∀ (κ κ' : ℝ) (j : MeanIdx ρ), (0 < j.1 ∧ 1 ≤ j.2.2.2.2) → 0 < κ' → κ' ≤ κ →
      Real.exp (-(κ * j.1 * j.2.2.2.2 / (j.1 ^ (-ρ)) ^ 2)) ≤
        Real.exp (-(κ' * j.1 * j.2.2.2.2 / (j.1 ^ (-ρ)) ^ 2)) := by
    intro κ κ' j hj hκ' hκκ'
    apply Real.exp_le_exp.2
    apply neg_le_neg
    apply div_le_div_of_nonneg_right _ (sq_nonneg _)
    have : 0 ≤ j.1 * j.2.2.2.2 := mul_nonneg hj.1.le (by linarith [hj.2])
    nlinarith [mul_le_mul_of_nonneg_right hκκ' this]
  have hpos : ∀ j : MeanIdx ρ, (0 < j.1 ∧ 1 ≤ j.2.2.2.2) → 0 < j.1 ∧ 0 < j.1 ^ (-ρ) :=
    fun j hj => ⟨hj.1, Real.rpow_pos_of_pos hj.1 _⟩
  obtain ⟨C, N, κ, ν₀, hκ, hν₀, H⟩ :=
    finite_uniform (ι := MeanIdx ρ) (meanPairs (i + a) k) (fun j => 0 < j.1 ∧ 1 ≤ j.2.2.2.2)
      (fun j => j.1) (fun j => j.1 ^ (-ρ))
      (fun κ j => Real.exp (-(κ * j.1 * j.2.2.2.2 / (j.1 ^ (-ρ)) ^ 2)))
      hD0 hDm hpos
      (fun p => ((i + a).choose p.1 : ℝ) * (k.choose p.2 : ℝ))
      (fun p j => termVal ρ m i a k p j.1 j.2.1.1 j.2.2.1 j.2.2.2.1 j.2.2.2.2) hterm
  refine ⟨C, N, κ, ν₀, hκ, hν₀, ?_⟩
  intro ν hν hνν tr hb q η s hs
  have hs0 : 0 < s := by linarith
  have key := H ⟨ν, ⟨tr, hb⟩, q, η, s⟩ ⟨hν, hs⟩ hνν
  exact (leib_abs_le hL hSm ρ ν hν tr hb q s η hs0 m i a k).trans key

end UnforcedLeray.Short.PartIIa
