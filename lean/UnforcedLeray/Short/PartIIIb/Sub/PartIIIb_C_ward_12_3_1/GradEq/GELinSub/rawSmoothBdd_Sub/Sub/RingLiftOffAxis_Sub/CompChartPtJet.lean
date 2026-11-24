import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_5_2_1_2_org
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.RingLift.ChartJets
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GELinSub.rawSmoothBdd_Sub.Sub.RingLiftOffAxis_Sub

/-!
# Organizer task `PartIII-b:C/ward/12/3/1/2/6/1/3/1/org/1/org/1/3`: `compChartPtJet`

Source of record: `the November 2 reference manuscript`, SP 2346-2366 (chart calculus).
Pointwise version of `IIb.compChartJets`: Faà di Bruno (`norm_iteratedFDerivWithin_comp_le`) on the
open set `axisᶜ` with the chart bounds `IIb.chartJets` at the level `S = age + 1`, the profile
derivatives bounded by the sum `∑_{l ≤ j} ‖D^l b (chart y)‖` and the weights absorbed.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff
open UnforcedLeray UnforcedLeray.Short.IIb

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem compChartPtJet : UnforcedLeray.Short.PartIIIb.Concrete.CompChartPtJet := by
  intro j
  have hdata : ∀ i : ℕ, ∃ (C : ℝ) (k : ℕ), 0 < C ∧
      (1 ≤ i → ∀ (S R τ : ℝ), 0 < S → 1 ≤ R → ∀ y : Space, y ∉ Axi.axis →
        Axi.age R y < S →
        ‖iteratedFDeriv ℝ i (Axi.chart R τ) y‖ ≤ C * (1 + S) ^ k * (1 + |Axi.trans R y|)) := by
    intro i
    by_cases hi : 1 ≤ i
    · obtain ⟨C, k, hC, h⟩ := chartJets i hi
      exact ⟨C, k, hC, fun _ => h⟩
    · exact ⟨1, 0, one_pos, fun h => absurd h hi⟩
  choose C k hC hb using hdata
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = 1 + ∑ i ∈ Finset.range (j + 1), C i := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K : ℕ, K = ∑ i ∈ Finset.range (j + 1), k i := ⟨_, rfl⟩
  have hsumC : 0 ≤ ∑ i ∈ Finset.range (j + 1), C i :=
    Finset.sum_nonneg (fun i _ => (hC i).le)
  have hA1 : 1 ≤ A := by rw [hA]; linarith
  have hA0 : 0 ≤ A := by linarith
  have hCA : ∀ i, i ≤ j → C i ≤ A := by
    intro i hi
    have h1 := Finset.single_le_sum (f := C) (fun i _ => (hC i).le)
      (Finset.mem_range.2 (Nat.lt_succ_of_le hi))
    rw [hA]; linarith
  have hkK : ∀ i, i ≤ j → k i ≤ K := by
    intro i hi
    rw [hK]
    exact Finset.single_le_sum (f := k) (fun i _ => Nat.zero_le _)
      (Finset.mem_range.2 (Nat.lt_succ_of_le hi))
  have hjfac : (0 : ℝ) < (j.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos j
  refine ⟨(j.factorial : ℝ) * A ^ j * 2 ^ (K * j), K * j,
    mul_pos (mul_pos hjfac (pow_pos (by linarith) j)) (pow_pos two_pos _), ?_⟩
  intro R τ b hR hb' y hy n hn
  have hR0 : 0 < R := lt_of_lt_of_le one_pos hR
  have hage0 : 0 < Axi.age R y := age_pos_of hR0 hy
  obtain ⟨S, hSdef⟩ : ∃ S : ℝ, S = Axi.age R y + 1 := ⟨_, rfl⟩
  have hS : 0 < S := by rw [hSdef]; linarith
  have hage : Axi.age R y < S := by rw [hSdef]; linarith
  have hS1 : (1 : ℝ) ≤ 1 + S := by linarith
  have hS0 : (0 : ℝ) ≤ 1 + S := by linarith
  have hS_le : 1 + S ≤ 2 * (1 + Axi.age R y) := by rw [hSdef]; linarith
  have hP0 : (0 : ℝ) ≤ 1 + Axi.age R y := by linarith
  obtain ⟨w, hw⟩ : ∃ w : ℝ, w = 1 + |Axi.trans R y| := ⟨_, rfl⟩
  have hw1 : 1 ≤ w := by rw [hw]; linarith [abs_nonneg (Axi.trans R y)]
  have hw0 : 0 < w := by linarith
  have hchart : ContDiffOn ℝ ∞ (Axi.chart R τ) Axi.axisᶜ :=
    ChartJetsAux.contDiffOn_chart hR0.ne' τ
  have hopen : IsOpen (Axi.axisᶜ : Set Space) := Axi.isOpen_compl_axis
  have htopen : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := isOpen_Ioi.prod isOpen_univ
  have hmaps : MapsTo (Axi.chart R τ) Axi.axisᶜ (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := by
    intro z hz
    exact ⟨age_pos_of hR0 hz, mem_univ _⟩
  have hx : y ∈ (Axi.axisᶜ : Set Space) := hy
  obtain ⟨Ssum, hSsum⟩ : ∃ Ssum : ℝ,
      Ssum = ∑ l ∈ Finset.range (j + 1), ‖iteratedFDeriv ℝ l b (Axi.chart R τ y)‖ := ⟨_, rfl⟩
  have hS0sum : 0 ≤ Ssum := by rw [hSsum]; exact Finset.sum_nonneg fun _ _ => norm_nonneg _
  -- profile bounds at the chart point
  have hbound0 : ∀ i, i ≤ n →
      ‖iteratedFDerivWithin ℝ i b (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) (Axi.chart R τ y)‖ ≤ Ssum := by
    intro i hi
    rw [iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) i htopen (hmaps hx), hSsum]
    exact Finset.single_le_sum (f := fun l => ‖iteratedFDeriv ℝ l b (Axi.chart R τ y)‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_range.2 (Nat.lt_succ_of_le (le_trans hi hn)))
  -- chart bounds on the open set
  have hD : ∀ i, 1 ≤ i → i ≤ n → ‖iteratedFDerivWithin ℝ i (Axi.chart R τ) Axi.axisᶜ y‖
      ≤ (A * (1 + S) ^ K * w) ^ i := by
    intro i hi1 hin
    rw [iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) i hopen hx]
    have hij : i ≤ j := le_trans hin hn
    have h := hb i hi1 S R τ hS hR y hy hage
    rw [← hw] at h
    have hle : C i * (1 + S) ^ (k i) * w ≤ A * (1 + S) ^ K * w := by
      apply mul_le_mul_of_nonneg_right _ hw0.le
      exact mul_le_mul (hCA i hij) (pow_le_pow_right₀ hS1 (hkK i hij))
        (pow_nonneg hS0 _) hA0
    have hDw : 1 ≤ A * (1 + S) ^ K * w :=
      one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hA1 (one_le_pow₀ hS1)) hw1
    exact h.trans (hle.trans (le_self_pow₀ hDw (by omega)))
  have key := norm_iteratedFDerivWithin_comp_le (𝕜 := ℝ) (g := b) (f := Axi.chart R τ)
    (n := n) (s := Axi.axisᶜ) (t := Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) (x := y) (N := ∞)
    hb' hchart (by exact_mod_cast le_top) htopen.uniqueDiffOn hopen.uniqueDiffOn
    hmaps hx hbound0 hD
  have e : iteratedFDeriv ℝ n (fun z => b (Axi.chart R τ z)) y =
      iteratedFDerivWithin ℝ n (b ∘ Axi.chart R τ) Axi.axisᶜ y :=
    (iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) n hopen hx).symm
  rw [e, ← hw, ← hSsum]
  refine key.trans ?_
  -- the weights: `n! ≤ j!`, `A^n ≤ A^j`, `(1+S)^{Kn} ≤ 2^{Kj}(1+age)^{Kj}`, `w^n ≤ w^j`
  have hDn : (A * (1 + S) ^ K * w) ^ n = A ^ n * (1 + S) ^ (K * n) * w ^ n := by
    rw [mul_pow, mul_pow, ← pow_mul]
  have hfac : (n.factorial : ℝ) ≤ (j.factorial : ℝ) := by exact_mod_cast Nat.factorial_le hn
  have hAn : A ^ n ≤ A ^ j := pow_le_pow_right₀ hA1 hn
  have hwn : w ^ n ≤ w ^ j := pow_le_pow_right₀ hw1 hn
  have hX : (1 + S) ^ (K * n) ≤ 2 ^ (K * j) * (1 + Axi.age R y) ^ (K * j) := by
    calc (1 + S) ^ (K * n) ≤ (1 + S) ^ (K * j) :=
          pow_le_pow_right₀ hS1 (Nat.mul_le_mul (le_refl K) hn)
      _ ≤ (2 * (1 + Axi.age R y)) ^ (K * j) := pow_le_pow_left₀ hS0 hS_le _
      _ = 2 ^ (K * j) * (1 + Axi.age R y) ^ (K * j) := mul_pow _ _ _
  have hAn0 : 0 ≤ A ^ n := pow_nonneg hA0 n
  have hAj0 : 0 ≤ A ^ j := pow_nonneg hA0 j
  have hX0 : 0 ≤ (1 + S) ^ (K * n) := pow_nonneg hS0 _
  have hY0 : 0 ≤ 2 ^ (K * j) * (1 + Axi.age R y) ^ (K * j) :=
    mul_nonneg (pow_nonneg two_pos.le _) (pow_nonneg hP0 _)
  have hw0n : 0 ≤ w ^ n := pow_nonneg hw0.le _
  have hAX : A ^ n * (1 + S) ^ (K * n) ≤ A ^ j * (2 ^ (K * j) * (1 + Axi.age R y) ^ (K * j)) :=
    mul_le_mul hAn hX hX0 hAj0
  have h2 : A ^ n * (1 + S) ^ (K * n) * w ^ n ≤
      A ^ j * (2 ^ (K * j) * (1 + Axi.age R y) ^ (K * j)) * w ^ j :=
    mul_le_mul hAX hwn hw0n (mul_nonneg hAj0 hY0)
  have h1 : (n.factorial : ℝ) * Ssum ≤ (j.factorial : ℝ) * Ssum :=
    mul_le_mul_of_nonneg_right hfac hS0sum
  have h3 : 0 ≤ A ^ n * (1 + S) ^ (K * n) * w ^ n :=
    mul_nonneg (mul_nonneg hAn0 hX0) hw0n
  have h4 : 0 ≤ (j.factorial : ℝ) * Ssum := mul_nonneg hjfac.le hS0sum
  rw [hDn]
  calc (n.factorial : ℝ) * Ssum * (A ^ n * (1 + S) ^ (K * n) * w ^ n)
      ≤ (j.factorial : ℝ) * Ssum *
          (A ^ j * (2 ^ (K * j) * (1 + Axi.age R y) ^ (K * j)) * w ^ j) :=
        mul_le_mul h1 h2 h3 h4
    _ = (j.factorial : ℝ) * A ^ j * 2 ^ (K * j) * (1 + Axi.age R y) ^ (K * j) *
          w ^ j * Ssum := by ring

end UnforcedLeray.Short.PartIIIb.Concrete
