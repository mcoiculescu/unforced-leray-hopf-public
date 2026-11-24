import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_5_2_1_2_org
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.RingLift.ChartJets

/-!
# Composite jets, task `PartII-b:G4/5/2/1/4/1`

Source of record: `the November 2 reference manuscript` lines 2360-2366, 2386-2387.
`CompChartJets` (the Faà di Bruno step of the ring lift) is proved from `chartJets`
(`ChartJets`, task `PartII-b:G4/5/2/1/2`) by `norm_iteratedFDerivWithin_comp_le` on the open set
`axisᶜ`: the chart derivatives of order `i ≤ j` are bounded by `A (1+S)^K (1+|η(y)|)`, the
profile derivatives by `M (1+|η(y)|)^{-j}`, and the factor `w = 1 + |η(y)|` is absorbed since
`w^n ≤ w^j`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray

/-- **Composite jets** (`CompChartJets` of the organize file, SP 2360-2366): the composite
`b ∘ chart` satisfies the Faà di Bruno bound with constants `C = j! A^j` and `k = K j`. -/
theorem compChartJets : UnforcedLeray.Short.IIb.CompChartJets := by
  intro j
  -- per-order data of the chart bound (trivial for `i = 0`, where it is not needed)
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
  refine ⟨(j.factorial : ℝ) * A ^ j, K * j, mul_pos hjfac (pow_pos (by linarith) j), ?_⟩
  intro S R τ M b hS hR hM hb' hbd y hy hage n hn
  have hR0 : 0 < R := lt_of_lt_of_le one_pos hR
  have hS1 : (1 : ℝ) ≤ 1 + S := by linarith
  have hS0 : (0 : ℝ) ≤ 1 + S := by linarith
  have hchart : ContDiffOn ℝ ∞ (Axi.chart R τ) Axi.axisᶜ :=
    ChartJetsAux.contDiffOn_chart hR0.ne' τ
  have hopen : IsOpen (Axi.axisᶜ : Set Space) := Axi.isOpen_compl_axis
  have hx : y ∈ (Axi.axisᶜ : Set Space) := hy
  obtain ⟨w, hw⟩ : ∃ w : ℝ, w = 1 + |Axi.trans R y| := ⟨_, rfl⟩
  have hw1 : 1 ≤ w := by rw [hw]; linarith [abs_nonneg (Axi.trans R y)]
  have hw0 : 0 < w := by linarith
  have hwj : 0 < w ^ j := pow_pos hw0 j
  -- profile bounds at the chart point (the weight `(1+|η|)^j` is `w^j`)
  have hbound0 : ∀ i, i ≤ n →
      ‖iteratedFDerivWithin ℝ i b univ (Axi.chart R τ y)‖ ≤ M * (w ^ j)⁻¹ := by
    intro i hi
    rw [iteratedFDerivWithin_univ]
    have h := hbd i (le_trans hi hn) (Axi.chart R τ y)
    have hxy : (Axi.chart R τ y).2.2 = Axi.trans R y := rfl
    rw [hxy, ← hw] at h
    have h' : ‖iteratedFDeriv ℝ i b (Axi.chart R τ y)‖ * w ^ j ≤ M := by
      rw [mul_comm]; exact h
    rw [le_mul_inv_iff₀ hwj]
    exact h'
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
    (n := n) (s := Axi.axisᶜ) (t := univ) (x := y) (N := ∞)
    hb'.contDiffOn hchart (by exact_mod_cast le_top) uniqueDiffOn_univ hopen.uniqueDiffOn
    (mapsTo_univ _ _) hx hbound0 hD
  have e : iteratedFDeriv ℝ n (fun z => b (Axi.chart R τ z)) y =
      iteratedFDerivWithin ℝ n (b ∘ Axi.chart R τ) Axi.axisᶜ y :=
    (iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) n hopen hx).symm
  rw [e]
  refine key.trans ?_
  have hLHS : (n.factorial : ℝ) * (M * (w ^ j)⁻¹) * (A * (1 + S) ^ K * w) ^ n
      = (n.factorial : ℝ) * M * A ^ n * (1 + S) ^ (K * n) * (w ^ n * (w ^ j)⁻¹) := by
    rw [mul_pow, mul_pow, ← pow_mul]
    ring
  rw [hLHS]
  have hwn : w ^ n ≤ w ^ j := pow_le_pow_right₀ hw1 hn
  have hwinv : w ^ n * (w ^ j)⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv, div_le_one hwj]
    exact hwn
  have hfac : (n.factorial : ℝ) ≤ (j.factorial : ℝ) := by exact_mod_cast Nat.factorial_le hn
  have hfac0 : (0 : ℝ) ≤ (n.factorial : ℝ) := by positivity
  have hAn : A ^ n ≤ A ^ j := pow_le_pow_right₀ hA1 hn
  have hQ : (1 + S) ^ (K * n) ≤ (1 + S) ^ (K * j) :=
    pow_le_pow_right₀ hS1 (Nat.mul_le_mul (le_refl K) hn)
  have hX0 : 0 ≤ (n.factorial : ℝ) * M * A ^ n * (1 + S) ^ (K * n) :=
    mul_nonneg (mul_nonneg (mul_nonneg hfac0 hM) (pow_nonneg hA0 n)) (pow_nonneg hS0 _)
  have a1 : (n.factorial : ℝ) * M ≤ (j.factorial : ℝ) * M :=
    mul_le_mul_of_nonneg_right hfac hM
  have a2 : (n.factorial : ℝ) * M * A ^ n ≤ (j.factorial : ℝ) * M * A ^ j :=
    mul_le_mul a1 hAn (pow_nonneg hA0 n) (mul_nonneg hjfac.le hM)
  have a3 : (n.factorial : ℝ) * M * A ^ n * (1 + S) ^ (K * n)
      ≤ (j.factorial : ℝ) * M * A ^ j * (1 + S) ^ (K * j) :=
    mul_le_mul a2 hQ (pow_nonneg hS0 _) (mul_nonneg (mul_nonneg hjfac.le hM) (pow_nonneg hA0 j))
  calc (n.factorial : ℝ) * M * A ^ n * (1 + S) ^ (K * n) * (w ^ n * (w ^ j)⁻¹)
      ≤ (n.factorial : ℝ) * M * A ^ n * (1 + S) ^ (K * n) * 1 :=
        mul_le_mul_of_nonneg_left hwinv hX0
    _ = (n.factorial : ℝ) * M * A ^ n * (1 + S) ^ (K * n) := mul_one _
    _ ≤ (j.factorial : ℝ) * M * A ^ j * (1 + S) ^ (K * j) := a3
    _ = (j.factorial : ℝ) * A ^ j * (1 + S) ^ (K * j) * M := by ring

end UnforcedLeray.Short.IIb
