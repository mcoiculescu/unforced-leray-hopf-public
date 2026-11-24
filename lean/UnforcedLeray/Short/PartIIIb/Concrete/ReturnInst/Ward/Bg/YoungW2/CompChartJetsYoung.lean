import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.Bg.YoungW2.Defs

/-!
# Composite jets of a profile smooth on `s > 0` (source 2360-2366, 2386-2387, 5461-5464)

Source of record: `the November 2 reference manuscript` (73 pages).

Leaf of `PartIII-b:C/ward/12` (`BgCompChartJetsYoung`, `Ward/Bg/YoungW2/Defs.lean`).  The proof of
`IIb.compChartJets` (`PartII-b/Tasks/AffineColumnComparison/RingLift/CompChartJets.lean`) with the
profile taken within the open set `t = {s > 0}` instead of `univ`: Faà di Bruno
(`norm_iteratedFDerivWithin_comp_le`) on `axisᶜ → t`, the chart bounds of `IIb.chartJets`, and the
profile bound at the single point `chart R τ y` (where the derivative within the open set `t` is the
derivative).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology UnforcedLeray.Axi
open scoped ContDiff Nat

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **`BgCompChartJetsYoung`** (source 2360-2366, 2386-2387, 5461-5464). -/
theorem bgCompChartJetsYoung : BgCompChartJetsYoung := by
  intro j
  have hdata : ∀ i : ℕ, ∃ (C : ℝ) (k : ℕ), 0 < C ∧
      (1 ≤ i → ∀ (S R τ : ℝ), 0 < S → 1 ≤ R → ∀ y : Space, y ∉ axis →
        age R y < S →
        ‖iteratedFDeriv ℝ i (chart R τ) y‖ ≤ C * (1 + S) ^ k * (1 + |trans R y|)) := by
    intro i
    by_cases hi : 1 ≤ i
    · obtain ⟨C, k, hC, h⟩ := UnforcedLeray.Short.IIb.chartJets i hi
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
  intro S R τ M b hS hR hM hb' y hy hage hbd n hn
  have hR0 : 0 < R := lt_of_lt_of_le one_pos hR
  have hS1 : (1 : ℝ) ≤ 1 + S := by linarith
  have hS0 : (0 : ℝ) ≤ 1 + S := by linarith
  have hchart : ContDiffOn ℝ ∞ (chart R τ) axisᶜ :=
    UnforcedLeray.Short.IIb.ChartJetsAux.contDiffOn_chart hR0.ne' τ
  have hopen : IsOpen (axisᶜ : Set Space) := isOpen_compl_axis
  have ht : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := isOpen_Ioi.prod isOpen_univ
  have hx : y ∈ (axisᶜ : Set Space) := hy
  have hmaps : MapsTo (chart R τ) (axisᶜ : Set Space) (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) :=
    fun z hz => ⟨age_pos hR0.ne' hz, mem_univ _⟩
  have hcy : chart R τ y ∈ Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)) := hmaps hx
  obtain ⟨w, hw⟩ : ∃ w : ℝ, w = 1 + |trans R y| := ⟨_, rfl⟩
  have hw1 : 1 ≤ w := by rw [hw]; linarith [abs_nonneg (trans R y)]
  have hw0 : 0 < w := by linarith
  have hwj : 0 < w ^ j := pow_pos hw0 j
  -- profile bounds at the chart point (the weight `(1+|η|)^j` is `w^j`)
  have hbound0 : ∀ i, i ≤ n →
      ‖iteratedFDerivWithin ℝ i b (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) (chart R τ y)‖ ≤
        M * (w ^ j)⁻¹ := by
    intro i hi
    rw [iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) i ht hcy]
    have h := hbd i (le_trans hi hn)
    rw [← hw] at h
    have h' : ‖iteratedFDeriv ℝ i b (chart R τ y)‖ * w ^ j ≤ M := by
      rw [mul_comm]; exact h
    rw [le_mul_inv_iff₀ hwj]
    exact h'
  -- chart bounds on the open set
  have hD : ∀ i, 1 ≤ i → i ≤ n → ‖iteratedFDerivWithin ℝ i (chart R τ) axisᶜ y‖
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
  have key := norm_iteratedFDerivWithin_comp_le (𝕜 := ℝ) (g := b) (f := chart R τ)
    (n := n) (s := axisᶜ) (t := Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) (x := y) (N := ∞)
    hb' hchart (by exact_mod_cast le_top) ht.uniqueDiffOn hopen.uniqueDiffOn hmaps hx hbound0 hD
  have e : iteratedFDeriv ℝ n (fun z => b (chart R τ z)) y =
      iteratedFDerivWithin ℝ n (b ∘ chart R τ) axisᶜ y :=
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

#print axioms bgCompChartJetsYoung

end UnforcedLeray.Short.PartIIIb.Concrete
