import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.RingLift.ChartJets
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.RingLift.SqrtFrameJets
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.RingLift.OffAxis
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.InletProfileWeightedJets
import UnforcedLeray.Short.PartIIa.Tasks.R08InletSolenoidal.InletSmoothExt.AxisFlatSmooth
import UnforcedLeray.Lib.AxisymmetricB.FlatExtension

/-!
# Smoothness of the frozen-stream datum columns off the origin

Helper for `PartII-b:B2` (`Short/PartII-b/Tasks/DatumFacts.lean`).
Shows that for each `i : Fin 2`, the datum column
`Nv p.R (fun m => datumProfile p.ε (p.frozenStream i) m.2) 0`
is `C^∞` on `{0}ᶜ`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb.DatumFactsAux

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.Blueprint UnforcedLeray.Axi
open UnforcedLeray.Short.PartIIa

abbrev E3 := ℝ × (ℝ × ℝ)

/-- Pointwise composite jet bound for `b ∘ chart R τ` at an off-axis point `y`, requiring the
profile bound only at `chart R τ y`. -/
theorem compChart_pointwise_jet (j : ℕ) :
    ∃ (C : ℝ) (k : ℕ), 0 < C ∧
      ∀ (S R τ M : ℝ) (b : E3 → Axi.Merid), 0 < S → 1 ≤ R → 0 ≤ M →
        ContDiff ℝ ∞ b →
        ∀ y : Space, y ∉ Axi.axis → Axi.age R y < S →
          (∀ l ≤ j, (1 + |(Axi.chart R τ y).2.2|) ^ j *
            ‖iteratedFDeriv ℝ l b (Axi.chart R τ y)‖ ≤ M) →
          ∀ n ≤ j,
            ‖iteratedFDeriv ℝ n (fun z => b (Axi.chart R τ z)) y‖ ≤ C * (1 + S) ^ k * M := by
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
  intro S R τ M b hS hR hM hb' y hy hage hbd n hn
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
  have hbound0 : ∀ i, i ≤ n →
      ‖iteratedFDerivWithin ℝ i b univ (Axi.chart R τ y)‖ ≤ M * (w ^ j)⁻¹ := by
    intro i hi
    rw [iteratedFDerivWithin_univ]
    have h := hbd i (le_trans hi hn)
    have hxy : (Axi.chart R τ y).2.2 = Axi.trans R y := rfl
    rw [hxy, ← hw] at h
    have h' : ‖iteratedFDeriv ℝ i b (Axi.chart R τ y)‖ * w ^ j ≤ M := by
      rw [mul_comm]; exact h
    rw [le_mul_inv_iff₀ hwj]
    exact h'
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
  have h1 : (n.factorial : ℝ) * M * A ^ n * (1 + S) ^ (K * n) * (w ^ n * (w ^ j)⁻¹)
      ≤ (n.factorial : ℝ) * M * A ^ n * (1 + S) ^ (K * n) * 1 := by
    apply mul_le_mul_of_nonneg_left hwinv
    exact mul_nonneg (mul_nonneg (mul_nonneg hfac0 hM) (pow_nonneg hA0 _)) (pow_nonneg hS0 _)
  have h2 : (n.factorial : ℝ) * A ^ n ≤ (j.factorial : ℝ) * A ^ j :=
    mul_le_mul hfac hAn (pow_nonneg hA0 _) (by positivity)
  have h3 : (n.factorial : ℝ) * A ^ n * (1 + S) ^ (K * n)
      ≤ (j.factorial : ℝ) * A ^ j * (1 + S) ^ (K * j) :=
    mul_le_mul h2 hQ (pow_nonneg hS0 _) (mul_nonneg (by positivity) (pow_nonneg hA0 _))
  calc (n.factorial : ℝ) * M * A ^ n * (1 + S) ^ (K * n) * (w ^ n * (w ^ j)⁻¹)
      ≤ ((n.factorial : ℝ) * A ^ n * (1 + S) ^ (K * n)) * M := by linarith
    _ ≤ ((j.factorial : ℝ) * A ^ j * (1 + S) ^ (K * j)) * M :=
      mul_le_mul_of_nonneg_right h3 hM

/-- Pointwise off-axis jet bound for `Nv R b τ` at `y ∉ axis`. -/
theorem nv_pointwise_jet (j : ℕ) :
    ∃ (C : ℝ) (k : ℕ), 0 < C ∧
      ∀ (S R τ M : ℝ) (b : E3 → Axi.Merid), 0 < S → 1 ≤ R → 0 ≤ M →
        ContDiff ℝ ∞ b →
        ∀ y : Space, y ∉ Axi.axis → Axi.age R y ≤ S →
          (∀ l ≤ j, (1 + |(Axi.chart R τ y).2.2|) ^ j *
            ‖iteratedFDeriv ℝ l b (Axi.chart R τ y)‖ ≤ M) →
          ‖iteratedFDeriv ℝ j (Axi.Nv R b τ) y‖ ≤ C * (1 + S) ^ k * M := by
  have hSFall : ∀ i : ℕ, ∃ (C : ℝ) (k : ℕ), 0 < C ∧ ∀ (S R : ℝ), 0 < S → 1 ≤ R →
      ∀ y : Space, y ∉ Axi.axis → Axi.age R y < S →
        ‖iteratedFDeriv ℝ i (fun z => √(Axi.age R z)) y‖ ≤ C * (1 + S) ^ k ∧
        ‖iteratedFDeriv ℝ i Axi.frameL y‖ ≤ C * (1 + S) ^ k :=
    fun i => sqrtFrameJets i
  choose Cs ks hCs hSF using hSFall
  obtain ⟨C2, k2, hC2, hcc⟩ := compChart_pointwise_jet j
  obtain ⟨Cq, hCq⟩ : ∃ x : ℝ, x = ∑ i ∈ Finset.range (j + 1), Cs i := ⟨_, rfl⟩
  obtain ⟨Kq, hKq⟩ : ∃ K : ℕ, K = ∑ i ∈ Finset.range (j + 1), ks i := ⟨_, rfl⟩
  have hCs_le : ∀ i, i ≤ j → Cs i ≤ Cq := fun i hi => by
    rw [hCq]
    exact Finset.single_le_sum (f := Cs) (fun l _ => (hCs l).le)
      (Finset.mem_range.2 (Nat.lt_succ_of_le hi))
  have hks_le : ∀ i, i ≤ j → ks i ≤ Kq := fun i hi => by
    rw [hKq]
    exact Finset.single_le_sum (f := ks) (fun l _ => Nat.zero_le _)
      (Finset.mem_range.2 (Nat.lt_succ_of_le hi))
  have hCq0 : 0 < Cq := by
    rw [hCq]
    exact Finset.sum_pos (fun l _ => hCs l) ⟨0, by simp⟩
  refine ⟨(((j : ℝ) + 1) * 2 ^ j) ^ 2 * Cq ^ 2 * C2 * 2 ^ (2 * Kq + k2), 2 * Kq + k2, ?_, ?_⟩
  · exact mul_pos (mul_pos (mul_pos (pow_pos (by positivity) 2) (pow_pos hCq0 2)) hC2)
      (by positivity)
  intro S R τ M b hS hR hM hb y hy hage hder
  have hR0 : R ≠ 0 := (lt_of_lt_of_le one_pos hR).ne'
  have hopen : IsOpen (Axi.axisᶜ : Set Space) := Axi.isOpen_compl_axis
  have hyc : y ∈ (Axi.axisᶜ : Set Space) := hy
  have hS' : 0 < S + 1 := by linarith
  have hage' : Axi.age R y < S + 1 := by linarith
  have hpos : 0 ≤ 1 + (S + 1) := by linarith
  have hS1 : (1 : ℝ) ≤ 1 + (S + 1) := by linarith
  have hA : ∀ i, i ≤ j → ‖iteratedFDerivWithin ℝ i (fun z => √(Axi.age R z)) Axi.axisᶜ y‖
      ≤ Cq * (1 + (S + 1)) ^ Kq := by
    intro i hi
    rw [iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := fun z => √(Axi.age R z)) i hopen hyc]
    refine ((hSF i (S + 1) R hS' hR y hy hage').1).trans ?_
    exact mul_le_mul (hCs_le i hi) (pow_le_pow_right₀ hS1 (hks_le i hi)) (pow_nonneg hpos _)
      hCq0.le
  have hB : ∀ i, i ≤ j → ‖iteratedFDerivWithin ℝ i Axi.frameL Axi.axisᶜ y‖
      ≤ Cq * (1 + (S + 1)) ^ Kq := by
    intro i hi
    rw [iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := Axi.frameL) i hopen hyc]
    refine ((hSF i (S + 1) R hS' hR y hy hage').2).trans ?_
    exact mul_le_mul (hCs_le i hi) (pow_le_pow_right₀ hS1 (hks_le i hi)) (pow_nonneg hpos _)
      hCq0.le
  have hC : ∀ i, i ≤ j → ‖iteratedFDerivWithin ℝ i (fun z => b (Axi.chart R τ z)) Axi.axisᶜ y‖
      ≤ C2 * (1 + (S + 1)) ^ k2 * M := by
    intro i hi
    rw [iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := fun z => b (Axi.chart R τ z)) i hopen hyc]
    exact hcc (S + 1) R τ M b hS' hR hM hb y hy hage' hder i hi
  have hX : 0 ≤ Cq * (1 + (S + 1)) ^ Kq := mul_nonneg hCq0.le (pow_nonneg hpos _)
  have hY : 0 ≤ C2 * (1 + (S + 1)) ^ k2 * M :=
    mul_nonneg (mul_nonneg hC2.le (pow_nonneg hpos _)) hM
  have hGc : ∀ m, m ≤ j → ‖iteratedFDerivWithin ℝ m
      (fun z => Axi.frameL z (b (Axi.chart R τ z))) Axi.axisᶜ y‖
      ≤ ((j : ℝ) + 1) * 2 ^ j * (Cq * (1 + (S + 1)) ^ Kq) * (C2 * (1 + (S + 1)) ^ k2 * M) := by
    intro m hm
    have h := RingLiftOffAxisAux.clm_bound (f := Axi.frameL) (g := fun z => b (Axi.chart R τ z))
      (n := m) (A := Cq * (1 + (S + 1)) ^ Kq) (B := C2 * (1 + (S + 1)) ^ k2 * M)
      ChartJetsAux.contDiffOn_frameL (ChartJetsAux.contDiffOn_comp_chart hb hR0 τ)
      hopen.uniqueDiffOn hyc (fun i hi => hB i (hi.trans hm)) (fun i hi => hC i (hi.trans hm))
    refine h.trans ?_
    have hmono : ((m : ℝ) + 1) * 2 ^ m ≤ ((j : ℝ) + 1) * 2 ^ j := by
      have h1 : (m : ℝ) ≤ j := by exact_mod_cast hm
      have h2 : (2 : ℝ) ^ m ≤ 2 ^ j := pow_le_pow_right₀ (by norm_num) hm
      exact mul_le_mul (by linarith) h2 (by positivity) (by positivity)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hmono hX) hY
  have hSmul : ‖iteratedFDerivWithin ℝ j (fun z => √(Axi.age R z) • Axi.frameL z
      (b (Axi.chart R τ z))) Axi.axisᶜ y‖
      ≤ ((j : ℝ) + 1) * 2 ^ j * (Cq * (1 + (S + 1)) ^ Kq) *
        (((j : ℝ) + 1) * 2 ^ j * (Cq * (1 + (S + 1)) ^ Kq) * (C2 * (1 + (S + 1)) ^ k2 * M)) :=
    RingLiftOffAxisAux.smul_bound (f := fun z => √(Axi.age R z))
      (g := fun z => Axi.frameL z (b (Axi.chart R τ z))) (n := j)
      (A := Cq * (1 + (S + 1)) ^ Kq)
      (B := ((j : ℝ) + 1) * 2 ^ j * (Cq * (1 + (S + 1)) ^ Kq) * (C2 * (1 + (S + 1)) ^ k2 * M))
      (ChartJetsAux.contDiffOn_sqrt_age hR0)
      (ChartJetsAux.contDiffOn_frameL.clm_apply (ChartJetsAux.contDiffOn_comp_chart hb hR0 τ))
      hopen.uniqueDiffOn hyc hA (fun i hi => hGc i hi)
  have e := iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := Axi.Nv R b τ) j hopen hyc
  rw [← e]
  have hNv : ‖iteratedFDerivWithin ℝ j (Axi.Nv R b τ) Axi.axisᶜ y‖
      ≤ ((j : ℝ) + 1) * 2 ^ j * (Cq * (1 + (S + 1)) ^ Kq) *
        (((j : ℝ) + 1) * 2 ^ j * (Cq * (1 + (S + 1)) ^ Kq) * (C2 * (1 + (S + 1)) ^ k2 * M)) := by
    rw [ChartJetsAux.Nv_eq_fun]
    exact hSmul
  have hsub : (1 + (S + 1) : ℝ) ≤ 2 * (1 + S) := by linarith
  have hpowK : (1 + (S + 1) : ℝ) ^ (2 * Kq + k2) ≤ 2 ^ (2 * Kq + k2) * (1 + S) ^ (2 * Kq + k2) := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ hpos hsub _
  have hK : 0 ≤ ((((j : ℝ) + 1) * 2 ^ j) ^ 2 * Cq ^ 2 * C2) :=
    mul_nonneg (mul_nonneg (by positivity) (by positivity)) hC2.le
  calc _ ≤ _ := hNv
    _ = ((((j : ℝ) + 1) * 2 ^ j) ^ 2 * Cq ^ 2 * C2) * (1 + (S + 1)) ^ (2 * Kq + k2) * M := by
      ring
    _ ≤ ((((j : ℝ) + 1) * 2 ^ j) ^ 2 * Cq ^ 2 * C2) * (2 ^ (2 * Kq + k2) * (1 + S) ^ (2 * Kq + k2))
        * M := by
      apply mul_le_mul_of_nonneg_right _ hM
      exact mul_le_mul_of_nonneg_left hpowK hK
    _ = ((((j : ℝ) + 1) * 2 ^ j) ^ 2 * Cq ^ 2 * C2 * 2 ^ (2 * Kq + k2)) * (1 + S) ^ (2 * Kq + k2)
        * M := by ring

/-- On `flatRegion δ M`, a profile `b` with rapid transverse decay gives `‖D^j (Nv R b 0) y‖ ≤ K ϱ(y)`. -/
theorem nv_bound_on_flatRegion {R : ℝ} (hR : 1 ≤ R) {b : E3 → Axi.Merid} (hb : ContDiff ℝ ∞ b)
    (hbw : ∀ j w : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ l ≤ j, ∀ m : E3,
      (1 + |m.2.2|) ^ (j + w) * ‖iteratedFDeriv ℝ l b m‖ ≤ B)
    {δ M : ℝ} (hδ : 0 < δ) (j : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ y ∈ flatRegion δ M,
      ‖iteratedFDeriv ℝ j (Axi.Nv R b 0) y‖ ≤ K * Axi.ϱ y := by
  obtain ⟨C, k, hC, hnv⟩ := nv_pointwise_jet j
  obtain ⟨B, hB0, hB⟩ := hbw j (2 * k + 1)
  refine ⟨C * (1 + R ^ 2) ^ k * B * δ⁻¹ ^ (2 * k + 1), by positivity, ?_⟩
  intro y hy
  obtain ⟨hya, hy1, hyδ, _⟩ := hy
  have hR0 : 0 < R := lt_of_lt_of_le one_pos hR
  have hr : 0 < Axi.ϱ y := Axi.ϱ_pos hya
  have hage : 0 < Axi.age R y := Axi.age_pos hR0.ne' hya
  set w := 1 + |Axi.trans R y| with hw
  have hw0 : 0 < w := by rw [hw]; positivity
  have hMy0 : 0 ≤ B * (w ^ (2 * k + 1))⁻¹ := by positivity
  have hder : ∀ l ≤ j, (1 + |(Axi.chart R 0 y).2.2|) ^ j *
      ‖iteratedFDeriv ℝ l b (Axi.chart R 0 y)‖ ≤ B * (w ^ (2 * k + 1))⁻¹ := by
    intro l hl
    have hxy : (Axi.chart R 0 y).2.2 = Axi.trans R y := rfl
    have hb' := hB l hl (Axi.chart R 0 y)
    rw [hxy, ← hw, pow_add, mul_right_comm] at hb'
    exact (le_mul_inv_iff₀ (pow_pos hw0 _)).2 hb'
  have hj := hnv (Axi.age R y) R 0 (B * (w ^ (2 * k + 1))⁻¹) b hage hR hMy0 hb y hya le_rfl hder
  have hage_le : 1 + Axi.age R y ≤ (1 + R ^ 2) * (Axi.ϱ y)⁻¹ ^ 2 := by
    unfold Axi.age
    have hr2 : (Axi.ϱ y) ^ 2 ≤ 1 := by nlinarith [hy1]
    have h1 : 1 ≤ (Axi.ϱ y)⁻¹ ^ 2 := by
      rw [inv_pow]
      exact one_le_inv₀ (pow_pos hr 2) |>.2 hr2
    have h2 : R ^ 2 / (Axi.ϱ y) ^ 2 = R ^ 2 * (Axi.ϱ y)⁻¹ ^ 2 := by
      rw [div_eq_mul_inv, inv_pow]
    linarith
  have hpow_age : (1 + Axi.age R y) ^ k ≤ (1 + R ^ 2) ^ k * (Axi.ϱ y)⁻¹ ^ (2 * k) := by
    calc (1 + Axi.age R y) ^ k
        ≤ ((1 + R ^ 2) * (Axi.ϱ y)⁻¹ ^ 2) ^ k := pow_le_pow_left₀ (by positivity) hage_le k
      _ = (1 + R ^ 2) ^ k * (Axi.ϱ y)⁻¹ ^ (2 * k) := by rw [mul_pow, ← pow_mul]
  have htr_ge : δ * (Axi.ϱ y)⁻¹ ≤ w := by
    have htr : |Axi.trans R y| = R * |y 2| * (Axi.ϱ y)⁻¹ := by
      unfold Axi.trans
      rw [abs_div, abs_mul, abs_of_pos hR0, abs_of_pos hr, div_eq_mul_inv]
    have h1 : 1 * δ ≤ R * |y 2| := mul_le_mul hR hyδ hδ.le hR0.le
    have h2 : δ * (Axi.ϱ y)⁻¹ ≤ R * |y 2| * (Axi.ϱ y)⁻¹ := by
      simpa using mul_le_mul_of_nonneg_right h1 (inv_nonneg.2 hr.le)
    rw [hw, htr]
    linarith
  have hwinv : w⁻¹ ≤ δ⁻¹ * Axi.ϱ y := by
    have h1 := inv_anti₀ (mul_pos hδ (inv_pos.2 hr)) htr_ge
    rwa [mul_inv, inv_inv] at h1
  have hpow_w : (w ^ (2 * k + 1))⁻¹ ≤ δ⁻¹ ^ (2 * k + 1) * (Axi.ϱ y) ^ (2 * k) * Axi.ϱ y := by
    rw [← inv_pow]
    calc (w⁻¹) ^ (2 * k + 1)
        ≤ (δ⁻¹ * Axi.ϱ y) ^ (2 * k + 1) := pow_le_pow_left₀ (inv_nonneg.2 hw0.le) hwinv _
      _ = δ⁻¹ ^ (2 * k + 1) * (Axi.ϱ y) ^ (2 * k) * Axi.ϱ y := by
        rw [mul_pow, pow_succ]
        ring
  have hcancel : (Axi.ϱ y)⁻¹ ^ (2 * k) * (Axi.ϱ y) ^ (2 * k) = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ hr.ne', one_pow]
  calc ‖iteratedFDeriv ℝ j (Axi.Nv R b 0) y‖
      ≤ C * (1 + Axi.age R y) ^ k * (B * (w ^ (2 * k + 1))⁻¹) := hj
    _ = C * B * ((1 + Axi.age R y) ^ k * (w ^ (2 * k + 1))⁻¹) := by ring
    _ ≤ C * B * (((1 + R ^ 2) ^ k * (Axi.ϱ y)⁻¹ ^ (2 * k)) *
          (δ⁻¹ ^ (2 * k + 1) * (Axi.ϱ y) ^ (2 * k) * Axi.ϱ y)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul hpow_age hpow_w (by positivity) (by positivity)
    _ = C * (1 + R ^ 2) ^ k * B * δ⁻¹ ^ (2 * k + 1) *
          ((Axi.ϱ y)⁻¹ ^ (2 * k) * (Axi.ϱ y) ^ (2 * k)) * Axi.ϱ y := by ring
    _ = C * (1 + R ^ 2) ^ k * B * δ⁻¹ ^ (2 * k + 1) * Axi.ϱ y := by
      rw [hcancel, mul_one]

/-- A field `f` that is `C^∞` off the axis, vanishes on the axis, and satisfies
`‖D^j f(y)‖ ≤ K_j ϱ(y)` on every `flatRegion δ M` (`δ > 0`) is `C^∞` at every nonzero axis point. -/
theorem contDiffAt_of_rho_bound {f : Space → Space} (hf : ContDiffOn ℝ ∞ f Axi.axisᶜ)
    (hf0 : ∀ y ∈ Axi.axis, f y = 0)
    (hfb : ∀ δ M : ℝ, 0 < δ → ∀ j : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ y ∈ flatRegion δ M,
      ‖iteratedFDeriv ℝ j f y‖ ≤ K * Axi.ϱ y)
    {x₀ : Space} (_hx₀ : x₀ ∈ Axi.axis) (hx₀2 : x₀ 2 ≠ 0) :
    ContDiffAt ℝ ∞ f x₀ := by
  set a : ℝ := |x₀ 2| with ha
  have ha0 : 0 < a := abs_pos.2 hx₀2
  choose Kf hKf0 hKf using hfb (a / 2) (2 * a) (by linarith)
  obtain ⟨ψ, hψin, hψout⟩ : ∃ ψ : ContDiffBump x₀, ψ.rIn = a / 4 ∧ ψ.rOut = a / 2 :=
    ⟨⟨a / 4, a / 2, by linarith, by linarith⟩, rfl, rfl⟩
  have hψS : ContDiff ℝ ∞ (⇑ψ) := ψ.contDiff
  choose Bψ hBψ using fun n => afs_cutoff_bdd ψ n
  have hgS : ContDiffOn ℝ ∞ (fun y => ψ y • f y) Axi.axisᶜ := hψS.contDiffOn.smul hf
  have hkey : ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ y : Space, y ∉ Axi.axis → Axi.ϱ y < 1 →
      ‖iteratedFDeriv ℝ n (fun z => ψ z • f z) y‖ ≤ C * Axi.ϱ y := by
    intro n
    set Cn : ℝ := ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * |Bψ i| * Kf (n - i) with hCn
    have hCn0 : 0 ≤ Cn := Finset.sum_nonneg fun i _ => by
      have := hKf0 (n - i)
      positivity
    refine ⟨Cn, hCn0, fun y hy hy1 => ?_⟩
    by_cases hd : dist y x₀ ≤ a / 2
    · have hd' : |y 2 - x₀ 2| ≤ a / 2 := (afs_abs_coord_le x₀ y).trans hd
      have hA := abs_sub_abs_le_abs_sub (x₀ 2) (y 2)
      have hB := abs_sub_abs_le_abs_sub (y 2) (x₀ 2)
      have hC := abs_sub_comm (x₀ 2) (y 2)
      have hyW : y ∈ flatRegion (a / 2) (2 * a) := ⟨hy, hy1, by linarith, by linarith⟩
      have hL := afs_leibniz (f := ⇑ψ) (g := f) hψS.contDiffOn hf hy n
      calc ‖iteratedFDeriv ℝ n (fun z => ψ z • f z) y‖
          ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (⇑ψ) y‖ *
              ‖iteratedFDeriv ℝ (n - i) f y‖ := hL
        _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * |Bψ i| * Kf (n - i) * Axi.ϱ y := by
          refine Finset.sum_le_sum fun i _ => ?_
          have h1 : ‖iteratedFDeriv ℝ i (⇑ψ) y‖ ≤ |Bψ i| := (hBψ i y).trans (le_abs_self _)
          have h2 : ‖iteratedFDeriv ℝ (n - i) f y‖ ≤ Kf (n - i) * Axi.ϱ y := hKf (n - i) y hyW
          have h3 := mul_le_mul h1 h2 (norm_nonneg _) (abs_nonneg _)
          have h4 := mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ (n.choose i : ℝ))
          linarith
        _ = Cn * Axi.ϱ y := by rw [hCn, Finset.sum_mul]
    · have hd' : a / 2 < dist y x₀ := not_le.1 hd
      have hU : {z : Space | a / 2 < dist z x₀} ∈ 𝓝 y :=
        (isOpen_lt continuous_const (continuous_id.dist continuous_const)).mem_nhds hd'
      have hgz : (fun z => ψ z • f z) =ᶠ[𝓝 y] (fun _ : Space => (0 : Space)) := by
        filter_upwards [hU] with z hz
        have hz0 : ψ z = 0 := ψ.zero_of_le_dist (x := z) (by rw [hψout]; exact le_of_lt hz)
        simp [hz0]
      rw [(hgz.iteratedFDeriv ℝ n).eq_of_nhds, iteratedFDeriv_fun_zero]
      simp only [Pi.zero_apply, norm_zero]
      exact mul_nonneg hCn0 (Axi.ϱ_nonneg y)
  choose Cg hCg0 hCg using hkey
  have hgC : ∀ k : ℕ, ContDiff ℝ k (fun y => ψ y • f y) := by
    intro k
    refine Axi.contDiff_of_tendsto_axis k (fun y hy => by simp [hf0 y hy])
      (hgS.of_le (by exact_mod_cast le_top)) ?_
    intro n _ y₀ hy₀
    have hρ0 : Axi.ϱ y₀ = 0 := (Axi.mem_axis_iff y₀).1 hy₀
    have hlim : Tendsto (fun y => Cg n * Axi.ϱ y) (𝓝[Axi.axisᶜ] y₀) (𝓝 0) := by
      have hc : Continuous (fun y => Cg n * Axi.ϱ y) := continuous_const.mul Axi.continuous_ϱ
      have := hc.tendsto y₀
      rw [hρ0, mul_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    have hnear : ∀ᶠ y in 𝓝[Axi.axisᶜ] y₀, Axi.ϱ y < 1 := by
      have : ∀ᶠ y in 𝓝 y₀, Axi.ϱ y < 1 :=
        Axi.continuous_ϱ.continuousAt.eventually_lt continuousAt_const (by rw [hρ0]; exact one_pos)
      exact this.filter_mono nhdsWithin_le_nhds
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim
    filter_upwards [hnear, self_mem_nhdsWithin] with y hy1 hy
    exact hCg n y hy hy1
  have hfg : f =ᶠ[𝓝 x₀] (fun y => ψ y • f y) := by
    filter_upwards [Metric.ball_mem_nhds x₀ (show (0 : ℝ) < a / 4 by linarith)] with y hy
    have hψ1 : ψ y = 1 := by
      apply ψ.one_of_mem_closedBall
      rw [hψin]
      exact Metric.ball_subset_closedBall hy
    simp [hψ1]
  rw [contDiffAt_infty]
  intro k
  exact ((hgC k).contDiffAt).congr_of_eventuallyEq hfg

/-- The projection `(s, (q, η)) ↦ (0, (q, η))` on `E3 = ℝ × (ℝ × ℝ)`. -/
def projZeroS : E3 →L[ℝ] E3 :=
  (0 : E3 →L[ℝ] ℝ).prod (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))

theorem projZeroS_apply (m : E3) : projZeroS m = (0, m.2) := rfl

theorem norm_projZeroS_le : ‖projZeroS‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun m => ?_
  rw [projZeroS_apply, Prod.norm_def, norm_zero, one_mul, max_eq_right (norm_nonneg m.2)]
  exact le_max_right ‖m.1‖ ‖m.2‖

/-- At `s = 0`, `p.inletProfile i (0, m.2)` equals `datumProfile p.ε (p.frozenStream i) m.2`. -/
theorem datumProfile_frozenStream_eq_inletProfile (p : Params) (i : Fin 2) (m : E3) :
    datumProfile p.ε (p.frozenStream i) m.2 = p.inletProfile i (projZeroS m) := by
  have hH4 : 0 < p.H / 4 := by have := p.H_pos; positivity
  have hev : p.cutStream i =ᶠ[𝓝 (0, m.2)] (fun n : E3 => p.frozenStream i n.2) := by
    have hU : {n : E3 | n.1 < p.H / 4} ∈ 𝓝 (0, m.2) :=
      (isOpen_lt continuous_fst continuous_const).mem_nhds hH4
    filter_upwards [hU] with n hn
    unfold Params.cutStream
    rw [ageCutoff_eq_one p.H_pos (le_of_lt hn), one_mul]
  have hfd : fderiv ℝ (p.cutStream i) (0, m.2) =
      fderiv ℝ (fun n : E3 => p.frozenStream i n.2) (0, m.2) := hev.fderiv_eq
  have hcomp : (fun n : E3 => p.frozenStream i n.2) =
      (p.frozenStream i) ∘ (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)) := rfl
  have hfdsnd : ∀ v : ℝ × ℝ,
      fderiv ℝ (fun n : E3 => p.frozenStream i n.2) (0, m.2) (0, v) =
        fderiv ℝ (p.frozenStream i) m.2 v := by
    intro v
    by_cases hdiff : DifferentiableAt ℝ (p.frozenStream i) m.2
    · rw [hcomp, (hdiff.hasFDerivAt.comp (0, m.2) hasFDerivAt_snd).fderiv]
      rfl
    · have hnd : ¬ DifferentiableAt ℝ (fun n : E3 => p.frozenStream i n.2) (0, m.2) := by
        intro hd
        apply hdiff
        have h1 : (p.frozenStream i) =
            (fun n : E3 => p.frozenStream i n.2) ∘ (fun x : ℝ × ℝ => ((0 : ℝ), x)) := rfl
        rw [h1]
        exact hd.comp m.2 ((differentiableAt_const 0).prodMk differentiableAt_id)
      rw [fderiv_zero_of_not_differentiableAt hdiff, fderiv_zero_of_not_differentiableAt hnd]
      rfl
  unfold Params.inletProfile Axi.ringStreamProfile datumProfile partialEta partialXi
  simp only [projZeroS_apply, Axi.dEta, Axi.dQ, Axi.dS, hfd, hfdsnd]
  have hcut0 : p.cutStream i (0, m.2) = p.frozenStream i m.2 := by
    unfold Params.cutStream
    rw [ageCutoff_eq_one p.H_pos hH4.le, one_mul]
  have hRinv : p.R⁻¹ = p.ε := inv_inv p.ε
  rw [hcut0, hRinv]
  simp

/-- Each frozen-stream datum column `Nv p.R (fun m => datumProfile p.ε (p.frozenStream i) m.2) 0`
is `C^∞` on `{0}ᶜ` in the background regime (`p.ν ≤ 1`). -/
theorem contDiffOn_frozenDatum
    {lam : ℂ} {q : Planar.Profile} (hq : Planar.IsGrowingEigenpair lam q)
    {dm dp : ℝ} {p : Params} {d : ℝ} (hreg : BgRegime p d dm dp)
    (hν1 : p.ν ≤ 1) (hmode : p.mode = q) (i : Fin 2) :
    ContDiffOn ℝ ∞ (Axi.Nv p.R (fun m => datumProfile p.ε (p.frozenStream i) m.2) 0) {0}ᶜ := by
  have hνpos : 0 < p.ν := p.ν_pos
  have hR1 : 1 ≤ p.R := by
    have hε : p.ε ≤ 1 := by
      rw [hreg.eps_eq]
      apply Real.exp_le_one_iff.mpr
      have : 0 ≤ d / p.ν := div_nonneg (by linarith [hreg.dm_pos, hreg.dm_le]) hνpos.le
      rw [neg_div]; linarith
    exact one_le_inv₀ p.ε_pos |>.mpr hε
  have hR0 : p.R ≠ 0 := p.R_pos.ne'
  have hc1 : 1 ≤ p.c := by
    rw [hreg.c_eq, one_le_inv₀ (by positivity)]
    nlinarith
  have hH : 0 < p.H := p.H_pos
  set b : E3 → Axi.Merid := fun m => datumProfile p.ε (p.frozenStream i) m.2 with hb_def
  have hb_eq : b = (p.inletProfile i) ∘ projZeroS :=
    funext fun m => datumProfile_frozenStream_eq_inletProfile p i m
  obtain ⟨_, _, _, _, _, h0'⟩ := cutStreamJets lam q hq 1
  have hcutsm0 : ContDiff ℝ ∞ (p.cutStream i) := (h0' p hmode hc1 hH i).1
  have hinletsm : ContDiff ℝ ∞ (p.inletProfile i) := by
    unfold Params.inletProfile
    exact inletCD_ringStreamProfile hcutsm0
  have hb_sm : ContDiff ℝ ∞ b := by
    rw [hb_eq]
    exact hinletsm.comp projZeroS.contDiff
  have hbw : ∀ j w : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ l ≤ j, ∀ m : E3,
      (1 + |m.2.2|) ^ (j + w) * ‖iteratedFDeriv ℝ l b m‖ ≤ B := by
    intro j w
    obtain ⟨C3, κ, N, hC3, hκ, h3'⟩ := cutStreamJets lam q hq (j + 1)
    obtain ⟨C4, hC4, h4'⟩ := ringStreamJetsDecay j
    have hcpos : 0 < p.c := by linarith
    obtain ⟨hcutsm, hcut⟩ := h3' p hmode hc1 hH i
    set M : ℝ := C3 * (1 + p.H⁻¹) ^ (j + 1) * p.c ^ N with hM
    have hM0 : 0 ≤ M := by positivity
    have hring := h4' p.R (p.H / 2) p.c κ M (p.cutStream i) hR1 (by positivity) hcpos hκ hM0
      hcutsm
      (fun x hx => by
        unfold Params.cutStream
        simp [ageCutoff_eq_zero hH hx.le])
      (fun x hx => cutStreamSVanish lam q hq p hmode hc1 hH i x hx)
      (fun l hl x => hcut l hl x)
    set W : ℝ := Real.exp 1 * (j + w).factorial * (1 + (κ / 2 / p.c)⁻¹) ^ (j + w) with hW
    set A : ℝ := C4 * (1 + p.H / 2) * (1 + p.c / κ) * M with hA
    refine ⟨A * W, by positivity, fun l hl m => ?_⟩
    have hcomp : ‖iteratedFDeriv ℝ l b m‖ ≤
        ‖iteratedFDeriv ℝ l (p.inletProfile i) (projZeroS m)‖ := by
      rw [hb_eq, projZeroS.iteratedFDeriv_comp_right hinletsm m (by exact_mod_cast le_top)]
      refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
      have hprod : ∏ _i : Fin l, ‖projZeroS‖ ≤ 1 := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        exact pow_le_one₀ (norm_nonneg _) norm_projZeroS_le
      calc _ ≤ ‖iteratedFDeriv ℝ l (p.inletProfile i) (projZeroS m)‖ * 1 :=
            mul_le_mul_of_nonneg_left hprod (norm_nonneg _)
        _ = _ := mul_one _
    have hmain := hring l hl (projZeroS m)
    have hm2 : (projZeroS m).2.2 = m.2.2 := rfl
    rw [hm2] at hmain
    have ha : 0 < κ / 2 / p.c := by positivity
    have hwt : (1 + |m.2.2|) ^ (j + w) * Real.exp (-((κ / 2) * |m.2.2| / p.c)) ≤ W := by
      have e : -((κ / 2) * |m.2.2| / p.c) = -((κ / 2 / p.c) * |m.2.2|) := by ring
      rw [e]
      exact InletWeightAux.one_add_pow_mul_exp_le (j + w) ha (abs_nonneg m.2.2)
    calc (1 + |m.2.2|) ^ (j + w) * ‖iteratedFDeriv ℝ l b m‖
        ≤ (1 + |m.2.2|) ^ (j + w) * ‖iteratedFDeriv ℝ l (p.inletProfile i) (projZeroS m)‖ :=
          mul_le_mul_of_nonneg_left hcomp (by positivity)
      _ ≤ (1 + |m.2.2|) ^ (j + w) * (A * Real.exp (-((κ / 2) * |m.2.2| / p.c))) :=
          mul_le_mul_of_nonneg_left hmain (by positivity)
      _ = A * ((1 + |m.2.2|) ^ (j + w) * Real.exp (-((κ / 2) * |m.2.2| / p.c))) := by ring
      _ ≤ A * W := mul_le_mul_of_nonneg_left hwt (by positivity)
  have hoff : ContDiffOn ℝ ∞ (Axi.Nv p.R b 0) Axi.axisᶜ := by
    rw [ChartJetsAux.Nv_eq_fun]
    exact (ChartJetsAux.contDiffOn_sqrt_age hR0).smul
      (ChartJetsAux.contDiffOn_frameL.clm_apply (ChartJetsAux.contDiffOn_comp_chart hb_sm hR0 0))
  have hax0 : ∀ y ∈ Axi.axis, Axi.Nv p.R b 0 y = 0 := by
    intro y hy
    have h0 : Axi.ϱ y = 0 := (Axi.mem_axis_iff y).1 hy
    simp [Axi.Nv, Axi.age, h0]
  intro x hx
  by_cases hxa : x ∈ Axi.axis
  · have hx2 : x 2 ≠ 0 := fun h => hx (eq_zero_of_mem_axis_of_snd_eq_zero hxa h)
    exact (contDiffAt_of_rho_bound hoff hax0
      (fun δ M hδ j => nv_bound_on_flatRegion hR1 hb_sm hbw hδ j) hxa hx2).contDiffWithinAt
  · exact (hoff.contDiffAt (Axi.isOpen_compl_axis.mem_nhds hxa)).contDiffWithinAt

end UnforcedLeray.Short.IIb.DatumFactsAux
