import UnforcedLeray.Short.PartIIa.Sub.PartIIa_F04_2

/-!


Source of record: `the November 2 reference manuscript`, lines 1478-1480.

Construction. Fix the bump `ppBump` (positive exactly on `ball 0 (1/2)`, zero off `closedBall 0 (1/2)`),
window centres `c_j = j/2` for `j < n`, and `Φ(x) = ∑_j ppBump (x - c_j)`. The periodisation
`V(τ) = ∑_k Φ(τ - kP)` is smooth (locally a finite sum), `P`-periodic and positive once `2P < n`.
Then `η_j(τ) = ppBump (τ - c_j) / V(τ)` is smooth with compact support in a window of radius `1/2`,
and `∑_k ∑_j η_j(τ - kP) = V(τ)/V(τ) = 1`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

/-- A fixed smooth bump: positive on `ball 0 (1/2)`, zero off `closedBall 0 (1/2)`. -/
def ppBump : ContDiffBump (0 : ℝ) :=
  { rIn := 1 / 4, rOut := 1 / 2, rIn_pos := by norm_num, rIn_lt_rOut := by norm_num }

lemma ppBump_contDiff : ContDiff ℝ ∞ (ppBump : ℝ → ℝ) := ppBump.contDiff

lemma ppBump_nonneg (y : ℝ) : 0 ≤ ppBump y := ppBump.nonneg

lemma ppBump_pos {y : ℝ} (hy : |y| < 1 / 2) : 0 < ppBump y := by
  apply ppBump.pos_of_mem_ball
  show y ∈ Metric.ball (0 : ℝ) (1 / 2)
  rw [Metric.mem_ball, Real.dist_eq, sub_zero]
  exact hy

lemma ppBump_zero {y : ℝ} (hy : 1 / 2 ≤ |y|) : ppBump y = 0 := by
  apply ppBump.zero_of_le_dist
  rw [Real.dist_eq, sub_zero]
  exact hy

/-- Window centres `c_j = j/2`. -/
def ppC (n : ℕ) (j : Fin n) : ℝ := ((j : ℕ) : ℝ) / 2

/-- The shifted bumps summed over the windows. -/
def ppPhi (n : ℕ) (x : ℝ) : ℝ := ∑ j : Fin n, ppBump (x - ppC n j)

lemma ppPhi_nonneg (n : ℕ) (x : ℝ) : 0 ≤ ppPhi n x :=
  Finset.sum_nonneg (fun _ _ => ppBump_nonneg _)

lemma ppPhi_contDiff (n : ℕ) : ContDiff ℝ ∞ (ppPhi n) := by
  unfold ppPhi
  apply ContDiff.sum
  intro j _
  exact ppBump_contDiff.comp (contDiff_id.sub contDiff_const)

lemma ppPhi_bound (n : ℕ) : ∃ R : ℝ, ∀ x, R < |x| → ppPhi n x = 0 := by
  refine ⟨∑ j : Fin n, |ppC n j| + 1, fun x hx => ?_⟩
  unfold ppPhi
  apply Finset.sum_eq_zero
  intro j _
  apply ppBump_zero
  have hj : |ppC n j| ≤ ∑ i : Fin n, |ppC n i| :=
    Finset.single_le_sum (f := fun i => |ppC n i|) (fun i _ => abs_nonneg _) (Finset.mem_univ j)
  have h1 : |x| ≤ |x - ppC n j| + |ppC n j| := by
    have := abs_add_le (x - ppC n j) (ppC n j)
    simpa using this
  linarith

/-- Periodisation of a function vanishing for large `|x|`: locally a finite sum. -/
lemma ppPer_finite {Φ : ℝ → ℝ} {R : ℝ} (hR : ∀ x, R < |x| → Φ x = 0) {P : ℝ} (hP : 0 < P)
    (τ0 : ℝ) : ∃ K : ℕ, ∀ τ : ℝ, |τ - τ0| < P → ∀ k : ℤ, (K : ℤ) < |k| →
      Φ (τ - (k : ℝ) * P) = 0 := by
  refine ⟨⌈(R + |τ0| + 1) / P⌉₊, fun τ hτ k hk => ?_⟩
  have hKP : R + |τ0| + 1 ≤ ((⌈(R + |τ0| + 1) / P⌉₊ : ℕ) : ℝ) * P := by
    have h := Nat.le_ceil ((R + |τ0| + 1) / P)
    rwa [div_le_iff₀ hP] at h
  have hk1 : ((⌈(R + |τ0| + 1) / P⌉₊ : ℕ) : ℤ) + 1 ≤ |k| := hk
  have hk2 : ((⌈(R + |τ0| + 1) / P⌉₊ : ℕ) : ℝ) + 1 ≤ |(k : ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast hk1
  have hkP : (((⌈(R + |τ0| + 1) / P⌉₊ : ℕ) : ℝ) + 1) * P ≤ |(k : ℝ)| * P :=
    mul_le_mul_of_nonneg_right hk2 hP.le
  have e2 : (((⌈(R + |τ0| + 1) / P⌉₊ : ℕ) : ℝ) + 1) * P
      = ((⌈(R + |τ0| + 1) / P⌉₊ : ℕ) : ℝ) * P + P := by ring
  have habs : |(k : ℝ) * P| = |(k : ℝ)| * P := by rw [abs_mul, abs_of_pos hP]
  have htau : |τ| ≤ |τ0| + P := by
    have := abs_sub_abs_le_abs_sub τ τ0
    have h2 : |τ - τ0| < P := hτ
    linarith
  have hsplit : |(k : ℝ) * P| ≤ |τ - (k : ℝ) * P| + |τ| := by
    have h := abs_add_le (-(τ - (k : ℝ) * P)) τ
    have e : -(τ - (k : ℝ) * P) + τ = (k : ℝ) * P := by ring
    rw [e, abs_neg] at h
    exact h
  apply hR
  linarith

lemma ppPer_summable {Φ : ℝ → ℝ} {R : ℝ} (hR : ∀ x, R < |x| → Φ x = 0) {P : ℝ} (hP : 0 < P)
    (τ0 : ℝ) : Summable (fun k : ℤ => Φ (τ0 - (k : ℝ) * P)) := by
  obtain ⟨K, hK⟩ := ppPer_finite hR hP τ0
  apply summable_of_ne_finset_zero (s := Finset.Icc (-(K : ℤ)) K)
  intro k hk
  apply hK τ0 (by rw [sub_self, abs_zero]; exact hP) k
  simp only [Finset.mem_Icc] at hk
  exact lt_abs.mpr (by omega)

lemma ppPer_contDiff {Φ : ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ) {R : ℝ}
    (hR : ∀ x, R < |x| → Φ x = 0) {P : ℝ} (hP : 0 < P) :
    ContDiff ℝ ∞ (fun τ => ∑' k : ℤ, Φ (τ - (k : ℝ) * P)) := by
  rw [contDiff_iff_contDiffAt]
  intro τ0
  obtain ⟨K, hK⟩ := ppPer_finite hR hP τ0
  have hfin : ContDiffAt ℝ ∞
      (fun τ => ∑ k ∈ Finset.Icc (-(K : ℤ)) K, Φ (τ - (k : ℝ) * P)) τ0 := by
    apply ContDiff.contDiffAt
    apply ContDiff.sum
    intro k _
    exact hΦ.comp (contDiff_id.sub contDiff_const)
  refine hfin.congr_of_eventuallyEq ?_
  filter_upwards [Metric.ball_mem_nhds τ0 hP] with τ hτ
  have hτ' : |τ - τ0| < P := by
    rw [← Real.dist_eq]
    exact Metric.mem_ball.mp hτ
  have hz : ∀ k ∉ Finset.Icc (-(K : ℤ)) K, Φ (τ - (k : ℝ) * P) = 0 := by
    intro k hk
    apply hK τ hτ' k
    apply lt_abs.mpr
    simp only [Finset.mem_Icc] at hk
    omega
  exact tsum_eq_sum hz

lemma ppPer_periodic (Φ : ℝ → ℝ) (P τ : ℝ) (k : ℤ) :
    ∑' m : ℤ, Φ ((τ - (k : ℝ) * P) - (m : ℝ) * P) = ∑' m : ℤ, Φ (τ - (m : ℝ) * P) := by
  refine Eq.trans ?_ ((Equiv.addRight k).tsum_eq (fun m : ℤ => Φ (τ - (m : ℝ) * P)))
  congr 1
  funext m
  show Φ _ = Φ (τ - (((m + k : ℤ)) : ℝ) * P)
  congr 1
  push_cast
  ring

/-- The periodisation `V(τ) = ∑_k Φ(τ - kP)`. -/
def ppV (n : ℕ) (P : ℝ) (τ : ℝ) : ℝ := ∑' k : ℤ, ppPhi n (τ - (k : ℝ) * P)

lemma ppV_contDiff (n : ℕ) {P : ℝ} (hP : 0 < P) : ContDiff ℝ ∞ (ppV n P) := by
  obtain ⟨R, hR⟩ := ppPhi_bound n
  exact ppPer_contDiff (ppPhi_contDiff n) hR hP

lemma ppV_periodic (n : ℕ) (P : ℝ) (τ : ℝ) (k : ℤ) : ppV n P (τ - (k : ℝ) * P) = ppV n P τ :=
  ppPer_periodic (ppPhi n) P τ k

lemma ppPhi_pos_of {n : ℕ} {s : ℝ} (hs0 : 0 ≤ s) (hs : 2 * s < n) : 0 < ppPhi n s := by
  have hj1 : ((⌊2 * s⌋₊ : ℕ) : ℝ) ≤ 2 * s := Nat.floor_le (by linarith)
  have hj2 : 2 * s < ((⌊2 * s⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one (2 * s)
  have jn : ⌊2 * s⌋₊ < n := by
    have : ((⌊2 * s⌋₊ : ℕ) : ℝ) < (n : ℝ) := by linarith
    exact_mod_cast this
  let i : Fin n := ⟨⌊2 * s⌋₊, jn⟩
  have hci : ppC n i = ((⌊2 * s⌋₊ : ℕ) : ℝ) / 2 := rfl
  have hbump : 0 < ppBump (s - ppC n i) := by
    apply ppBump_pos
    rw [abs_lt, hci]
    constructor <;> linarith
  have hle : ppBump (s - ppC n i) ≤ ppPhi n s :=
    Finset.single_le_sum (f := fun j : Fin n => ppBump (s - ppC n j))
      (fun _ _ => ppBump_nonneg _) (Finset.mem_univ i)
  linarith

lemma ppV_pos (n : ℕ) {P : ℝ} (hP : 0 < P) (hn : 2 * P < n) (τ : ℝ) : 0 < ppV n P τ := by
  obtain ⟨R, hR⟩ := ppPhi_bound n
  have hfl1 := Int.floor_le (τ / P)
  have hfl2 := Int.lt_floor_add_one (τ / P)
  have hs0 : 0 ≤ τ - (⌊τ / P⌋ : ℝ) * P := by
    have := (le_div_iff₀ hP).mp hfl1
    linarith
  have hsP : τ - (⌊τ / P⌋ : ℝ) * P < P := by
    have h3 : τ < ((⌊τ / P⌋ : ℝ) + 1) * P := (div_lt_iff₀ hP).mp hfl2
    have e : ((⌊τ / P⌋ : ℝ) + 1) * P = (⌊τ / P⌋ : ℝ) * P + P := by ring
    linarith
  have hpos : 0 < ppPhi n (τ - (⌊τ / P⌋ : ℝ) * P) :=
    ppPhi_pos_of hs0 (by linarith)
  unfold ppV
  exact (ppPer_summable hR hP τ).tsum_pos (fun k => ppPhi_nonneg _ _) ⌊τ / P⌋ hpos

lemma ppPartition_of {n : ℕ} {P : ℝ} (hP : 0 < P) (hn : 2 * P < n) :
    IsPeriodPartition P (ppC n) (fun (j : Fin n) (τ : ℝ) => ppBump (τ - ppC n j) * (ppV n P τ)⁻¹) := by
  unfold IsPeriodPartition
  refine ⟨fun j => ?_, fun τ => ?_⟩
  · have hV : ContDiff ℝ ∞ (ppV n P) := ppV_contDiff n hP
    have hsupp : Function.support (fun τ : ℝ => ppBump (τ - ppC n j) * (ppV n P τ)⁻¹)
        ⊆ Icc (ppC n j - 1 / 2) (ppC n j + 1 / 2) := by
      intro τ hτ
      have hb : ppBump (τ - ppC n j) ≠ 0 := left_ne_zero_of_mul hτ
      have habs : |τ - ppC n j| < 1 / 2 := by
        by_contra h
        push Not at h
        exact hb (ppBump_zero h)
      rw [abs_lt] at habs
      exact ⟨by linarith [habs.1], by linarith [habs.2]⟩
    have htsupp : tsupport (fun τ : ℝ => ppBump (τ - ppC n j) * (ppV n P τ)⁻¹)
        ⊆ Icc (ppC n j - 1 / 2) (ppC n j + 1 / 2) :=
      closure_minimal hsupp isClosed_Icc
    refine ⟨?_, ?_, ?_⟩
    · exact (ppBump_contDiff.comp (contDiff_id.sub contDiff_const)).mul
        (hV.inv (fun τ => (ppV_pos n hP hn τ).ne'))
    · exact IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport _) htsupp
    · intro x hx
      have hx' := htsupp hx
      exact ⟨by linarith [hx'.1], by linarith [hx'.2]⟩
  · -- the partition identity
    have step1 : ∀ k : ℤ, ∑ j : Fin n, ppBump (τ - (k : ℝ) * P - ppC n j) *
        (ppV n P (τ - (k : ℝ) * P))⁻¹ = ppPhi n (τ - (k : ℝ) * P) * (ppV n P τ)⁻¹ := by
      intro k
      unfold ppPhi
      rw [ppV_periodic, Finset.sum_mul]
    show ∑' k : ℤ, ∑ j : Fin n, ppBump (τ - (k : ℝ) * P - ppC n j) *
        (ppV n P (τ - (k : ℝ) * P))⁻¹ = 1
    rw [tsum_congr step1, tsum_mul_right]
    exact mul_inv_cancel₀ (ppV_pos n hP hn τ).ne'

theorem periodPartition_proof : UnforcedLeray.Short.PartIIa.PeriodPartition := by
  intro P hP
  have hn : 2 * P < ((⌈2 * P⌉₊ + 1 : ℕ) : ℝ) := by
    have := Nat.le_ceil (2 * P)
    push_cast
    linarith
  exact ⟨⌈2 * P⌉₊ + 1, ppC _, fun j τ => ppBump (τ - ppC _ j) * (ppV _ P τ)⁻¹,
    ppPartition_of hP hn⟩

end UnforcedLeray.Short.PartIIa
