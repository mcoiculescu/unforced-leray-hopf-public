import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_masked_18_3_4_2_1
import UnforcedLeray.Short.PartIIIb.NearInst.Chart

/-!
# `boxCartLiftSupport` (`PartIII-b:C/near/masked/18/3/4/2/1/2`)

Source 2681-2691, 3916-3921.  `cartLift R c m τ z = F (s • nsSym (m p)) Fᵀ` with `F = cylFrame z`
(entries bounded by `1`), `p = chartOf R c z τ`, `s = p.1`.  The band of a box tensor forces
`m p ≠ 0 → s₁ ≤ s ≤ s₂` and `|p.2.2| ≤ L`, which gives a uniform entry bound and confines the
nonzero values of `cartLift` to the closed ball of radius `(R + |L|)/√s₁`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization

open MeasureTheory Set UnforcedLeray.Axi
open UnforcedLeray.Short.PartIIIb.Concrete
open UnforcedLeray.Short.PartIIIb.NearInst (cartLift IsBoxTensor hRad chartOf cylFrame nsSym symRZ)

/-- Entrywise bound for `F * G * Fᵀ`. -/
lemma entry_triple (F G : Matrix (Fin 3) (Fin 3) ℝ) (K : ℝ) (hF : ∀ i j, |F i j| ≤ 1)
    (hG : ∀ i j, |G i j| ≤ K) (hK : 0 ≤ K) (j k : Fin 3) :
    |(F * G * F.transpose) j k| ≤ 9 * K := by
  have hFG : ∀ b, |(F * G) j b| ≤ 3 * K := by
    intro b
    rw [Matrix.mul_apply]
    calc |∑ a, F j a * G a b| ≤ ∑ a, |F j a * G a b| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _a : Fin 3, K := Finset.sum_le_sum fun a _ => by
          rw [abs_mul]
          exact mul_le_mul (hF j a) (hG a b) (abs_nonneg _) zero_le_one |>.trans (le_of_eq (one_mul K))
      _ = 3 * K := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          push_cast
          ring
  rw [Matrix.mul_apply]
  calc |∑ b, (F * G) j b * F.transpose b k| ≤ ∑ b, |(F * G) j b * F.transpose b k| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _b : Fin 3, 3 * K := Finset.sum_le_sum fun b _ => by
        rw [abs_mul, Matrix.transpose_apply]
        exact (mul_le_mul (hFG b) (hF k b) (abs_nonneg _) (by linarith)).trans
          (le_of_eq (mul_one _))
    _ = 9 * K := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring

lemma abs_comp_le_norm (T : Ten3) (p : Fin 3 × Fin 3) : |T p| ≤ ‖T‖ := by
  have := PiLp.norm_apply_le T p
  rwa [Real.norm_eq_abs] at this

lemma nsSym_zero_apply (a b : Fin 3) : nsSym (0 : Ten3) a b = 0 := by
  fin_cases a <;> fin_cases b <;> simp [nsSym, symRZ]

lemma symRZ_abs_le (T : Ten3) : |symRZ T| ≤ ‖T‖ := by
  have h3 := abs_le.1 (abs_comp_le_norm T (0, 2))
  have h4 := abs_le.1 (abs_comp_le_norm T (2, 0))
  unfold symRZ
  rw [abs_le]
  constructor <;> linarith [h3.1, h3.2, h4.1, h4.2]

lemma nsSym_zero : nsSym (0 : Ten3) = 0 := by
  ext a b
  exact nsSym_zero_apply a b

lemma nsSym_abs_le (T : Ten3) (a b : Fin 3) : |nsSym T a b| ≤ ‖T‖ := by
  have hn := norm_nonneg T
  fin_cases a <;> fin_cases b <;> first
    | exact abs_comp_le_norm T (0, 0)
    | exact abs_comp_le_norm T (1, 1)
    | exact abs_comp_le_norm T (2, 2)
    | exact symRZ_abs_le T
    | (change |(0 : ℝ)| ≤ ‖T‖; rw [abs_zero]; exact hn)

lemma abs_div_hRad_le (x : ℝ) (z : Space) (hx : |x| ≤ hRad z) : |x / hRad z| ≤ 1 := by
  by_cases h0 : hRad z = 0
  · simp [h0]
  · have hpos : 0 < hRad z := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm h0)
    rw [abs_div, abs_of_pos hpos, div_le_one hpos]
    exact hx

theorem boxCartLiftSupport :
    UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.BoxCartLiftSupport := by
  intro R c hR hc m hm
  obtain ⟨_, ⟨B0, hB0⟩, ⟨s1, s2, L, hs1, hband⟩⟩ := hm
  have hu : 0 < Real.sqrt s1 := Real.sqrt_pos.2 hs1
  have hu2 : Real.sqrt s1 * Real.sqrt s1 = s1 := Real.mul_self_sqrt hs1.le
  -- support radius
  have hsupp : ∀ τ : ℝ, ∀ z : Space, cartLift R c m τ z ≠ 0 →
      ‖z‖ ≤ (R + |L|) / Real.sqrt s1 := by
    intro τ z hz
    have hp : m (chartOf R c z τ) ≠ 0 := by
      intro h
      apply hz
      unfold cartLift
      rw [h, nsSym_zero]
      simp
    obtain ⟨h1, _h2, h3⟩ := hband _ hp
    have e1 : (chartOf R c z τ).1 = R ^ 2 / hRad z ^ 2 := rfl
    have e2 : (chartOf R c z τ).2.2 = R * z 2 / hRad z := rfl
    rw [e1] at h1
    rw [e2] at h3
    have hRn : 0 ≤ hRad z := Real.sqrt_nonneg _
    have hpos : 0 < hRad z := by
      rcases hRn.eq_or_lt with h0 | h0
      · exfalso
        rw [← h0] at h1
        simp at h1
        linarith
      · exact h0
    have hh2 : hRad z ^ 2 = z 0 ^ 2 + z 1 ^ 2 := by
      unfold hRad
      rw [Real.sq_sqrt (by positivity)]
    have hsq : s1 * hRad z ^ 2 ≤ R ^ 2 := (le_div_iff₀ (pow_pos hpos 2)).1 h1
    have hsqr : (Real.sqrt s1 * hRad z) ^ 2 = s1 * hRad z ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hs1.le]
    have huh : Real.sqrt s1 * hRad z ≤ R := by
      nlinarith [mul_pos hu hpos]
    have hA : R * |z 2| ≤ |L| * hRad z := by
      have habs : |R * z 2 / hRad z| = R * |z 2| / hRad z := by
        rw [abs_div, abs_mul, abs_of_pos hR, abs_of_pos hpos]
      rw [habs, div_le_iff₀ hpos] at h3
      calc R * |z 2| ≤ L * hRad z := h3
        _ ≤ |L| * hRad z := mul_le_mul_of_nonneg_right (le_abs_self L) hpos.le
    have hz2 : Real.sqrt s1 * |z 2| ≤ |L| := by
      refine le_of_mul_le_mul_left ?_ hR
      calc R * (Real.sqrt s1 * |z 2|) = Real.sqrt s1 * (R * |z 2|) := by ring
        _ ≤ Real.sqrt s1 * (|L| * hRad z) := mul_le_mul_of_nonneg_left hA hu.le
        _ = |L| * (Real.sqrt s1 * hRad z) := by ring
        _ ≤ |L| * R := mul_le_mul_of_nonneg_left huh (abs_nonneg L)
        _ = R * |L| := by ring
    have hnz : ‖z‖ ≤ hRad z + |z 2| := by
      rw [EuclideanSpace.norm_eq, Fin.sum_univ_three]
      simp only [Real.norm_eq_abs, sq_abs]
      have hRn' : 0 ≤ hRad z + |z 2| := add_nonneg hRn (abs_nonneg _)
      calc Real.sqrt (z 0 ^ 2 + z 1 ^ 2 + z 2 ^ 2)
          ≤ Real.sqrt ((hRad z + |z 2|) ^ 2) := by
            apply Real.sqrt_le_sqrt
            nlinarith [mul_nonneg hRn (abs_nonneg (z 2)), sq_abs (z 2)]
        _ = hRad z + |z 2| := Real.sqrt_sq hRn'
    have hfin : Real.sqrt s1 * ‖z‖ ≤ R + |L| := by
      nlinarith [mul_le_mul_of_nonneg_left hnz hu.le]
    rw [le_div_iff₀ hu]
    nlinarith
  -- uniform entry bound
  have hFb : ∀ z : Space, ∀ i j : Fin 3, |cylFrame z i j| ≤ 1 := by
    intro z i j
    have ha : |z 0 / hRad z| ≤ 1 := abs_div_hRad_le _ z (Real.abs_le_sqrt (by nlinarith [sq_nonneg (z 1)]))
    have hb : |z 1 / hRad z| ≤ 1 := abs_div_hRad_le _ z (Real.abs_le_sqrt (by nlinarith [sq_nonneg (z 0)]))
    fin_cases i <;> fin_cases j <;> simp [cylFrame, ha, hb]
  refine ⟨9 * (|s2| * |B0|), Metric.closedBall (0 : Space) ((R + |L|) / Real.sqrt s1),
    isCompact_closedBall _ _, fun τ z => ⟨fun j k => ?_, fun hz => ?_⟩⟩
  · have hG : ∀ a b : Fin 3, |((chartOf R c z τ).1 • nsSym (m (chartOf R c z τ))) a b|
        ≤ |s2| * |B0| := by
      intro a b
      rw [Matrix.smul_apply, smul_eq_mul]
      by_cases hT : m (chartOf R c z τ) = 0
      · rw [hT, nsSym_zero_apply, mul_zero, abs_zero]
        positivity
      · obtain ⟨h1, h2, _⟩ := hband _ hT
        have hs : 0 ≤ (chartOf R c z τ).1 := by
          unfold chartOf
          positivity
        rw [abs_mul, abs_of_nonneg hs]
        have hn : |nsSym (m (chartOf R c z τ)) a b| ≤ |B0| :=
          (nsSym_abs_le _ a b).trans ((hB0 _).trans (le_abs_self B0))
        exact mul_le_mul (h2.trans (le_abs_self s2)) hn (abs_nonneg _) (abs_nonneg _)
    have key := entry_triple (cylFrame z) ((chartOf R c z τ).1 • nsSym (m (chartOf R c z τ)))
      (|s2| * |B0|) (hFb z) hG (by positivity) j k
    unfold cartLift
    exact key
  · by_contra hne
    apply hz
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hsupp τ z hne

end UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization
