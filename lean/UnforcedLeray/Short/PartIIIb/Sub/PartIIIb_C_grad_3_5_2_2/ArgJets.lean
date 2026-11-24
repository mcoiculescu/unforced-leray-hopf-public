import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_5_2_2

/-!
# `PartIII-b:C/grad/3/5/2/2` task 1b: uniform jet bounds for `sq2(x_j)/(4a)`

Source `the November 2 reference manuscript`
5063-5079, 4974-4980.  The exponent `sq2(x_j)/(4a)` is written as `P_j · H` with
`P_j = (x_j)_1² + (x_j)_2²` and `H = (4a)⁻¹`.  The jets of `H` are bounded on `U` by compactness;
the jets of the affine factors of `P_j` are bounded by `K (1+|j|)`; Leibniz gives the claim.
-/

set_option autoImplicit false

noncomputable section

open Set

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Jets of order `≤ 3` of a function smooth on an open set `S` are bounded on `U` when
`closure U ⊆ S` is bounded. -/
lemma aj_compact {S : Set Chart} (hS : IsOpen S) (f : Chart → ℝ) (hf : ContDiffOn ℝ 3 f S)
    (U : Set Chart) (hUo : IsOpen U) (hUS : closure U ⊆ S) (hbd : Bornology.IsBounded (closure U)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ i : ℕ, i ≤ 3 → ∀ p ∈ U, ‖iteratedFDerivWithin ℝ i f U p‖ ≤ M := by
  have hK : IsCompact (closure U) := Metric.isCompact_of_isClosed_isBounded isClosed_closure hbd
  have hbound : ∀ i : ℕ, i ≤ 3 → ∃ C : ℝ, ∀ x ∈ closure U, ‖iteratedFDerivWithin ℝ i f S x‖ ≤ C := by
    intro i hi
    have hcont : ContinuousOn (iteratedFDerivWithin ℝ i f S) S :=
      hf.continuousOn_iteratedFDerivWithin (by exact_mod_cast hi) hS.uniqueDiffOn
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hcont.mono hUS)
    exact ⟨C, hC⟩
  have hUeq : ∀ i : ℕ, ∀ p ∈ U, iteratedFDerivWithin ℝ i f U p = iteratedFDerivWithin ℝ i f S p := by
    intro i p hp
    exact (iteratedFDerivWithin_of_isOpen i hUo hp).trans
      (iteratedFDerivWithin_of_isOpen i hS (hUS (subset_closure hp))).symm
  obtain ⟨C0, hC0⟩ := hbound 0 (by norm_num)
  obtain ⟨C1, hC1⟩ := hbound 1 (by norm_num)
  obtain ⟨C2, hC2⟩ := hbound 2 (by norm_num)
  obtain ⟨C3, hC3⟩ := hbound 3 (by norm_num)
  refine ⟨|C0| + |C1| + |C2| + |C3|, by positivity, ?_⟩
  intro i hi p hp
  rw [hUeq i p hp]
  have hpc : p ∈ closure U := subset_closure hp
  have a0 := abs_nonneg C0
  have a1 := abs_nonneg C1
  have a2 := abs_nonneg C2
  have a3 := abs_nonneg C3
  have b0 := le_abs_self C0
  have b1 := le_abs_self C1
  have b2 := le_abs_self C2
  have b3 := le_abs_self C3
  interval_cases i
  · have := hC0 p hpc
    linarith
  · have := hC1 p hpc
    linarith
  · have := hC2 p hpc
    linarith
  · have := hC3 p hpc
    linarith

/-- Leibniz bound with a uniform constant: jets of a product of two functions with bounded
jets on `U` (order `≤ 3`). -/
lemma aj_prod (U : Set Chart) (hUo : IsOpen U) (f g : Chart → ℝ)
    (hf : ContDiffOn ℝ 3 f U) (hg : ContDiffOn ℝ 3 g U) (A B : ℝ) (hA0 : 0 ≤ A) (hB0 : 0 ≤ B)
    (hA : ∀ i : ℕ, i ≤ 3 → ∀ p ∈ U, ‖iteratedFDerivWithin ℝ i f U p‖ ≤ A)
    (hB : ∀ i : ℕ, i ≤ 3 → ∀ p ∈ U, ‖iteratedFDerivWithin ℝ i g U p‖ ≤ B) :
    ∀ k : ℕ, k ≤ 3 → ∀ p ∈ U, ‖iteratedFDerivWithin ℝ k (fun y => f y * g y) U p‖ ≤ 8 * A * B := by
  intro k hk p hp
  have hkN : (k : WithTop ℕ∞) ≤ 3 := by exact_mod_cast hk
  refine (norm_iteratedFDerivWithin_mul_le hf hg hUo.uniqueDiffOn hp hkN).trans ?_
  have hmain := pla_sum_choose_le k (fun i => ‖iteratedFDerivWithin ℝ i f U p‖)
    (fun i => ‖iteratedFDerivWithin ℝ i g U p‖) A B
    (fun i hi => hA i (hi.trans hk) p hp) (fun i hi => hB i (hi.trans hk) p hp)
    (fun _ => norm_nonneg _) (fun _ => norm_nonneg _) hA0
  have h2k : (2 : ℝ) ^ k ≤ 8 := by
    interval_cases k <;> norm_num
  have hAB : 0 ≤ A * B := mul_nonneg hA0 hB0
  calc _ ≤ 2 ^ k * A * B := hmain
    _ ≤ 8 * A * B := by nlinarith

/-- Sums with uniform bounds. -/
lemma aj_add (U : Set Chart) (hUo : IsOpen U) (f g : Chart → ℝ)
    (hf : ContDiffOn ℝ 3 f U) (hg : ContDiffOn ℝ 3 g U) (A B : ℝ)
    (hA : ∀ i : ℕ, i ≤ 3 → ∀ p ∈ U, ‖iteratedFDerivWithin ℝ i f U p‖ ≤ A)
    (hB : ∀ i : ℕ, i ≤ 3 → ∀ p ∈ U, ‖iteratedFDerivWithin ℝ i g U p‖ ≤ B) :
    ∀ k : ℕ, k ≤ 3 → ∀ p ∈ U, ‖iteratedFDerivWithin ℝ k (fun y => f y + g y) U p‖ ≤ A + B := by
  intro k hk p hp
  have hkN : (k : WithTop ℕ∞) ≤ 3 := by exact_mod_cast hk
  have e : iteratedFDerivWithin ℝ k (fun y => f y + g y) U p
      = iteratedFDerivWithin ℝ k f U p + iteratedFDerivWithin ℝ k g U p :=
    iteratedFDerivWithin_add_apply ((hf.contDiffWithinAt hp).of_le hkN)
      ((hg.contDiffWithinAt hp).of_le hkN) hUo.uniqueDiffOn hp
  rw [e]
  exact (norm_add_le _ _).trans (add_le_add (hA k hk p hp) (hB k hk p hp))

/-- The `x_1`-factor of `x_j` (depends on `j` through a constant). -/
def ajU (ν : ℝ) (j : ℤ) : Chart → ℝ := fun y => y.2.1 - (j : ℝ) * cOf ν

/-- The `x_2`-factor. -/
def ajG : Chart → ℝ := fun y => y.2.2

/-- `P_j = (x_j)_1² + (x_j)_2²` written through `ajU` and `ajG`. -/
def ajP (ν : ℝ) (j : ℤ) : Chart → ℝ :=
  fun y => ajU ν j y * ajU ν j y + ajG y * ajG y

/-- `H = (4a)⁻¹`. -/
def ajH (ν : ℝ) : Chart → ℝ := fun y => (4 * ageA ν y.1)⁻¹

theorem psijArgJets (ν : ℝ) (hν : 0 < ν) (U : Set Chart) (hUo : IsOpen U) (hcl : closure U ⊆ {p : Chart | 0 < p.1}) (hbd : Bornology.IsBounded (closure U)) : ∃ D : ℝ, 1 ≤ D ∧ ∀ j : ℤ, ∀ p ∈ U, ∀ i : ℕ, 1 ≤ i → i ≤ 3 → ‖iteratedFDerivWithin ℝ i (fun q : Chart => sq2 (xj ν j q.2) / (4 * ageA ν q.1)) U p‖ ≤ (D * (1 + |(j : ℝ)|) ^ 2) ^ i := by
  -- radius of `U` in the `x`-directions
  obtain ⟨r, hr⟩ := hbd.subset_closedBall 0
  obtain ⟨R, hR0, hRb⟩ : ∃ R : ℝ, 0 ≤ R ∧ ∀ p ∈ U, ‖p‖ ≤ R :=
    ⟨|r|, abs_nonneg r, fun p hp =>
      (mem_closedBall_zero_iff.mp (hr (subset_closure hp))).trans (le_abs_self r)⟩
  have hx1R : ∀ p ∈ U, |p.2.1| ≤ R := fun p hp => by
    have h1 : ‖p.2.1‖ ≤ ‖p‖ := (norm_fst_le p.2).trans (norm_snd_le p)
    have := h1.trans (hRb p hp)
    simpa [Real.norm_eq_abs] using this
  -- smoothness of the coordinate factors
  have hY1 : ContDiff ℝ 3 (fun y : Chart => y.2.1) := by fun_prop
  have hY2 : ContDiff ℝ 3 ajG := by
    unfold ajG
    fun_prop
  have hY1' : ContDiffOn ℝ 3 (fun y : Chart => y.2.1) univ := hY1.contDiffOn
  have hY2' : ContDiffOn ℝ 3 ajG univ := hY2.contDiffOn
  -- j-independent jet bounds of the coordinate functions
  obtain ⟨K1, hK1, hK1b⟩ := aj_compact isOpen_univ (fun y : Chart => y.2.1) hY1' U hUo
    (subset_univ _) hbd
  obtain ⟨K2, hK2, hK2b⟩ := aj_compact isOpen_univ ajG hY2' U hUo (subset_univ _) hbd
  -- jet bound of `H`
  have hHcd : ContDiffOn ℝ 3 (ajH ν) {p : Chart | 0 < p.1} := by
    have h1 : ContDiff ℝ 3 (fun y : Chart => 4 * ageA ν y.1) := by
      unfold ageA
      fun_prop
    unfold ajH
    exact h1.contDiffOn.inv (fun p hp => mul_ne_zero (by norm_num) (psc2_ageA_ne ν hν p hp))
  obtain ⟨MH, hMH, hMHb⟩ := aj_compact psc2_isOpen_pos (ajH ν) hHcd U hUo hcl hbd
  -- the constant `Kc` and the `j`-bound `Kc * (1 + |j|)`
  obtain ⟨Kc, hKc⟩ : ∃ Kc : ℝ, Kc = |cOf ν| + R + K1 + K2 := ⟨_, rfl⟩
  have hcOf : 0 ≤ |cOf ν| := abs_nonneg _
  have hKc0 : 0 ≤ Kc := by
    rw [hKc]
    linarith
  have hKcK1 : K1 ≤ Kc := by
    rw [hKc]
    linarith
  have hKcK2 : K2 ≤ Kc := by
    rw [hKc]
    linarith
  have hKcA : ∀ j : ℤ, Kc ≤ Kc * (1 + |(j : ℝ)|) := fun j =>
    le_mul_of_one_le_right hKc0 (by linarith [abs_nonneg (j : ℝ)])
  have hAj0 : ∀ j : ℤ, 0 ≤ Kc * (1 + |(j : ℝ)|) := fun j =>
    mul_nonneg hKc0 (by linarith [abs_nonneg (j : ℝ)])
  -- smoothness of `x_1 - j c`
  have hUcd : ∀ j : ℤ, ContDiff ℝ 3 (ajU ν j) := by
    intro j
    unfold ajU
    fun_prop
  -- jets of `x_1 - j c` with a bound linear in `|j|`
  have hUjet : ∀ j : ℤ, ∀ i : ℕ, i ≤ 3 → ∀ p ∈ U,
      ‖iteratedFDerivWithin ℝ i (ajU ν j) U p‖ ≤ Kc * (1 + |(j : ℝ)|) := by
    intro j i hi p hp
    have hj0 : 0 ≤ |(j : ℝ)| := abs_nonneg _
    rcases Nat.eq_zero_or_pos i with h0 | hpos
    · subst h0
      rw [norm_iteratedFDerivWithin_zero]
      have hval : ‖ajU ν j p‖ ≤ R + |(j : ℝ)| * |cOf ν| := by
        unfold ajU
        rw [Real.norm_eq_abs]
        calc |p.2.1 - (j : ℝ) * cOf ν| ≤ |p.2.1| + |(j : ℝ) * cOf ν| := abs_sub _ _
          _ = |p.2.1| + |(j : ℝ)| * |cOf ν| := by rw [abs_mul]
          _ ≤ R + |(j : ℝ)| * |cOf ν| := by linarith [hx1R p hp]
      have hbig : R + |(j : ℝ)| * |cOf ν| ≤ Kc * (1 + |(j : ℝ)|) := by
        rw [hKc]
        nlinarith [mul_nonneg hR0 hj0, mul_nonneg hK1 hj0, mul_nonneg hK2 hj0, hcOf, hK1, hK2,
          mul_nonneg hcOf hj0]
      exact hval.trans hbig
    · have hne : i ≠ 0 := by omega
      have hA1 : ContDiffWithinAt ℝ (i : WithTop ℕ∞) (fun y : Chart => y.2.1) U p :=
        (hY1.contDiffWithinAt).of_le (by exact_mod_cast hi)
      have hA2 : ContDiffWithinAt ℝ (i : WithTop ℕ∞) (fun _ : Chart => (j : ℝ) * cOf ν) U p :=
        contDiffWithinAt_const
      have e : ajU ν j = (fun y : Chart => y.2.1) - (fun _ : Chart => (j : ℝ) * cOf ν) := rfl
      rw [e, iteratedFDerivWithin_sub_apply hA1 hA2 hUo.uniqueDiffOn hp,
        iteratedFDerivWithin_const_of_ne hne]
      simp only [Pi.zero_apply, sub_zero]
      exact (hK1b i hi p hp).trans (hKcK1.trans (hKcA j))
  -- jets of `P_j = (x_1 - j c)² + x_2²`
  have hPjet : ∀ j : ℤ, ∀ k : ℕ, k ≤ 3 → ∀ p ∈ U,
      ‖iteratedFDerivWithin ℝ k (ajP ν j) U p‖
        ≤ 8 * (Kc * (1 + |(j : ℝ)|)) * (Kc * (1 + |(j : ℝ)|))
          + 8 * (Kc * (1 + |(j : ℝ)|)) * (Kc * (1 + |(j : ℝ)|)) := by
    intro j k hk p hp
    have hA := hAj0 j
    have hu := aj_prod U hUo (ajU ν j) (ajU ν j) (hUcd j).contDiffOn (hUcd j).contDiffOn
      _ _ hA hA (hUjet j) (hUjet j)
    have hg := aj_prod U hUo ajG ajG hY2.contDiffOn hY2.contDiffOn _ _ hA hA
      (fun i hi p hp => (hK2b i hi p hp).trans (hKcK2.trans (hKcA j)))
      (fun i hi p hp => (hK2b i hi p hp).trans (hKcK2.trans (hKcA j)))
    have hf1 : ContDiffOn ℝ 3 (fun y : Chart => ajU ν j y * ajU ν j y) U :=
      ((hUcd j).mul (hUcd j)).contDiffOn
    have hf2 : ContDiffOn ℝ 3 (fun y : Chart => ajG y * ajG y) U :=
      (hY2.mul hY2).contDiffOn
    exact aj_add U hUo (fun y : Chart => ajU ν j y * ajU ν j y)
      (fun y : Chart => ajG y * ajG y) hf1 hf2 _ _
      (fun i hi p hp => hu i hi p hp) (fun i hi p hp => hg i hi p hp) k hk p hp
  -- the product `P_j · H`
  have hProd : ∀ j : ℤ, ∀ k : ℕ, k ≤ 3 → ∀ p ∈ U,
      ‖iteratedFDerivWithin ℝ k (fun y => ajP ν j y * ajH ν y) U p‖
        ≤ 8 * (16 * (Kc * (1 + |(j : ℝ)|)) * (Kc * (1 + |(j : ℝ)|))) * MH := by
    intro j k hk p hp
    have hPcd : ContDiffOn ℝ 3 (ajP ν j) U := by
      unfold ajP
      exact (((hUcd j).mul (hUcd j)).add (hY2.mul hY2)).contDiffOn
    have hA := hAj0 j
    have hPb : ∀ i : ℕ, i ≤ 3 → ∀ p ∈ U,
        ‖iteratedFDerivWithin ℝ i (ajP ν j) U p‖ ≤ 16 * (Kc * (1 + |(j : ℝ)|)) * (Kc * (1 + |(j : ℝ)|)) := by
      intro i hi q hq
      have := hPjet j i hi q hq
      linarith
    exact aj_prod U hUo (ajP ν j) (ajH ν) hPcd (hHcd.mono (fun q hq => hcl (subset_closure hq)))
      _ MH (mul_nonneg (mul_nonneg (by norm_num) hA) hA) hMH hPb (fun i hi q hq => hMHb i hi q hq)
      k hk p hp
  -- the final constant
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = 128 * Kc ^ 2 * MH := ⟨_, rfl⟩
  have hbound_all : ∀ j : ℤ, ∀ k : ℕ, k ≤ 3 → ∀ p ∈ U,
      ‖iteratedFDerivWithin ℝ k (fun q : Chart => sq2 (xj ν j q.2) / (4 * ageA ν q.1)) U p‖
        ≤ E * (1 + |(j : ℝ)|) ^ 2 := by
    intro j k hk p hp
    have hFeq : (fun q : Chart => sq2 (xj ν j q.2) / (4 * ageA ν q.1))
        = fun y => ajP ν j y * ajH ν y := by
      funext y
      simp only [ajP, ajU, ajG, ajH, sq2, xj]
      ring
    rw [hFeq]
    refine (hProd j k hk p hp).trans (le_of_eq ?_)
    rw [hE]
    ring
  have hE0 : 0 ≤ E := by
    rw [hE]
    exact mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) hMH
  refine ⟨max 1 E, le_max_left _ _, ?_⟩
  intro j p hp i hi1 hi3
  have hx : 1 ≤ (1 + |(j : ℝ)|) ^ 2 := by nlinarith [abs_nonneg (j : ℝ)]
  have hD1 : 1 ≤ max 1 E := le_max_left _ _
  have hDE : E ≤ max 1 E := le_max_right _ _
  have hxD : 1 ≤ max 1 E * (1 + |(j : ℝ)|) ^ 2 := one_le_mul_of_one_le_of_one_le hD1 hx
  have hpow : max 1 E * (1 + |(j : ℝ)|) ^ 2 ≤ (max 1 E * (1 + |(j : ℝ)|) ^ 2) ^ i :=
    le_self_pow₀ hxD (by omega)
  have hEx : E * (1 + |(j : ℝ)|) ^ 2 ≤ max 1 E * (1 + |(j : ℝ)|) ^ 2 :=
    mul_le_mul_of_nonneg_right hDE (by positivity)
  exact (hbound_all j i hi3 p hp).trans (hEx.trans hpow)

end UnforcedLeray.Short.PartIIIb.Concrete
