import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_7_2_1_2_1_4

/-!
# `PartIII-a:T21/2/7/2/1/2/1/4`, task `countWords`: counting words of basis directions

Proves `CountWords` (defined in `Sub/PartIII-a_T21_2_7_2_1_2_1_4.lean`, SP 3060-3073, calculus only).
The map `i ↦ (ageCount i, spatWord i)` is at most `2 ^ n`-to-one: `i` is determined by its set of
age positions `{k | i k = 0}` together with its spatial word, and `ageCount` plus the length of
`spatWord` add up to `n`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIIa

/-- Splitting off the first letter of a word of basis directions. -/
theorem cwSpatWordCons {m : ℕ} (a : Fin 3) (t : Fin m → Fin 3) :
    spatWord (Fin.cons a t : Fin (m + 1) → Fin 3) =
      if h : a = 0 then spatWord t else a.pred h :: spatWord t := by
  unfold spatWord
  rw [List.ofFn_succ]
  by_cases h : a = 0 <;> simp [h]

/-- Splitting off the first letter in the age count. -/
theorem cwAgeCountCons {m : ℕ} (a : Fin 3) (t : Fin m → Fin 3) :
    ageCount (Fin.cons a t : Fin (m + 1) → Fin 3) = (if a = 0 then 1 else 0) + ageCount t := by
  unfold ageCount
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_succ]
  simp

/-- Length identity: the spatial word has length `n - ageCount i`. -/
theorem cwLengthAdd : ∀ (n : ℕ) (i : Fin n → Fin 3), (spatWord i).length + ageCount i = n
  | 0, i => by simp [spatWord, ageCount]
  | m + 1, i => by
    obtain ⟨a, t, rfl⟩ : ∃ a t, i = Fin.cons a t := ⟨i 0, Fin.tail i, (Fin.cons_self_tail i).symm⟩
    have ih := cwLengthAdd m t
    rw [cwSpatWordCons, cwAgeCountCons]
    by_cases h : a = 0 <;> simp [h] <;> omega

theorem cwPredInj : ∀ a b : Fin 3, ∀ (ha : a ≠ 0) (hb : b ≠ 0), a.pred ha = b.pred hb → a = b := by
  decide

/-- The spatial word together with the age positions determines the word. -/
theorem cwEqOfSpatWord : ∀ (n : ℕ) (i i' : Fin n → Fin 3),
    (∀ k, (i k = 0 ↔ i' k = 0)) → spatWord i = spatWord i' → i = i'
  | 0, i, i', _, _ => funext fun k => k.elim0
  | m + 1, i, i', hA, hW => by
    obtain ⟨a, t, rfl⟩ : ∃ a t, i = Fin.cons a t := ⟨i 0, Fin.tail i, (Fin.cons_self_tail i).symm⟩
    obtain ⟨b, t', rfl⟩ : ∃ b t', i' = Fin.cons b t' :=
      ⟨i' 0, Fin.tail i', (Fin.cons_self_tail i').symm⟩
    have h0 : a = 0 ↔ b = 0 := by simpa using hA 0
    have ht : ∀ k, (t k = 0 ↔ t' k = 0) := fun k => by simpa using hA k.succ
    rw [cwSpatWordCons, cwSpatWordCons] at hW
    by_cases ha : a = 0
    · have hb : b = 0 := h0.mp ha
      subst ha
      subst hb
      simp only [dite_true] at hW
      have hT := cwEqOfSpatWord m t t' ht hW
      subst hT
      rfl
    · have hb : b ≠ 0 := fun hb => ha (h0.mpr hb)
      simp only [dif_neg ha, dif_neg hb, List.cons.injEq] at hW
      obtain ⟨hp, hT⟩ := hW
      have hab : a = b := cwPredInj a b ha hb hp
      subst hab
      have hT' := cwEqOfSpatWord m t t' ht hT
      subst hT'
      rfl

/-- Each fibre of `i ↦ spatWord i` has at most `2 ^ n` elements. -/
theorem cwCardFiber (n : ℕ) (w : List (Fin 2)) :
    (Finset.univ.filter fun i : Fin n → Fin 3 => spatWord i = w).card ≤ 2 ^ n := by
  calc (Finset.univ.filter fun i : Fin n → Fin 3 => spatWord i = w).card
      ≤ (Finset.univ : Finset (Finset (Fin n))).card := by
        apply Finset.card_le_card_of_injOn (fun i : Fin n → Fin 3 => Finset.univ.filter fun k => i k = 0)
        · intro i _
          exact Finset.mem_univ _
        · intro i hi i' hi' heq
          simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hi hi'
          have hk : ∀ k, (i k = 0 ↔ i' k = 0) := fun k => by
            have := Finset.ext_iff.mp heq k
            simpa using this
          exact cwEqOfSpatWord n i i' hk (hi.trans hi'.symm)
    _ = 2 ^ n := by rw [Finset.card_univ, Fintype.card_finset, Fintype.card_fin]

theorem cwExistsOfFn : ∀ (m : ℕ) (w : List (Fin 2)), w.length = m → ∃ v : Fin m → Fin 2, List.ofFn v = w
  | m, w, hw => by
    subst hw
    exact ⟨w.get, List.ofFn_get w⟩

/-- Fibre sum bound over a finset of words of fixed length `m`. -/
theorem cwSumFiber (n m : ℕ) (s : Finset (Fin n → Fin 3)) (g : List (Fin 2) → ℝ)
    (hg : ∀ w, 0 ≤ g w) (hs : ∀ i ∈ s, (spatWord i).length = m) :
    ∑ i ∈ s, g (spatWord i) ≤ 2 ^ n * ∑ v : Fin m → Fin 2, g (List.ofFn v) := by
  calc ∑ i ∈ s, g (spatWord i)
      = ∑ w ∈ s.image spatWord, ∑ i ∈ s.filter (fun i => spatWord i = w), g (spatWord i) :=
        (Finset.sum_fiberwise_of_maps_to (fun i hi => Finset.mem_image_of_mem _ hi) _).symm
    _ = ∑ w ∈ s.image spatWord, ((s.filter (fun i => spatWord i = w)).card : ℝ) * g w := by
        apply Finset.sum_congr rfl
        intro w _
        rw [Finset.sum_congr rfl (fun i hi => by rw [(Finset.mem_filter.mp hi).2]),
          Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ w ∈ s.image spatWord, (2 : ℝ) ^ n * g w := by
        apply Finset.sum_le_sum
        intro w _
        apply mul_le_mul_of_nonneg_right _ (hg w)
        have hnat : (s.filter (fun i => spatWord i = w)).card ≤ 2 ^ n :=
          le_trans
            (Finset.card_le_card (fun i hi =>
              Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2⟩))
            (cwCardFiber n w)
        exact_mod_cast hnat
    _ = 2 ^ n * ∑ w ∈ s.image spatWord, g w := by rw [Finset.mul_sum]
    _ ≤ 2 ^ n * ∑ v : Fin m → Fin 2, g (List.ofFn v) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        calc ∑ w ∈ s.image spatWord, g w
            ≤ ∑ w ∈ (Finset.univ : Finset (Fin m → Fin 2)).image List.ofFn, g w := by
              apply Finset.sum_le_sum_of_subset_of_nonneg
              · intro w hw
                obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hw
                obtain ⟨v, hv⟩ := cwExistsOfFn m (spatWord i) (hs i hi)
                exact Finset.mem_image.mpr ⟨v, Finset.mem_univ _, hv⟩
              · intro w _ _
                exact hg w
          _ = ∑ v : Fin m → Fin 2, g (List.ofFn v) :=
              Finset.sum_image (fun _ _ _ _ h => List.ofFn_injective h)

theorem countWords : UnforcedLeray.Short.IIIa.CountWords := by
  intro n f hf
  have hA : ∀ i : Fin n → Fin 3, ageCount i ∈ Finset.range (n + 1) := fun i => by
    rw [Finset.mem_range]
    have := cwLengthAdd n i
    omega
  calc ∑ i : Fin n → Fin 3, f (ageCount i) (spatWord i)
      = ∑ j ∈ Finset.range (n + 1), ∑ i ∈ Finset.univ.filter (fun i => ageCount i = j),
          f j (spatWord i) := by
        rw [← Finset.sum_fiberwise_of_maps_to (g := ageCount) (t := Finset.range (n + 1))
          (fun i _ => hA i) (fun i => f (ageCount i) (spatWord i))]
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro i hi
        rw [(Finset.mem_filter.mp hi).2]
    _ ≤ ∑ j ∈ Finset.range (n + 1), 2 ^ n * ∑ v : Fin (n - j) → Fin 2, f j (List.ofFn v) := by
        apply Finset.sum_le_sum
        intro j _
        apply cwSumFiber n (n - j) _ (f j) (hf j)
        intro i hi
        have := cwLengthAdd n i
        have hj := (Finset.mem_filter.mp hi).2
        omega
    _ = 2 ^ n * ∑ j ∈ Finset.range (n + 1), ∑ v : Fin (n - j) → Fin 2, f j (List.ofFn v) :=
        (Finset.mul_sum _ _ _).symm

end UnforcedLeray.Short.IIIa
