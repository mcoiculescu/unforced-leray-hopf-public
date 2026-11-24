import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Lemmas

/-!
# Proof of `outPartitionSum` (source 3958-3977): the output regions partition the chart.
Target: `NearInst/Delta/Lemmas.lean`, `OutPartitionSum`.  Helpers are local to this file.

Pointwise, the indicators of `{s < s₋}`, `{s ≥ S}`, `tailSet`, and the bins
`binSet (e j) (e (j+1)) L` (with `e j = binEdge s₋ S N j`, `e 0 = s₋`, `e N = S`, strictly
increasing) sum to `1`.  On the `Lp` side the restrictions add up a.e. to the identity.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Delta

open UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Short.PartIIIb.NearInst UnforcedLeray.Cons.C03.Concrete
  UnforcedLeray.Blueprint.Planar

/-- The indicator of a bin: `1` iff `l ≤ s < r` and `|η| ≤ L`. -/
theorem ind_binSet_apply (l r L : ℝ) (x : Chart) :
    ind (binSet l r L) x = if (l ≤ x.1 ∧ x.1 < r) ∧ |x.2.2| ≤ L then 1 else 0 := by
  by_cases h : (l ≤ x.1 ∧ x.1 < r) ∧ |x.2.2| ≤ L
  · have hm : x ∈ binSet l r L := ⟨h.1.1, h.1.2, h.2⟩
    unfold ind
    rw [Set.indicator_of_mem hm, if_pos h]
  · have hm : x ∉ binSet l r L := fun hm => h ⟨⟨hm.1, hm.2.1⟩, hm.2.2⟩
    unfold ind
    rw [Set.indicator_of_notMem hm, if_neg h]

/-- The partition of `[e 0, e n)` by consecutive intervals of a monotone sequence. -/
theorem sum_ite_partition (e : ℕ → ℝ) (hmono : Monotone e) (s : ℝ) (n : ℕ) :
    (∑ j ∈ Finset.range n, if e j ≤ s ∧ s < e (j + 1) then (1 : ℝ) else 0) =
      if e 0 ≤ s ∧ s < e n then 1 else 0 := by
  induction n with
  | zero =>
    rw [Finset.sum_range_zero, if_neg]
    rintro ⟨h1, h2⟩
    linarith
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    by_cases h0 : e 0 ≤ s
    · by_cases h : s < e n
      · have h' : s < e (n + 1) := lt_of_lt_of_le h (hmono (Nat.le_succ n))
        have hn : ¬ (e n ≤ s) := not_le.2 h
        rw [if_pos ⟨h0, h⟩, if_neg (fun hh => hn hh.1), if_pos ⟨h0, h'⟩, add_zero]
      · have hn : e n ≤ s := not_lt.1 h
        have h' : s < e (n + 1) ∨ ¬ s < e (n + 1) := em _
        rcases h' with h' | h'
        · rw [if_neg (fun hh => h hh.2), if_pos ⟨hn, h'⟩, if_pos ⟨h0, h'⟩, zero_add]
        · rw [if_neg (fun hh => h hh.2), if_neg (fun hh => h' hh.2), if_neg (fun hh => h' hh.2),
            zero_add]
    · have hn : ¬ (e n ≤ s) := fun hn => h0 ((hmono (Nat.zero_le n)).trans hn)
      rw [if_neg (fun hh => h0 hh.1), if_neg (fun hh => hn hh.1), if_neg (fun hh => h0 hh.1),
        add_zero]

/-- The partition identity pointwise (source 3958-3977). -/
theorem partition_pt (sm S δ L : ℝ) (hsm : 0 < sm) (hS : sm < S) (hδ : 0 < δ) (x : Chart) :
    ind (ageBelow sm) x + ind (ageAbove S) x + ind (tailSet sm S L) x +
      ∑ j ∈ Finset.range (binCount sm S δ),
        ind (binSet (binEdge sm S (binCount sm S δ) j)
          (binEdge sm S (binCount sm S δ) (j + 1)) L) x = 1 := by
  have hN : binCount sm S δ ≠ 0 := (binCount_pos sm S δ).ne'
  have hmono : Monotone (binEdge sm S (binCount sm S δ)) :=
    (strictMono_nat_of_lt_succ (binEdge_lt_succ hsm hS hN)).monotone
  rcases lt_or_ge x.1 sm with h1 | h1
  · have hb : ind (ageBelow sm) x = 1 := by simp [ind, ageBelow, h1]
    have ha : ind (ageAbove S) x = 0 := by
      simp [ind, ageAbove, not_le.2 (lt_of_lt_of_le h1 hS.le)]
    have ht : ind (tailSet sm S L) x = 0 := by simp [ind, tailSet, not_le.2 h1]
    have hs : ∑ j ∈ Finset.range (binCount sm S δ),
        ind (binSet (binEdge sm S (binCount sm S δ) j)
          (binEdge sm S (binCount sm S δ) (j + 1)) L) x = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      have hj := binEdge_ge hsm hS.le (binCount sm S δ) j
      simp [ind, binSet, not_le.2 (lt_of_lt_of_le h1 hj)]
    rw [hb, ha, ht, hs]
    norm_num
  · rcases lt_or_ge x.1 S with h2 | h2
    · have hb : ind (ageBelow sm) x = 0 := by simp [ind, ageBelow, not_lt.2 h1]
      have ha : ind (ageAbove S) x = 0 := by simp [ind, ageAbove, not_le.2 h2]
      by_cases hη : L < |x.2.2|
      · have ht : ind (tailSet sm S L) x = 1 := by simp [ind, tailSet, h1, h2, hη]
        have hs : ∑ j ∈ Finset.range (binCount sm S δ),
            ind (binSet (binEdge sm S (binCount sm S δ) j)
              (binEdge sm S (binCount sm S δ) (j + 1)) L) x = 0 := by
          apply Finset.sum_eq_zero
          intro j _
          simp [ind, binSet, not_le.2 hη]
        rw [hb, ha, ht, hs]
        norm_num
      · have hη' : |x.2.2| ≤ L := not_lt.1 hη
        have ht : ind (tailSet sm S L) x = 0 := by simp [ind, tailSet, hη]
        have hs : ∑ j ∈ Finset.range (binCount sm S δ),
            ind (binSet (binEdge sm S (binCount sm S δ) j)
              (binEdge sm S (binCount sm S δ) (j + 1)) L) x = 1 := by
          simp only [ind_binSet_apply, hη', and_true]
          rw [sum_ite_partition (binEdge sm S (binCount sm S δ)) hmono x.1 (binCount sm S δ),
            binEdge_zero, binEdge_last hsm hN, if_pos ⟨h1, h2⟩]
        rw [hb, ha, ht, hs]
        norm_num
    · have hb : ind (ageBelow sm) x = 0 := by
        simp [ind, ageBelow, not_lt.2 (hS.le.trans h2)]
      have ha : ind (ageAbove S) x = 1 := by simp [ind, ageAbove, h2]
      have ht : ind (tailSet sm S L) x = 0 := by simp [ind, tailSet, not_lt.2 h2]
      have hs : ∑ j ∈ Finset.range (binCount sm S δ),
          ind (binSet (binEdge sm S (binCount sm S δ) j)
            (binEdge sm S (binCount sm S δ) (j + 1)) L) x = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        have hj' : j + 1 ≤ binCount sm S δ := Finset.mem_range.1 hj
        have hle := binEdge_le_last hsm hS.le hj'
        simp [ind, binSet, not_lt.2 (hle.trans h2)]
      rw [hb, ha, ht, hs]
      norm_num

/-- Restrictions of `u` by a finite family of measurable sets add up to the indicator sum. -/
theorem sum_restr_ae {c : ℝ} (A : ℕ → Set Chart) (hA : ∀ j, MeasurableSet (A j)) (u : Hsp c)
    (n : ℕ) :
    ((∑ j ∈ Finset.range n, outRestr c (A j) u : Hsp c) : Chart → Merid) =ᵐ[ageμ c (-3 / 2)]
      fun x => (∑ j ∈ Finset.range n, ind (A j) x) • (u : Chart → Merid) x := by
  induction n with
  | zero =>
    simp only [Finset.sum_range_zero, zero_smul]
    filter_upwards [Lp.coeFn_zero Merid 2 (ageμ c (-3 / 2))] with x hx
    rw [hx]
    rfl
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hn : (outRestr c (A n) u : Chart → Merid) =ᵐ[ageμ c (-3 / 2)]
        fun x => ind (A n) x • (u : Chart → Merid) x :=
      restrLp_ae (hA n) u
    filter_upwards [Lp.coeFn_add (∑ j ∈ Finset.range n, outRestr c (A j) u) (outRestr c (A n) u),
      ih, hn] with x h1 h2 h3
    have h2' : ((∑ j ∈ Finset.range n, outRestr c (A j) u : Hsp c) : Chart → Merid) x =
        (∑ j ∈ Finset.range n, ind (A j) x) • (u : Chart → Merid) x := h2
    have h3' : (outRestr c (A n) u : Chart → Merid) x = ind (A n) x • (u : Chart → Merid) x := h3
    rw [h1]
    show ((∑ j ∈ Finset.range n, outRestr c (A j) u : Hsp c) : Chart → Merid) x +
        (outRestr c (A n) u : Chart → Merid) x = _
    rw [h2', h3', ← add_smul, Finset.sum_range_succ]

/-- **The output partition** (source 3958-3977). -/
theorem outPartitionSum : OutPartitionSum := by
  intro c sm S δ L hsm hS hδ u
  apply Lp.ext
  have hA := measurableSet_ageBelow sm
  have hB := measurableSet_ageAbove S
  have hC := measurableSet_tailSet sm S L
  have e1 := Lp.coeFn_add (outRestr c (ageBelow sm) u) (outRestr c (ageAbove S) u)
  have e2 := Lp.coeFn_add (outRestr c (ageBelow sm) u + outRestr c (ageAbove S) u)
    (outRestr c (tailSet sm S L) u)
  have e3 := Lp.coeFn_add
    (outRestr c (ageBelow sm) u + outRestr c (ageAbove S) u + outRestr c (tailSet sm S L) u)
    (∑ j ∈ Finset.range (binCount sm S δ),
      outRestr c (binSet (binEdge sm S (binCount sm S δ) j)
        (binEdge sm S (binCount sm S δ) (j + 1)) L) u)
  have r1 : (outRestr c (ageBelow sm) u : Chart → Merid) =ᵐ[ageμ c (-3 / 2)]
      fun x => ind (ageBelow sm) x • (u : Chart → Merid) x := restrLp_ae hA u
  have r2 : (outRestr c (ageAbove S) u : Chart → Merid) =ᵐ[ageμ c (-3 / 2)]
      fun x => ind (ageAbove S) x • (u : Chart → Merid) x := restrLp_ae hB u
  have r3 : (outRestr c (tailSet sm S L) u : Chart → Merid) =ᵐ[ageμ c (-3 / 2)]
      fun x => ind (tailSet sm S L) x • (u : Chart → Merid) x := restrLp_ae hC u
  have r4 : ((∑ j ∈ Finset.range (binCount sm S δ),
      outRestr c (binSet (binEdge sm S (binCount sm S δ) j)
        (binEdge sm S (binCount sm S δ) (j + 1)) L) u : Hsp c) : Chart → Merid)
      =ᵐ[ageμ c (-3 / 2)] fun x => (∑ j ∈ Finset.range (binCount sm S δ),
        ind (binSet (binEdge sm S (binCount sm S δ) j)
          (binEdge sm S (binCount sm S δ) (j + 1)) L) x) • (u : Chart → Merid) x :=
    sum_restr_ae (fun j => binSet (binEdge sm S (binCount sm S δ) j)
      (binEdge sm S (binCount sm S δ) (j + 1)) L)
      (fun j => measurableSet_binSet _ _ _) u (binCount sm S δ)
  filter_upwards [e3, e2, e1, r1, r2, r3, r4] with x h3 h2 h1 q1 q2 q3 q4
  have h3' := h3
  rw [h3', Pi.add_apply, h2, Pi.add_apply, h1, Pi.add_apply, q1, q2, q3, q4]
  show ind (ageBelow sm) x • (u : Chart → Merid) x + ind (ageAbove S) x • (u : Chart → Merid) x +
      ind (tailSet sm S L) x • (u : Chart → Merid) x +
      (∑ j ∈ Finset.range (binCount sm S δ),
        ind (binSet (binEdge sm S (binCount sm S δ) j)
          (binEdge sm S (binCount sm S δ) (j + 1)) L) x) • (u : Chart → Merid) x =
    (u : Chart → Merid) x
  rw [← add_smul, ← add_smul, ← add_smul, partition_pt sm S δ L hsm hS hδ x, one_smul]

end UnforcedLeray.Short.PartIIIb.NearInst.Delta
