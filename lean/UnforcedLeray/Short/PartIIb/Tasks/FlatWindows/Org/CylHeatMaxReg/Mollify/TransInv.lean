import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T13_1_4_3_1

/-!
# Part II-b, task `PartII-b:T13/1/4/3/1/1` (`chmCylTransInv`): translation invariance of `cylMeas`

Source: `the November 2 reference manuscript` (SP) lines 1933-1935: the cylinder
norm is over one centred cell, and shifts cost nothing.

`cylMeas c = ds ⊗ (c⁻¹ dq on [-c/2, c/2)) ⊗ dη`.  For `y = (y0, (t, y2))`, translation by `-y`
in Lebesgue measure on `Coord` moves the cell in `q` to the strip `[-c/2 - t, c/2 - t)`.  For an
a.e. `c`-periodic `G`, the integral of `G` over the `q`-strip `[b, b + c)` does not depend on `b`:
adjacent strips are compared through their common part, and the shift by exactly `c` moves
`[a + c, b + c)` back onto `[a, b)` (the shift identity uses only that `qShift c` preserves
Lebesgue measure and `G ∘ qShift c = G` a.e.).  Chaining adjacent strips gives every `b`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

open MeasureTheory Set Filter
open scoped ENNReal

/-- Integral of `G` over the `q`-strip `[b, b + c)` of `Coord`. -/
def chmTIS (c : ℝ) (G : Coord → ℝ≥0∞) (b : ℝ) : ℝ≥0∞ :=
  ∫⁻ x, {x : Coord | x.2.1 ∈ Ico b (b + c)}.indicator G x

/-- The product measure `cylMeas c` as a restricted Lebesgue measure on `Coord`. -/
theorem chmTI_cyl_eq (c : ℝ) :
    cylMeas c = ENNReal.ofReal c⁻¹ • volume.restrict {x : Coord | x.2.1 ∈ Ico (-c / 2) (c / 2)} := by
  have h1 : {x : Coord | x.2.1 ∈ Ico (-c / 2) (c / 2)} = univ ×ˢ (Ico (-c / 2) (c / 2) ×ˢ univ) := by
    ext x
    simp [Set.mem_prod]
  have h2 : (volume : Measure ℝ).prod
      ((volume : Measure (ℝ × ℝ)).restrict (Ico (-c / 2) (c / 2) ×ˢ univ))
      = (volume : Measure Coord).restrict (univ ×ˢ (Ico (-c / 2) (c / 2) ×ˢ univ)) := by
    have := Measure.prod_restrict (μ := (volume : Measure ℝ)) (ν := (volume : Measure (ℝ × ℝ)))
      (univ : Set ℝ) (Ico (-c / 2) (c / 2) ×ˢ univ)
    rw [Measure.restrict_univ] at this
    exact this
  rw [h1]
  unfold cylMeas UnforcedLeray.Cyl.avgμ UnforcedLeray.Cyl.cellμ UnforcedLeray.Cyl.cell
  rw [Measure.prod_smul_right, h2]

/-- Pointwise splitting of a `q`-strip at an intermediate point. -/
theorem chmTI_split_pt {G : Coord → ℝ≥0∞} {p q r : ℝ} (hpq : p ≤ q) (hqr : q ≤ r) (x : Coord) :
    {x : Coord | x.2.1 ∈ Ico p r}.indicator G x
      = {x : Coord | x.2.1 ∈ Ico p q}.indicator G x
        + {x : Coord | x.2.1 ∈ Ico q r}.indicator G x := by
  classical
  simp only [Set.indicator_apply, Set.mem_setOf_eq, Set.mem_Ico]
  by_cases h1 : p ≤ x.2.1 ∧ x.2.1 < q
  · have h2 : ¬ (q ≤ x.2.1) := not_le.2 h1.2
    have h3 : x.2.1 < r := lt_of_lt_of_le h1.2 hqr
    simp only [if_pos (⟨h1.1, h3⟩ : p ≤ x.2.1 ∧ x.2.1 < r), if_pos h1,
      if_neg (fun h : q ≤ x.2.1 ∧ x.2.1 < r => h2 h.1), add_zero]
  · by_cases h2 : q ≤ x.2.1 ∧ x.2.1 < r
    · have h3 : p ≤ x.2.1 := le_trans hpq h2.1
      have h4 : ¬ (x.2.1 < q) := not_lt.2 h2.1
      simp only [if_pos (⟨h3, h2.2⟩ : p ≤ x.2.1 ∧ x.2.1 < r),
        if_neg (fun h : p ≤ x.2.1 ∧ x.2.1 < q => h4 h.2), if_pos h2, zero_add]
    · have h5 : ¬ (p ≤ x.2.1 ∧ x.2.1 < r) := by
        rintro ⟨hp, hr⟩
        by_cases hq : x.2.1 < q
        · exact h1 ⟨hp, hq⟩
        · exact h2 ⟨not_lt.1 hq, hr⟩
      simp only [if_neg h5, if_neg h1, if_neg h2, add_zero]

/-- Additivity of the `q`-strip integral at an intermediate point. -/
theorem chmTI_lint_split {G : Coord → ℝ≥0∞} (hG : Measurable G) {p q r : ℝ} (hpq : p ≤ q)
    (hqr : q ≤ r) :
    ∫⁻ x, {x : Coord | x.2.1 ∈ Ico p r}.indicator G x
      = (∫⁻ x, {x : Coord | x.2.1 ∈ Ico p q}.indicator G x)
        + (∫⁻ x, {x : Coord | x.2.1 ∈ Ico q r}.indicator G x) := by
  have hm : ∀ A : Set ℝ, MeasurableSet A →
      Measurable ({x : Coord | x.2.1 ∈ A}.indicator G) := fun A hA =>
    hG.indicator ((measurable_fst.comp measurable_snd) hA)
  calc ∫⁻ x, {x : Coord | x.2.1 ∈ Ico p r}.indicator G x
      = ∫⁻ x, ({x : Coord | x.2.1 ∈ Ico p q}.indicator G x
          + {x : Coord | x.2.1 ∈ Ico q r}.indicator G x) :=
        lintegral_congr fun x => chmTI_split_pt hpq hqr x
    _ = (∫⁻ x, {x : Coord | x.2.1 ∈ Ico p q}.indicator G x)
          + (∫⁻ x, {x : Coord | x.2.1 ∈ Ico q r}.indicator G x) :=
        lintegral_add_left (hm (Ico p q) measurableSet_Ico)
          (fun x => {x : Coord | x.2.1 ∈ Ico q r}.indicator G x)

/-- Shift identity: for a.e. `c`-periodic `G`, moving the strip `A` by `c` leaves the integral. -/
theorem chmTI_shift_ind {c : ℝ} {G : Coord → ℝ≥0∞} (hc : ∀ᵐ x : Coord, G (qShift c x) = G x)
    (A : Set ℝ) :
    ∫⁻ x, {x : Coord | x.2.1 ∈ A}.indicator G x
      = ∫⁻ x, {x : Coord | x.2.1 ∈ (fun q : ℝ => q + c) ⁻¹' A}.indicator G x := by
  classical
  have hv : ∀ x : Coord, x + ((0 : ℝ), ((c : ℝ), (0 : ℝ))) = qShift c x := fun x =>
    Prod.ext (by simp [qShift]) (Prod.ext (by simp [qShift]) (by simp [qShift]))
  calc ∫⁻ x, {x : Coord | x.2.1 ∈ A}.indicator G x
      = ∫⁻ x, {x : Coord | x.2.1 ∈ A}.indicator G (x + ((0 : ℝ), ((c : ℝ), (0 : ℝ)))) :=
        (lintegral_add_right_eq_self (fun x => {x : Coord | x.2.1 ∈ A}.indicator G x) _).symm
    _ = ∫⁻ x, {x : Coord | x.2.1 ∈ (fun q : ℝ => q + c) ⁻¹' A}.indicator G x := by
        refine lintegral_congr_ae ?_
        filter_upwards [hc] with x hx
        have hq : (qShift c x).2.1 = x.2.1 + c := rfl
        simp only [hv x, Set.indicator_apply, Set.mem_setOf_eq, Set.mem_preimage, hx, hq]

/-- Translation of a `Coord`-integral of `G (· - y)` against the indicator of a set. -/
theorem chmTI_translate (G : Coord → ℝ≥0∞) (y : Coord) (P : Set Coord) :
    ∫⁻ x, P.indicator (fun x => G (x - y)) x
      = ∫⁻ x, ((fun z : Coord => z + y) ⁻¹' P).indicator G x := by
  classical
  have h := lintegral_add_right_eq_self
    (μ := (volume : Measure Coord))
    (fun z : Coord => ((fun z : Coord => z + y) ⁻¹' P).indicator G (z - y)) y
  simp only [add_sub_cancel_right] at h
  calc ∫⁻ x, P.indicator (fun x => G (x - y)) x
      = ∫⁻ x, ((fun z : Coord => z + y) ⁻¹' P).indicator G (x - y) :=
        lintegral_congr fun x => by
          simp only [Set.indicator_apply, Set.mem_preimage, sub_add_cancel]
    _ = ∫⁻ x, ((fun z : Coord => z + y) ⁻¹' P).indicator G x := h.symm

/-- Adjacent strips have the same integral. -/
theorem chmTI_adj {c : ℝ} {G : Coord → ℝ≥0∞} (hG : Measurable G)
    (hc : ∀ᵐ x : Coord, G (qShift c x) = G x) {a b : ℝ} (hab : a ≤ b) (hba : b ≤ a + c) :
    chmTIS c G a = chmTIS c G b := by
  have e1 := chmTI_lint_split hG (p := a) (q := b) (r := a + c) hab hba
  have e2 := chmTI_lint_split hG (p := b) (q := a + c) (r := b + c) hba (by linarith)
  have hpre : (fun q : ℝ => q + c) ⁻¹' Ico (a + c) (b + c) = Ico a b := by
    ext q
    simp only [Set.mem_preimage, Set.mem_Ico]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  have e3 := chmTI_shift_ind (c := c) hc (Ico (a + c) (b + c))
  rw [hpre] at e3
  unfold chmTIS
  rw [e1, e2, e3]
  exact add_comm _ _

/-- Chaining adjacent strips over `n` steps of length at most `c`. -/
theorem chmTI_chain {c : ℝ} {G : Coord → ℝ≥0∞} (hcpos : 0 < c) (hG : Measurable G)
    (hc : ∀ᵐ x : Coord, G (qShift c x) = G x) :
    ∀ n : ℕ, ∀ a d : ℝ, 0 ≤ d → d ≤ n * c → chmTIS c G a = chmTIS c G (a + d) := by
  intro n
  induction n with
  | zero =>
    intro a d hd0 hdn
    have hd : d = 0 := le_antisymm (by simpa using hdn) hd0
    subst hd
    simp
  | succ n ih =>
    intro a d hd0 hdn
    by_cases hd : d ≤ c
    · exact chmTI_adj hG hc (by linarith) (by linarith)
    · have h1 : chmTIS c G a = chmTIS c G (a + c) :=
        chmTI_adj hG hc (by linarith) le_rfl
      have hcast : ((n + 1 : ℕ) : ℝ) * c = n * c + c := by push_cast; ring
      have h2 := ih (a + c) (d - c) (by linarith [not_le.1 hd]) (by linarith)
      rw [show a + c + (d - c) = a + d by ring] at h2
      exact h1.trans h2

/-- The strip integral is independent of the position of the strip. -/
theorem chmTI_const {c : ℝ} {G : Coord → ℝ≥0∞} (hcpos : 0 < c) (hG : Measurable G)
    (hc : ∀ᵐ x : Coord, G (qShift c x) = G x) (a b : ℝ) :
    chmTIS c G a = chmTIS c G b := by
  rcases le_total a b with h | h
  · obtain ⟨n, hn⟩ := exists_nat_gt ((b - a) / c)
    have hdn : b - a ≤ n * c := by
      rw [div_lt_iff₀ hcpos] at hn
      linarith
    have := chmTI_chain hcpos hG hc n a (b - a) (by linarith) hdn
    rwa [show a + (b - a) = b by ring] at this
  · obtain ⟨n, hn⟩ := exists_nat_gt ((a - b) / c)
    have hdn : a - b ≤ n * c := by
      rw [div_lt_iff₀ hcpos] at hn
      linarith
    have := chmTI_chain hcpos hG hc n b (a - b) (by linarith) hdn
    rw [show b + (a - b) = a by ring] at this
    exact this.symm

/-- **Leaf `PartII-b:T13/1/4/3/1/1`.** Translation invariance of the cylinder integral of an
a.e. `q`-periodic measurable function (SP 1933-1935). -/
theorem chmCylTransInv : UnforcedLeray.Short.IIb.ChmCylTransInv := by
  intro c hc G hG hae y
  obtain ⟨y0, t, y2⟩ := y
  have hP0 : MeasurableSet {x : Coord | x.2.1 ∈ Ico (-c / 2) (c / 2)} :=
    (measurable_fst.comp measurable_snd) measurableSet_Ico
  rw [chmTI_cyl_eq c, lintegral_smul_measure, lintegral_smul_measure]
  congr 1
  rw [← lintegral_indicator hP0 (fun x => G (x - (y0, (t, y2)))), ← lintegral_indicator hP0 G,
    chmTI_translate G (y0, (t, y2))]
  have hQ : (fun z : Coord => z + (y0, (t, y2))) ⁻¹' {x : Coord | x.2.1 ∈ Ico (-c / 2) (c / 2)}
      = {z : Coord | z.2.1 ∈ Ico (-c / 2 - t) (-c / 2 - t + c)} := by
    ext z
    simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_Ico, Prod.fst_add, Prod.snd_add]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  rw [hQ]
  have hconst := chmTI_const hc hG hae (-c / 2 - t) (-c / 2)
  unfold chmTIS at hconst
  rw [show -c / 2 + c = c / 2 by ring] at hconst
  exact hconst

end UnforcedLeray.Short.IIb

end
