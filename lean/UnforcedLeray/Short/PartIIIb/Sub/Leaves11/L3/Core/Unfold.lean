import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_inst_11_3_3

/-!
# `PartIII-b:C/inst/11/3/3/1`: unfolding of the lattice sum over one cell

Source `shorter-proof-2026-11-02.tex` lines 5063-5079: the cell integral of a lattice sum of
translates equals the plane integral. The translates `cell c + (n c, 0)` tile the plane, and each
point `y` lies in exactly one translate `S n = {y | y.1 + n c ∈ [-c/2, c/2)}`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem latUnfold : LatUnfold := by
  intro c hc F hF
  have hcell : MeasurableSet (UnforcedLeray.Cyl.cell c) := measurableSet_Ico.prod MeasurableSet.univ
  -- the translate `S n` of the cell
  let S : ℤ → Set (ℝ × ℝ) := fun n => {y | y.1 + (n : ℝ) * c ∈ Ico (-c / 2) (c / 2)}
  have hSm : ∀ n : ℤ, MeasurableSet (S n) := fun n =>
    (measurable_fst.add_const ((n : ℝ) * c)) measurableSet_Ico
  -- one translate of the cell integral
  have hterm : ∀ n : ℤ, ∫⁻ x in UnforcedLeray.Cyl.cell c, F (x.1 - (n : ℝ) * c, x.2)
      = ∫⁻ y, (S n).indicator F y := by
    intro n
    have hmem : ∀ x : ℝ × ℝ, x ∈ UnforcedLeray.Cyl.cell c ↔
        x + (-((n : ℝ) * c), 0) ∈ S n := by
      intro x
      simp only [UnforcedLeray.Cyl.cell, S, mem_prod, mem_univ, and_true, mem_setOf_eq,
        Prod.fst_add]
      rw [show x.1 + -((n : ℝ) * c) + (n : ℝ) * c = x.1 by ring]
    have hpt : ∀ x : ℝ × ℝ,
        (UnforcedLeray.Cyl.cell c).indicator (fun x : ℝ × ℝ => F (x.1 - (n : ℝ) * c, x.2)) x
          = (S n).indicator F (x + (-((n : ℝ) * c), 0)) := by
      intro x
      by_cases h : x ∈ UnforcedLeray.Cyl.cell c
      · rw [indicator_of_mem h, indicator_of_mem ((hmem x).1 h)]
        congr 1
        ext <;> simp [sub_eq_add_neg]
      · rw [indicator_of_notMem h, indicator_of_notMem (fun h' => h ((hmem x).2 h'))]
    have hT : MeasurePreserving (fun x : ℝ × ℝ => x + (-((n : ℝ) * c), 0)) volume volume :=
      measurePreserving_add_right _ _
    calc ∫⁻ x in UnforcedLeray.Cyl.cell c, F (x.1 - (n : ℝ) * c, x.2)
        = ∫⁻ x, (UnforcedLeray.Cyl.cell c).indicator
            (fun x : ℝ × ℝ => F (x.1 - (n : ℝ) * c, x.2)) x := (lintegral_indicator hcell _).symm
      _ = ∫⁻ x, (S n).indicator F (x + (-((n : ℝ) * c), 0)) := lintegral_congr hpt
      _ = ∫⁻ y, (S n).indicator F y := hT.lintegral_comp (hF.indicator (hSm n))
  -- the translates cover each point exactly once
  have hcover : ∀ y : ℝ × ℝ, ∑' n : ℤ, (S n).indicator F y = F y := by
    intro y
    set m : ℤ := ⌊(y.1 + c / 2) / c⌋ with hm
    have hfl1 : (m : ℝ) ≤ (y.1 + c / 2) / c := Int.floor_le _
    have hfl2 : (y.1 + c / 2) / c < (m : ℝ) + 1 := Int.lt_floor_add_one _
    have hmc1 : (m : ℝ) * c ≤ y.1 + c / 2 := (le_div_iff₀ hc).1 hfl1
    have hmc2 : y.1 + c / 2 < (m : ℝ) * c + c := by
      have h := (div_lt_iff₀ hc).1 hfl2
      rw [add_mul, one_mul] at h
      exact h
    have hy0 : y ∈ S (-m) := by
      show y.1 + ((-m : ℤ) : ℝ) * c ∈ Ico (-c / 2) (c / 2)
      push_cast
      constructor <;> linarith
    have key : ∀ b : ℤ, y ∈ S b → b = -m := by
      intro b hb
      obtain ⟨hb1, hb2⟩ := (hb : y.1 + (b : ℝ) * c ∈ Ico (-c / 2) (c / 2))
      have e : ((b : ℝ) + (m : ℝ)) * c = (b : ℝ) * c + (m : ℝ) * c := by ring
      have hA : ((b : ℝ) + m) * c < 1 * c := by rw [e, one_mul]; linarith
      have hB : -1 * c < ((b : ℝ) + m) * c := by rw [e]; linarith
      have d1 : (b : ℝ) + m < 1 := lt_of_mul_lt_mul_right hA hc.le
      have d2 : -1 < (b : ℝ) + m := lt_of_mul_lt_mul_right hB hc.le
      have d1' : b + m < 1 := by exact_mod_cast d1
      have d2' : -1 < b + m := by exact_mod_cast d2
      omega
    rw [tsum_eq_single (-m) ?_]
    · exact indicator_of_mem hy0 F
    · intro b hb
      have hnot : y ∉ S b := fun h => hb (key b h)
      exact indicator_of_notMem hnot F
  calc ∫⁻ x in UnforcedLeray.Cyl.cell c, ∑' n : ℤ, F (x.1 - (n : ℝ) * c, x.2)
      = ∑' n : ℤ, ∫⁻ x in UnforcedLeray.Cyl.cell c, F (x.1 - (n : ℝ) * c, x.2) :=
        lintegral_tsum fun n => (hF.comp (by fun_prop)).aemeasurable
    _ = ∑' n : ℤ, ∫⁻ y, (S n).indicator F y := tsum_congr hterm
    _ = ∫⁻ y, ∑' n : ℤ, (S n).indicator F y :=
        (lintegral_tsum fun n => (hF.indicator (hSm n)).aemeasurable).symm
    _ = ∫⁻ y, F y := lintegral_congr hcover

end UnforcedLeray.Short.PartIIIb.Concrete
