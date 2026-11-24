import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_3_3_1_dec

set_option autoImplicit false

noncomputable section

open MeasureTheory Set

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

/-- Integer `q`-periodicity: a `c`-periodic (in `q`) function is invariant under all integer
multiples of `c` in `q`. -/
private lemma per_int_s3 {V : Type*} (g : UnforcedLeray.Cyl.Plane → V) (c : ℝ)
    (hg : ∀ x : ℝ × ℝ, g (x.1 + c, x.2) = g x) (x : ℝ × ℝ) (n : ℤ) :
    g (x.1 + (Int.cast n : ℝ) * c, x.2) = g x := by
  induction n using Int.induction_on with
  | zero => simp
  | succ i ih =>
    calc g (x.1 + (Int.cast (i + 1 : ℤ) : ℝ) * c, x.2)
        = g ((x.1 + (Int.cast i : ℝ) * c) + c, x.2) :=
          congrArg g (Prod.ext (by dsimp only; push_cast; ring) rfl)
      _ = g (x.1 + (Int.cast i : ℝ) * c, x.2) := hg (x.1 + (Int.cast i : ℝ) * c, x.2)
      _ = g x := ih
  | pred i ih =>
    calc g (x.1 + (Int.cast (-(i : ℤ) - 1) : ℝ) * c, x.2)
        = g ((x.1 + (Int.cast (-(i : ℤ) - 1) : ℝ) * c) + c, x.2) :=
          (hg (x.1 + (Int.cast (-(i : ℤ) - 1) : ℝ) * c, x.2)).symm
      _ = g (x.1 + (Int.cast (-(i : ℤ)) : ℝ) * c, x.2) :=
          congrArg g (Prod.ext (by dsimp only; push_cast; ring) rfl)
      _ = g x := ih

/-- **Sub3: uniqueness of continuous periodic representatives** (see `PeriodicContUnique`).
Proof: the open set `U = {z₁ ≠ z₂}` is `q`-periodic and has measure zero on the cell, hence
measure zero on the plane (the integer translates of the cell cover the plane); a nonempty open
set has positive measure, so `U = ∅`. -/
theorem periodicContUnique : PeriodicContUnique := by
  intro c hc z₁ z₂ h₁ h₂ hp₁ hp₂ hae
  set U : Set UnforcedLeray.Cyl.Plane := {x | z₁ x ≠ z₂ x} with hU_def
  have hUo : IsOpen U := isOpen_ne_fun h₁ h₂
  have hinv : ∀ (n : ℤ) (x : ℝ × ℝ), (x.1 + (n : ℝ) * c, x.2) ∈ U ↔ x ∈ U := by
    intro n x
    simp only [hU_def, mem_setOf_eq]
    rw [per_int_s3 z₁ c hp₁ x n, per_int_s3 z₂ c hp₂ x n]
  have hcm : MeasurableSet (UnforcedLeray.Cyl.cell c) :=
    measurableSet_Ico.prod MeasurableSet.univ
  have hcell : volume (U ∩ UnforcedLeray.Cyl.cell c) = 0 := by
    have h : (volume.restrict (UnforcedLeray.Cyl.cell c)) {x | ¬ z₁ x = z₂ x} = 0 :=
      ae_iff.mp hae
    rw [Measure.restrict_apply' hcm] at h
    exact h
  have hcover : ∀ x : ℝ × ℝ, ∃ n : ℤ, (x.1 + (n : ℝ) * c, x.2) ∈ UnforcedLeray.Cyl.cell c := by
    intro x
    refine ⟨-⌊(x.1 + c / 2) / c⌋, ?_⟩
    have h1 := Int.floor_le ((x.1 + c / 2) / c)
    have h2 := Int.lt_floor_add_one ((x.1 + c / 2) / c)
    have h3 := (le_div_iff₀ hc).mp h1
    have h4 := (div_lt_iff₀ hc).mp h2
    refine ⟨⟨?_, ?_⟩, mem_univ _⟩
    · push_cast
      linarith
    · push_cast
      linarith
  have hpiece : ∀ n : ℤ, volume (U ∩ {x : ℝ × ℝ | (x.1 + (n : ℝ) * c, x.2) ∈ UnforcedLeray.Cyl.cell c}) = 0 := by
    intro n
    have hpre : (fun x : ℝ × ℝ => x + (((n : ℝ) * c), (0 : ℝ))) ⁻¹' (U ∩ UnforcedLeray.Cyl.cell c)
        = U ∩ {x : ℝ × ℝ | (x.1 + (n : ℝ) * c, x.2) ∈ UnforcedLeray.Cyl.cell c} := by
      ext x
      have e : x + (((n : ℝ) * c), (0 : ℝ)) = (x.1 + (n : ℝ) * c, x.2) := by
        ext <;> simp
      simp only [mem_preimage, mem_inter_iff, mem_setOf_eq, e]
      rw [hinv n x]
    rw [← hpre, measure_preimage_add_right]
    exact hcell
  have hall : volume U = 0 := by
    have hsub : U ⊆ ⋃ n : ℤ, (U ∩ {x : ℝ × ℝ | (x.1 + (n : ℝ) * c, x.2) ∈ UnforcedLeray.Cyl.cell c}) := by
      intro x hx
      obtain ⟨n, hn⟩ := hcover x
      exact mem_iUnion.mpr ⟨n, hx, hn⟩
    exact measure_mono_null hsub (measure_iUnion_null hpiece)
  funext x
  by_contra hne
  have hxU : x ∈ U := hne
  have hpos : 0 < volume U := hUo.measure_pos (μ := volume) ⟨x, hxU⟩
  rw [hall] at hpos
  exact lt_irrefl _ hpos

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
