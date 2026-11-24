import UnforcedLeray.Short.PartI.Sub.T02
import UnforcedLeray.Lib.Cylinder.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Interval

/-!
# Part I, task `PartI:ClassicalOdd/CellNeg`: integrability on the centred cell under `z ↦ -z`

Source of record: `the November 2 reference manuscript`, line 288 (uniqueness for the
reflected pair `(-v(-z), p(-z))`). The centred cell is `Cyl.cell c = Ico (-c/2) (c/2) ×ˢ univ`
(`Lib/Cylinder/Basic.lean`). Its negative is `Ioc (-c/2) (c/2) ×ˢ univ`, which differs from it only
on the two lines `q = ±c/2`, a null set, so no periodicity is needed.

## What is proved here

`integrableOn_cell_neg`: an integrable function on `Cyl.cell c` stays integrable on `Cyl.cell c`
after reflection `z ↦ -z`. The proof transports integrability to `-(Cyl.cell c)` by measure
preservation of negation, then replaces `-(Cyl.cell c)` by `Cyl.cell c` up to a null set.

Helpers are prefixed `cn`: `cnNeg_cell_eq`, `cnNull_prod_singleton`, `cnNeg_cell_ae`.
-/

open MeasureTheory Set
open UnforcedLeray.Cyl (Plane)

namespace UnforcedLeray.Short.PartI

/-- The negative of the centred cell is the cell with the opposite endpoint convention. -/
lemma cnNeg_cell_eq (c : ℝ) :
    -(Cyl.cell c) = Ioc (-c / 2) (c / 2) ×ˢ (univ : Set ℝ) := by
  ext ⟨x, y⟩
  simp only [Cyl.cell, Set.mem_neg, Set.mem_prod, Set.mem_Ico, Set.mem_Ioc, Set.mem_univ,
    and_true, Prod.neg_mk]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by linarith, by linarith⟩

/-- A vertical line `{a} × ℝ` is null for the planar Lebesgue measure. -/
lemma cnNull_prod_singleton (a : ℝ) :
    (volume : Measure (ℝ × ℝ)) (({a} : Set ℝ) ×ˢ (univ : Set ℝ)) = 0 := by
  rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_singleton, zero_mul]

/-- The negative of the centred cell agrees with the cell up to a null set. -/
lemma cnNeg_cell_ae (c : ℝ) : -(Cyl.cell c) =ᵐ[volume] Cyl.cell c := by
  rw [cnNeg_cell_eq, Cyl.cell, ae_eq_set]
  constructor
  · refine measure_mono_null ?_ (cnNull_prod_singleton (c / 2))
    rintro ⟨x, y⟩ hp
    have h1 : x ∈ Ioc (-c / 2) (c / 2) := (Set.mem_prod.1 ((Set.mem_sdiff _).1 hp).1).1
    have hnot : x ∉ Ico (-c / 2) (c / 2) := fun h =>
      ((Set.mem_sdiff _).1 hp).2 (Set.mk_mem_prod h (Set.mem_univ _))
    have hx : x = c / 2 := by
      by_contra hne
      apply hnot
      exact ⟨by linarith [h1.1], lt_of_le_of_ne h1.2 hne⟩
    exact Set.mk_mem_prod (Set.mem_singleton_iff.2 hx) (Set.mem_univ _)
  · refine measure_mono_null ?_ (cnNull_prod_singleton (-c / 2))
    rintro ⟨x, y⟩ hp
    have h1 : x ∈ Ico (-c / 2) (c / 2) := (Set.mem_prod.1 ((Set.mem_sdiff _).1 hp).1).1
    have hnot : x ∉ Ioc (-c / 2) (c / 2) := fun h =>
      ((Set.mem_sdiff _).1 hp).2 (Set.mk_mem_prod h (Set.mem_univ _))
    have hx : x = -c / 2 := by
      by_contra hne
      apply hnot
      exact ⟨lt_of_le_of_ne h1.1 (Ne.symm hne), by linarith [h1.2]⟩
    exact Set.mk_mem_prod (Set.mem_singleton_iff.2 hx) (Set.mem_univ _)

/-- Integrability on the centred cell is preserved by the reflection `z ↦ -z` (source line 288). -/
theorem integrableOn_cell_neg {c : ℝ} {f : Plane → ℝ} (hint : IntegrableOn f (Cyl.cell c)) :
    IntegrableOn (fun z : Plane => f (-z)) (Cyl.cell c) := by
  have hneg : IntegrableOn f (-(Cyl.cell c)) := hint.congr_set_ae (cnNeg_cell_ae c)
  have hpre : (fun z : Plane => -z) ⁻¹' (-(Cyl.cell c)) = Cyl.cell c := by
    ext z
    simp only [Set.mem_preimage, Set.mem_neg, neg_neg]
  have hmp : MeasurePreserving (fun z : Plane => -z) volume volume :=
    Measure.measurePreserving_neg volume
  have hemb : MeasurableEmbedding (fun z : Plane => -z) :=
    (MeasurableEquiv.neg Plane).measurableEmbedding
  have hcomp := (hmp.integrableOn_comp_preimage hemb (f := f) (s := -(Cyl.cell c))).2 hneg
  rw [hpre] at hcomp
  exact hcomp

end UnforcedLeray.Short.PartI
