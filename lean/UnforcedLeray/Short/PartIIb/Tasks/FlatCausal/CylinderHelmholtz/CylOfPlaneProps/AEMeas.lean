import UnforcedLeray.Short.PartIIb.Sub.T12_1_5
import UnforcedLeray.Lib.CylinderB.Periodize

/-!
# Part II-b, leaf `PartII-b:T12/1/5/1` (`CylLpAEMeas`): a.e. measurability of periodic `L^r` fields

Source of record: `the November 2 reference manuscript` line 1670 (`P_0` the
ordinary planar cylinder projection). The target is `CylLpAEMeas` of `Sub/T12_1_5.lean`.

Proof: `avgμ c` is a positive multiple of Lebesgue measure on the centred cell, so `F` is
a.e.-strongly measurable on the cell. Each translate `{z | z + (n c, 0) ∈ cell}` carries `F`
by periodicity and translation invariance, and these translates cover the plane.
-/

namespace UnforcedLeray.Short.IIb

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

theorem cylLpAEMeas : CylLpAEMeas := by
  unfold CylLpAEMeas
  intro c r F hc hF
  obtain ⟨hper, hmem⟩ := hF
  have hper' : UnforcedLeray.Cyl.IsPeriodic c F := hper
  -- Step 1: `F` is a.e.-strongly measurable on one cell for Lebesgue measure.
  have hpos : ENNReal.ofReal c⁻¹ ≠ 0 := (ENNReal.ofReal_pos.2 (inv_pos.2 hc)).ne'
  have hac : volume.restrict (UnforcedLeray.Cyl.cell c) ≪ UnforcedLeray.Cyl.avgμ c := by
    unfold UnforcedLeray.Cyl.avgμ UnforcedLeray.Cyl.cellμ
    exact Measure.absolutelyContinuous_smul hpos
  have h1 : AEStronglyMeasurable F (volume.restrict (UnforcedLeray.Cyl.cell c)) :=
    hmem.aestronglyMeasurable.mono_ac hac
  -- Step 2: each translate of the cell carries `F`, by periodicity and translation invariance.
  have hS : ∀ n : ℤ, AEStronglyMeasurable F
      (volume.restrict
        ((fun z : ℝ × ℝ => (z.1 + (n : ℝ) * c, z.2)) ⁻¹' UnforcedLeray.Cyl.cell c)) := by
    intro n
    have hτ : MeasurePreserving (fun z : ℝ × ℝ => (z.1 + (n : ℝ) * c, z.2))
        (volume.restrict
          ((fun z : ℝ × ℝ => (z.1 + (n : ℝ) * c, z.2)) ⁻¹' UnforcedLeray.Cyl.cell c))
        (volume.restrict (UnforcedLeray.Cyl.cell c)) :=
      (UnforcedLeray.Cyl.measurePreserving_shift ((n : ℝ) * c)).restrict_preimage
        (UnforcedLeray.Cyl.measurableSet_cell c)
    have hcomp := h1.comp_measurePreserving hτ
    have hFeq : (F ∘ fun z : ℝ × ℝ => (z.1 + (n : ℝ) * c, z.2)) = F :=
      funext fun z => hper'.add_int_mul n z
    rw [hFeq] at hcomp
    exact hcomp
  -- Step 3: the translates cover the plane, so the measurability passes to `volume`.
  have hcover : (⋃ n : ℤ,
      (fun z : ℝ × ℝ => (z.1 + (n : ℝ) * c, z.2)) ⁻¹' UnforcedLeray.Cyl.cell c) = univ := by
    apply Set.eq_univ_of_forall
    intro z
    rw [Set.mem_iUnion]
    refine ⟨-⌊(z.1 + c / 2) / c⌋, ?_⟩
    have hk1 : ((⌊(z.1 + c / 2) / c⌋ : ℤ) : ℝ) ≤ (z.1 + c / 2) / c := Int.floor_le _
    have hk2 : (z.1 + c / 2) / c < ((⌊(z.1 + c / 2) / c⌋ : ℤ) : ℝ) + 1 :=
      Int.lt_floor_add_one _
    rw [le_div_iff₀ hc] at hk1
    rw [div_lt_iff₀ hc] at hk2
    simp only [Set.mem_preimage, UnforcedLeray.Cyl.mem_cell]
    push_cast
    constructor <;> nlinarith
  have hall : AEStronglyMeasurable F
      (volume.restrict
        (⋃ n : ℤ, (fun z : ℝ × ℝ => (z.1 + (n : ℝ) * c, z.2)) ⁻¹' UnforcedLeray.Cyl.cell c)) :=
    AEStronglyMeasurable.iUnion hS
  rw [hcover, Measure.restrict_univ] at hall
  exact hall

end UnforcedLeray.Short.IIb
