import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Order.Interval.Set.UnorderedInterval
import Mathlib.Order.Interval.Set.OrdConnected
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.NhdsWithin
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Data.Set.Piecewise

/-!
# `PartIII-a:T23/9/2/1/1`: measurability of the primitive `r ↦ ∫₀^r g` for arbitrary `g`

Source of record: `the November 2 reference manuscript`, `greenInverse` (around line 2054).
For an arbitrary `g : ℝ → ℂ` the interval integral is `0` when `g` is not interval integrable.
The set `S = {r | IntervalIntegrable g 0 r}` is order connected and contains `0`; the primitive is
continuous on `S` and vanishes off `S`, so it is measurable.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology

namespace UnforcedLeray.Short.IIIa.T23_9_Sub

/-- Continuity of `r ↦ ∫ t..r g` on an order-connected set `S` on which `g` is pairwise interval
integrable, for a base point `t ∈ S`. -/
theorem primGen_contOn (S : Set ℝ) (hS : S.OrdConnected) (g : ℝ → ℂ)
    (hg : ∀ x ∈ S, ∀ y ∈ S, IntervalIntegrable g volume x y) (t : ℝ) (ht : t ∈ S) :
    ContinuousOn (fun x => ∫ s in t..x, g s) S := by
  have hloc : ∀ z ∈ S, ∀ y ∈ S, ContinuousOn (fun x => ∫ s in t..x, g s) (Set.uIcc z y) := by
    intro z hz y hy
    have h1 : ContinuousOn (fun x => ∫ s in z..x, g s) (Set.uIcc z y) :=
      intervalIntegral.continuousOn_primitive_interval' (hg z hz y hy) Set.left_mem_uIcc
    have h2 : ∀ x ∈ Set.uIcc z y, (∫ s in t..x, g s) = (∫ s in t..z, g s) + ∫ s in z..x, g s := by
      intro x hx
      have hxS : x ∈ S := hS.uIcc_subset hz hy hx
      rw [intervalIntegral.integral_add_adjacent_intervals (hg t ht z hz) (hg z hz x hxS)]
    exact (continuousOn_const.add h1).congr h2
  intro r0 hr0
  by_cases hup : ∃ y ∈ S, r0 < y
  · obtain ⟨y, hy, hry⟩ := hup
    by_cases hdn : ∃ z ∈ S, z < r0
    · obtain ⟨z, hz, hzr⟩ := hdn
      have hc := hloc z hz y hy
      rw [Set.uIcc_of_le (hzr.trans hry).le] at hc
      refine (hc.continuousWithinAt ⟨hzr.le, hry.le⟩).mono_of_mem_nhdsWithin ?_
      exact mem_nhdsWithin_of_mem_nhds (Icc_mem_nhds hzr hry)
    · have hno : ∀ x ∈ S, r0 ≤ x := fun x hx => not_lt.1 (fun h => hdn ⟨x, hx, h⟩)
      have hc := hloc r0 hr0 y hy
      rw [Set.uIcc_of_le hry.le] at hc
      refine (hc.continuousWithinAt ⟨le_refl r0, hry.le⟩).mono_of_mem_nhdsWithin ?_
      refine Filter.mem_of_superset (inter_mem_nhdsWithin S (Iio_mem_nhds hry)) ?_
      intro x hx
      exact ⟨hno x hx.1, le_of_lt (show x < y from hx.2)⟩
  · by_cases hdn : ∃ z ∈ S, z < r0
    · obtain ⟨z, hz, hzr⟩ := hdn
      have hno : ∀ x ∈ S, x ≤ r0 := fun x hx => not_lt.1 (fun h => hup ⟨x, hx, h⟩)
      have hc := hloc z hz r0 hr0
      rw [Set.uIcc_of_le hzr.le] at hc
      refine (hc.continuousWithinAt ⟨hzr.le, le_refl r0⟩).mono_of_mem_nhdsWithin ?_
      refine Filter.mem_of_superset (inter_mem_nhdsWithin S (Ioi_mem_nhds hzr)) ?_
      intro x hx
      exact ⟨le_of_lt (show z < x from hx.2), hno x hx.1⟩
    · have hsub : S ⊆ {r0} := by
        intro x hx
        rcases lt_trichotomy x r0 with h | h | h
        · exact (hdn ⟨x, hx, h⟩).elim
        · exact Set.mem_singleton_iff.2 h
        · exact (hup ⟨x, hx, h⟩).elim
      exact continuousWithinAt_singleton.mono hsub

/-- A function that is continuous on an order-connected set `S` and vanishes off `S` is Borel. -/
theorem measurable_of_pw (S : Set ℝ) (hS : S.OrdConnected) (F : ℝ → ℂ)
    (hF : ContinuousOn F S) (hzero : ∀ r, r ∉ S → F r = 0) : Measurable F := by
  classical
  have hm : Measurable (S.piecewise F (fun _ => (0 : ℂ))) :=
    ContinuousOn.measurable_piecewise hF continuousOn_const hS.measurableSet
  have heq : F = S.piecewise F (fun _ => (0 : ℂ)) := by
    funext r
    by_cases hr : r ∈ S
    · simp [Set.piecewise, hr]
    · simp [Set.piecewise, hr, hzero r hr]
  rw [heq]
  exact hm

/-- Generic form: the primitive from `0` is measurable once `S = {r | IntervalIntegrable g 0 r}`. -/
theorem prim_meas_of (g : ℝ → ℂ) (S : Set ℝ) (hS : ∀ r, r ∈ S ↔ IntervalIntegrable g volume 0 r) :
    Measurable (fun r : ℝ => ∫ s in (0 : ℝ)..r, g s) := by
  have hOC : S.OrdConnected := by
    refine ⟨fun x hx y hy z hz => ?_⟩
    rw [hS] at hx hy ⊢
    rcases le_total 0 z with h0 | h0
    · exact IntervalIntegrable.mono_set hy
        (Set.uIcc_subset_uIcc Set.left_mem_uIcc (Set.mem_uIcc.2 (Or.inl ⟨h0, hz.2⟩)))
    · exact IntervalIntegrable.mono_set hx
        (Set.uIcc_subset_uIcc Set.left_mem_uIcc (Set.mem_uIcc.2 (Or.inr ⟨hz.1, h0⟩)))
  have hpair : ∀ x ∈ S, ∀ y ∈ S, IntervalIntegrable g volume x y := by
    intro x hx y hy
    rw [hS] at hx hy
    exact (IntervalIntegrable.symm hx).trans hy
  have h0S : (0 : ℝ) ∈ S := (hS 0).2 (intervalIntegrable_iff.2 (by simp))
  refine measurable_of_pw S hOC (fun r => ∫ s in (0 : ℝ)..r, g s)
    (primGen_contOn S hOC g hpair 0 h0S) ?_
  intro r hr
  exact intervalIntegral.integral_undef (fun h => hr ((hS r).2 h))

theorem measurable_primitive_zero (g : ℝ → ℂ) : Measurable (fun r : ℝ => ∫ s in (0 : ℝ)..r, g s) :=
  prim_meas_of g {r : ℝ | IntervalIntegrable g volume 0 r} (fun _ => Iff.rfl)

end UnforcedLeray.Short.IIIa.T23_9_Sub

#print axioms UnforcedLeray.Short.IIIa.T23_9_Sub.measurable_primitive_zero
