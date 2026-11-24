import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Order.Interval.Set.UnorderedInterval
import Mathlib.Order.Interval.Set.OrdConnected
import Mathlib.Order.Interval.Set.LinearOrder
import Mathlib.Order.Interval.Set.Disjoint
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.NhdsWithin
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Data.Set.Piecewise

/-!
# `PartIII-a:T23/9/2/1/2`: measurability of the tail `r ↦ ∫_{(r,∞)} g` for arbitrary `g`

Source of record: `the November 2 reference manuscript`, `greenInverse` (around line 2054).
For an arbitrary `g : ℝ → ℂ` the set integral is `0` when `g` is not integrable on `(r,∞)`.
The set `T = {r | IntegrableOn g (r,∞)}` is order connected (it is upward closed), the tail is
`∫_{(t,∞)} g - ∫_t^r g` on `T` for any base point `t ∈ T`, hence continuous on `T`, and it vanishes off `T`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology

namespace UnforcedLeray.Short.IIIa.T23_9_Sub

/-- Continuity of `r ↦ ∫ t..r g` on an order-connected set `S` on which `g` is pairwise interval
integrable, for a base point `t ∈ S`. -/
theorem primGen_contOn2 (S : Set ℝ) (hS : S.OrdConnected) (g : ℝ → ℂ)
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
theorem measurable_of_pw2 (S : Set ℝ) (hS : S.OrdConnected) (F : ℝ → ℂ)
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

/-- Tail identity: for `t, r` with `g` integrable on both tails,
`∫_{(r,∞)} g = ∫_{(t,∞)} g - ∫_t^r g`. -/
theorem tail_eq2 (g : ℝ → ℂ) (t r : ℝ) (ht : IntegrableOn g (Ioi t)) (hr : IntegrableOn g (Ioi r)) :
    ∫ s in Ioi r, g s = (∫ s in Ioi t, g s) - ∫ s in t..r, g s := by
  rcases le_total t r with h | h
  · have hsplit : ∫ s in Ioi t, g s = (∫ s in Ioc t r, g s) + ∫ s in Ioi r, g s := by
      rw [← Set.Ioc_union_Ioi_eq_Ioi h]
      exact MeasureTheory.setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
        (IntegrableOn.mono_set ht (fun z hz => hz.1)) hr
    rw [intervalIntegral.integral_of_le h]
    linear_combination -hsplit
  · have hsplit : ∫ s in Ioi r, g s = (∫ s in Ioc r t, g s) + ∫ s in Ioi t, g s := by
      rw [← Set.Ioc_union_Ioi_eq_Ioi h]
      exact MeasureTheory.setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
        (IntegrableOn.mono_set hr (fun z hz => hz.1)) ht
    rw [intervalIntegral.integral_symm r t, intervalIntegral.integral_of_le h]
    linear_combination hsplit

/-- Generic form: the tail is measurable once `T = {r | IntegrableOn g (r,∞)}`. -/
theorem tail_meas (g : ℝ → ℂ) (T : Set ℝ) (hT : ∀ r, r ∈ T ↔ IntegrableOn g (Ioi r)) :
    Measurable (fun r : ℝ => ∫ s in Ioi r, g s) := by
  have hOC : T.OrdConnected := by
    refine ⟨fun x hx y _ z hz => ?_⟩
    rw [hT] at hx ⊢
    exact IntegrableOn.mono_set hx (Set.Ioi_subset_Ioi hz.1)
  have hpair : ∀ x ∈ T, ∀ y ∈ T, IntervalIntegrable g volume x y := by
    intro x hx y hy
    rw [hT] at hx hy
    rw [intervalIntegrable_iff]
    rcases le_total x y with h | h
    · rw [Set.uIoc_of_le h]
      exact IntegrableOn.mono_set hx (fun z hz => hz.1)
    · rw [Set.uIoc_of_ge h]
      exact IntegrableOn.mono_set hy (fun z hz => hz.1)
  rcases T.eq_empty_or_nonempty with hE | ⟨t0, ht0⟩
  · refine measurable_of_pw2 T hOC _ ?_ ?_
    · rw [hE]
      exact continuousOn_empty _
    · intro r hr
      exact MeasureTheory.integral_undef (fun h => hr ((hT r).2 h))
  · have ht0' : IntegrableOn g (Ioi t0) := (hT t0).1 ht0
    have hcont := primGen_contOn2 T hOC g hpair t0 ht0
    have hsub : ContinuousOn (fun r => (∫ s in Ioi t0, g s) - ∫ s in t0..r, g s) T :=
      continuousOn_const.sub hcont
    have hF : ContinuousOn (fun r => ∫ s in Ioi r, g s) T :=
      hsub.congr (fun r hr => tail_eq2 g t0 r ht0' ((hT r).1 hr))
    refine measurable_of_pw2 T hOC _ hF ?_
    intro r hr
    exact MeasureTheory.integral_undef (fun h => hr ((hT r).2 h))

theorem measurable_integral_Ioi (g : ℝ → ℂ) : Measurable (fun r : ℝ => ∫ s in Ioi r, g s) :=
  tail_meas g {r : ℝ | IntegrableOn g (Ioi r)} (fun _ => Iff.rfl)

end UnforcedLeray.Short.IIIa.T23_9_Sub

#print axioms UnforcedLeray.Short.IIIa.T23_9_Sub.measurable_integral_Ioi
