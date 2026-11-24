import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G2_1_org_C
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T09_6a
import UnforcedLeray.Short.PartIIb.Tasks.NvCNorm.PeriodicRepresentative
import UnforcedLeray.Short.PartIIb.Tasks.NvCNorm.ChartNull
import UnforcedLeray.Short.PartIIb.Tasks.NvCNorm.NullSets

/-!
# Part II-b, `PartII-b:G2/1/org/C/3`: `IsKOut` depends only on the `hMeas`-a.e. class
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.B0411

theorem physKOutCongr_int_shift {c : ℝ} {f : CProf}
    (h : ∀ s ξ η, f (s, (ξ + c, η)) = f (s, (ξ, η))) (k : ℤ) (s ξ η : ℝ) :
    f (s, (ξ + (k : ℝ) * c, η)) = f (s, (ξ, η)) := by
  induction k using Int.induction_on with
  | zero => simp
  | succ n ih =>
    have e : ξ + ((n : ℤ) + 1 : ℤ) * c = (ξ + (n : ℤ) * c) + c := by push_cast; ring
    rw [e, h, ih]
  | pred n ih =>
    have e : ξ + (-(n : ℤ) - 1 : ℤ) * c = (ξ + (-(n : ℤ) - 1 : ℤ) * c) := rfl
    have e2 : ξ + (-(n : ℤ) : ℤ) * c = (ξ + (-(n : ℤ) - 1 : ℤ) * c) + c := by push_cast; ring
    have := h s (ξ + (-(n : ℤ) - 1 : ℤ) * c) η
    rw [← e2] at this
    rw [← this, ih]

theorem physKOutCongr : PhysKOutCongr := by
  intro p d dm dp hreg b g g' hg hg' hae hK Φ hΦ
  have hc := p.c_pos
  have hε := p.ε_pos
  refine (hK Φ hΦ).trans ?_
  -- representatives
  obtain ⟨gr, Mg, hgrm, hgrp, hMgm, hMg0, hMgp, hgM⟩ :=
    periodicRepresentative p.c bgp hc g hg.periodic hg.meas
  obtain ⟨gr', Mg', hgrm', hgrp', hMgm', hMg0', hMgp', hgM'⟩ :=
    periodicRepresentative p.c bgp hc g' hg'.periodic hg'.meas
  have hN : Axi.ageμ p.c (bgp / 2 - 5 / 2) {x : Coord | ¬ (g x = g' x)} = 0 :=
    MeasureTheory.ae_iff.1 hae
  obtain ⟨E, hEsub, hEm, hE0⟩ := exists_measurable_superset_of_null
    (NvCNorm.volume_null_of_ageμ_null hc hN)
  set A : Set Coord := E ∪ Mg ∪ Mg' with hA
  have hAm : MeasurableSet A := (hEm.union hMgm).union hMgm'
  have hA0 : volume A = 0 := measure_union_null (measure_union_null hE0 hMg0) hMg0'
  set M : Set Coord := ⋃ k : ℤ, qShift ((k : ℝ) * p.c) ⁻¹' A with hM
  have hMm : MeasurableSet M := MeasurableSet.iUnion fun k => periodicRep_preimage_measurable hAm
  have hM0 : volume M = 0 := measure_iUnion_null fun k => periodicRep_preimage_null hAm hA0
  have hMp : ∀ s ξ η, (s, (ξ + p.c, η)) ∈ M ↔ (s, (ξ, η)) ∈ M :=
    fun s ξ η => periodicRep_iUnion_periodic p.c A s ξ η
  -- pointwise equality off M
  have hkey : ∀ x : Coord, 0 < x.1 → x ∉ M → g x = g' x := by
    intro x hx hxM
    have h0 : x ∉ A := fun h => hxM (Set.mem_iUnion.2 ⟨0, by
      show qShift (((0 : ℤ) : ℝ) * p.c) x ∈ A
      rw [Int.cast_zero, zero_mul, qShift_zero]; exact h⟩)
    obtain ⟨k₀, hk₀⟩ : ∃ k₀ : ℤ, Axi.cellRep p.c x.2.1 = x.2.1 + (k₀ : ℝ) * p.c :=
      ⟨-⌊(x.2.1 + p.c / 2) / p.c⌋, by unfold Axi.cellRep; push_cast; ring⟩
    have hw : (x.1, (x.2.1 + (k₀ : ℝ) * p.c, x.2.2)) ∉ A := fun h =>
      hxM (Set.mem_iUnion.2 ⟨k₀, h⟩)
    have hwc : (x.1, (x.2.1 + (k₀ : ℝ) * p.c, x.2.2)) ∈ Ioi (0 : ℝ) ×ˢ Axi.qCell p.c := by
      rw [← hk₀]; exact Set.mk_mem_prod hx (periodicRep_mem_qCell hc x.2.1 x.2.2)
    set w : Coord := (x.1, (x.2.1 + (k₀ : ℝ) * p.c, x.2.2)) with hwdef
    have hw1 : g w = gr w := hgM w hx (fun h => hw (Or.inl (Or.inr h)))
    have hw2 : g' w = gr' w := hgM' w hx (fun h => hw (Or.inr h))
    have hw3 : g w = g' w := by
      by_contra hne
      exact hw (Or.inl (Or.inl (hEsub ⟨hne, hwc⟩)))
    have hx1 : g x = gr x := hgM x hx (fun h => h0 (Or.inl (Or.inr h)))
    have hx2 : g' x = gr' x := hgM' x hx (fun h => h0 (Or.inr h))
    have hp1 : gr w = gr x := physKOutCongr_int_shift hgrp k₀ x.1 x.2.1 x.2.2
    have hp2 : gr' w = gr' x := physKOutCongr_int_shift hgrp' k₀ x.1 x.2.1 x.2.2
    rw [hx1, hx2, ← hp1, ← hp2, ← hw1, ← hw2, hw3]
  -- chart null
  have hP : p.period = 2 * p.c / p.R := by
    unfold Params.period Params.R
    field_simp
  have hnull := chartNullPullback p.R p.c p.period (inv_pos.2 hε) hc hP M hMm hM0 hMp
  unfold pairF phaseInt
  congr 1
  refine setIntegral_congr_ae (measurableSet_Ioc (a := (0:ℝ)) (b := p.period)) ?_
  filter_upwards [(ae_restrict_iff' (measurableSet_Ioc (a := (0:ℝ)) (b := p.period))).1 hnull] with τ hτ' _
  have hτ := hτ' ‹_›
  refine integral_congr_ae ?_
  filter_upwards [hτ, Axi.ae_not_mem_axis] with y hy hyax
  have hpos : 0 < (Axi.chart p.R τ y).1 := Axi.age_pos (inv_pos.2 hε).ne' hyax
  have := hkey _ hpos hy
  rw [NvC_congr_chart this]

end UnforcedLeray.Short.IIb
