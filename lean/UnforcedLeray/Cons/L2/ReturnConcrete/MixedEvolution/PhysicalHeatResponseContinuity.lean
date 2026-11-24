import UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.KernelPhysicalHeatComposition
import UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.PhysicalHeatS0ContinuityOn

/-!
# Strong continuity of the actual response at positive ages

The cross-composition law expresses a positive response orbit locally as the actual strongly
continuous weighted S₀ orbit applied to one fixed positive-age response value.
-/

set_option autoImplicit false
set_option maxHeartbeats 500000

noncomputable section

open Filter Set
open scoped Topology

namespace UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution

/-- For each actual weighted flux, its physical signed heat-response orbit is strongly continuous
on the positive short strip. This uses the actual S₀/response composition law, not an unweighted
L² continuity statement. -/
theorem continuousOn_actualWeightedHeatResponse_apply {c m : ℝ} [Fact (0 < c)]
    (hc1 : 1 ≤ c) (hm : 1 ≤ m) (F : ActualFlux (c := c) (m := m)) :
    ContinuousOn (fun t : ℝ =>
      actualWeightedHeatResponse (c := c) (m := m) (hm := hm) t F) (Ioc 0 1) := by
  intro t ht
  let b : ℝ := t / 2
  have hb : 0 < b := by dsimp [b]; linarith [ht.1]
  have hbt : b < t := by dsimp [b]; linarith [ht.1]
  have hb1 : b ≤ 1 := by dsimp [b]; linarith [ht.2]
  let ageMap : Icc b 1 → Icc (0 : ℝ) 1 := fun s =>
    ⟨(s : ℝ) - b, ⟨by have hs := s.property; linarith [hs.1],
      by have hs := s.property; linarith [hs.2]⟩⟩
  have hageMap : Continuous ageMap := by
    apply continuous_induced_rng.mpr
    exact continuous_subtype_val.sub continuous_const
  let clip : ℝ → Icc (0 : ℝ) 1 := fun s =>
    ⟨max 0 (min 1 (s - b)), ⟨le_max_left _ _,
      max_le (by norm_num) (min_le_left _ _)⟩⟩
  have hclip : Continuous clip := by
    apply continuous_induced_rng.mpr
    fun_prop
  let orbit : Icc (0 : ℝ) 1 → ActualVorticity (c := c) (m := m) hm := fun u =>
    actualWeightedHeatS0 (c := c) hc1 hm u.property.1 u.property.2
      (actualWeightedHeatResponse (c := c) (m := m) (hm := hm) b F)
  have horbit : Continuous orbit :=
    continuous_actualWeightedHeatS0_apply hc1 hm
      (actualWeightedHeatResponse (c := c) (m := m) (hm := hm) b F)
  let g : ℝ → ActualVorticity (c := c) (m := m) hm := fun s => orbit (clip s)
  have hg : Continuous g := horbit.comp hclip
  have hEq : ∀ s ∈ Icc b 1,
      actualWeightedHeatResponse (c := c) (m := m) (hm := hm) (s : ℝ) F = g s := by
    intro s hs
    let s' : Icc b 1 := ⟨s, hs⟩
    have ha0 : 0 ≤ (s : ℝ) - b := sub_nonneg.mpr hs.1
    have ha1 : (s : ℝ) - b ≤ 1 := by linarith [hs.2, hb.le]
    have hsum : ((s : ℝ) - b) + b = (s : ℝ) := by ring
    have hclipEq : clip s = ageMap s' := by
      apply Subtype.ext
      change max 0 (min 1 (s - b)) = s - b
      rw [min_eq_right ha1, max_eq_right ha0]
    have hcross := actualWeightedHeatS0_comp_actualWeightedHeatResponse
      (c := c) (m := m) hc1 hm ha0 hb ha1 (by rw [hsum]; exact hs.2) F
    have hage := actualWeightedHeatS0_age_congr (c := c) (m := m) hc1 hm rfl
      ha0 ha1 (ageMap s').property.1 (ageMap s').property.2
    have hvalue := congrArg (fun L : ActualVorticity (c := c) (m := m) hm →L[ℝ]
        ActualVorticity (c := c) (m := m) hm => L
          (actualWeightedHeatResponse (c := c) (m := m) (hm := hm) b F)) hage
    have hcrossValue :
        actualWeightedHeatS0 (c := c) hc1 hm ha0 ha1
          (actualWeightedHeatResponse (c := c) (m := m) (hm := hm) b F) =
        actualWeightedHeatResponse (c := c) (m := m) (hm := hm) (s : ℝ) F := by
      rw [hsum] at hcross
      exact hcross
    change actualWeightedHeatResponse (c := c) (m := m) (hm := hm) (s : ℝ) F =
      orbit (clip s)
    rw [← hcrossValue, ← hvalue]
    rw [hclipEq]
  have hmem : Icc b 1 ∈ 𝓝[Ioc 0 1] t := by
    refine mem_nhdsWithin.2 ⟨Ioi b, isOpen_Ioi, hbt, ?_⟩
    rintro s ⟨hsb, hs⟩
    exact ⟨le_of_lt hsb, hs.2⟩
  have htIcc : t ∈ Icc b 1 := ⟨le_of_lt hbt, ht.2⟩
  have hgAt : ContinuousAt g t := hg.continuousAt
  have hgWithin : ContinuousWithinAt g (Ioc 0 1) t :=
    hgAt.continuousWithinAt.mono_of_mem_nhdsWithin hmem
  have hevent : (fun s : ℝ =>
      actualWeightedHeatResponse (c := c) (m := m) (hm := hm) s F) =ᶠ[𝓝[Ioc 0 1] t]
      fun s => g s := by
    filter_upwards [hmem] with s hs
    exact hEq s hs
  have hlocal : ContinuousWithinAt
      (fun s : ℝ => actualWeightedHeatResponse (c := c) (m := m) (hm := hm) s F)
      (Ioc 0 1) t := by
    exact hgWithin.congr_of_eventuallyEq_of_mem hevent ht
  exact hlocal

end UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution

#print axioms UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.continuousOn_actualWeightedHeatResponse_apply
