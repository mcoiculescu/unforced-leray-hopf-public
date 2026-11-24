import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_5_1_3
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.MetricSpace.Bounded

/-!
# `PartIII-b:C/grad/3/5/1/3` L2: compact regions (source 4991)

Proves `HpACompact`: a bounded `U` with closure in `{s > 0}` lies in `s0 ≤ s ≤ s1`, `‖x‖ ≤ R`
with `s0 > 0`. The min and max of `s` and the bound of `x` are attained on the compact set
`{q} ∪ closure U`, where `q = (1, (0,0))` is added so that the set is nonempty.
-/

set_option autoImplicit false

noncomputable section

open Set Metric

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem hpACompact : HpACompact := by
  intro U hbd hcl
  have hUb : Bornology.IsBounded U := Bornology.IsBounded.subset hbd subset_closure
  have hcomp : IsCompact (closure U) := hUb.isCompact_closure
  set q : Chart := (1, (0, 0)) with hq
  set K : Set Chart := {q} ∪ closure U with hK
  have hKc : IsCompact K := (isCompact_singleton).union hcomp
  have hne : K.Nonempty := ⟨q, Set.mem_union_left _ (Set.mem_singleton q)⟩
  obtain ⟨m, hmK, hmin⟩ := hKc.exists_isMinOn hne (continuous_fst.continuousOn)
  obtain ⟨M, hMK, hmax⟩ := hKc.exists_isMaxOn hne (continuous_fst.continuousOn)
  obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn (continuous_snd.continuousOn)
  have hm0 : 0 < m.1 := by
    rcases hmK with hm | hm
    · rw [Set.mem_singleton_iff.mp hm]
      norm_num [hq]
    · exact hcl hm
  have hsle : m.1 ≤ M.1 := isMinOn_iff.mp hmin M hMK
  refine ⟨m.1, M.1, C, hm0, hsle, ?_⟩
  intro p hpU
  have hpK : p ∈ K := Set.mem_union_right _ (subset_closure hpU)
  exact ⟨isMinOn_iff.mp hmin p hpK, isMaxOn_iff.mp hmax p hpK, hC p hpK⟩

end UnforcedLeray.Short.PartIIIb.Concrete
