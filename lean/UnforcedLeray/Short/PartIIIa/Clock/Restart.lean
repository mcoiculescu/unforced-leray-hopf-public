import UnforcedLeray.Short.PartIIIa.Defs

/-!
# Part III-a full clock: restart of a linearised flow (SP 3085-3090)

"Factor at `t + 1/2`" in the long-gap step (SP 3085) uses that the restriction of a weak
linearised flow from `f` at age `t` to `[t', ∞)` is the weak linearised flow from `w t'` at age `t'`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology

namespace UnforcedLeray.Short.IIIa

theorem IsLinearisedFlow.restart {ν c m : ℝ} {tr : UnforcedLeray.B0140.TrainSol ν c} {t : ℝ}
    {f : ℝ × ℝ → ℂ} {w : ℝ → ℝ × ℝ → ℂ} {u : ℝ → ℝ × ℝ → Fin 2 → ℂ}
    (h : IsLinearisedFlow ν c m tr t f w u) {t' : ℝ} (ht : t ≤ t') :
    IsLinearisedFlow ν c m tr t' (w t') w u where
  initial := Filter.EventuallyEq.rfl
  memX s hs := h.memX s (ht.trans hs)
  strongCont s hs := by
    have := h.strongCont s (ht.trans hs)
    exact this.mono_left (nhdsWithin_mono _ (Ici_subset_Ici.2 ht))
  biotSavart s hs := h.biotSavart s (ht.trans hs)
  integrable φ hφ r hr := h.integrable φ hφ r (ht.trans hr)
  timeIntegrable φ hφ s hs := by
    refine (h.timeIntegrable φ hφ s (ht.trans hs)).mono_set ?_
    exact Set.uIcc_subset_uIcc (Set.mem_uIcc.2 (Or.inl ⟨ht, hs⟩)) (Set.mem_uIcc.2 (Or.inl ⟨ht.trans hs, le_rfl⟩))
  weak φ hφ s hs := by
    have h1 := h.weak φ hφ s (ht.trans hs)
    have h2 := h.weak φ hφ t' ht
    have hI1 := h.timeIntegrable φ hφ t' ht
    have hI2 := h.timeIntegrable φ hφ s (ht.trans hs)
    have hI3 : IntervalIntegrable
        (fun r => ∫ x in B0579.cell c, flowIntegrand tr (w r) (u r) r φ x) volume t' s :=
      hI2.mono_set (Set.uIcc_subset_uIcc (Set.mem_uIcc.2 (Or.inl ⟨ht, hs⟩)) (Set.mem_uIcc.2 (Or.inl ⟨ht.trans hs, le_rfl⟩)))
    rw [h1, h2, ← intervalIntegral.integral_add_adjacent_intervals hI1 hI3]
    ring

end UnforcedLeray.Short.IIIa
