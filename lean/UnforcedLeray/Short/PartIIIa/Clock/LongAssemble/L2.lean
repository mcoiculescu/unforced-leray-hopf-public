import UnforcedLeray.Short.PartIIIa.Defs

/-!
# Part III-a long assembly, L2: finiteness of the sup of `‖w r‖_{X_{m,c}}` on `[t, s]`

Proves `UnforcedLeray.Short.IIIa.xNorm_bounded_on_Icc` (task PartIII-a:T21/long/2).

Proof. The map `r ↦ xNorm c m (w r)` is upper semicontinuous on `Icc t s`: by the triangle
inequality `xNorm (w r) ≤ xNorm (w r - w x) + xNorm (w x)`, and `strongCont` gives
`xNorm (w r - w x) → 0` as `r → x` within `Ici t`, while `xNorm (w x) < ∞` by `memX`.
An upper semicontinuous function attains its maximum on the nonempty compact `Icc t s`, and the
maximum is finite; the empty case gives `0`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

theorem xNorm_bounded_on_Icc {ν c m t s : ℝ} {tr : UnforcedLeray.B0140.TrainSol ν c} {f : ℝ × ℝ → ℂ} {w : ℝ → ℝ × ℝ → ℂ} {u : ℝ → ℝ × ℝ → Fin 2 → ℂ} (h : IsLinearisedFlow ν c m tr t f w u) : (⨆ r ∈ Set.Icc t s, xNorm c m (w r)) ≠ ⊤ := by
  have hF : ∀ r, t ≤ r → xNorm c m (w r) < ⊤ := fun r hr => (h.memX r hr).eLpNorm_lt_top
  have hsemi : UpperSemicontinuousOn (fun r => xNorm c m (w r)) (Icc t s) := by
    intro x hx y hy
    have hFx : xNorm c m (w x) ≠ ⊤ := (hF x hx.1).ne
    have hpos : 0 < y - xNorm c m (w x) := tsub_pos_iff_lt.2 hy
    have hT := (h.strongCont x hx.1).mono_left
      (nhdsWithin_mono x (fun r (hr : r ∈ Icc t s) => (hr.1 : r ∈ Ici t)))
    have hD := (tendsto_order.1 hT).2 _ hpos
    filter_upwards [hD, self_mem_nhdsWithin] with r hr hrI
    have htri : xNorm c m (w r) ≤ xNorm c m (w r - w x) + xNorm c m (w x) := by
      have hm1 : AEStronglyMeasurable (w r - w x) (UnforcedLeray.B0579.cellMeasure c m) :=
        (h.memX r hrI.1).1.sub (h.memX x hx.1).1
      have hm2 : AEStronglyMeasurable (w x) (UnforcedLeray.B0579.cellMeasure c m) :=
        (h.memX x hx.1).1
      calc xNorm c m (w r) = eLpNorm ((w r - w x) + w x) 2 (UnforcedLeray.B0579.cellMeasure c m) := by
            unfold xNorm; rw [sub_add_cancel]
        _ ≤ eLpNorm (w r - w x) 2 (UnforcedLeray.B0579.cellMeasure c m)
              + eLpNorm (w x) 2 (UnforcedLeray.B0579.cellMeasure c m) :=
            eLpNorm_add_le hm1 hm2 (by norm_num)
        _ = xNorm c m (w r - w x) + xNorm c m (w x) := rfl
    calc xNorm c m (w r) ≤ xNorm c m (w r - w x) + xNorm c m (w x) := htri
      _ < y - xNorm c m (w x) + xNorm c m (w x) := ENNReal.add_lt_add_right hFx hr
      _ = y := tsub_add_cancel_of_le hy.le
  rcases Set.eq_empty_or_nonempty (Icc t s) with hE | hne
  · rw [hE]; simp
  · obtain ⟨x, hx, hmax⟩ := UpperSemicontinuousOn.exists_isMaxOn hne isCompact_Icc hsemi
    refine ne_top_of_le_ne_top (hF x hx.1).ne (iSup₂_le fun r hr => ?_)
    exact isMaxOn_iff.1 hmax r hr

end UnforcedLeray.Short.IIIa
