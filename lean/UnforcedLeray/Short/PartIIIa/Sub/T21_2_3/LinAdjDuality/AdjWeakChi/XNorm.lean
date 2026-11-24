import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_3_1_8_1

/-!
# Part III-a, task `PartIII-a:T21/2/3/1/8/1/2`: the uniform `X_{-m}` bound `AdjWXNormBdd`

Source of record: `the November 2 reference manuscript` lines 3052-3058. The weak
solution `r ↦ φ(r)` of `IsAdjointWeak` is strongly continuous in `X_{-m,c}` on `[t, s]`
(`strongCont`), so `r ↦ ‖φ(r)‖_{X_{-m,c}}` is continuous on the compact `[t, s]` and bounded.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- Continuity within `[t, s]` of `r ↦ ‖φ r‖_{X_{-m,c}}` (ENNReal-valued), from the strong
continuity of `r ↦ φ r` in `X_{-m,c}` and the finiteness of each `‖φ r‖`. -/
theorem xNorm_continuousWithinAt_of_strongCont {c m t s : ℝ} {φ : ℝ → ℝ × ℝ → ℂ}
    (hmem : ∀ r ∈ Icc t s, MemLp (φ r) 2 (B0579.cellMeasure c (-m)))
    (hcont : ∀ r ∈ Icc t s,
      Tendsto (fun r' => xNorm c (-m) (φ r' - φ r)) (𝓝[Icc t s] r) (𝓝 0))
    (r : ℝ) (hr : r ∈ Icc t s) :
    ContinuousWithinAt (fun r' => xNorm c (-m) (φ r')) (Icc t s) r := by
  have hF : xNorm c (-m) (φ r) ≠ ⊤ := (hmem r hr).2.ne
  -- upper triangle inequality `‖φ r'‖ ≤ ‖φ r‖ + ‖φ r' - φ r‖`
  have hup : ∀ r' ∈ Icc t s,
      xNorm c (-m) (φ r') ≤ xNorm c (-m) (φ r) + xNorm c (-m) (φ r' - φ r) := by
    intro r' hr'
    have e : φ r' = φ r + (φ r' - φ r) := by
      funext x; simp only [Pi.add_apply, Pi.sub_apply]; ring
    unfold xNorm
    conv_lhs => rw [e]
    exact eLpNorm_add_le (hmem r hr).1 ((hmem r' hr').sub (hmem r hr)).1 (by norm_num)
  -- lower triangle inequality `‖φ r‖ ≤ ‖φ r'‖ + ‖φ r' - φ r‖`
  have hdown : ∀ r' ∈ Icc t s,
      xNorm c (-m) (φ r) ≤ xNorm c (-m) (φ r') + xNorm c (-m) (φ r' - φ r) := by
    intro r' hr'
    have h := eLpNorm_add_le (μ := B0579.cellMeasure c (-m)) (p := 2) (hmem r' hr').1
      (((hmem r' hr').sub (hmem r hr)).neg).1 (by norm_num)
    rw [eLpNorm_neg] at h
    have e : φ r' + -(φ r' - φ r) = φ r := by
      funext x; simp only [Pi.add_apply, Pi.neg_apply, Pi.sub_apply]; ring
    rw [e] at h
    unfold xNorm
    exact h
  have hD : Tendsto (fun r' => xNorm c (-m) (φ r' - φ r)) (𝓝[Icc t s] r) (𝓝 0) := hcont r hr
  have hup_t : Tendsto (fun r' => xNorm c (-m) (φ r) + xNorm c (-m) (φ r' - φ r))
      (𝓝[Icc t s] r) (𝓝 (xNorm c (-m) (φ r) + 0)) := tendsto_const_nhds.add hD
  have hlow_t : Tendsto (fun r' => xNorm c (-m) (φ r) - xNorm c (-m) (φ r' - φ r))
      (𝓝[Icc t s] r) (𝓝 (xNorm c (-m) (φ r) - 0)) :=
    ENNReal.Tendsto.sub tendsto_const_nhds hD (Or.inl hF)
  rw [add_zero] at hup_t
  rw [tsub_zero] at hlow_t
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow_t hup_t ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with r' hr'
    exact tsub_le_iff_right.2 (hdown r' hr')
  · filter_upwards [self_mem_nhdsWithin] with r' hr'
    exact hup r' hr'

/-- **Leaf `.../2`** (SP 3052-3058; `IsAdjointWeak.memX`, `strongCont`, `tendsto_toReal_eLpNorm`):
`ρ ↦ ‖φ(ρ)‖_{X_{-m}}` is continuous on the compact `[t, s]`, hence bounded on `(t, s)`. -/
theorem adjWXNormBdd (m : ℝ) : UnforcedLeray.Short.IIIa.AdjWXNormBdd m := by
  intro hm ν c tr t s g φ hc hctx
  have hW := hctx.2.2.2.2.2.1
  have hcont : ∀ r ∈ Icc t s,
      ContinuousWithinAt (fun r' => xNorm c (-m) (φ r')) (Icc t s) r :=
    fun r hr => xNorm_continuousWithinAt_of_strongCont (fun r' hr' => hW.memX r' hr')
      (fun r' hr' => hW.strongCont r' hr') r hr
  have hG : ContinuousOn (fun r' => (xNorm c (-m) (φ r')).toReal) (Icc t s) := by
    intro r hr
    have hF : xNorm c (-m) (φ r) ≠ ⊤ := (hW.memX r hr).2.ne
    have hT : ContinuousAt ENNReal.toReal (xNorm c (-m) (φ r)) := ENNReal.continuousAt_toReal hF
    exact ContinuousAt.comp_continuousWithinAt (f := fun r' => xNorm c (-m) (φ r')) (x := r)
      hT (hcont r hr)
  obtain ⟨M, hM⟩ := (isCompact_Icc.image_of_continuousOn hG).bddAbove
  refine ⟨M, fun r hr => ?_⟩
  have hrI : r ∈ Icc t s := Ioo_subset_Icc_self hr
  have hF : xNorm c (-m) (φ r) ≠ ⊤ := (hW.memX r hrI).2.ne
  have hle : (xNorm c (-m) (φ r)).toReal ≤ M :=
    hM (Set.mem_image_of_mem _ hrI)
  calc xNorm c (-m) (φ r) = ENNReal.ofReal ((xNorm c (-m) (φ r)).toReal) :=
        (ENNReal.ofReal_toReal hF).symm
    _ ≤ ENNReal.ofReal M := ENNReal.ofReal_le_ofReal hle

end UnforcedLeray.Short.IIIa
