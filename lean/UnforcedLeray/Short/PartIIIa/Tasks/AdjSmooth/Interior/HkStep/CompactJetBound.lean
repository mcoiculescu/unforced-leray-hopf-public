import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.HkStep.Defs

/-!
# `PartIII-a:T21/2/7/2/1/1/5/1`: weighted jet norms are finite and bounded on compact age sets

Source of record: `the November 2 reference manuscript` (SP), lines 3060-3061.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- Reverse triangle inequality for the weighted norm `xNorm` on `MemLp` fields. -/
theorem abs_toReal_xNorm_sub_le {c m : ℝ} {f g : ℝ × ℝ → ℂ}
    (hf : MemLp f 2 (B0579.cellMeasure c (-m))) (hg : MemLp g 2 (B0579.cellMeasure c (-m))) :
    |(xNorm c (-m) f).toReal - (xNorm c (-m) g).toReal| ≤ (xNorm c (-m) (f - g)).toReal := by
  have hfg : MemLp (f - g) 2 (B0579.cellMeasure c (-m)) := hf.sub hg
  have hf1 : xNorm c (-m) f ≤ xNorm c (-m) (f - g) + xNorm c (-m) g := by
    unfold xNorm
    calc eLpNorm f 2 (B0579.cellMeasure c (-m))
        = eLpNorm ((f - g) + g) 2 (B0579.cellMeasure c (-m)) := by rw [sub_add_cancel]
      _ ≤ eLpNorm (f - g) 2 (B0579.cellMeasure c (-m)) + eLpNorm g 2 (B0579.cellMeasure c (-m)) :=
          eLpNorm_add_le hfg.1 hg.1 (by norm_num)
  have hg1 : xNorm c (-m) g ≤ xNorm c (-m) f + xNorm c (-m) (f - g) := by
    unfold xNorm
    calc eLpNorm g 2 (B0579.cellMeasure c (-m))
        = eLpNorm (f - (f - g)) 2 (B0579.cellMeasure c (-m)) := by rw [sub_sub_cancel]
      _ ≤ eLpNorm f 2 (B0579.cellMeasure c (-m)) + eLpNorm (f - g) 2 (B0579.cellMeasure c (-m)) :=
          eLpNorm_sub_le hf.1 hfg.1 (by norm_num)
  have hfin : ∀ {h : ℝ × ℝ → ℂ}, MemLp h 2 (B0579.cellMeasure c (-m)) →
      xNorm c (-m) h ≠ ⊤ := fun hh => hh.eLpNorm_lt_top.ne
  have hF := hfin hf
  have hG := hfin hg
  have hD := hfin hfg
  have e1 : (xNorm c (-m) f).toReal ≤ (xNorm c (-m) (f - g)).toReal + (xNorm c (-m) g).toReal := by
    have := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hD, hG⟩) hf1
    rwa [ENNReal.toReal_add hD hG] at this
  have e2 : (xNorm c (-m) g).toReal ≤ (xNorm c (-m) f).toReal + (xNorm c (-m) (f - g)).toReal := by
    have := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hF, hD⟩) hg1
    rwa [ENNReal.toReal_add hF hD] at this
  have hd0 : 0 ≤ (xNorm c (-m) (f - g)).toReal := ENNReal.toReal_nonneg
  exact abs_sub_le_iff.2 ⟨by linarith, by linarith⟩

/-- Continuity within `I` of the real weighted norm of a family `F` that is continuous into
`X_{-m,c}` within `I`. -/
theorem xNorm_toReal_continuousWithinAt {c m : ℝ} {I : Set ℝ} {F : ℝ → ℝ × ℝ → ℂ} {r0 : ℝ}
    (hmem : ∀ r ∈ I, MemLp (F r) 2 (B0579.cellMeasure c (-m))) (hr0 : r0 ∈ I)
    (hT : Tendsto (fun r' => xNorm c (-m) (F r' - F r0)) (𝓝[I] r0) (𝓝 0)) :
    ContinuousWithinAt (fun r => (xNorm c (-m) (F r)).toReal) I r0 := by
  unfold ContinuousWithinAt
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hd : Tendsto (fun r' => (xNorm c (-m) (F r' - F r0)).toReal) (𝓝[I] r0) (𝓝 0) := by
    have h0 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hT
    rw [ENNReal.toReal_zero] at h0
    exact h0
  refine squeeze_zero' (Filter.Eventually.of_forall fun _ => norm_nonneg _) ?_ hd
  refine Filter.eventually_of_mem self_mem_nhdsWithin (fun r hr => ?_)
  rw [Real.norm_eq_abs]
  exact abs_toReal_xNorm_sub_le (hmem r hr) (hmem r0 hr0)

/-- **Weighted jet norms are bounded on compact age sets** (SP 3060-3061: the weighted energies
are finite on compact age intervals). Proof: for each word `w` with `|w| ≤ k`, the real function
`r ↦ ‖D r w‖_{X_{-m,c}}` is continuous within `I` (`xNorm_toReal_continuousWithinAt`), hence bounded
on the compact `K ⊆ I`; the sum of the bounds over `wordsLE k` bounds every top and lower field. -/
theorem compactJetBound : UnforcedLeray.Short.IIIa.CompactJetBound := by
  intro c m k I K φ D hjet hT hKc hKI
  have hword : ∀ w : List (Fin 2), ∃ B : ℝ, w.length ≤ k →
      ∀ r ∈ K, (xNorm c (-m) (D r w)).toReal ≤ B := by
    intro w
    by_cases hw : w.length ≤ k
    · have hcont : ContinuousOn (fun r => (xNorm c (-m) (D r w)).toReal) I := by
        intro r0 hr0
        exact xNorm_toReal_continuousWithinAt (fun r hr => (hjet r hr).memX w hw) hr0
          (hT w hw r0 hr0)
      obtain ⟨B, hB⟩ := hKc.exists_bound_of_continuousOn (hcont.mono hKI)
      refine ⟨B, fun _ r hr => ?_⟩
      have h := hB r hr
      rw [Real.norm_eq_abs] at h
      exact (le_abs_self _).trans h
    · exact ⟨0, fun h => absurd h hw⟩
  choose B hB using hword
  refine ⟨∑ w ∈ wordsLE k, |B w|, fun r hr w hw => ?_⟩
  have hfin : xNorm c (-m) (D r w) ≠ ⊤ :=
    ((hjet r (hKI hr)).memX w hw).eLpNorm_lt_top.ne
  calc xNorm c (-m) (D r w)
      = ENNReal.ofReal (xNorm c (-m) (D r w)).toReal := (ENNReal.ofReal_toReal hfin).symm
    _ ≤ ENNReal.ofReal (∑ w ∈ wordsLE k, |B w|) := by
        apply ENNReal.ofReal_le_ofReal
        exact (hB w hw r hr).trans ((le_abs_self _).trans
          (Finset.single_le_sum (f := fun w => |B w|) (fun _ _ => abs_nonneg _)
            (mem_wordsLE.2 hw)))

end UnforcedLeray.Short.IIIa
