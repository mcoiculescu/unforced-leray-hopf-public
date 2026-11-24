import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T22_2_1_2_3

/-!

is bounded on a compact age interval

Source: `the November 2 reference manuscript`
(SP 2074-2105). The map `s ↦ ‖ω s‖_{L²(cellMeasure c m)}` is continuous on `[t₀, ∞)` because
`strongCont` says `ω` is continuous into `L²(cellMeasure c m)` there; a continuous real
function on a compact interval is bounded.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIb

/-- The weighted norm of a free cylinder flow is continuous in age on `[t₀, ∞)`. -/
theorem cylFlowNorm_continuousWithinAt {m : ℝ} {ν c : ℝ} {tr : B0140.TrainSol ν c} {t₀ : ℝ}
    {f : B0579.Plane → ℝ} {ω : ℝ → B0579.Plane → ℝ} (hω : IsFreeCylFlow m tr t₀ f ω)
    (s : ℝ) (hs0 : t₀ ≤ s) :
    ContinuousWithinAt (fun s' => (eLpNorm (ω s') 2 (B0579.cellMeasure c m)).toReal)
      (Ici t₀) s := by
  set μ := B0579.cellMeasure c m with hμ
  have hBfin : eLpNorm (ω s) 2 μ ≠ ⊤ := (hω.memX s hs0).2.ne
  have hD : Tendsto (fun s' => eLpNorm (ω s' - ω s) 2 μ) (𝓝[Ici t₀] s) (𝓝 0) :=
    hω.strongCont s hs0
  have hD' : Tendsto (fun s' => (eLpNorm (ω s' - ω s) 2 μ).toReal) (𝓝[Ici t₀] s) (𝓝 0) := by
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hD
    simpa [Function.comp_def] using this
  unfold ContinuousWithinAt
  apply tendsto_iff_dist_tendsto_zero.2
  refine squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg) ?_ hD'
  filter_upwards [self_mem_nhdsWithin, hD.eventually (gt_mem_nhds (by norm_num : (0 : ℝ≥0∞) < 1))]
    with s' hs' hd1
  have hs'0 : t₀ ≤ s' := hs'
  have hAm : AEStronglyMeasurable (ω s') μ := (hω.memX s' hs'0).1
  have hBm : AEStronglyMeasurable (ω s) μ := (hω.memX s hs0).1
  have hDm : AEStronglyMeasurable (ω s' - ω s) μ := hAm.sub hBm
  have hAfin : eLpNorm (ω s') 2 μ ≠ ⊤ := (hω.memX s' hs'0).2.ne
  have hdfin : eLpNorm (ω s' - ω s) 2 μ ≠ ⊤ := (hd1.trans ENNReal.one_lt_top).ne
  have hp : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  have e1 : eLpNorm (ω s') 2 μ ≤ eLpNorm (ω s' - ω s) 2 μ + eLpNorm (ω s) 2 μ := by
    have h := eLpNorm_add_le hDm hBm hp
    rwa [sub_add_cancel] at h
  have e2 : eLpNorm (ω s) 2 μ ≤ eLpNorm (ω s' - ω s) 2 μ + eLpNorm (ω s') 2 μ := by
    have h := eLpNorm_add_le (hBm.sub hAm) hAm hp
    rw [sub_add_cancel] at h
    rwa [eLpNorm_sub_comm (ω s) (ω s') 2 μ] at h
  have k1 : (eLpNorm (ω s') 2 μ).toReal ≤
      (eLpNorm (ω s' - ω s) 2 μ).toReal + (eLpNorm (ω s) 2 μ).toReal := by
    rw [← ENNReal.toReal_add hdfin hBfin]
    exact ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hdfin, hBfin⟩) e1
  have k2 : (eLpNorm (ω s) 2 μ).toReal ≤
      (eLpNorm (ω s' - ω s) 2 μ).toReal + (eLpNorm (ω s') 2 μ).toReal := by
    rw [← ENNReal.toReal_add hdfin hAfin]
    exact ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hdfin, hAfin⟩) e2
  rw [Real.dist_eq, abs_sub_le_iff]
  constructor <;> linarith

end UnforcedLeray.Short.IIb

open UnforcedLeray UnforcedLeray.Short.IIb in
theorem cylFlowNormBound : UnforcedLeray.Short.IIb.CylFlowNormBound := by
  intro m hm ν c tr t₀ f ω hω t₁ ht
  have hcont : ContinuousOn (fun s' => (eLpNorm (ω s') 2 (B0579.cellMeasure c m)).toReal)
      (Icc t₀ t₁) := by
    intro s hs
    exact (cylFlowNorm_continuousWithinAt hω s hs.1).mono Icc_subset_Ici_self
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  refine ⟨B, fun r hr => ?_⟩
  have h := hB r hr
  rw [Real.norm_eq_abs] at h
  exact (le_abs_self _).trans h
