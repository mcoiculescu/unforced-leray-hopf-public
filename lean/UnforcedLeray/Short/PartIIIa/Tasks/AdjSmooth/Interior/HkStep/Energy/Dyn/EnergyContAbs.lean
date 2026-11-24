import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.HkStep.Energy.Dyn.Defs
import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.HkStep.Shared

/-!
# `EnergyContAbs` (task `PartIII-a:T21/2/7/2/1/1/5/18/1/12`)

Continuity of the mollified energies `r ↦ cellEnergy c m j (ρ_n ⋆ φ(r))` on `[a, b]`.
Source: SP lines 3060-3071. Helpers are local copies (distinct names) of the leaves used by
`MollConvJet`, so that this file is self-contained.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

theorem eca_pdWordR_props (K : ℝ × ℝ → ℝ) (hK : ContDiff ℝ ∞ K) (hKs : HasCompactSupport K)
    (hK1 : ∀ y : ℝ × ℝ, 1 < ‖y‖ → K y = 0) (w : List (Fin 2)) :
    ContDiff ℝ ∞ (pdWordR w K) ∧ HasCompactSupport (pdWordR w K) ∧
      ∀ y : ℝ × ℝ, 1 < ‖y‖ → pdWordR w K y = 0 := by
  induction w with
  | nil => exact ⟨hK, hKs, hK1⟩
  | cons j w ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    refine ⟨?_, ?_, ?_⟩
    · exact B0579.contDiff_pd h1 j
    · have hpd : B0579.pd j (pdWordR w K) =
          fun x => fderiv ℝ (pdWordR w K) x (B0579.dir j) := rfl
      show HasCompactSupport (B0579.pd j (pdWordR w K))
      rw [hpd]
      exact h2.fderiv_apply ℝ (B0579.dir j)
    · intro y hy
      show B0579.pd j (pdWordR w K) y = 0
      have hopen : IsOpen {z : ℝ × ℝ | 1 < ‖z‖} := isOpen_lt continuous_const continuous_norm
      have hev : pdWordR w K =ᶠ[𝓝 y] (fun _ : ℝ × ℝ => (0 : ℝ)) :=
        Filter.eventually_of_mem (hopen.mem_nhds hy) (fun z hz => h3 z hz)
      unfold B0579.pd
      rw [hev.fderiv_eq]
      simp

theorem eca_cellConv_integrable (K : ℝ × ℝ → ℝ) (hK : Continuous K) (hKs : HasCompactSupport K)
    (g : ℝ × ℝ → ℂ) (hg : LocallyIntegrable g volume) (x : ℝ × ℝ) :
    Integrable (fun y => K y • g (x - y)) volume := by
  have h := (hKs.convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ) hK hg) x
  have h2 := h.integrable
  simpa [ContinuousLinearMap.lsmul_apply] using h2

theorem eca_cellConv_sub (K : ℝ × ℝ → ℝ) (hK : Continuous K) (hKs : HasCompactSupport K)
    (g h : ℝ × ℝ → ℂ) (hg : LocallyIntegrable g volume) (hh : LocallyIntegrable h volume)
    (x : ℝ × ℝ) : cellConv K (g - h) x = cellConv K g x - cellConv K h x := by
  unfold cellConv
  simp only [Pi.sub_apply, smul_sub]
  exact integral_sub (eca_cellConv_integrable K hK hKs g hg x)
    (eca_cellConv_integrable K hK hKs h hh x)

/-- The reverse triangle inequality for the `X_{m,c}` norms of two fields in `X`. -/
theorem eca_abs_xNorm_sub_le (c m : ℝ) (u v : ℝ × ℝ → ℂ)
    (hu : MemLp u 2 (B0579.cellMeasure c (-m))) (hv : MemLp v 2 (B0579.cellMeasure c (-m))) :
    |(xNorm c (-m) u).toReal - (xNorm c (-m) v).toReal| ≤ (xNorm c (-m) (u - v)).toReal := by
  unfold xNorm
  have hu' : eLpNorm u 2 (B0579.cellMeasure c (-m)) ≠ ⊤ := hu.eLpNorm_lt_top.ne
  have hv' : eLpNorm v 2 (B0579.cellMeasure c (-m)) ≠ ⊤ := hv.eLpNorm_lt_top.ne
  have hD' : eLpNorm (u - v) 2 (B0579.cellMeasure c (-m)) ≠ ⊤ :=
    (hu.sub hv).eLpNorm_lt_top.ne
  have key1 : eLpNorm u 2 (B0579.cellMeasure c (-m)) ≤
      eLpNorm (u - v) 2 (B0579.cellMeasure c (-m)) + eLpNorm v 2 (B0579.cellMeasure c (-m)) := by
    have := eLpNorm_add_le (hu.sub hv).1 hv.1 (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    rw [sub_add_cancel] at this
    exact this
  have hneg : eLpNorm (v - u) 2 (B0579.cellMeasure c (-m)) =
      eLpNorm (u - v) 2 (B0579.cellMeasure c (-m)) := by
    rw [← neg_sub u v, eLpNorm_neg]
  have key2 : eLpNorm v 2 (B0579.cellMeasure c (-m)) ≤
      eLpNorm (u - v) 2 (B0579.cellMeasure c (-m)) + eLpNorm u 2 (B0579.cellMeasure c (-m)) := by
    have := eLpNorm_add_le (hv.sub hu).1 hu.1 (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    rw [sub_add_cancel, hneg] at this
    exact this
  have hA : (eLpNorm u 2 (B0579.cellMeasure c (-m))).toReal ≤
      (eLpNorm (u - v) 2 (B0579.cellMeasure c (-m))).toReal +
        (eLpNorm v 2 (B0579.cellMeasure c (-m))).toReal := by
    have := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hD', hv'⟩) key1
    rwa [ENNReal.toReal_add hD' hv'] at this
  have hB : (eLpNorm v 2 (B0579.cellMeasure c (-m))).toReal ≤
      (eLpNorm (u - v) 2 (B0579.cellMeasure c (-m))).toReal +
        (eLpNorm u 2 (B0579.cellMeasure c (-m))).toReal := by
    have := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hD', hu'⟩) key2
    rwa [ENNReal.toReal_add hD' hu'] at this
  exact abs_sub_le_iff.2 ⟨by linarith, by linarith⟩

/-- A family in `X_{m,c}` continuous within `I` in the sense of `xNorm` of differences has
continuous norms within `I`. -/
theorem eca_continuousOn_xNorm (c m : ℝ) (I : Set ℝ) (G : ℝ → ℝ × ℝ → ℂ)
    (hG : ∀ r ∈ I, MemLp (G r) 2 (B0579.cellMeasure c (-m)))
    (hcont : ∀ r ∈ I, Tendsto (fun r' => xNorm c (-m) (G r' - G r)) (𝓝[I] r) (𝓝 0)) :
    ContinuousOn (fun r => (xNorm c (-m) (G r)).toReal) I := by
  intro r hr
  show Tendsto (fun r' => (xNorm c (-m) (G r')).toReal) (𝓝[I] r)
    (𝓝 (xNorm c (-m) (G r)).toReal)
  have h1 : Tendsto (fun r' => (xNorm c (-m) (G r' - G r)).toReal) (𝓝[I] r) (𝓝 0) := by
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (hcont r hr)
    rw [ENNReal.toReal_zero] at this
    exact this
  have h2 : Tendsto (fun r' => (xNorm c (-m) (G r')).toReal - (xNorm c (-m) (G r)).toReal)
      (𝓝[I] r) (𝓝 0) := by
    apply squeeze_zero_norm' _ h1
    filter_upwards [self_mem_nhdsWithin] with r' hr'
    rw [Real.norm_eq_abs]
    exact eca_abs_xNorm_sub_le c m (G r') (G r) (hG r' hr') (hG r hr)
  have h3 := h2.add_const (xNorm c (-m) (G r)).toReal
  rw [zero_add] at h3
  refine Tendsto.congr (fun r' => ?_) h3
  simp

theorem energyContAbs (hB : UnforcedLeray.Short.IIIa.CellConvBound)
    (hD : UnforcedLeray.Short.IIIa.CellConvDeriv) (hL : UnforcedLeray.Short.IIIa.CellPeriodicLocInt)
    (hK : UnforcedLeray.Short.IIIa.MollKerProps) : UnforcedLeray.Short.IIIa.EnergyContAbs := by
  intro c m j n a b φ hc hφ hφtend
  obtain ⟨C, hC0, hBC⟩ := hB c m hc
  obtain ⟨hKc, hKs, hKz⟩ := hK n
  have hw : ∀ w : List (Fin 2), ContinuousOn
      (fun r => (xNorm c (-m) (adjSpatial w (cellMoll n (φ r)))).toReal) (Icc a b) := by
    intro w
    obtain ⟨K1c, K1s, K1z⟩ := eca_pdWordR_props (molKer n) hKc hKs hKz w
    have hG : ∀ r ∈ Icc a b, adjSpatial w (cellMoll n (φ r)) =
        cellConv (pdWordR w (molKer n)) (φ r) := fun r hr =>
      (hD c m (molKer n) (φ r) hc hKc hKs (hφ r hr).1 (hφ r hr).2).2.2 w
    have hmem : ∀ r ∈ Icc a b, MemLp (adjSpatial w (cellMoll n (φ r))) 2
        (B0579.cellMeasure c (-m)) := by
      intro r hr
      rw [hG r hr]
      exact (hBC _ (φ r) K1c.continuous K1z (hφ r hr).1 (hφ r hr).2).1
    have hT : ∀ r ∈ Icc a b, Tendsto
        (fun r' => xNorm c (-m) (adjSpatial w (cellMoll n (φ r')) - adjSpatial w (cellMoll n (φ r))))
        (𝓝[Icc a b] r) (𝓝 0) := by
      intro r hr
      have hlim : Tendsto (fun r' => ENNReal.ofReal (C * ∫ y, |pdWordR w (molKer n) y|) *
          xNorm c (-m) (φ r' - φ r)) (𝓝[Icc a b] r)
          (𝓝 (ENNReal.ofReal (C * ∫ y, |pdWordR w (molKer n) y|) * 0)) :=
        ENNReal.Tendsto.const_mul (hφtend r hr) (Or.inr ENNReal.ofReal_ne_top)
      rw [mul_zero] at hlim
      have hbound : ∀ᶠ r' in 𝓝[Icc a b] r,
          xNorm c (-m) (adjSpatial w (cellMoll n (φ r')) - adjSpatial w (cellMoll n (φ r))) ≤
            ENNReal.ofReal (C * ∫ y, |pdWordR w (molKer n) y|) * xNorm c (-m) (φ r' - φ r) := by
        filter_upwards [eventually_mem_nhdsWithin] with r' hr'
        have hL' := hL c m (φ r') hc (hφ r' hr').1 (hφ r' hr').2
        have hL'' := hL c m (φ r) hc (hφ r hr).1 (hφ r hr).2
        have hdiff : adjSpatial w (cellMoll n (φ r')) - adjSpatial w (cellMoll n (φ r)) =
            cellConv (pdWordR w (molKer n)) (φ r' - φ r) := by
          rw [hG r' hr', hG r hr]
          funext x
          exact (eca_cellConv_sub (pdWordR w (molKer n)) K1c.continuous K1s (φ r') (φ r)
            hL'.2 hL''.2 x).symm
        have hperdiff : ∀ x : ℝ × ℝ, (φ r' - φ r) (x.1 + c, x.2) = (φ r' - φ r) x := by
          intro x
          simp only [Pi.sub_apply, (hφ r' hr').1 x, (hφ r hr).1 x]
        have hmemdiff : MemLp (φ r' - φ r) 2 (B0579.cellMeasure c (-m)) :=
          (hφ r' hr').2.sub (hφ r hr).2
        rw [hdiff]
        exact (hBC (pdWordR w (molKer n)) (φ r' - φ r) K1c.continuous K1z hperdiff hmemdiff).2
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
        (Filter.Eventually.of_forall fun _ => zero_le) hbound
    exact eca_continuousOn_xNorm c m (Icc a b) (fun r => adjSpatial w (cellMoll n (φ r)))
      hmem hT
  unfold cellEnergy
  exact continuousOn_finsetSum _ (fun w _ => (hw w).pow 2)

end UnforcedLeray.Short.IIIa
