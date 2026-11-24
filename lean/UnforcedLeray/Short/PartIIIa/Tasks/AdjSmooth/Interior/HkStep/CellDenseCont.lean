import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.HkStep.CellDenseCont.Weight
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.HkStep.CellDenseCont.Support
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.HkStep.CellDenseCont.Truncate

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace UnforcedLeray.Short.IIIa

/-- (a4) Density of continuous periodic band-limited fields in the periodic `X_{-m,c}`
(SP 3060-3061): truncate to a box inside the open cell, approximate by a continuous compactly
supported field in `L²` of the (finite) weighted measure on a compact set, cut off by a continuous
`χ` vanishing on `|x₁| ≥ c/2`, and extend periodically. -/
theorem cellDenseCont : UnforcedLeray.Short.IIIa.CellDenseCont := by
  intro c m f hc hper hf ε hε
  have hε2 : (0 : ℝ) < ε / 2 := by linarith
  -- (1) truncation
  obtain ⟨n, hn⟩ : ∃ n : ℕ, eLpNorm (f - (cddBox c n).indicator f) 2 (B0579.cellMeasure c (-m))
      < ENNReal.ofReal (ε / 2) :=
    ((tendsto_order.1 (tendsto_truncate hf)).2 _ (ENNReal.ofReal_pos.2 hε2)).exists
  -- (2) the cutoff
  let t : Set (ℝ × ℝ) := {x | x.1 ≤ -(c / 2)} ∪ {x | c / 2 ≤ x.1}
  have ht : IsClosed t :=
    (isClosed_le continuous_fst continuous_const).union (isClosed_le continuous_const continuous_fst)
  have hdisj : Disjoint (cddBox c n) t := by
    rw [Set.disjoint_left]
    intro x hx hxt
    have := cddBox_subset n hx
    rcases hxt with h | h
    · exact absurd h (not_le.2 this.1)
    · exact absurd h (not_le.2 this.2)
  obtain ⟨χ, hχ1, hχ0, hχcs, hχr⟩ :=
    exists_continuous_one_zero_of_isCompact (isCompact_cddBox c n) ht hdisj
  set S := tsupport (χ : ℝ × ℝ → ℝ) with hS
  have hSc : IsCompact S := hχcs
  have hχ_out : ∀ x : ℝ × ℝ, x ∉ S → χ x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport hx
  -- (3) approximation on the finite measure `μ|_S`
  obtain ⟨C, hCpos, hCle⟩ := cellMeasure_restrict_le (c := c) (m := -m) hSc
  set μ := B0579.cellMeasure c (-m) with hμ
  have : IsFiniteMeasure (μ.restrict S) := by
    refine ⟨?_⟩
    calc (μ.restrict S) univ = (μ.restrict S) S := by
          rw [Measure.restrict_apply_univ, Measure.restrict_apply_self]
      _ ≤ ((C : ℝ≥0∞) • (volume : Measure (ℝ × ℝ))) S := hCle S
      _ < ∞ := by
          rw [Measure.smul_apply, smul_eq_mul]
          exact ENNReal.mul_lt_top ENNReal.coe_lt_top hSc.measure_lt_top
  let g : ℝ × ℝ → ℂ := (cddBox c n).indicator f
  have hKS : cddBox c n ⊆ S := by
    intro x hx
    apply subset_tsupport
    show χ x ≠ 0
    rw [hχ1 hx]; exact one_ne_zero
  have hg : MemLp g 2 (μ.restrict S) := (hf.indicator (cddBox_closed c n)).restrict S
  obtain ⟨h0, h0cs, h0le, h0c, -⟩ := hg.exists_hasCompactSupport_eLpNorm_sub_le (p := 2)
    (by norm_num) (ε := ENNReal.ofReal (ε / 2)) (by simpa using hε2)
  let h1 : ℝ × ℝ → ℂ := fun x => ((χ x : ℝ) : ℂ) * h0 x
  have h1c : Continuous h1 := (Complex.continuous_ofReal.comp χ.continuous).mul h0c
  have h1_out : ∀ x : ℝ × ℝ, x ∉ S → h1 x = 0 := fun x hx => by simp [h1, hχ_out x hx]
  have h1_t : ∀ x : ℝ × ℝ, (x.1 ≤ -(c / 2) ∨ c / 2 ≤ x.1) → h1 x = 0 := fun x hx => by
    have : χ x = 0 := hχ0 (show x ∈ t from hx)
    simp [h1, this]
  refine ⟨perRep c h1, continuous_perRep hc h1c h1_t,
    fun x => perRep_periodic hc h1 x, ?_, ?_⟩
  · obtain ⟨R, hR⟩ := hSc.exists_bound_of_continuousOn
      (f := fun x : ℝ × ℝ => x.2) continuous_snd.continuousOn
    refine ⟨R, fun x hx => ?_⟩
    have : (toIcoMod hc (-(c / 2)) x.1, x.2) ∉ S := fun hmem => by
      have : |x.2| ≤ R := by simpa [Real.norm_eq_abs] using hR _ hmem
      linarith
    simp only [perRep, hc, ↓reduceDIte]
    exact h1_out _ this
  · show eLpNorm (f - perRep c h1) 2 μ ≤ ENNReal.ofReal ε
    have hae : f - perRep c h1 =ᵐ[μ] f - h1 :=
      (perRep_ae_cellMeasure hc (-m) h1).mono fun x hx => by simp [hx]
    rw [eLpNorm_congr_ae hae]
    have hsplit : f - h1 = (f - g) + (g - h1) := by abel
    have hgm : AEStronglyMeasurable g μ := hf.1.indicator (cddBox_closed c n)
    have hA : eLpNorm (g - h1) 2 μ ≤ ENNReal.ofReal (ε / 2) := by
      have hsupp : g - h1 = S.indicator (g - h1) := by
        funext x
        by_cases hx : x ∈ S
        · simp [hx]
        · have hg0 : g x = 0 := by
            simp only [g]
            rw [Set.indicator_of_notMem]
            exact fun hxK => hx (hKS hxK)
          simp [hx, hg0, h1_out x hx]
      rw [hsupp, eLpNorm_indicator_eq_eLpNorm_restrict hSc.measurableSet]
      refine le_trans (eLpNorm_mono fun x => ?_) h0le
      have hgx : g x = (χ x : ℂ) * g x := by
        by_cases hx : x ∈ cddBox c n
        · simp [hχ1 hx]
        · simp [g, hx]
      have hid : (g - h1) x = (χ x : ℂ) * (g x - h0 x) := by
        simp only [Pi.sub_apply, h1]
        rw [mul_sub, ← hgx]
      rw [hid, norm_mul]
      have := hχr x
      simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg this.1, Pi.sub_apply]
      exact mul_le_of_le_one_left (norm_nonneg _) this.2
    calc eLpNorm (f - h1) 2 μ ≤ eLpNorm (f - g) 2 μ + eLpNorm (g - h1) 2 μ := by
          rw [hsplit]
          exact eLpNorm_add_le (hf.1.sub hgm) (hgm.sub h1c.aestronglyMeasurable) (by norm_num)
      _ ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := add_le_add hn.le hA
      _ = ENNReal.ofReal ε := by
          rw [← ENNReal.ofReal_add hε2.le hε2.le]
          congr 1; ring

end UnforcedLeray.Short.IIIa
