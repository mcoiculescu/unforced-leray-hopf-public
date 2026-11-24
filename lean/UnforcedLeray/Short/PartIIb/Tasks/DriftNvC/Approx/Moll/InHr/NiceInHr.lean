import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T08_2_3_2

/-!
# Part II-b, task `PartII-b:T08/2/3/2/3` (`NiceInHr`): a nice profile lies in `H_r`

Source of record: `the November 2 reference manuscript`, lines 1898-1915.
Target `niceInHr_proof : NiceInHr` (`Sub/PartIIb_T08_2_3_2.lean`).

A nice profile `g` is smooth, everywhere `c`-periodic in `q`, and vanishes off the window
`W = [s₀,s₁] × ℝ × [-L,L]`.  Membership in `H_r` needs: periodicity (everywhere, hence a.e.),
measurability (continuity), and finiteness of `eLpNorm g (ofReal r) (hMeas c r)`.  The measure
`hMeas c r = ageμ c (r/2-5/2)` is carried by the cell `q ∈ [-c/2, c/2)`, so on the cell the
profile is bounded by its maximum on the compact box `[s₀,s₁] × cell × [-L,L]`, and the window
has finite `hMeas`-measure (`Cyl.avgμ_univ_prod`, bounded density `s^a` on `[s₀,s₁]`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

namespace NiceInHrHelp

instance sFinite_avg (c : ℝ) : SFinite (Cyl.avgμ c) := by
  unfold Cyl.avgμ
  infer_instance

/-- The age measure of a window `[s₀,s₁] × ℝ × [-L,L]` is finite when `s₀ > 0`. -/
theorem ageμ_window_lt_top {c : ℝ} (hc : 0 < c) (a s₀ s₁ L : ℝ) (hs₀ : 0 < s₀) :
    Axi.ageμ c a (Icc s₀ s₁ ×ˢ (univ ×ˢ Icc (-L) L)) < ⊤ := by
  unfold Axi.ageμ
  rw [Measure.prod_prod, Cyl.avgμ_univ_prod hc, withDensity_apply _ measurableSet_Icc]
  refine ENNReal.mul_lt_top ?_ measure_Icc_lt_top
  have hcont : ContinuousOn (fun t : ℝ => t ^ a) (Icc s₀ s₁) :=
    ContinuousOn.rpow_const continuousOn_id fun x hx => Or.inl (ne_of_gt (lt_of_lt_of_le hs₀ hx.1))
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  have hle : ∫⁻ x in Icc s₀ s₁, ENNReal.ofReal (x ^ a) ∂(volume.restrict (Ioi (0 : ℝ))) ≤
      ∫⁻ x in Icc s₀ s₁, ENNReal.ofReal C ∂(volume.restrict (Ioi (0 : ℝ))) := by
    refine setLIntegral_mono' measurableSet_Icc fun x hx => ?_
    apply ENNReal.ofReal_le_ofReal
    have h := hC x hx
    rw [Real.norm_eq_abs] at h
    exact (le_abs_self _).trans h
  refine lt_of_le_of_lt hle ?_
  rw [setLIntegral_const]
  refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
  exact lt_of_le_of_lt (Measure.restrict_apply_le _ _) measure_Icc_lt_top

/-- `hMeas`-almost every point has `q ∈ [-c/2, c/2)`. -/
theorem ae_ageμ_q_mem' {c : ℝ} (a : ℝ) :
    ∀ᵐ x ∂(Axi.ageμ c a), x.2.1 ∈ Ico (-c / 2) (c / 2) := by
  rw [ae_iff]
  unfold Axi.ageμ
  have heq : {x : Coord | ¬ x.2.1 ∈ Ico (-c / 2) (c / 2)} =
      (univ : Set ℝ) ×ˢ ((Ico (-c / 2) (c / 2))ᶜ ×ˢ (univ : Set ℝ)) := by
    ext x; simp
  rw [heq, Measure.prod_prod]
  have : Cyl.avgμ c ((Ico (-c / 2) (c / 2))ᶜ ×ˢ (univ : Set ℝ)) = 0 := by
    rw [Cyl.avgμ, Measure.smul_apply, Cyl.cellμ, Measure.restrict_apply
      (measurableSet_Ico.compl.prod MeasurableSet.univ)]
    have : (Ico (-c / 2) (c / 2))ᶜ ×ˢ (univ : Set ℝ) ∩ Cyl.cell c = ∅ := by
      ext x; simp [Cyl.cell]
    simp [this]
  simp [this]

end NiceInHrHelp

open NiceInHrHelp in
/-- **Target** `niceInHr_proof` (`PartII-b:T08/2/3/2/3`). -/
theorem niceInHr_proof : UnforcedLeray.Short.IIb.NiceInHr := by
  intro c r g hc hg
  obtain ⟨hsm, hper, s₀, s₁, L, hs₀, hz⟩ := hg
  set W : Set Coord := Icc s₀ s₁ ×ˢ (univ ×ˢ Icc (-L) L) with hWdef
  have hWm : MeasurableSet W :=
    measurableSet_Icc.prod (MeasurableSet.univ.prod measurableSet_Icc)
  -- the profile vanishes off the window
  have hgW : g = W.indicator g := by
    funext x
    by_cases hx : x ∈ W
    · exact (indicator_of_mem hx g).symm
    · rw [indicator_of_notMem hx]
      apply hz x
      by_contra hcon
      push Not at hcon
      obtain ⟨h1, h2, h3⟩ := hcon
      exact hx ⟨⟨h1, h2⟩, ⟨mem_univ _, abs_le.mp h3⟩⟩
  -- a bound on the cell part of the window
  set K : Set Coord := Icc s₀ s₁ ×ˢ (Icc (-c / 2) (c / 2) ×ˢ Icc (-L) L) with hKdef
  have hKc : IsCompact K := isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  obtain ⟨M, hM⟩ := hKc.exists_bound_of_continuousOn hsm.continuous.continuousOn
  have hμW : Axi.ageμ c (r / 2 - 5 / 2) W < ⊤ :=
    ageμ_window_lt_top hc (r / 2 - 5 / 2) s₀ s₁ L hs₀
  have hae : ∀ᵐ x ∂(Axi.ageμ c (r / 2 - 5 / 2)), ‖g x‖ ≤ max M 0 := by
    filter_upwards [ae_ageμ_q_mem' (c := c) (r / 2 - 5 / 2)] with x hx
    by_cases hW' : x ∈ W
    · have hxK : x ∈ K := ⟨hW'.1, ⟨Ico_subset_Icc_self hx, hW'.2.2⟩⟩
      exact le_max_of_le_left (by simpa [Real.norm_eq_abs] using hM x hxK)
    · have hg0 : g x = 0 := by
        have h := congrFun hgW x
        rw [indicator_of_notMem hW'] at h
        exact h
      simp [hg0]
  have : IsFiniteMeasure ((Axi.ageμ c (r / 2 - 5 / 2)).restrict W) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hμW⟩
  have hmem : MemLp g (ENNReal.ofReal r) ((Axi.ageμ c (r / 2 - 5 / 2)).restrict W) :=
    MemLp.of_bound hsm.continuous.aestronglyMeasurable (max M 0) (ae_restrict_of_ae hae)
  have heq : eLpNorm g (ENNReal.ofReal r) (hMeas c r) =
      eLpNorm g (ENNReal.ofReal r) ((hMeas c r).restrict W) := by
    conv_lhs => rw [hgW]
    exact eLpNorm_indicator_eq_eLpNorm_restrict hWm
  refine ⟨ae_of_all _ hper, hsm.continuous.aestronglyMeasurable, ?_⟩
  unfold hNorm
  rw [heq]
  exact hmem.eLpNorm_lt_top

end UnforcedLeray.Short.IIb
