import UnforcedLeray.Short.PartIIb.Sub.T12_6
import UnforcedLeray.Short.PartIIb.Tasks.FlatUnique.CellStream.HrBox

/-!
# Part II-b, task `PartII-b:T12/6/1` (`DsolIntegrable`): Hölder on the support of the test

Source of record: `the November 2 reference manuscript`, lines 1920-1930 (SP 1924).
Target: `dsolIntegrable : DsolIntegrable` of `Sub/T12_6.lean`.

Proof. A coordinate test `φ` has compact support inside `{s > 0}`, so its support lies in a box
`B = [σ,H] × [-R,R] × [-L,L]` with `σ > 0` (`isCoordTest_box`). On `B` the component `b_i` is
integrable (`hrBoxIntegrable`, the box integrability of `H_r` profiles). The factor
`cpd j φ` is continuous with compact support, hence bounded, and vanishes off `B`. So
`b_i · cpd j φ = cpd j φ · 1_B b_i` is integrable by `Integrable.bdd_mul`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-- The compact support of a coordinate test lies in a box `[σ,H] × [-R,R] × [-L,L]` with `σ > 0`. -/
theorem isCoordTest_box {φ : Coord → ℝ} (hφ : IsCoordTest φ) :
    ∃ σ H R L : ℝ, 0 < σ ∧ tsupport φ ⊆ Icc σ H ×ˢ (Icc (-R) R ×ˢ Icc (-L) L) := by
  have hK : IsCompact (tsupport φ) := hφ.compact
  rcases (tsupport φ).eq_empty_or_nonempty with he | hne
  · refine ⟨1, 1, 1, 1, one_pos, ?_⟩
    rw [he]
    exact empty_subset _
  · obtain ⟨x0, hx0, hmin⟩ := hK.exists_isMinOn hne continuous_fst.continuousOn
    obtain ⟨C1, hC1⟩ :=
      isBounded_iff_forall_norm_le.1 ((hK.image continuous_fst).isBounded)
    obtain ⟨C2, hC2⟩ :=
      isBounded_iff_forall_norm_le.1 ((hK.image (continuous_fst.comp continuous_snd)).isBounded)
    obtain ⟨C3, hC3⟩ :=
      isBounded_iff_forall_norm_le.1 ((hK.image (continuous_snd.comp continuous_snd)).isBounded)
    have hpos : 0 < x0.1 := (Set.mem_prod.1 (hφ.supp hx0)).1
    refine ⟨x0.1, C1, C2, C3, hpos, fun x hx => ?_⟩
    have h1 : |x.1| ≤ C1 := by simpa [Real.norm_eq_abs] using hC1 x.1 ⟨x, hx, rfl⟩
    have h2 : |x.2.1| ≤ C2 := by simpa [Real.norm_eq_abs] using hC2 x.2.1 ⟨x, hx, rfl⟩
    have h3 : |x.2.2| ≤ C3 := by simpa [Real.norm_eq_abs] using hC3 x.2.2 ⟨x, hx, rfl⟩
    have hs : x0.1 ≤ x.1 := hmin hx
    exact ⟨⟨hs, (abs_le.1 h1).2⟩, abs_le.1 h2, abs_le.1 h3⟩

/-- **Leaf `PartII-b:T12/6/1`** (SP 1924): `b_i · cpd j φ` is Lebesgue integrable for `b ∈ H_r`,
`1 < r`, and a coordinate test `φ`. -/
theorem dsolIntegrable : DsolIntegrable := by
  intro c r b hc hr1 _hr3 hb φ hφ i j
  obtain ⟨σ, H, R, L, hσ, hsub⟩ := isCoordTest_box hφ
  have hBm : MeasurableSet (Icc σ H ×ˢ (Icc (-R) R ×ˢ Icc (-L) L)) :=
    measurableSet_Icc.prod (measurableSet_Icc.prod measurableSet_Icc)
  have hbox : IntegrableOn (fun x : Coord => b x i)
      (Icc σ H ×ˢ (Icc (-R) R ×ˢ Icc (-L) L)) volume :=
    hrBoxIntegrable c r b hc hr1 hb σ H R L hσ i
  have hbi : Integrable ((Icc σ H ×ˢ (Icc (-R) R ×ˢ Icc (-L) L)).indicator
      (fun x : Coord => b x i)) volume :=
    hbox.integrable_indicator hBm
  have hcont : Continuous (fun x : Coord => cpd j φ x) := by
    have h1 : Continuous (fderiv ℝ φ) := hφ.smooth.continuous_fderiv (by simp)
    exact h1.clm_apply continuous_const
  have hcs : HasCompactSupport (fun x : Coord => cpd j φ x) :=
    hφ.compact.fderiv_apply ℝ (cdir j)
  obtain ⟨M, hM⟩ := hcont.bounded_above_of_compact_support hcs
  have hzero : ∀ x : Coord, x ∉ Icc σ H ×ˢ (Icc (-R) R ×ˢ Icc (-L) L) → cpd j φ x = 0 := by
    intro x hx
    have hnt : x ∉ tsupport φ := fun h => hx (hsub h)
    have h0 : x ∉ Function.support (fderiv ℝ φ) := fun h => hnt (support_fderiv_subset ℝ h)
    have h1 : fderiv ℝ φ x = 0 := by simpa [Function.mem_support] using h0
    unfold cpd
    rw [h1, ContinuousLinearMap.zero_apply]
  have hfun : (fun x : Coord => b x i * (cpd j φ x : ℂ)) =
      fun x : Coord => ((cpd j φ x : ℝ) : ℂ) *
        (Icc σ H ×ˢ (Icc (-R) R ×ˢ Icc (-L) L)).indicator (fun y : Coord => b y i) x := by
    funext x
    by_cases hx : x ∈ Icc σ H ×ˢ (Icc (-R) R ×ˢ Icc (-L) L)
    · rw [Set.indicator_of_mem hx]
      ring
    · rw [Set.indicator_of_notMem hx, hzero x hx]
      simp
  have hmeas : AEStronglyMeasurable (fun x : Coord => ((cpd j φ x : ℝ) : ℂ)) volume :=
    (Complex.continuous_ofReal.comp hcont).aestronglyMeasurable
  have hbound : ∀ᵐ x ∂(volume : Measure Coord), ‖((cpd j φ x : ℝ) : ℂ)‖ ≤ M :=
    Filter.Eventually.of_forall fun x => by
      have := hM x
      simpa [Complex.norm_real] using this
  rw [hfun]
  exact hbi.bdd_mul hmeas hbound

end UnforcedLeray.Short.IIb
