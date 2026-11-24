import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_3_5

/-!
# Part III-a, `PartIII-a:T21/2/3/5/1`: measurability of weakly differentiable functions

Source: `the November 2 reference manuscript` (SP) lines 2823-2826.
This proves `WeakCellMeas`: a function with a weak cell derivative in one direction `j`
(tested against the cylinder tests `B0579.IsCylTest`) is a.e. strongly measurable on the cell.

Method. For every point `x` there is a cylinder test `ψ` with `∂_j ψ(x) ≠ 0`:
`ψ = cos(2π/c (q - a)) · bump(η)` for `j = 0` (periodic in `q` with period `c`), and
`ψ = (η - η₀) · bump(η)` for `j = 1`. On the open set `{∂_j ψ ≠ 0}` one has
`φ = (φ ∂_j ψ) · (∂_j ψ)⁻¹` a.e., and `φ ∂_j ψ` is integrable on the cell. A countable subcover
of the open cover (second countability) and `aestronglyMeasurable_iUnion_iff` finish.
If `c ≤ 0` the cell `[-c/2, c/2) × ℝ` is empty.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- A smooth bump on `ℝ`, equal to `1` at `t₀` and vanishing at distance `≥ 2` from `t₀`. -/
lemma wcm_exists_bump (t₀ : ℝ) :
    ∃ B : ℝ → ℝ, ContDiff ℝ ∞ B ∧ B t₀ = 1 ∧ ∀ t, 2 ≤ dist t t₀ → B t = 0 := by
  let b : ContDiffBump t₀ :=
    { rIn := 1, rOut := 2, rIn_pos := one_pos, rIn_lt_rOut := one_lt_two }
  exact ⟨⇑b, b.contDiff, b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le),
    fun t ht => b.zero_of_le_dist ht⟩

/-- Partial derivative of a product of one-variable factors in the `q` direction. -/
lemma wcm_pd0 (F G : ℝ → ℝ) (x : ℝ × ℝ) {F' G' : ℝ}
    (hF : HasDerivAt F F' x.1) (hG : HasDerivAt G G' x.2) :
    UnforcedLeray.B0579.pd 0 (fun y => F y.1 * G y.2) x = F' * G x.2 := by
  have h1 : HasFDerivAt (fun y : ℝ × ℝ => F y.1) (F' • ContinuousLinearMap.fst ℝ ℝ ℝ) x :=
    hF.comp_hasFDerivAt x hasFDerivAt_fst
  have h2 : HasFDerivAt (fun y : ℝ × ℝ => G y.2) (G' • ContinuousLinearMap.snd ℝ ℝ ℝ) x :=
    hG.comp_hasFDerivAt x hasFDerivAt_snd
  have h3 : HasFDerivAt (fun y : ℝ × ℝ => F y.1 * G y.2)
      (F x.1 • (G' • ContinuousLinearMap.snd ℝ ℝ ℝ) + G x.2 • (F' • ContinuousLinearMap.fst ℝ ℝ ℝ)) x :=
    h1.mul h2
  rw [UnforcedLeray.B0579.pd, h3.fderiv]
  simp [UnforcedLeray.B0579.dir] <;> ring

/-- Partial derivative of a function of `η` alone in the `η` direction. -/
lemma wcm_pd1 (G : ℝ → ℝ) (x : ℝ × ℝ) {G' : ℝ} (hG : HasDerivAt G G' x.2) :
    UnforcedLeray.B0579.pd 1 (fun y => G y.2) x = G' := by
  have h2 : HasFDerivAt (fun y : ℝ × ℝ => G y.2) (G' • ContinuousLinearMap.snd ℝ ℝ ℝ) x :=
    hG.comp_hasFDerivAt x hasFDerivAt_snd
  rw [UnforcedLeray.B0579.pd, h2.fderiv]
  simp [UnforcedLeray.B0579.dir]

lemma wcm_test0 (c : ℝ) (hc : 0 < c) (x : ℝ × ℝ) :
    ∃ ψ : ℝ × ℝ → ℝ, UnforcedLeray.B0579.IsCylTest c ψ ∧ UnforcedLeray.B0579.pd 0 ψ x ≠ 0 := by
  obtain ⟨B, hBc, hB1, hBz⟩ := wcm_exists_bump x.2
  have hBd : HasDerivAt B (deriv B x.2) x.2 :=
    ((hBc.differentiable (by simp)) x.2).hasDerivAt
  have hc0 : c ≠ 0 := hc.ne'
  refine ⟨fun y => Real.cos (2 * Real.pi / c * (y.1 - (x.1 - c / 4))) * B y.2, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · exact (Real.contDiff_cos.comp (contDiff_const.mul (contDiff_fst.sub contDiff_const))).mul
        (hBc.comp contDiff_snd)
    · intro y
      show Real.cos (2 * Real.pi / c * (y.1 + c - (x.1 - c / 4))) * B y.2
        = Real.cos (2 * Real.pi / c * (y.1 - (x.1 - c / 4))) * B y.2
      have h : 2 * Real.pi / c * (y.1 + c - (x.1 - c / 4))
          = 2 * Real.pi / c * (y.1 - (x.1 - c / 4)) + 2 * Real.pi := by
        field_simp
        ring
      rw [h, Real.cos_add_two_pi]
    · refine ⟨|x.2| + 2, fun y hy => ?_⟩
      have h2 : 2 ≤ dist y.2 x.2 := by
        rw [Real.dist_eq]
        have := abs_sub_abs_le_abs_sub y.2 x.2
        linarith
      show Real.cos _ * B y.2 = 0
      rw [hBz _ h2, mul_zero]
  · have hF : HasDerivAt (fun q : ℝ => Real.cos (2 * Real.pi / c * (q - (x.1 - c / 4))))
        (-Real.sin (2 * Real.pi / c * (x.1 - (x.1 - c / 4))) * (2 * Real.pi / c * 1)) x.1 := by
      have h1 : HasDerivAt (fun q : ℝ => 2 * Real.pi / c * (q - (x.1 - c / 4)))
          (2 * Real.pi / c * 1) x.1 :=
        ((hasDerivAt_id' x.1).sub_const (x.1 - c / 4)).const_mul _
      exact h1.cos
    have key : UnforcedLeray.B0579.pd 0
        (fun y => Real.cos (2 * Real.pi / c * (y.1 - (x.1 - c / 4))) * B y.2) x
        = (-Real.sin (2 * Real.pi / c * (x.1 - (x.1 - c / 4))) * (2 * Real.pi / c * 1)) * B x.2 :=
      wcm_pd0 _ _ x hF hBd
    have hsin : Real.sin (2 * Real.pi / c * (x.1 - (x.1 - c / 4))) = 1 := by
      have e : 2 * Real.pi / c * (x.1 - (x.1 - c / 4)) = Real.pi / 2 := by
        field_simp
        ring
      rw [e, Real.sin_pi_div_two]
    have hpos : 0 < 2 * Real.pi / c := by positivity
    rw [key, hB1, hsin]
    intro h
    linarith

lemma wcm_test1 (c : ℝ) (hc : 0 < c) (x : ℝ × ℝ) :
    ∃ ψ : ℝ × ℝ → ℝ, UnforcedLeray.B0579.IsCylTest c ψ ∧ UnforcedLeray.B0579.pd 1 ψ x ≠ 0 := by
  obtain ⟨B, hBc, hB1, hBz⟩ := wcm_exists_bump x.2
  have hBd : HasDerivAt B (deriv B x.2) x.2 :=
    ((hBc.differentiable (by simp)) x.2).hasDerivAt
  have hGd : HasDerivAt (fun t : ℝ => (t - x.2) * B t) 1 x.2 := by
    have h := ((hasDerivAt_id' x.2).sub_const x.2).mul hBd
    refine h.congr_deriv ?_
    rw [hB1]
    ring
  refine ⟨fun y => (y.2 - x.2) * B y.2, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · exact (contDiff_snd.sub contDiff_const).mul (hBc.comp contDiff_snd)
    · intro y
      rfl
    · refine ⟨|x.2| + 2, fun y hy => ?_⟩
      have h2 : 2 ≤ dist y.2 x.2 := by
        rw [Real.dist_eq]
        have := abs_sub_abs_le_abs_sub y.2 x.2
        linarith
      show (y.2 - x.2) * B y.2 = 0
      rw [hBz _ h2, mul_zero]
  · have key : UnforcedLeray.B0579.pd 1 (fun y => (y.2 - x.2) * B y.2) x = 1 :=
      wcm_pd1 (fun t : ℝ => (t - x.2) * B t) x hGd
    rw [key]
    exact one_ne_zero

lemma wcm_test (j : Fin 2) (c : ℝ) (hc : 0 < c) (x : ℝ × ℝ) :
    ∃ ψ : ℝ × ℝ → ℝ, UnforcedLeray.B0579.IsCylTest c ψ ∧ UnforcedLeray.B0579.pd j ψ x ≠ 0 := by
  fin_cases j
  · exact wcm_test0 c hc x
  · exact wcm_test1 c hc x

/-- **Measurability of weakly differentiable functions** (SP 2823-2826). -/
theorem weakCellMeas : WeakCellMeas := by
  intro c j φ g hφ
  obtain ⟨hI, -⟩ := hφ
  by_cases hc : 0 < c
  · choose ψ hψt hψne using fun x : ℝ × ℝ => wcm_test j c hc x
    have hV : ∀ x : ℝ × ℝ, {z : ℝ × ℝ | UnforcedLeray.B0579.pd j (ψ x) z ≠ 0} ∈ 𝓝 x := by
      intro x
      exact ((hψt x).pd j).continuous.continuousAt.eventually_ne (hψne x)
    obtain ⟨s, hsc, hcov⟩ := TopologicalSpace.countable_cover_nhds hV
    haveI : Countable s := hsc.to_subtype
    have hpiece : ∀ x ∈ s, AEStronglyMeasurable φ
        (volume.restrict (B0579.cell c ∩ {z : ℝ × ℝ | UnforcedLeray.B0579.pd j (ψ x) z ≠ 0})) := by
      intro x _
      have hpc : Continuous (UnforcedLeray.B0579.pd j (ψ x)) := ((hψt x).pd j).continuous
      have hpm : Measurable (UnforcedLeray.B0579.pd j (ψ x)) := hpc.measurable
      have hmeasSet : MeasurableSet
          (B0579.cell c ∩ {z : ℝ × ℝ | UnforcedLeray.B0579.pd j (ψ x) z ≠ 0}) :=
        (B0579.measurableSet_cell c).inter (hpm (MeasurableSet.compl (measurableSet_singleton 0)))
      have hint : IntegrableOn (fun z => φ z * ((UnforcedLeray.B0579.pd j (ψ x) z : ℝ) : ℂ))
          (B0579.cell c) :=
        (hI (ψ x) (hψt x)).1
      have hmeasφ : AEStronglyMeasurable (fun z => φ z * ((UnforcedLeray.B0579.pd j (ψ x) z : ℝ) : ℂ))
          (volume.restrict (B0579.cell c ∩ {z : ℝ × ℝ | UnforcedLeray.B0579.pd j (ψ x) z ≠ 0})) :=
        hint.aestronglyMeasurable.mono_set Set.inter_subset_left
      have hinv : AEStronglyMeasurable
          (fun z => (((UnforcedLeray.B0579.pd j (ψ x) z)⁻¹ : ℝ) : ℂ))
          (volume.restrict (B0579.cell c ∩ {z : ℝ × ℝ | UnforcedLeray.B0579.pd j (ψ x) z ≠ 0})) :=
        (Complex.measurable_ofReal.comp hpm.inv).aestronglyMeasurable
      refine (hmeasφ.mul hinv).congr ?_
      refine ae_restrict_of_forall_mem hmeasSet ?_
      intro z hz
      have hz0 : UnforcedLeray.B0579.pd j (ψ x) z ≠ 0 := hz.2
      have h1 : ((UnforcedLeray.B0579.pd j (ψ x) z : ℝ) : ℂ)
          * (((UnforcedLeray.B0579.pd j (ψ x) z)⁻¹ : ℝ) : ℂ) = 1 := by
        rw [← Complex.ofReal_mul, mul_inv_cancel₀ hz0, Complex.ofReal_one]
      show φ z * ((UnforcedLeray.B0579.pd j (ψ x) z : ℝ) : ℂ)
          * (((UnforcedLeray.B0579.pd j (ψ x) z)⁻¹ : ℝ) : ℂ) = φ z
      linear_combination (φ z) * h1
    have hsub : B0579.cell c ⊆
        ⋃ i : s, (B0579.cell c ∩ {z : ℝ × ℝ | UnforcedLeray.B0579.pd j (ψ i) z ≠ 0}) := by
      intro z hz
      have hz' : z ∈ ⋃ x ∈ s, {w : ℝ × ℝ | UnforcedLeray.B0579.pd j (ψ x) w ≠ 0} := by
        rw [show (⋃ x ∈ s, {w : ℝ × ℝ | UnforcedLeray.B0579.pd j (ψ x) w ≠ 0}) = univ from hcov]
        exact Set.mem_univ z
      obtain ⟨x, hx, hzx⟩ := Set.mem_iUnion₂.mp hz'
      exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hz, hzx⟩
    have hU : AEStronglyMeasurable φ
        (volume.restrict (⋃ i : s, (B0579.cell c ∩ {z : ℝ × ℝ | UnforcedLeray.B0579.pd j (ψ i) z ≠ 0}))) :=
      aestronglyMeasurable_iUnion_iff.mpr (fun i => hpiece i.1 i.2)
    exact hU.mono_set hsub
  · have hc' : c ≤ 0 := not_lt.mp hc
    have hlt : ¬ (-(c / 2) < c / 2) := by
      intro h
      linarith
    have hE : B0579.cell c = ∅ := by
      unfold B0579.cell
      rw [Set.Ico_eq_empty hlt, Set.empty_prod]
    rw [hE, MeasureTheory.Measure.restrict_empty]
    exact aestronglyMeasurable_zero_measure φ

end UnforcedLeray.Short.IIIa
